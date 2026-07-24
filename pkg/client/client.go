package client

import (
	"errors"

	//@ "math"

	//@ "github.com/felixlinker/keytrans-verification/pkg/arb"
	"github.com/felixlinker/keytrans-verification/pkg/crypto"
	"github.com/felixlinker/keytrans-verification/pkg/proofs"
	"github.com/felixlinker/keytrans-verification/pkg/trees/prefix"
	"github.com/felixlinker/keytrans-verification/pkg/utils"
	//@ utilsrel "github.com/felixlinker/keytrans-verification/pkg/utils-rel"
)

// Package client implements the client-side verification logic for key
// transparency. It provides functions to verify that a transparency log
// correctly reports the latest version of a user's key, using binary ladder
// proofs and prefix tree lookups.
//
// The core verification functions are:
//   - VerifyLatest: verifies a search response and checks that the returned
//     version is the latest, combining update verification with a greatest
//     version check.
//   - VerifyLatestKey: verifies a claimed greatest version against all frontier
//     nodes of the implicit binary search tree, ensuring no greater version
//     exists in the log.
//   - CheckGreatest: checks a single prefix tree against the binary ladder
//     steps to confirm consistency with the claimed greatest version.
//
// All exported verification functions carry Gobra specifications for formal
// verification of hyperproperties (information flow) in extended hyper mode.

// ##(--hyperMode extended --enableExperimentalHyperFeatures)

/*@
// RootHashesInv encapsulates per-element permissions for root hash slices.
pred RootHashesInv(hashes [][]byte) {
	forall i int :: { &hashes[i] } 0 <= i && i < len(hashes) ==> acc(&hashes[i]) && utils.BytesMem(hashes[i])
}

ghost
requires acc(RootHashesInv(hashes), _)
requires 0 <= idx && idx < len(hashes)
decreases
pure func GetRootHashContent(hashes [][]byte, idx int) seq[byte] {
	return unfolding acc(RootHashesInv(hashes), _) in utils.GetBytesContent(hashes[idx])
}
@*/

type SearchRequest struct {
	Last  *uint32
	Label []byte
	// TODO: optional<uint32> version
}

/*@
pred (s *SearchRequest) Inv() {
	acc(s) && (s.Last != nil ==> acc(s.Last)) && utils.BytesMem(s.Label)
}

ghost
requires acc(s.Inv(), _)
decreases
pure func (s *SearchRequest) LabelContent() seq[byte] {
	return unfolding acc(s.Inv(), _) in utils.GetBytesContent(s.Label)
}
@*/

type SearchResponse struct {
	// NOTE: Per spec, Version is a uint32, but we use a uint64 for internal
	// compatibility.
	Full_tree_head *FullTreeHead
	Version        *uint64
	Binary_ladder  []*proofs.BinaryLadderStep
	Search         *proofs.CombinedTreeProof
	Opening        []byte
	Value          *crypto.UpdateValue // value associated with queried label
}

/*@
pred (s *SearchResponse) Inv() {
	acc(s) && acc(s.Full_tree_head.Inv()) &&
	(s.Version != nil ==> acc(s.Version)) &&
	proofs.BinaryLadderStepsInv(s.Binary_ladder) && acc(s.Search.Inv()) &&
	acc(utils.BytesMem(s.Opening)) && acc(s.Value.Inv())
}
@*/

// @ requires noPerm < p
// @ requires acc(proofs.PrefixProofsInv(prfs)) && acc(proofs.BinaryLadderStepsInv(ladder))
// @ preserves acc(utils.BytesMem(label), p)
// @ preserves acc(st.Inv(), p)
// @ ensures err == nil ==> 0 < len(pts) && prefix.PrefixesInv(pts)
func (st *UserState) buildPrefixes(label []byte, version uint64, prfs []*proofs.PrefixProof, ladder []*proofs.BinaryLadderStep /*@, ghost p perm @*/) (pts []*prefix.Tree, err error) {
	// @ unfold acc(st.Inv(), p)
	// @ unfold acc(st.Config.Inv(), p)
	err = proofs.PullLeaves(prfs, ladder, st.Config.VrfPublicKey, label, version /*@, p/2 @*/)
	// @ fold acc(st.Config.Inv(), p)
	// @ fold acc(st.Inv(), p)
	if err == nil {
		pts, err = st.MkPrefixes(prfs /*@, p/2 @*/)
	}
	return
}

// @ requires acc(st.Inv())
// @ preserves acc(query.Inv())
// @ requires  acc(resp.Inv())
// @ ensures   err == nil ==> acc(st.Inv()) && acc(res.Inv())
// hyper-postcondition:
// // @ ensures   err == nil &&
// // @	low(query.LabelContent()) &&
// // @ 	(unfolding acc(resp.Inv(), p) in low(resp.Full_tree_head.Tree_head.Tree_size) && low(len(resp.Search.Prefix_proofs))) ==>
// // @		unfolding acc(resp.Inv(), p) in resp.Version != nil && low(*resp.Version)
func (st *UserState) VerifyLatest(query *SearchRequest, resp *SearchResponse) (res *crypto.UpdateValue, err error) {
	// we use `err` to skip later phases instead of returning early, which is not yet supported by Gobra's hypermode.

	// @ unfold acc(query.Inv())
	label := utils.Copy(query.Label /*@, perm(1/2) @*/)
	// @ fold acc(query.Inv())

	// Phase 1: UpdateView
	// @ unfold acc(resp.Inv())
	// @ unfold acc(resp.Search.Inv())

	if /*@ unfolding acc(resp.Full_tree_head.Inv()) in @*/ resp.Full_tree_head.Tree_head != nil {
		newTreeSize := /*@ unfolding acc(resp.Full_tree_head.Inv()) in unfolding acc(resp.Full_tree_head.Tree_head.Inv()) in @*/ resp.Full_tree_head.Tree_head.Tree_size
		err = st.UpdateView(newTreeSize, resp.Search.Timestamps, resp.Search.Inclusion /*@, perm(1/2) @*/)
	}

	// Phase 2: Validation checks (resp.Inv() still unfolded)
	if err == nil && resp.Version == nil {
		err = errors.New("no version provided")
	}
	if err == nil {
		// @ assert resp.Version != nil // sanity check
		// @ assume 0 <= *resp.Version
		ladderIndices /*@, idx @*/ := proofs.FullBinaryLadderSteps(*resp.Version /*@, 0 @*/)
		if len(resp.Binary_ladder) != len(ladderIndices) {
			err = errors.New("length of binary ladder does not match greatest version")
		}
	}

	// Phase 3: Build prefix pts
	var lookups *prefix.Lookups
	if err == nil {
		// @ unfold acc(st.Inv())
		// @ unfold acc(st.Config.Inv())
		lookups, err = prefix.MkLookups(label, *resp.Version, st.Config.VrfPublicKey, resp.Binary_ladder /*@, perm(1/2) @*/)
		// @ fold acc(st.Config.Inv())
		// @ fold acc(st.Inv())
	}

	var pts []*prefix.Tree
	if err == nil {
		pts, err = st.buildPrefixes(label, *resp.Version, resp.Search.Prefix_proofs, resp.Binary_ladder /*@, perm(1/2) @*/)
	}

	// Phase 4: VerifyLatestKey
	if err == nil {
		// TODO: Monitoring
		cv /*@@@*/ := crypto.CommitmentValue{
			Opening: resp.Opening,
			Label:   label,
			Version: *resp.Version,
			Update:  resp.Value,
		}
		// @ fold acc(cv.Inv())
		// @ ghost var p perm
		_, err /*@, p @*/ = VerifyLatestKey(&cv, lookups, pts /*@, perm(1/2) @*/)
		// @ unfold acc(cv.Inv())
	}

	// Phase 5: Single return
	if err == nil {
		res = resp.Value
	}
	return
}

type MonitoringMapEntry struct {
	Position uint64
	Version  uint64
}

// @ requires  noPerm < p
// @ preserves acc(cv.Inv(), p)
// @ preserves acc(lookups.Inv(), p)
// @ requires acc(prefix.PrefixesInv(prefixTrees), p)
// @ ensures noPerm < rp
// @ ensures acc(prefix.PrefixesInv(prefixTrees), rp)
// @ requires  0 < len(prefixTrees) // && len(prefixTrees) <= math.MaxUint64
// hyper-postcondition:
// // @ ensures   err == nil &&
// // @	low(len(prefixTrees)) && low(query.LabelContent()) &&
// // @	low(GetRootHashContent(prefixRootHash, len(prefixTrees)-1)) ==>
// // @		unfolding acc(resp.Inv(), p) in low(*resp.Version)
// // @ decreases
// returns an error if verification fails and a non-nil map entry if an entry needs to be monitored
func VerifyLatestKey(cv *crypto.CommitmentValue, lookups *prefix.Lookups, prefixTrees []*prefix.Tree /*@, ghost p perm @*/) (entry *MonitoringMapEntry, err error /*@, ghost rp perm @*/) {
	// we use `err` to skip loop iterations instead of
	// returning early, which is not yet supported by Gobra's hypermode.

	var commitment []byte
	// @ ghost rp = p
	// @ invariant noPerm < rp && rp <= p
	// @ invariant acc(cv.Inv(), p) && acc(lookups.Inv(), p)
	// @ invariant acc(prefix.PrefixesInv(prefixTrees), rp)
	// @ invariant 0 <= idx && idx <= len(prefixTrees)
	// hyper-invariants:
	// // @ invariant low(len(prefixTrees)) ==> low(idx)
	// // @ invariant low(len(prefixTrees)) && idx == len(prefixTrees) && err == nil &&
	// // @ 	low(query.LabelContent()) &&
	// // @ 	low(GetRootHashContent(prefixRootHash, len(prefixTrees)-1)) ==>
	// // @			low(t)
	// // @ decreases len(prefixTrees) - idx
	for idx := 0; idx < len(prefixTrees) && err == nil; idx++ {
		// TODO: Check monitoring
		//@ unfold acc(prefix.PrefixesInv(prefixTrees), rp)
		commitment, err /*@, rp @*/ = lookups.CheckPrefixTree(prefixTrees[idx] /*@, rp @*/)
		if commitment != nil && err != nil {
			if !crypto.VerifyCommitmentValue(commitment, cv /*@, rp @*/) {
				err = errors.New("commitments did not match")
			}
		}
		//@ fold acc(prefix.PrefixesInv(prefixTrees), rp)
	}

	if commitment == nil {
		err = errors.New("no key commitment in last entry")
	}

	return
}
