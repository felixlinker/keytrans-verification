package client

import (
	"crypto/sha256"
	"errors"

	//@ "math"

	//@ "github.com/felixlinker/keytrans-verification/pkg/arb"
	"github.com/felixlinker/keytrans-verification/pkg/crypto"
	"github.com/felixlinker/keytrans-verification/pkg/proofs"
	"github.com/felixlinker/keytrans-verification/pkg/trees"
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
pred RootHashesInv(hashes []*[sha256.Size]byte) {
	forall i int :: { &hashes[i] } 0 <= i && i < len(hashes) ==> acc(&hashes[i]) && utils.BytesMem(hashes[i][:])
}

ghost
requires acc(RootHashesInv(hashes), _)
requires 0 <= idx && idx < len(hashes)
decreases
pure func GetRootHashContent(hashes []*[sha256.Size]byte, idx int) seq[byte] {
	return unfolding acc(RootHashesInv(hashes), _) in utils.GetBytesContent(hashes[idx][:])
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
	acc(s.Opening) && acc(s.Value.Inv())
}
@*/

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
	// @ unfold acc(utils.BytesMem(query.Label))
	label := make([]byte, len(query.Label))
	copy(label, query.Label /*@, perm(1/2) @*/)
	// @ fold acc(utils.BytesMem(query.Label))
	// @ fold acc(query.Inv())

	// Phase 1: UpdateView
	// @ unfold acc(resp.Inv())
	// @ unfold acc(resp.Search.Inv())

	fth := resp.Full_tree_head
	// @ unfold acc(fth.Inv())
	if fth.headType == FullTreeHeadUpdated {
		err = st.UpdateView( /*@ unfolding acc(fth.Tree_head.Inv()) in @*/ fth.Tree_head.Tree_size, resp.Search.Timestamps, resp.Search.Inclusion /*@, perm(1/2) @*/)
	}
	// @ fold acc(fth.Inv())

	// Phase 2: Validation checks (resp.Inv() still unfolded)
	if err == nil && resp.Version == nil {
		err = errors.New("no version provided")
	}
	if err == nil {
		// @ assert resp.Version != nil // sanity check
		// TODO: Limitation by Gobra
		// @ assume 0 <= *resp.Version
		ladderIndices /*@, idx @*/ := proofs.FullBinaryLadderSteps(uint64(*resp.Version) /*@, 0 @*/)
		if len(resp.Binary_ladder) != len(ladderIndices) {
			err = errors.New("length of binary ladder does not match greatest version")
		}
	}

	// Phase 3: Build prefix pts
	var lookups *trees.Lookups
	if err == nil {
		// @ unfold acc(st.Inv())
		// @ unfold acc(st.Config.Inv())
		lookups, err = trees.MkLookups(label, *resp.Version, st.Config.VrfPublicKey, resp.Binary_ladder /*@, perm(1/2) @*/)
		// @ fold acc(st.Config.Inv())
		// @ fold acc(st.Inv())
	}

	var pts []*trees.Prefix
	if err == nil {
		// @ unfold acc(st.Inv())
		// @ unfold acc(st.Config.Inv())
		err = proofs.PullLeaves(resp.Search.Prefix_proofs, resp.Binary_ladder, st.Config.VrfPublicKey, label, *resp.Version /*@, perm(1/2) @*/)
		// @ fold acc(st.Config.Inv())
		// @ fold acc(st.Inv())
	}
	if err == nil {
		pts, err = st.MkPrefixes(resp.Search.Prefix_proofs /*@, perm(1/2) @*/)
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
// @ requires acc(trees.PrefixesInv(prefixTrees), p)
// @ ensures noPerm < rp
// @ ensures acc(trees.PrefixesInv(prefixTrees), rp)
// @ requires  0 < len(prefixTrees) // && len(prefixTrees) <= math.MaxUint64
// hyper-postcondition:
// // @ ensures   err == nil &&
// // @	low(len(prefixTrees)) && low(query.LabelContent()) &&
// // @	low(GetRootHashContent(prefixRootHash, len(prefixTrees)-1)) ==>
// // @		unfolding acc(resp.Inv(), p) in low(*resp.Version)
// // @ decreases
// returns an error if verification fails and a non-nil map entry if an entry needs to be monitored
func VerifyLatestKey(cv *crypto.CommitmentValue, lookups *trees.Lookups, prefixTrees []*trees.Prefix /*@, ghost p perm @*/) (entry *MonitoringMapEntry, err error /*@, ghost rp perm @*/) {
	// we use `err` to skip loop iterations instead of
	// returning early, which is not yet supported by Gobra's hypermode.

	var commitment *[sha256.Size]byte
	// @ ghost rp = p
	// @ invariant noPerm < rp && rp <= p
	// @ invariant acc(cv.Inv(), p) && acc(lookups.Inv(), p)
	// @ invariant acc(trees.PrefixesInv(prefixTrees), rp)
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
		//@ unfold acc(trees.PrefixesInv(prefixTrees), rp)
		commitment, err /*@, rp @*/ = lookups.CheckPrefixTree(prefixTrees[idx] /*@, rp @*/)
		if commitment != nil && err != nil {
			if !crypto.VerifyCommitmentValue(utils.FromDigest(*commitment), cv /*@, rp @*/) {
				err = errors.New("commitments did not match")
			}
		}
		//@ fold acc(trees.PrefixesInv(prefixTrees), rp)
	}

	if commitment == nil {
		err = errors.New("no key commitment in last entry")
	}

	return
}
