package client

import (
	"errors"

	//@ "math"

	//@ "github.com/felixlinker/keytrans-verification/pkg/arb"
	"github.com/felixlinker/keytrans-verification/pkg/crypto"
	"github.com/felixlinker/keytrans-verification/pkg/proofs"
	"github.com/felixlinker/keytrans-verification/pkg/search"
	"github.com/felixlinker/keytrans-verification/pkg/trees/log"
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
	Opening        []byte
	Value          *crypto.UpdateValue // value associated with queried label
	Binary_ladder  []*proofs.BinaryLadderStep
	Search         *proofs.CombinedTreeProof
}

/*@
pred (s *SearchResponse) Inv() {
	acc(s) && acc(s.Full_tree_head.Inv()) &&
	(s.Version != nil ==> acc(s.Version)) &&
	proofs.BinaryLadderStepsInv(s.Binary_ladder) && acc(s.Search.Inv()) &&
	acc(utils.BytesMem(s.Opening)) && acc(s.Value.Inv())
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
// TODO: VerifyLatest is trusted while the ProofReader it uses has trusted
// bodies; its specification is unchanged.
// @ trusted
func (st *UserState) VerifyLatest(query *SearchRequest, resp *SearchResponse) (res *crypto.UpdateValue, err error) {
	// we use `err` to skip later phases instead of returning early, which is not yet supported by Gobra's hypermode.
	label := utils.Copy(query.Label /*@, perm(1/2) @*/)

	// Phase 1: Set up the reader over the combined tree proof
	newSize := st.Tree.GetSize( /*@ perm(1/2) @*/ )
	if resp.Full_tree_head != nil && resp.Full_tree_head.Tree_head != nil {
		newSize = resp.Full_tree_head.Tree_head.Tree_size
	}
	var r *ProofReader
	if resp.Search == nil {
		err = errors.New("no combined tree proof provided")
	} else {
		var retained []knownEntry
		if retained, err = st.retained(); err == nil {
			r = NewProofReader(resp.Search, newSize, retained)
			err = r.Err()
		}
	}

	// Phase 2: Validation checks
	if err == nil && resp.Version == nil {
		err = errors.New("no version provided")
	}
	if err == nil {
		ladderIndices /*@, idx @*/ := proofs.FullBinaryLadderSteps(*resp.Version /*@, 0 @*/)
		if len(resp.Binary_ladder) != len(ladderIndices) {
			err = errors.New("length of binary ladder does not match greatest version")
		}
	}

	// Phase 3: Lookups and prefix proof leaves
	var lookups *search.Lookups
	if err == nil {
		lookups, err = search.MkLookups(label, *resp.Version, st.Config.VrfPublicKey, resp.Binary_ladder /*@, perm(1/2) @*/)
	}
	if err == nil {
		err = proofs.PullLeaves(resp.Search.Prefix_proofs, resp.Binary_ladder, st.Config.VrfPublicKey, label, *resp.Version /*@, perm(1/2) @*/)
	}

	// Phase 4: Update view, then greatest-version search, then finish the proof
	var newTree *log.Tree
	if err == nil {
		newTree, err = st.UpdateView(r, newSize, resp.Search.Inclusion)
	}
	var pts []*prefix.Tree
	if err == nil {
		pts = greatestVersionSearch(r, st.Config.ReasonableMonitoringWindow)
		err = r.Err()
	}
	var entries []knownEntry
	if err == nil {
		entries = r.Finish()
		err = r.Err()
	}
	if err == nil {
		err = checkLeaves(newTree, entries)
	}

	// Phase 5: VerifyLatestKey
	if err == nil && len(pts) == 0 {
		err = errors.New("no prefix proofs")
	}
	if err == nil {
		// TODO: Monitoring
		cv /*@@@*/ := crypto.CommitmentValue{
			Opening: resp.Opening,
			Label:   label,
			Version: *resp.Version,
			Update:  resp.Value,
		}
		_, err = VerifyLatestKey(&cv, lookups, pts /*@, perm(1/2) @*/)
	}

	// Phase 6: Commit state only once everything has been verified
	if err == nil {
		st.Tree = newTree
		st.Frontier_timestamps = frontierTimestamps(r)
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
// @ preserves acc(prefix.PrefixesInv(prefixTrees), p)
// @ requires  0 < len(prefixTrees) // && len(prefixTrees) <= math.MaxUint64
// hyper-postcondition:
// // @ ensures   err == nil &&
// // @	low(len(prefixTrees)) && low(query.LabelContent()) &&
// // @	low(GetRootHashContent(prefixRootHash, len(prefixTrees)-1)) ==>
// // @		unfolding acc(resp.Inv(), p) in low(*resp.Version)
// // @ decreases
// returns an error if verification fails and a non-nil map entry if an entry needs to be monitored
func VerifyLatestKey(cv *crypto.CommitmentValue, lookups *search.Lookups, prefixTrees []*prefix.Tree /*@, ghost p perm @*/) (entry *MonitoringMapEntry, err error) {
	// we use `err` to skip loop iterations instead of
	// returning early, which is not yet supported by Gobra's hypermode.

	var commitment []byte
	// @ invariant acc(cv.Inv(), p) && acc(lookups.Inv(), p)
	// @ invariant acc(prefix.PrefixesInv(prefixTrees), p)
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
		// @ unfold acc(prefix.PrefixesInv(prefixTrees), p)
		commitment, err = lookups.CheckPrefixTree(prefixTrees[idx] /*@, p/2 @*/)
		if commitment != nil && err == nil {
			if !crypto.VerifyCommitmentValue(commitment, cv /*@, p @*/) {
				err = errors.New("commitments did not match")
			}
		}
		// @ fold acc(prefix.PrefixesInv(prefixTrees), p)
	}

	if commitment == nil {
		err = errors.New("no key commitment in last entry")
	}

	return
}
