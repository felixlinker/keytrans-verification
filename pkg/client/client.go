package client

import (
	"crypto/sha256"
	"errors"

	//@ "math"

	//@ "github.com/felixlinker/keytrans-verification/pkg/arb"
	"github.com/felixlinker/keytrans-verification/pkg/crypto"
	"github.com/felixlinker/keytrans-verification/pkg/prefixtree"
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
// PrefixTreesInv encapsulates per-element permissions for prefix tree slices.
// Reduces quantifier count in the SIF product program.
pred PrefixTreesInv(trees []prefixtree.PT) {
		forall i int :: { &trees[i] } 0 <= i && i < len(trees) ==> acc(&trees[i]) && trees[i] != nil && trees[i].Inv()
}

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
	Value          *proofs.UpdateValue // value associated with queried label
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
func (st *UserState) VerifyLatest(query *SearchRequest, resp *SearchResponse) (res *proofs.UpdateValue, err error) {
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
		lookups, err = trees.MkLookups(label, *resp.Version, st.Config.SignaturePublicKey, resp.Binary_ladder /*@, perm(1/2) @*/)
		// @ fold acc(st.Config.Inv())
		// @ fold acc(st.Inv())
	}

	var pts []*trees.Prefix
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

// returns the full binary ladder together with tstar for the targets of the two
// executions (if both executions are active).
// @ requires 0 <= target
// @ ensures  proofs.BinaryLadderInv(r)
// @ ensures  0 <= idx && idx < len(r)
// @ ensures  proofs.IstStar(r, target, rel(target, 1), idx) // this is the same as wrapping it in `rel(_, 0)`
// @ ensures  rel(proofs.IstStar(r, target, rel(target, 0), idx), 1)
// @ decreases
func FullBinaryLadderSteps_with_tstar(target uint64) (r []uint64 /*@, ghost idx int @*/) {
	// the following ghost if stmt avoids an issue in the encoding where we
	// access `rel(target, 1)` before it is available (as it gets first copied
	// into a local variable)
	//@ ghost if true {} // acts like a "barrier" in the encoding
	/*@
	// t2 should be the other execution's target (if both are active).
	// we obtain the other execution's target by checking whether "this" execution's target
	// is equal to the first execution's target. This is an indirect way of figuring out
	// whether we currently look at the first or second execution:
	t2 := target == rel(target, 0) ? rel(target, 1) : rel(target, 0)
	ghost if t2 < 0 {
		t2 = 0 // make sure that t2 is non-negative even if the other execution is not active
	}
	@*/
	return proofs.FullBinaryLadderSteps(target /*@, t2 @*/)
}

// alternative implementation for `FullBinaryLadderSteps_with_tstar` based on universal introduction
// but deriving the same property about tstar
// @ requires 0 <= target
// @ ensures  proofs.BinaryLadderInv(r)
// @ ensures  0 <= idx && idx < len(r)
// @ ensures  proofs.IstStar(r, target, rel(target, 1), idx) // this is the same as wrapping it in `rel(_, 0)`
// @ ensures  rel(proofs.IstStar(r, target, rel(target, 0), idx), 1)
// @ decreases
func FullBinaryLadderSteps_with_tstar_alternative(target uint64) (r []uint64 /*@, ghost idx int @*/) {
	// let t2 be arbitrary:
	//@ t2 := arb.GetArbUint64()
	r /*@, idx @*/ = proofs.FullBinaryLadderSteps(target /*@, 0 <= t2 ? t2 : 0 @*/)

	// since t2 is arbitrary, termination of `FullBinaryLadderSteps` does not depend on t2, and
	// `r` is the same for all t2, we can perform a universal introduction on t2:
	//@ assert 0 <= t2 ==> proofs.IstStar(r, target, t2, idx)
	//@ assume forall t2 uint64 :: { proofs.IstStar(r, target, t2, idx) } 0 <= t2 ==> proofs.IstStar(r, target, t2, idx)
	// since `proofs.IstStar(r, target, t2, idx)` holds for all non-negative t2, it also holds for `rel(target, 1)` as
	// stated in the postcondition.
	return
}

// CheckGreatest iterates over the binary ladder steps and queries the prefix
// tree at each step to check consistency with t being the greatest version.
// Returns:
//
//	-1: a version at or below t is absent (gap detected)
//	 0: all steps are consistent (t is the greatest version)
//	+1: a version above t is present (greater version exists)
//
// @ requires  noPerm < p
// @ requires  prefixTree != nil
// @ preserves acc(prefixTree.Inv(), p)
// @ preserves acc(utils.BytesMem(label), p)
// @ preserves acc(utils.BytesMem(rootHash), p)
// @ requires  0 <= t
// @ ensures   err == nil ==> -1 <= res && res <= 1
// @ ensures   err == nil && res == 0 &&
// @ 	low(utils.GetBytesContent(label)) &&
// @ 	low(utils.GetBytesContent(rootHash)) ==>
// @ 		low(t)
// @ decreases
func CheckGreatest(prefixTree prefixtree.PT, label []byte, t uint64, rootHash []byte /*@, ghost p perm @*/) (res int, err error) {
	steps /*@, tStarIdx @*/ := FullBinaryLadderSteps_with_tstar(t)
	//@ unfold proofs.BinaryLadderInv(steps)

	determined := false // this flag encodes early returns, which are not yet supported by Gobra's hypermode
	//@ tStar := steps[tStarIdx]

	// after visiting `tStarIdx` and successfully passing all checks (i.e., `!determined`), one of the following two cases will hold.
	// as desired, these two conditions are contradictory unless `low(t)` holds, which establishes the postcondition.
	//@ labelSeq, rootHashSeq := utils.GetBytesContent(label), utils.GetBytesContent(rootHash)
	//@ non_incl_expected :=  prefixtree.GetCommitmentExists(labelSeq, tStar, rootHashSeq) && tStar <= t
	//@ incl_expected 	  := !prefixtree.GetCommitmentExists(labelSeq, tStar, rootHashSeq) &&     t  <  tStar

	//@ invariant acc(prefixTree.Inv(), p/2)
	//@ invariant acc(utils.BytesMem(rootHash), p/2) && rootHashSeq == utils.GetBytesContent(rootHash)
	//@ invariant acc(utils.BytesMem(label), p/2) && labelSeq == utils.GetBytesContent(label)
	//@ invariant acc(steps, 1/2)
	//@ invariant forall i int :: {steps[i]} 0 <= i && i < len(steps) ==> 0 <= steps[i]
	//@ invariant 0 <= idx && idx <= len(steps)
	//@ invariant 0 <= tStarIdx && tStarIdx < len(steps)
	//@ invariant tStar == steps[tStarIdx]
	//@ invariant determined != (res == 0 && err == nil)
	//@ invariant err == nil ==> -1 <= res && res <= 1
	//@ invariant tStarIdx < idx && !determined ==> non_incl_expected || incl_expected
	//@ decreases len(steps) - idx
	for idx := 0; idx < len(steps); idx++ {
		if !determined {
			step := steps[idx]
			var commitment []byte
			commitment, err = prefixTree.GetCommitment(label, step, rootHash /*@, p/4 @*/)
			if err != nil {
				if !determined {
					res = 404
					determined = true
				}
			} else {
				incl := commitment != nil
				if !incl && step <= t {
					res = -1
					determined = true
				}
				if incl && t < step {
					res = 1
					determined = true
				}
			}
		}
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
