package client

import (
	"crypto/sha256"
	"errors"

	//@ "github.com/felixlinker/keytrans-verification/pkg/arb"
	"github.com/felixlinker/keytrans-verification/pkg/prefixtree"
	"github.com/felixlinker/keytrans-verification/pkg/proofs"
	//@ "github.com/felixlinker/keytrans-verification/pkg/utils"
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
	forall i int :: { hashes[i] } 0 <= i && i < len(hashes) ==> acc(&hashes[i]) && utils.BytesMem(hashes[i][:])
}

ghost
requires acc(RootHashesInv(hashes), _)
requires 0 <= idx && idx < len(hashes)
decreases
pure func GetRootHashContent(hashes []*[sha256.Size]byte, idx int) seq[byte] {
	return unfolding acc(RootHashesInv(hashes), _) in utils.getContent(hashes[idx][:])
}
@*/

type TreeHead struct {
	Tree_size uint64
	Signature []byte
}

/*@
pred (t TreeHead) Inv() {
	acc(t.Signature)
}
@*/

type FullTreeHead struct {
	Tree_head TreeHead
	RootHash  []byte // Added RootHash for the prefixtree comparison if needed, currently a stub implementation
	// TODO: AuditorTreeHead auditor_tree_head
}

/*@
pred (f FullTreeHead) Inv() {
	f.Tree_head.Inv() && utils.BytesMem(f.RootHash)
}

ghost
decreases
requires acc(f.Inv(), _)
pure func (f FullTreeHead) Size() uint64 {
	return unfolding acc(f.Inv(), _) in f.Tree_head.Tree_size
}
@*/

type SearchRequest struct {
	Last  *uint32
	Label []byte
	// TODO: optional<uint32> version
}

/*@
pred (s SearchRequest) Inv() {
	acc(s.Last) && utils.BytesMem(s.Label)
}

ghost
requires acc(s.Inv(), _)
decreases
pure func (s SearchRequest) LabelContent() seq[byte] {
	return unfolding acc(s.Inv(), _) in utils.getContent(s.Label)
}
@*/

type SearchResponse struct {
	Full_tree_head FullTreeHead
	Version        *uint32
	Binary_ladder  []proofs.BinaryLadderStep
	Search         proofs.CombinedTreeProof
	Inclusion      proofs.InclusionProof
	Opening        []byte
	Value          proofs.UpdateValue // value associated with queried label
}

/*@
pred (s SearchResponse) Inv() {
	s.Full_tree_head.Inv() &&
	// `0 <= s.Version` holds trivially but Gobra currently
	// does not infer this property
	(s.Version != nil ==> acc(s.Version) && 0 <= *s.Version) &&
	acc(s.Binary_ladder) &&
	s.Search.Inv() &&
	s.Inclusion.Inv() &&
	acc(s.Opening) &&
	s.Value.Inv()
}
@*/

// @ requires noPerm < p
// @ preserves st.Inv()
// @ requires acc(config, p)
// @ requires acc(query.Inv(), p)
// @ requires unfolding acc(query.Inv(), p) in query.Label != nil
// @ requires low(query.LabelContent())
// @ requires acc(resp.Inv(), p)
// @ requires resp.Version != nil
// @ requires unfolding acc(resp.Inv(), p) in *resp.Version >= 0
// @ requires resp.Full_tree_head.RootHash != nil
// @ requires resp.Full_tree_head.Tree_head.Tree_size > 0
// @ requires resp.Full_tree_head.Tree_head.Tree_size <= uint64(len(resp.Search.Prefix_proofs))
// @ requires low(resp.Full_tree_head.Tree_head.Tree_size)
// @ requires low(len(resp.Search.Prefix_proofs))
// @ ensures err != nil ==> acc(resp.Inv(), p)
// @ ensures err == nil ==> acc(resp.Version, p) && low(*resp.Version)
// @ trusted // TODO: remove once we can verify the entire function
func (st *UserState) VerifyLatest(query SearchRequest, resp SearchResponse, config *Configuration /*@, ghost p perm @*/) (res *proofs.UpdateValue, err error) {
	// flag encoding early termination
	determined := false

	// Phase 1: UpdateView
	//@ unfold acc(resp.Inv(), p)
	err = st.UpdateView(resp.Full_tree_head, resp.Search /*@, p/2 @*/)
	if err != nil {
		determined = true
	}

	// Phase 2: Validation checks (resp.Inv() still unfolded)
	if !determined && resp.Version == nil {
		err = errors.New("no version provided")
		determined = true
	}
	if !determined && len(resp.Search.Prefix_roots) != 0 {
		err = errors.New("prefix roots provided")
		determined = true
	}
	if !determined {
		ladderIndices /*@, idx @*/ := proofs.FullBinaryLadderSteps(uint64(*resp.Version) /*@, 0 @*/)
		if len(resp.Binary_ladder) != len(ladderIndices) {
			err = errors.New("length of binary ladder does not match greatest version")
			determined = true
		}
	}

	// Phase 3: Build prefix trees
	n := len(resp.Search.Prefix_proofs)
	//@ fold acc(resp.Inv(), p)

	var trees []prefixtree.PT
	var rootHashes []*[sha256.Size]byte
	//@ ghost var rhContents seq[seq[byte]] = seq[seq[byte]]{}
	if !determined {
		trees, rootHashes, err = buildPrefixTrees(resp, n /*@, p @*/)
		if err != nil {
			determined = true
		} else {
			//@ rhContents = utilsrel.buildRootHashContents(rootHashes, n)
			//@ fold acc(RootHashesInv(rootHashes), p)
		}
	}

	// Phase 4: VerifyLatestKey
	decision := false
	if !determined {
		//@ unfold acc(resp.Inv(), p)
		//@ unfold acc(resp.Full_tree_head.Inv(), p)
		size := resp.Full_tree_head.Tree_head.Tree_size
		//@ assert size <= n
		//@ assert len(trees) == n && len(rootHashes) == n
		monitoringMap := make([]*MonitoringMapEntry, 0)
		var entry *MonitoringMapEntry
		decision, entry, err = VerifyLatestKey(trees, rootHashes, query, resp, config /*@, rhContents, p @*/)
		//@ unfold acc(query.Inv(), p)
		if entry != nil {
			monitoringMap = append( /*@ perm(1/2), @*/ monitoringMap, entry)
		}

		if !decision || err != nil {
			//@ fold acc(resp.Full_tree_head.Inv(), p)
			//@ fold acc(resp.Inv(), p)
			if err == nil {
				err = errors.New("Query response does not contain latest version")
			}
			determined = true
		}
	}

	// Phase 5: Single return
	if !determined && decision {
		// VerifyLatestKey ensures: err == nil && res ==> low(*resp.Version)
		// Don't fold resp.Inv() — keep acc(resp.Version, p) for postcondition
		//@ unfold acc(resp.Value.Inv(), p)
		res = &proofs.UpdateValue{Value: resp.Value.Value}
		//@ fold acc(resp.Value.Inv(), p)
		err = nil
	} else {
		res = nil
	}
	return res, err
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
// @ 	low(utils.getContent(label)) &&
// @ 	low(utils.getContent(rootHash)) ==>
// @ 		low(t)
// @ decreases
func CheckGreatest(prefixTree prefixtree.PT, label []byte, t uint64, rootHash []byte, size uint64 /*@, ghost p perm @*/) (res int, err error) {
	steps /*@, tStarIdx @*/ := FullBinaryLadderSteps_with_tstar(t)
	//@ unfold proofs.BinaryLadderInv(steps)

	determined := false // this flag encodes early returns, which are not yet supported by Gobra's hypermode
	//@ tStar := steps[tStarIdx]

	// after visiting `tStarIdx` and successfully passing all checks (i.e., `!determined`), one of the following two cases will hold.
	// as desired, these two conditions are contradictory unless `low(t)` holds, which establishes the postcondition.
	//@ labelSeq, rootHashSeq := utils.getContent(label), utils.getContent(rootHash)
	//@ non_incl_expected :=  prefixtree.GetCommitmentExists(labelSeq, tStar, rootHashSeq) && tStar <= t
	//@ incl_expected 	  := !prefixtree.GetCommitmentExists(labelSeq, tStar, rootHashSeq) &&     t  <  tStar

	//@ invariant acc(prefixTree.Inv(), p/2)
	//@ invariant acc(utils.BytesMem(rootHash), p/2) && rootHashSeq == utils.getContent(rootHash)
	//@ invariant acc(utils.BytesMem(label), p/2) && labelSeq == utils.getContent(label)
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
	Version  uint32
}

// @ requires  noPerm < p
// @ preserves acc(PrefixTreesInv(prefixTrees), p)
// @ preserves acc(RootHashesInv(prefixRootHash), p)
// @ requires  0 < len(prefixTrees) && len(prefixTrees) == len(prefixRootHash)
// @ preserves acc(query.Inv(), p)
// @ requires  acc(resp.Inv(), p)
// @ requires  unfolding acc(resp.Inv(), p) in resp.Version != nil
// @ preserves acc(config, p)
// @ ensures   acc(resp.Inv(), p)
// @ ensures   err == nil && entry != nil ==> acc(entry)
// hyper-postcondition:
// @ ensures   err == nil && res &&
// @	low(len(prefixTrees)) && low(query.LabelContent()) &&
// @	low(GetRootHashContent(prefixRootHash, len(prefixTrees)-1)) ==>
// @		unfolding acc(resp.Inv(), p) in low(*resp.Version)
// @ decreases
// returns a non-nil map entry if an entry needs to be monitored
func VerifyLatestKey(prefixTrees []prefixtree.PT, prefixRootHash []*[sha256.Size]byte, query SearchRequest, resp SearchResponse, monitorMap []MonitoringMapEntry, config *Configuration /*@, ghost p perm @*/) (res bool, entry *MonitoringMapEntry, err error) {
	size := uint64(len(prefixTrees))
	t := /*@ unfolding acc(resp.Inv(), p) in @*/ uint64(*resp.Version) // claimed greatest version
	searchTree := MkImplicitBinarySearchTree(uint64(len(prefixTrees)))
	frontiers := searchTree.FrontierNodes( /*@ 1/2 @*/ )
	terminalLogEntry := -1
	// flag encoding early termination:
	determined := false

	// TODO use res and err instead
	resultRes := true
	var resultErr error = nil
	if size == 0 || size <= t {
		resultRes = false
		resultErr = errors.New("version out of bounds")
		determined = true
	}

	//@ invariant noPerm < p
	//@ invariant acc(PrefixTreesInv(prefixTrees), p/2)
	//@ invariant acc(RootHashesInv(prefixRootHash), p/2)
	//@ invariant acc(frontiers, 1/2)
	//@ invariant acc(query.Inv(), p/2)
	//@ invariant acc(resp.Inv(), p/2)
	//@ invariant 0 <= fIdx && fIdx <= len(frontiers)
	//@ invariant -1 <= terminalLogEntry && terminalLogEntry < len(prefixTrees)
	//@ invariant forall i int :: { frontiers[i] } 0 <= i && i < len(frontiers) ==> 0 <= frontiers[i] && frontiers[i] < uint64(len(prefixTrees))
	//@ invariant determined ==> !resultRes
	//@ invariant !determined ==> resultRes && resultErr == nil
	// hyper-invariants:
	//@ invariant low(size) ==> low(fIdx)
	//@ invariant low(size) && fIdx == len(frontiers) && !determined &&
	//@ 	low(query.LabelContent()) &&
	//@ 	low(GetRootHashContent(prefixRootHash, int(frontiers[fIdx - 1]))) ==>
	//@			low(t)
	// note that `terminalLogEntry` might get set in different loop iterations
	// such that we do not obtain any hyper properties about it as CheckGreatest
	// provides information about `t` only if _both_ executions return 0.
	//@ decreases len(frontiers) - fIdx
	for fIdx := 0; fIdx < len(frontiers); fIdx++ {
		frontier := frontiers[fIdx]
		if !determined {
			//@ unfold acc(PrefixTreesInv(prefixTrees), p/4)
			prefixTree := prefixTrees[frontier]
			//@ unfold acc(RootHashesInv(prefixRootHash), p/4)
			rootHash := prefixRootHash[frontier][:]
			if frontier >= size {
				resultRes = false
				resultErr = errors.New("version out of bounds")
				determined = true
			}
			if !determined {
				//@ unfold acc(query.Inv(), p/4)
				LtGtOrEq, cgErr := CheckGreatest(prefixTree, query.Label, t, rootHash, size /*@, p/8 @*/)
				//@ fold acc(query.Inv(), p/4)
				if cgErr != nil {
					resultRes = false
					resultErr = cgErr
					determined = true
				} else if LtGtOrEq == 1 {
					resultRes = false
					resultErr = errors.New("greater version exists")
					determined = true
				} else if LtGtOrEq == -1 && fIdx == len(frontiers)-1 {
					// last frontier node for which we expect
					// a zero result. Anything else is an error
					resultRes = false
					resultErr = errors.New("Greatest version is not the greatest in the last iteration")
					determined = true
				} else if LtGtOrEq == 0 && terminalLogEntry == -1 {
					// we found a frontier node that has `t` as
					// the greatest version
					terminalLogEntry = int(frontier)
				}
			}
			//@ fold acc(RootHashesInv(prefixRootHash), p/4)
			//@ fold acc(PrefixTreesInv(prefixTrees), p/4)
		}
	}

	if terminalLogEntry == -1 && resultErr == nil {
		resultRes = false
		resultErr = errors.New("Claimed Version is not found.")
	}
	if frontiers[0] < uint64(terminalLogEntry) && config.Mode == 1 {
		entry = &MonitoringMapEntry{
			Position: uint64(len(frontiers) - 1),
			Version:  uint32(t),
		}
	}

	return resultRes, entry, resultErr
}

// buildPrefixTrees constructs prefix trees from the response's prefix proofs.
// @ requires noPerm < p
// @ requires acc(resp.Inv(), p)
// @ ensures acc(resp.Inv(), p)
// @ ensures resp.Version != nil ==> (unfolding acc(resp.Inv(), p) in *resp.Version >= 0)
// @ ensures err == nil ==> len(trees) == n
// @ ensures err == nil ==> acc(PrefixTreesInv(trees), p)
// @ ensures err == nil ==> len(rootHashes) == n
// @ ensures err == nil ==> forall j int :: {&rootHashes[j]} 0 <= j && j < n ==> acc(&rootHashes[j]) && acc(rootHashes[j])
// @ ensures err == nil ==> forall j int :: {&rootHashes[j]} 0 <= j && j < n ==> forall k int :: {rootHashes[j][k]} 0 <= k && k < sha256.Size ==> low(rootHashes[j][k])
// @ trusted
func buildPrefixTrees(resp SearchResponse, n int /*@, ghost p perm @*/) (trees []prefixtree.PT, rootHashes []*[sha256.Size]byte, err error) {
	trees = make([]prefixtree.PT, 0, n)
	rootHashes = make([]*[sha256.Size]byte, 0, n)
	//@ unfold acc(resp.Inv(), p)
	for i := 0; i < n; i++ {
		prf := /*@ unfolding acc(resp.Search.Inv(), p/2) in @*/ resp.Search.Prefix_proofs[i]
		if tree, treeErr := prefixtree.ToTree(prf, resp.Binary_ladder); treeErr != nil {
			//@ fold acc(resp.Inv(), p)
			return nil, nil, treeErr
		} else {
			trees = append( /*@ perm(1/2), @*/ trees, tree)
			rootHashes = append( /*@ perm(1/2), @*/ rootHashes, tree.Value)
		}
	}
	//@ fold acc(resp.Inv(), p)
	return trees, rootHashes, nil
}
