package client

import (
	"crypto/sha256"
	"errors"

	"github.com/felixlinker/keytrans-verification/pkg/prefixtree"
	"github.com/felixlinker/keytrans-verification/pkg/proofs"
)

// ##(--hyperMode extended --enableExperimentalHyperFeatures)

/*@
// Ghost helper functions for hyper-property verification

ghost
decreases
requires p > noPerm
requires acc(r1, p)
requires acc(r2,p)
pure
func BytesEqual(r1 []byte, r2 []byte, p perm) bool {
	return len(r1) == len(r2) && forall i int :: {r1[i], r2[i]} 0<=i && i < len(r1) ==> r1[i] ==r2[i]
}

ghost
decreases
requires p > noPerm
requires acc(r1, p)
requires acc(r2,p)
pure
func BytesNotEqual(r1 []byte, r2 []byte, p perm) bool {
	return !(len(r1) == len(r2) && forall i int :: {r1[i], r2[i]} 0<=i && i < len(r1) ==> r1[i] ==r2[i])
}

pred ByteLowInv(s []byte){
	acc(s) && low(len(s)) && (forall i int :: {s[i]} 0<= i && i < len(s) && low(s[i]))
}

pred UIntLowInv(s []uint64){
	acc(s) && low(len(s)) && (forall i int :: {s[i]} 0<= i && i < len(s) && low(s[i]))
}

ghost
decreases
pure func TStar(t1, t2 uint64) uint64 {
	return (t1 < 0 || t2 < 0 || t1 == t2) ? 0:
		t1 < t2 ?
      (proofs.TStar_pure(t1, t2)) :
      (proofs.TStar_pure(t2, t1))
}

ghost
requires acc(arr, _)
decreases
pure
func getContent(arr []byte) (res seq[byte]) {
  return GetByteContent(arr, 0)
}

ghost
requires acc(arr, _)
requires 0 <= idx && idx <= len(arr)
decreases len(arr) - idx
pure
func GetByteContent(arr []byte, idx int) (res seq[byte]) {
  return idx == len(arr) ? seq[byte]{} : seq[byte]{arr[idx]} ++ GetByteContent(arr, idx + 1)
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
	RootHash  []byte //Added RootHash for comparison
	// TODO: AuditorTreeHead auditor_tree_head
}

/*@
pred (f FullTreeHead) Inv() {
	f.Tree_head.Inv() && acc(f.RootHash)
}

ghost
decreases
requires acc(f.Inv(), _)
pure func (f FullTreeHead) Size() uint64 {
	return unfolding acc(f.Inv(), _) in f.Tree_head.Tree_size
}



@*/

type SearchRequest struct {
	Last  *uint64
	Label []byte
	// TODO: optional<uint32> version
}

/*@
pred (s SearchRequest) Inv() {
	acc(s.Last) && acc(s.Label)
}
@*/

type SearchResponse struct {
	Full_tree_head FullTreeHead
	Version        *uint32 // version; only present for latest-key queries
	Binary_ladder  []proofs.BinaryLadderStep
	Search         proofs.CombinedTreeProof
	Opening        []byte
	Value          proofs.UpdateValue // value associated with queried label
}

/*@
pred (s SearchResponse) Inv() {
	s.Full_tree_head.Inv() &&
	(s.Version != nil ==> acc(s.Version)) &&
	acc(s.Binary_ladder) &&
	s.Search.Inv() &&
	acc(s.Opening) &&
	s.Value.Inv()
}
@*/

// VerifyLatest verifies that the version claimed in resp is indeed the latest
// version for the queried label. It updates the user's view of the tree, validates
// the response fields, builds prefix trees, and delegates to VerifyLatestKey.
//
// Preconditions: resp must have a non-nil Version, a non-empty tree, the tree size
// must be low (public), and the query label must be low (public).
//
// Postconditions (hyper-property): if err==nil, resp.Version is low — meaning
// two executions with the same root hash agree on the latest version.
//
// Returns:
//   - res: the update value associated with the label (non-nil on success)
//   - err: non-nil if any verification step fails
//

// @ requires noPerm < p
// @ preserves st.Inv()
// @ preserves acc(query.Inv(), p)
// @ requires acc(resp.Inv(), p)
// @ requires resp.Version != nil
// @ requires acc(resp.Version, p)
// @ requires *resp.Version >= 0
// @ requires query.Label != nil
// @ requires acc(query.Label, p)
// @ requires low(len(query.Label)) && forall i int :: 0<=i && i < len(query.Label) ==> low(query.Label[i])
// @ requires low(resp.Full_tree_head.Tree_head.Tree_size)
// @ requires resp.Full_tree_head.Tree_head.Tree_size > 0
// @ requires resp.Full_tree_head.Tree_head.Tree_size <= uint64(len(resp.Search.Prefix_proofs))
// @ requires resp.Full_tree_head.RootHash != nil
// @ requires acc(config, p)
// @ ensures err != nil ==> acc(resp.Inv(), p)
// @ ensures err == nil ==> acc(res) && acc(res.Inv(), p)
// @ ensures err == nil ==> low(resp.Version)
func (st *UserState) VerifyLatest(query SearchRequest, resp SearchResponse, config *Configuration /*@, ghost p perm @*/) (res *proofs.UpdateValue, err error) {
	//@ unfold acc(resp.Inv(), p)

	determined := false
	var resultErr error = nil

	// Phase 1: UpdateView
	updateErr := st.UpdateView(resp.Full_tree_head, resp.Search /*@, p/2 @*/)
	if updateErr != nil {
		resultErr = updateErr
		determined = true
	}

	// Phase 2: Validation checks (resp.Inv() still unfolded)
	if !determined {
		if resp.Version == nil {
			resultErr = errors.New("no version provided")
			determined = true
		}
	}
	if !determined {
		ladderIndices := proofs.FullBinaryLadderSteps_wrapper(uint64(*resp.Version))
		if len(resp.Binary_ladder) != len(ladderIndices) {
			resultErr = errors.New("length of binary ladder does not match greatest version")
			determined = true
		}
	}

	// Phase 3: Build prefix trees
	n := len(resp.Search.Prefix_proofs)
	//@ fold acc(resp.Inv(), p)

	var trees []*prefixtree.PrefixTree
	var rootHashes []*[sha256.Size]byte
	if !determined {
		var buildErr error
		trees, rootHashes, buildErr = buildPrefixTrees(resp, n /*@, p @*/)
		if buildErr != nil {
			resultErr = buildErr
			determined = true
		}
	}

	// Phase 4: VerifyLatestKey
	decision := false
	if !determined {
		//@ unfold acc(resp.Inv(), p)
		//@ unfold acc(query.Inv(), p)
		//@ unfold acc(resp.Full_tree_head.Inv(), p)

		size := resp.Full_tree_head.Tree_head.Tree_size
		monitoringMap := make([]MonitoringMapEntry, 0)
		decision, resultErr = VerifyLatestKey(trees, rootHashes, size, query, resp, monitoringMap, config /*@, p/4 @*/)

		//@ fold acc(query.Inv(), p)

		if !decision || resultErr != nil {
			//@ fold acc(resp.Full_tree_head.Inv(), p)
			//@ fold acc(resp.Inv(), p)
			if resultErr == nil {
				resultErr = errors.New("Key not the greatest version")
			}
			determined = true
		}
	}

	// Phase 5: Single return
	if !determined && decision {
		// VerifyLatestKey ensures: err == nil && res ==> low(resp.Version)
		//@ unfold acc(resp.Value.Inv(), p)
		res = &proofs.UpdateValue{Value: resp.Value.Value}
		//@ fold acc(res.Inv(), p)
		err = nil
	} else {
		res = nil
		err = resultErr
	}
	return res, err
}

//Why >0 instead of >=0? Because the version 0 is always included and we assume that the version we are selecting is >=0
// If this constraint is violated, it's very easy to be captured
/*@
ghost
decreases
ensures res > 0
func GetInt() (res int)

@*/

/*@
ghost
decreases
requires acc(steps, 1/2)
requires t >= 0
requires forall t2 uint64 :: {proofs.TStar_wrapper(steps, t, t2)} proofs.TStar_wrapper(steps, t, t2)
requires forall t2 uint64 :: {proofs.TStar_wrapper(steps, t2, t)} proofs.TStar_wrapper(steps, t2, t)
ensures acc(steps, 1/2)
ensures rel(t,0) < rel(t,1) ==> 0 <= rel(idx1,0) && rel(idx1,0) < len(rel(steps,0)) && 0 <= rel(idx1,1) && rel(idx1,1) < len(rel(steps,1)) && rel(steps[rel(idx1,1)],1) == rel(steps[rel(idx1,0)],0) && rel(t,0) < rel(steps[rel(idx1,1)],1) && rel(steps[rel(idx1,1)],1) <= rel(t,1) && rel(t,0) < rel(steps[rel(idx1,0)],0) && rel(steps[rel(idx1,0)],0) <= rel(t,1)
ensures rel(t,0) < rel(t,1) ==> rel(steps[rel(idx1,0)],0) == proofs.TStar_pure(rel(t,0), rel(t,1))
ensures rel(t,0) > rel(t,1) ==> 0 <= rel(idx2,0) && rel(idx2,0) < len(rel(steps,0)) && 0 <= rel(idx2,1) && rel(idx2,1) < len(rel(steps,1)) && rel(steps[rel(idx2,1)],1) == rel(steps[rel(idx2,0)],0) && rel(t,1) < rel(steps[rel(idx2,1)],1) && rel(steps[rel(idx2,1)],1) <= rel(t,0) && rel(t,1) < rel(steps[rel(idx2,0)],0) && rel(steps[rel(idx2,0)],0) <= rel(t,0)
ensures rel(t,0) > rel(t,1) ==> rel(steps[rel(idx2,0)],0) == proofs.TStar_pure(rel(t,1), rel(t,0))
ensures idx1 > 0
ensures idx2 > 0
func EstablishTStarWitnesses(steps []uint64, t uint64) (idx1 int, idx2 int){
	// Replace it using rel(t,0), rel(t,1) and rel(steps,0), rel(steps,1)
	assert proofs.TStar_wrapper(rel(steps,0), rel(t,0), rel(t,1))
	assert rel(proofs.TStar_wrapper(rel(steps,1),rel(t,0),rel(t,1)), 1)

	assert proofs.TStar_wrapper(rel(steps,0), rel(t,1), rel(t,0))
	assert rel(proofs.TStar_wrapper(rel(steps,1),rel(t,1),rel(t,0)), 1)

	//Remove existential quantifier to replace the statement, adding an assume with it
	idx1 = GetInt()
	idx2 = GetInt()

	assume rel(t,0) < rel(t,1) ==> 0 <= rel(idx1,0) && rel(idx1,0) < len(rel(steps,0)) && 0 <= rel(idx1,1) && rel(idx1,1) < len(rel(steps,1)) && rel(steps[rel(idx1,1)],1) == rel(steps[rel(idx1,0)],0)&& rel(t,0) < rel(steps[rel(idx1,1)],1) && rel(steps[rel(idx1,1)],1) <= rel(t,1) && rel(steps[rel(idx1,0)],0) == proofs.TStar_pure(rel(t,0), rel(t,1))
	assume rel(t,0) > rel(t,1) ==> 0 <= rel(idx2,0) && rel(idx2,0) < len(rel(steps,0)) && 0 <= rel(idx2,1) && rel(idx2,1) < rel(len(steps),1) && rel(steps[rel(idx2,0)],0) == rel(steps[rel(idx2,1)],1)  && rel(t,1) < rel(steps[rel(idx2,1)],1) && rel(steps[rel(idx2,1)],1) <= rel(t,0) && rel(steps[rel(idx2,0)],0) == proofs.TStar_pure(rel(t,1), rel(t,0))


	assert rel(t,0) < rel(t,1) ==> 0 <= rel(idx1,0) && rel(idx1,0) < len(rel(steps,0)) && 0 <= rel(idx1,1) && rel(idx1,1) < len(rel(steps,1)) && rel(steps[rel(idx1,1)],1) == rel(steps[rel(idx1,0)],0)&& rel(t,0) < rel(steps[rel(idx1,1)],1) && rel(steps[rel(idx1,1)],1) <= rel(t,1)
	assert rel(t,0) > rel(t,1) ==> 0 <= rel(idx2,0) && rel(idx2,0) < len(rel(steps,0)) && 0 <= rel(idx2,1) && rel(idx2,1) < rel(len(steps),1) && rel(steps[rel(idx2,0)],0) == rel(steps[rel(idx2,1)],1)  && rel(t,1) < rel(steps[rel(idx2,1)],1) && rel(steps[rel(idx2,1)],1) <= rel(t,0)

	assert rel(t,0) > rel(t,1) ==> 0 <= rel(idx2,0) && rel(idx2,0) < len(rel(steps,0)) && 0 <= rel(idx2,1) && rel(idx2,1) < len(rel(steps,1)) && rel(steps[rel(idx2,1)],1) == rel(steps[rel(idx2,0)],0) && rel(t,1) < rel(steps[rel(idx2,0)],0) && rel(steps[rel(idx2,0)],0) <= rel(t,0)
	assert rel(t,0) < rel(t,1) ==> 0 <= rel(idx1,0) && rel(idx1,0) < len(rel(steps,0)) && 0 <= rel(idx1,1) && rel(idx1,1) < len(rel(steps,1)) && rel(steps[rel(idx1,1)],1) == rel(steps[rel(idx1,0)],0)&& rel(t,0) <rel(steps[rel(idx1,0)],0) && rel(steps[rel(idx1,0)],0) <= rel(t,1)

	assert rel(t,0) < rel(t,1) ==> low(idx1 < len(steps))
	assert rel(t,0) > rel(t,1) ==> low(idx2 < len(steps))

	//Move existential quantifier to the right side of the implication

	assert rel(t,0) < rel(t,1) ==> 0 <= rel(idx1,0) && rel(idx1,0) < len(rel(steps,0)) && 0 <= rel(idx1,1) && rel(idx1,1) < len(rel(steps,1)) && rel(steps[rel(idx1,1)],1) == rel(steps[rel(idx1,0)],0) && rel(t,0) < rel(steps[rel(idx1,1)],1) && rel(steps[rel(idx1,1)],1) <= rel(t,1) && rel(t,0) < rel(steps[rel(idx1,0)],0) && rel(steps[rel(idx1,0)],0) <= rel(t,1)
	assert rel(t,0) > rel(t,1) ==> 0 <= rel(idx2,0) && rel(idx2,0) < len(rel(steps,0)) && 0 <= rel(idx2,1) && rel(idx2,1) < len(rel(steps,1)) && rel(steps[rel(idx2,1)],1) == rel(steps[rel(idx2,0)],0) && rel(t,1) < rel(steps[rel(idx2,1)],1) && rel(steps[rel(idx2,1)],1) <= rel(t,0) && rel(t,1) < rel(steps[rel(idx2,0)],0) && rel(steps[rel(idx2,0)],0) <= rel(t,0)


}

//TODO: Change the permission to make sure that the steps[i]>=0 is not necessary.

ghost
decreases
requires acc(steps, 1/2)
requires t >= 0
requires len(steps) > 0 && steps[0] == 0
requires forall t2 uint64 :: {proofs.TStar_wrapper(steps, t, t2)} proofs.TStar_wrapper(steps, t, t2)
requires forall t2 uint64 :: {proofs.TStar_wrapper(steps, t2, t)} proofs.TStar_wrapper(steps, t2, t)
ensures acc(steps, 1/2)
ensures 0 <= idx && idx < len(steps)
ensures low(steps[idx])
ensures steps[idx] == TStar(rel(t, 0), rel(t, 1))
func FindTStarIdx(steps []uint64, t uint64) (idx int) {
	if low(t) {
		idx = 0
		assert steps[idx] == TStar(rel(t, 0), rel(t, 1))
		// steps[0] == 0 (precondition), 0 is low in both executions
		// 0 will occur in every FBLS unless t == 0
		// But t == 0 can never occur because this literally means that the version 0 is not inserted.
		// So there will be an error returned instead
		assert low(steps[idx])
	} else {
		idx1, idx2 := EstablishTStarWitnesses(steps, t)
		if rel(t, 0) < rel(t, 1) {
			idx = idx1
			assert low(idx < len(steps))
			// EstablishTStarWitnesses: rel(steps[rel(idx1,1)],1) == rel(steps[rel(idx1,0)],0)
			// Both equal TStar_pure(rel(t,0), rel(t,1)), so low(steps[idx])
			assert rel(steps[rel(idx1,1)],1) == rel(steps[rel(idx1,0)],0)
			assert low(steps[idx])
		} else {
			idx = idx2
			assert low(idx < len(steps))
			// EstablishTStarWitnesses: rel(steps[rel(idx2,0)],0) == rel(steps[rel(idx2,1)],1)
			// Both equal TStar_pure(rel(t,1), rel(t,0)), so low(steps[idx])
			assert rel(steps[rel(idx2,0)],0) == rel(steps[rel(idx2,1)],1)
			assert low(steps[idx])
		}
	}
	assert rel(idx,0) < rel(len(steps),0)
	assert rel(idx,1) < rel(len(steps),1)
	assert low(idx < len(steps))
	assert idx < len(steps)
}
@*/

// CheckCommitment walks the binary ladder steps for a label and checks whether
// version t is the greatest committed version in the prefix tree.
//
// For each step, it queries the prefix tree for a commitment at that version.
// A non-inclusion proof at step <= t means t is not yet the greatest (hole found).
// An inclusion proof at step > t means a greater version exists (violation).
//
// Preconditions: label and RootHash must be non-nil and low (public), t >= 0,
// prefixTree (if non-nil) must satisfy its invariant, tStarIdx must index a low
// step equal to TStar(t_exec0, t_exec1).
//
// Postconditions (hyper-property): if err==nil and res==0, then t is low —
// two executions with the same tree agree on the greatest version.
//
// Returns:
//   - res: -1 (greatest < t), 0 (t is greatest), 1 (greatest > t), 404 (tree error)
//   - err: non-nil on tree lookup errors
//
// @ requires label != nil
// @ requires acc(label)
// @ requires acc(RootHash)
// @ requires acc(steps)
// @ requires low(getContent(label))
// @ requires low(getContent(RootHash))
// @ requires t >= 0
// @ requires prefixTree != nil ==> prefixTree.Inv()
// @ requires forall i int :: {steps[i]} 0 <= i && i < len(steps) ==> steps[i] >= 0
// @ requires 0 <= tStarIdx && tStarIdx < len(steps)
// @ requires low(steps[tStarIdx])
// @ requires steps[tStarIdx] == TStar(rel(t, 0), rel(t, 1))
// Correct postcondition
// @ ensures err == nil && res == 0 ==> low(t)
func CheckCommitment(prefixTree *prefixtree.PrefixTree, steps []uint64, label []byte, t uint64, RootHash []byte, size uint64 /*@, ghost tStarIdx int@*/) (res int, err error) {
	resultRes := 0
	var resultErr error = nil
	var determined bool = false //The flag is used due to hyperproperty feature of gobra.
	//@ ghost var tStarVisited bool = false
	//@ ghost var tStar uint64 = steps[tStarIdx]

	//@ ghost var labelSeq seq[byte] = getContent(label)
	//@ ghost var RootHashSeq seq[byte] = getContent(RootHash)

	//@ non_incl_lemma := prefixtree.GetCommitmentIsDeterministic(labelSeq, tStar, RootHashSeq) && tStar <= t
	//@ incl_lemma := !prefixtree.GetCommitmentIsDeterministic(labelSeq, tStar, RootHashSeq) && t < tStar

	//@ invariant acc(RootHash)
	//@ invariant acc(label)
	//@ invariant acc(steps)
	//@ invariant forall i int :: {steps[i]} 0 <= i && i < len(steps) ==> steps[i] >= 0
	//@ invariant 0 <= idx && idx <= len(steps)
	//@ invariant tStar == steps[tStarIdx]
	//@ invariant steps[tStarIdx] == TStar(rel(t, 0), rel(t, 1))
	//@ invariant determined ==> resultRes != 0
	//@ invariant !determined ==> resultRes == 0 && resultErr == nil
	//@ invariant tStarIdx < idx && !determined ==> non_incl_lemma || incl_lemma
	for idx := 0; idx < len(steps); idx++ {
		if !determined {
			step := steps[idx]
			commitment, err := prefixTree.GetCommitment(label, step, RootHash /*@, labelSeq, RootHashSeq @*/)
			if err != nil {
				if !determined {
					resultRes = 404
					resultErr = err
					determined = true
				}
			} else {
				incl := commitment != nil
				if !incl {
					if step <= t {
						resultRes = -1
						resultErr = nil
						determined = true
					}

				} else {

					if t < step {
						resultRes = 1
						resultErr = nil
						determined = true
					}
				}
				/*@
				ghost if idx == tStarIdx{
					assert !determined ==> (non_incl_lemma || incl_lemma)
					tStarVisited = true
				}
				@*/
			}

		}

	}

	return resultRes, resultErr

}

// CheckGreatest computes the full binary ladder steps for version t and then
// delegates to CheckCommitment to verify whether t is the greatest version.
//
// Preconditions: label and RootHash must be non-nil and low (public), t >= 0,
// prefixTree (if non-nil) must satisfy its invariant.
//
// Postconditions (hyper-property): if err==nil and res==0, then t is low.
//
// Returns:
//   - res: -1 (greatest < t), 0 (t is greatest), 1 (greatest > t), 404 (tree error)
//   - err: non-nil on tree lookup errors
//

// @ requires label != nil
// @ requires acc(label)
// @ requires acc(RootHash)
// @ requires low(getContent(label))
// @ requires low(getContent(RootHash))
// @ requires t >= 0
// @ requires prefixTree != nil ==> prefixTree.Inv()
// @ ensures err == nil && res == 0 ==> low(t)
func CheckGreatest(prefixTree *prefixtree.PrefixTree, label []byte, t uint64, RootHash []byte, size uint64) (res int, err error) {
	steps := proofs.FullBinaryLadderSteps_wrapper(t)
	//@ tStarIdx := FindTStarIdx(steps, t)
	return CheckCommitment(prefixTree, steps, label, t, RootHash, size /*@, tStarIdx @*/)
}

type MonitoringMapEntry struct {
	Position uint64
	Version  uint32
}

// VerifyLatestKey iterates over all frontier nodes of the implicit binary search
// tree and calls CheckGreatest on each to verify that the claimed version is
// the greatest. For non-last frontiers, a result of 1 (greater version exists)
// is a failure. For the last frontier, the result must be exactly 0 (t is greatest).
// Optionally appends to monitor_map if the entry needs future monitoring.
//
// Preconditions: prefixTrees and rootHashes must have length >= size, all trees
// non-nil with valid invariants, resp.Version non-nil, size > 0, label and size
// must be low (public).
//
// Postconditions (hyper-property): if err==nil and res==true, then resp.Version
// is low — two executions with the same tree agree on the latest version.
//
// Returns:
//   - res: true if the claimed version is verified as the greatest
//   - err: non-nil describing the failure reason
//
// @ requires noPerm < p
// @ requires acc(monitor_map)
// @ requires acc(resp.Version,p)
// @ requires acc(query.Label,p)
// @ requires acc(prefixTrees,p)
// @ requires acc(prefixRootHash, p)
// @ requires acc(config,p)
// @ requires forall i int :: i >= 0 && i < len(prefixTrees) ==> acc(&prefixTrees[i])
// @ requires forall i int :: {&prefixTrees[i]} i >= 0 && i < len(prefixTrees) ==> acc(prefixTrees[i].Inv(), p)
// @ requires forall i int :: i >= 0 && i < len(prefixTrees) ==> prefixTrees[i] != nil
// @ requires acc(resp.Full_tree_head.RootHash, p)
// @ requires resp.Version != nil
// @ requires size > 0
// @ requires *resp.Version >=0
// @ requires resp.Full_tree_head.RootHash != nil
// @ requires low(size)
// @ requires size <= uint64(len(prefixTrees))
// @ requires query.Label != nil
// @ requires low(len(query.Label)) && forall i int :: 0 <= i && i < len(query.Label) ==> low(query.Label[i])
// @ ensures acc(resp.Version, p)
// @ ensures acc(query.Label, p)
// @ ensures acc(prefixTrees, p)
// @ ensures acc(prefixRootHash, p)
// @ ensures acc(config, p)
// @ ensures resp.Full_tree_head.RootHash != nil ==> acc(resp.Full_tree_head.RootHash, p)
// @ ensures err == nil && res ==> low(resp.Version)
func VerifyLatestKey(prefixTrees []*prefixtree.PrefixTree, prefixRootHash []*[sha256.Size]byte, size uint64, query SearchRequest, resp SearchResponse, monitor_map []MonitoringMapEntry, config *Configuration /*@, ghost p perm@*/) (res bool, err error) {
	t := resp.Version //Claimed greatest version
	tVal := uint64(*t)
	search_tree := MkImplicitBinarySearchTree(size)
	resultRes := true
	var resultErr error = nil
	frontiers := search_tree.FrontierNodes( /*@p, size@*/ )
	terminalLogEntry := -1
	determined := false

	if size == 0 || tVal >= size {
		resultRes = false
		resultErr = errors.New("version out of bounds")
		determined = true
	}

	// Loop: process all frontiers except the last
	// Easier than having a if{if {...}}

	//@ invariant acc(prefixTrees)
	//@ invariant forall i int :: i >= 0 && i < len(prefixTrees) ==> acc(&prefixTrees[i])
	//@ invariant forall i int :: {&prefixTrees[i]} i >= 0 && i < len(prefixTrees) ==> acc(prefixTrees[i])
	//@ invariant acc(prefixRootHash, p)
	//@ invariant acc(frontiers)
	//@ invariant acc(resp.Full_tree_head.RootHash, p)
	//@ invariant acc(query.Label, p)
	//@ invariant acc(resp.Version, p)
	//@ invariant acc(config, p)
	//@ invariant forall i int :: i >= 0 && i < len(prefixTrees) ==> prefixTrees[i] != nil
	//@ invariant forall i int :: i >= 0 && i < len(frontiers) ==> frontiers[i]>=0 && frontiers[i] < uint64(len(prefixTrees))
	//@ invariant low(size) ==> low(len(frontiers)) && forall j int :: j>= 0 && j < len(frontiers) ==> low(frontiers[j])
	//@ invariant 0 <= fIdx && fIdx <= len(frontiers) - 1
	//@ invariant len(frontiers) > 0
	//@ invariant determined ==> !resultRes
	//@ invariant !determined ==> resultRes && resultErr == nil
	for fIdx := 0; fIdx < len(frontiers)-1; fIdx++ {
		frontier := frontiers[fIdx]
		if !determined {
			Prefix_tree := prefixTrees[frontier]
			if prefixTrees[frontier] == nil {
				resultRes = false
				resultErr = errors.New("prefix tree is nil")
				determined = true
			} else {
				rootHash := prefixRootHash[frontier]
				if frontier >= size {
					resultRes = false
					resultErr = errors.New("version out of bounds")
					determined = true
				}

				LtGtOrEq, cgErr := CheckGreatest(Prefix_tree, query.Label, tVal, rootHash[:], size)
				if cgErr != nil {
					resultRes = false
					resultErr = cgErr
					determined = true
				} else if LtGtOrEq == 1 {
					resultRes = false
					resultErr = errors.New("greater version exists")
					determined = true
				} else if LtGtOrEq == 0 && terminalLogEntry == -1 {
					terminalLogEntry = int(frontier)
				}
			}
		}
	}

	// Process last frontier separately
	if !determined {
		frontier := frontiers[len(frontiers)-1]
		Prefix_tree := prefixTrees[frontier]
		if prefixTrees[frontier] == nil {
			resultRes = false
			resultErr = errors.New("prefix tree is nil")
			determined = true
		} else {
			rootHash := prefixRootHash[frontier]
			if frontier >= size {
				resultRes = false
				resultErr = errors.New("version out of bounds")
				determined = true
			}

			LtGtOrEq, cgErr := CheckGreatest(Prefix_tree, query.Label, tVal, rootHash[:], size)
			if cgErr != nil {
				resultRes = false
				resultErr = cgErr
				determined = true
			} else if LtGtOrEq != 0 {
				resultRes = false
				resultErr = errors.New("Greatest version is not the greatest in the last iteration")
				determined = true
			} else if terminalLogEntry == -1 {
				terminalLogEntry = int(frontier)
			}
		}
	}

	if terminalLogEntry == -1 && resultErr == nil {
		resultRes = false
		resultErr = errors.New("Claimed Version is not found.")
	}
	if frontiers[0] < uint64(terminalLogEntry) && config.Mode == 1 {
		entry := MonitoringMapEntry{
			Position: uint64(len(frontiers) - 1),
			Version:  *t,
		}
		monitor_map = append( /*@ perm(1/2), @*/ monitor_map, entry)
	}

	return resultRes, resultErr
}

// buildPrefixTrees constructs prefix trees from the SearchResponse's prefix proofs.
// Each prefix proof is converted into a PrefixTree and its root hash is extracted.
// The root hashes are assumed to be low (public) per the protocol specification.
//
// Preconditions: resp must satisfy its invariant with permission p.
//
// Postconditions: on success, returns n trees with valid invariants and n root
// hashes whose bytes are all low. On error, resp.Inv() permission is returned.
//
// Returns:
//   - trees: slice of n non-nil PrefixTree pointers
//   - rootHashes: slice of n sha256 root hashes (all bytes low)
//   - err: non-nil if any prefix proof cannot be converted
//

// @ requires noPerm < p
// @ requires acc(resp.Inv(), p)
// @ ensures err == nil ==> acc(resp.Inv(), p)
// @ ensures err == nil ==> acc(trees) && len(trees) == n
// @ ensures err == nil ==> forall j int :: 0 <= j && j < n ==> acc(&trees[j])
// @ ensures err == nil ==> forall j int :: 0 <= j && j < n ==> trees[j] != nil
// @ ensures err == nil ==> forall j int :: {&trees[j]} 0 <= j && j < n ==> trees[j].Inv()
// @ ensures err == nil ==> acc(rootHashes) && len(rootHashes) == n
// @ ensures err == nil ==> forall j int :: 0 <= j && j < n ==> acc(&rootHashes[j])
// @ ensures err == nil ==> forall j int :: 0 <= j && j < n ==> acc(rootHashes[j])
// @ ensures err == nil ==> forall j int :: 0 <= j && j < n ==> forall k int :: 0 <= k && k < sha256.Size ==> low(rootHashes[j][k])
// @ ensures err != nil ==> acc(resp.Inv(), p)
// @ trusted
func buildPrefixTrees(resp SearchResponse, n int /*@, ghost p perm @*/) (trees []*prefixtree.PrefixTree, rootHashes []*[sha256.Size]byte, err error) {
	trees = make([]*prefixtree.PrefixTree, 0, n)
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
