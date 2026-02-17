package client

import (
	"crypto/sha256"
	"errors"

	"github.com/felixlinker/keytrans-verification/pkg/proofs"
)

// ##(--hyperMode extended --enableExperimentalHyperFeatures)

/*@
//Compare the bytes of the arrays
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


@*/

type PT interface {
	// Returns non-nil if we can prove that the prefix tree contains a key for the
	// label and version pair provided. Returns nil if we can prove that the
	// prefix tree does not contain a key for the label and version pair provided.
	// Returns error in any other case.
	//@ pred Mem()
	GetCommitment(Label []byte, Version uint64, RootHash []byte) (res []byte, err error)
}

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
	Last  *uint32
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
	Inclusion      proofs.InclusionProof
	Opening        []byte
	Value          proofs.UpdateValue // value associated with queried label
}

/*@
pred (s SearchResponse) Inv() {
	s.Full_tree_head.Inv() &&
	(s.Version != nil ==> acc(s.Version)) &&
	acc(s.Binary_ladder) && // `proofs.BinaryLadderStep` does not have an invariant as it's just a value
	s.Search.Inv() &&
	s.Inclusion.Inv() &&
	acc(s.Opening) &&
	s.Value.Inv()
}
@*/

// @ requires noPerm < p
// @ preserves st.Inv()
// @ preserves acc(query.Inv(), p) && acc(resp.Inv(), p)
// @ requires resp.Version != nil
// @ requires acc(resp.Version, _)
// @ requires *resp.Version>= 0
// @ ensures err == nil ==> acc(res) && res.Inv()
// @ trusted
func (st *UserState) VerifyLatest(query SearchRequest, resp SearchResponse, config *Configuration /*@, ghost p perm @*/) (res *proofs.UpdateValue, err error) {
	//@ unfold acc(resp.Inv(), p)
	if err := st.UpdateView(resp.Full_tree_head, resp.Search /*@, p/2 @*/); err != nil {
		//@ fold acc(resp.Inv(), p)
		return nil, err
	} else if resp.Version == nil {
		//@ fold acc(resp.Inv(), p)
		return nil, errors.New("no version provided")
	} else if len(resp.Search.Prefix_roots) != 0 {
		//@ fold acc(resp.Inv(), p)
		return nil, errors.New("prefix roots provided")
	}
	ladderIndices := proofs.FullBinaryLadderSteps_wrapper(uint64(*resp.Version) /*@, t2 @*/)
	if len(resp.Binary_ladder) != len(ladderIndices) {
		//@ fold acc(resp.Inv(), p)
		return nil, errors.New("length of binary ladder does not match greatest version")
	}

	trees := make([]*proofs.PrefixTree, 0, len(resp.Search.Prefix_proofs))
	rootHashes := make([]*[sha256.Size]byte, 0, len(resp.Search.Prefix_roots))
	//@ fold acc(resp.Inv(), p)

	//Here, we assume that the tree is already built

	//@ invariant acc(resp.Inv(), p)
	// invariant unfolding acc(resp.Search.Inv(), p/2) in 0 <= i && i <= len(resp.Search.Prefix_proofs)
	//@ invariant 0 <= i && i <= len(resp.Search.Prefix_proofs)
	//@ invariant acc(trees)
	//@ invariant acc(rootHashes)
	for i := 0; i < len(resp.Search.Prefix_proofs); i++ {
		//@ unfold acc(resp.Inv(), p)
		prf := /*@ unfolding acc(resp.Search.Inv(), p/2) in @*/ resp.Search.Prefix_proofs[i]
		if tree, err := prf.ToTree(resp.Binary_ladder); err != nil {
			//@ fold acc(resp.Inv(), p)
			return nil, err
		} else {
			trees = append( /*@ perm(1/2), @*/ trees, tree)

			rootHashes = append( /*@ perm(1/2), @*/ rootHashes, tree.Value)
		}
		//@ fold acc(resp.Inv(), p)
	}

	// TODO: Verify proof of inclusion in all trees
	monitoringMap := make([]MonitoringMapEntry, 0)
	decision, err := VerifyLatestKey(trees, rootHashes, st.Size, query, resp, monitoringMap, config)
	if err != nil {
		res = nil
	}
	if decision == true {
		res = &resp.Value
		err = nil
	} else {
		res = nil
		err = errors.New("Key not the greatest version")
	}
	return res, err
}

//Lemma : Merkle Binding
// This Merkle binding theorem is needed for showing that the commitment is in the tree state
// It is also one of the important lemmas we need to show that the commitment we get is consistent
// We use the following paper to derive the following lemma
// Paper: https://arxiv.org/pdf/2501.10802

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
requires acc(steps)
requires rel(t,0) != rel(t,1)
requires forall i int :: {steps[i]} 0 <= i && i < len(steps) ==> steps[i] >= 0
requires forall t2 uint64 :: {proofs.TStar_wrapper(steps, t, t2)} proofs.TStar_wrapper(steps, t, t2)
requires forall t2 uint64 :: {proofs.TStar_wrapper(steps, t2, t)} proofs.TStar_wrapper(steps, t2, t)
ensures acc(steps)
ensures t0_ge_t1 == (rel(t,0) > rel(t,1))
ensures t0_le_t1 == (rel(t,0) < rel(t,1))
ensures t0_le_t1 ==> 0 <= rel(idx1,0) && rel(idx1,0) < len(rel(steps,0)) && 0 <= rel(idx1,1) && rel(idx1,1) < len(rel(steps,1)) && rel(steps[rel(idx1,1)],1) == rel(steps[rel(idx1,0)],0) && rel(t,0) < rel(steps[rel(idx1,1)],1) && rel(steps[rel(idx1,1)],1) <= rel(t,1) && rel(t,0) < rel(steps[rel(idx1,0)],0) && rel(steps[rel(idx1,0)],0) <= rel(t,1)
ensures t0_ge_t1 ==> 0 <= rel(idx2,0) && rel(idx2,0) < len(rel(steps,0)) && 0 <= rel(idx2,1) && rel(idx2,1) < len(rel(steps,1)) && rel(steps[rel(idx2,1)],1) == rel(steps[rel(idx2,0)],0) && rel(t,1) < rel(steps[rel(idx2,1)],1) && rel(steps[rel(idx2,1)],1) <= rel(t,0) && rel(t,1) < rel(steps[rel(idx2,0)],0) && rel(steps[rel(idx2,0)],0) <= rel(t,0)
ensures idx1 > 0
ensures idx2 > 0
ensures rel(idx1,0) == rel(idx1,1)
ensures rel(idx2,0) == rel(idx2,1)
ensures forall i int :: {steps[i]} 0 <= i && i < len(steps) ==> steps[i] >= 0
func EstablishTStarWitnesses(steps []uint64, t uint64) (t0_ge_t1 bool, t0_le_t1 bool, idx1 int, idx2 int){
	// assert forall t2 uint64 :: {proofs.TStar_wrapper(steps,t, t2)} proofs.TStar_wrapper(steps,t, t2)
	// assert forall t2 uint64 :: {proofs.TStar_wrapper(steps,t2, t)} proofs.TStar_wrapper(steps,t2,t)

	// Replace it using rel(t,0), rel(t,1) and rel(steps,0), rel(steps,1)
	assert proofs.TStar_wrapper(rel(steps,0), rel(t,0), rel(t,1))
	assert rel(proofs.TStar_wrapper(rel(steps,1),rel(t,0),rel(t,1)), 1)

	assert proofs.TStar_wrapper(rel(steps,0), rel(t,1), rel(t,0))
	assert rel(proofs.TStar_wrapper(rel(steps,1),rel(t,1),rel(t,0)), 1)

	//Condition
	t0_ge_t1 = rel(t,0) > rel(t,1)
	t0_le_t1 = rel(t,0) < rel(t,1)

	// assert exists idx2 int :: exists idx3 int :: t0_ge_t1 ==> 0 <= idx2 && idx2 < len(rel(steps,0)) && 0 <= idx3 && idx3 < len(rel(steps,1)) && rel(steps[idx3],1) == rel(steps[idx2],0) && rel(t,1) < rel(steps[idx3],1) && rel(steps[idx3],1) <= rel(t,0)
	// assert exists idx1 int :: exists idx4 int :: t0_le_t1 ==> 0 <= idx1 && idx1 < len(rel(steps,0)) && 0 <= idx4 && idx4 < len(rel(steps,1)) && rel(steps[idx4],1) == rel(steps[idx1],0)&& rel(t,0) < rel(steps[idx4],1) && rel(steps[idx4],1) <= rel(t,1)

	//Remove existential quantifier to replace the statement, adding an assume with it
	idx1 = GetInt()
	idx2 = GetInt()

	assume rel(t,0) < rel(t,1) ==> 0 <= rel(idx1,0) && rel(idx1,0) < len(rel(steps,0)) && 0 <= rel(idx1,1) && rel(idx1,1) < len(rel(steps,1)) && rel(steps[rel(idx1,1)],1) == rel(steps[rel(idx1,0)],0)&& rel(t,0) < rel(steps[rel(idx1,1)],1) && rel(steps[rel(idx1,1)],1) <= rel(t,1)
	assume rel(t,0) > rel(t,1) ==> 0 <= rel(idx2,0) && rel(idx2,0) < len(rel(steps,0)) && 0 <= rel(idx2,1) && rel(idx2,1) < rel(len(steps),1) && rel(steps[rel(idx2,0)],0) == rel(steps[rel(idx2,1)],1)  && rel(t,1) < rel(steps[rel(idx2,1)],1) && rel(steps[rel(idx2,1)],1) <= rel(t,0)

	assert t0_le_t1 ==> 0 <= rel(idx1,0) && rel(idx1,0) < len(rel(steps,0)) && 0 <= rel(idx1,1) && rel(idx1,1) < len(rel(steps,1)) && rel(steps[rel(idx1,1)],1) == rel(steps[rel(idx1,0)],0)&& rel(t,0) < rel(steps[rel(idx1,1)],1) && rel(steps[rel(idx1,1)],1) <= rel(t,1)
	assert t0_ge_t1 ==> 0 <= rel(idx2,0) && rel(idx2,0) < len(rel(steps,0)) && 0 <= rel(idx2,1) && rel(idx2,1) < rel(len(steps),1) && rel(steps[rel(idx2,0)],0) == rel(steps[rel(idx2,1)],1)  && rel(t,1) < rel(steps[rel(idx2,1)],1) && rel(steps[rel(idx2,1)],1) <= rel(t,0)

	assert t0_ge_t1 ==> 0 <= rel(idx2,0) && rel(idx2,0) < len(rel(steps,0)) && 0 <= rel(idx2,1) && rel(idx2,1) < len(rel(steps,1)) && rel(steps[rel(idx2,1)],1) == rel(steps[rel(idx2,0)],0) && rel(t,1) < rel(steps[rel(idx2,0)],0) && rel(steps[rel(idx2,0)],0) <= rel(t,0)
	assert t0_le_t1 ==> 0 <= rel(idx1,0) && rel(idx1,0) < len(rel(steps,0)) && 0 <= rel(idx1,1) && rel(idx1,1) < len(rel(steps,1)) && rel(steps[rel(idx1,1)],1) == rel(steps[rel(idx1,0)],0)&& rel(t,0) <rel(steps[rel(idx1,0)],0) && rel(steps[rel(idx1,0)],0) <= rel(t,1)

	//Move existential quantifier to the right side of the implication

	assert t0_le_t1 ==> 0 <= rel(idx1,0) && rel(idx1,0) < len(rel(steps,0)) && 0 <= rel(idx1,1) && rel(idx1,1) < len(rel(steps,1)) && rel(steps[rel(idx1,1)],1) == rel(steps[rel(idx1,0)],0) && rel(t,0) < rel(steps[rel(idx1,1)],1) && rel(steps[rel(idx1,1)],1) <= rel(t,1) && rel(t,0) < rel(steps[rel(idx1,0)],0) && rel(steps[rel(idx1,0)],0) <= rel(t,1)
	assert t0_ge_t1 ==> 0 <= rel(idx2,0) && rel(idx2,0) < len(rel(steps,0)) && 0 <= rel(idx2,1) && rel(idx2,1) < len(rel(steps,1)) && rel(steps[rel(idx2,1)],1) == rel(steps[rel(idx2,0)],0) && rel(t,1) < rel(steps[rel(idx2,1)],1) && rel(steps[rel(idx2,1)],1) <= rel(t,0) && rel(t,1) < rel(steps[rel(idx2,0)],0) && rel(steps[rel(idx2,0)],0) <= rel(t,0)

	assume rel(idx1,0) == rel(idx1,1)
	assume rel(idx2,0) == rel(idx2,1)
}
@*/

/*
CheckGreatest verifies if t is the greatest version
 Returns:

	-1: Greatest version < t (found hole at or below t), the greatest version does not exist so far
	 0: t is the greatest version
	 1: Greatest version > t (found commitment above t), violates t being the greatest version
*/

// TODO: We need to somehow grab the value of the root from the tree and see if the hash root is equal
// @ requires noPerm < p
// @ requires label != nil
// @ requires t >= 0
// @ requires prefixTree != nil ==> prefixTree.Inv()
// @ requires acc(label)
// @ requires acc(RootHash)
// @ requires low(len(label))
// @ requires forall i int :: {label[i]} 0<= i && i < len(label) ==> low(label[i])
// @ requires low(len(RootHash))
// @ requires forall i int :: {RootHash[i]} 0<= i && i < len(RootHash) ==>  low(RootHash[i])
// @ requires low(t>=0)
// Very basic postcondition
// @ ensures (res == 0 && err == nil) || (res == 404 && err != nil) || ((res == -1 || res == 1) && err == nil)
// The holy grail (Don't change it!):
//
//	ensures rel(err == nil, 0) && rel(err==nil,1) && rel(res==0, 0) && rel(res==0,1) ==> rel(t,0) == rel(t,1)
//
// Changed the right implication to low(t)
// @ ensures rel(err == nil, 0) && rel(err==nil,1) && rel(res==0, 0) && rel(res==0,1) ==> low(t)
func CheckGreatest(prefixTree *proofs.PrefixTree, label []byte, t uint64, RootHash []byte, size uint64 /*@, ghost p perm@*/) (res int, err error) {
	steps := proofs.FullBinaryLadderSteps_wrapper(t)

	//@ assume rel(t,0) != rel(t,1)

	//Postcondition from the FBLS
	//@ assert acc(steps)

	//@ t0_ge_t1, t0_le_t1, idx1, idx2 := EstablishTStarWitnesses(steps, t)

	resultRes := 0
	var resultErr error = nil
	var determined bool = false //The flag is used due to hyperproperty feature of gobra.
	idx := 0
	//@ assert acc(steps)

	// step0 != step1 and idx0 == idx1 ==> differences, with assume
	// Fixed iteration observation ==> assumes ==> arbitrary loop iteration

	//@ assume rel(idx1,0) == rel(idx1,1)
	//@ assume rel(idx2,0) == rel(idx2,1)

	/*	Idea:
		idx1 == idx4
		b11 := incl1 && TStar <= t1,
		b12 := incl2 && TStar <= t2
		t1 < TStar && TStar <= t2

		b21 := !incl1 && t1 < TStar
		b22 := !incl2 && t2 < TStar
		t1 < TStar && TStar <= t2


		(b11 || b12) && (b21 || b22) ==> low(t)
	*/

	//@ ghost var idx_ge_K2_0 bool = rel(idx, 0) >= rel(idx2, 0)
	//@ ghost var idx_ge_K2_1 bool = rel(idx, 1) >= rel(idx2, 1)
	//@ ghost var idx_ge_K1_0 bool = rel(idx, 0) >= rel(idx1, 0)
	//@ ghost var idx_ge_K1_1 bool = rel(idx, 1) >= rel(idx1, 1)
	//@ ghost var det_0 bool = rel(determined, 0)
	//@ ghost var det_1 bool = rel(determined, 1)

	//@ invariant acc(RootHash)
	//@ invariant acc(label)
	//@ invariant acc(steps)
	//@ invariant low(len(label))
	//@ invariant low(len(RootHash))
	//@ invariant forall i int :: {steps[i]} 0 <= i && i < len(steps) ==> steps[i] >= 0
	//@ invariant 0 <= idx && idx <= len(steps)
	//@ invariant rel(t, 0) != rel(t, 1)
	//@ invariant determined ==> (resultRes == 404 && resultErr != nil) || ((resultRes == -1 || resultRes == 1) && resultErr == nil)
	//@ invariant !determined ==> resultRes == 0 && resultErr == nil
	//@ invariant t0_le_t1 ==> 0 <= rel(idx1,0) && rel(idx1,0) < len(rel(steps,0)) && 0 <= rel(idx1,1) && rel(idx1,1) < len(rel(steps,1)) && rel(steps[rel(idx1,1)],1) == rel(steps[rel(idx1,0)],0) && rel(t,0) < rel(steps[rel(idx1,1)],1) && rel(steps[rel(idx1,1)],1) <= rel(t,1) && rel(t,0) < rel(steps[rel(idx1,0)],0) && rel(steps[rel(idx1,0)],0) <= rel(t,1)
	//@ invariant t0_ge_t1 ==> 0 <= rel(idx2,0) && rel(idx2,0) < len(rel(steps,0)) && 0 <= rel(idx2,1) && rel(idx2,1) < len(rel(steps,1)) && rel(steps[rel(idx2,1)],1) == rel(steps[rel(idx2,0)],0) && rel(t,1) < rel(steps[rel(idx2,1)],1) && rel(steps[rel(idx2,1)],1) <= rel(t,0) && rel(t,1) < rel(steps[rel(idx2,0)],0) && rel(steps[rel(idx2,0)],0) <= rel(t,0)
	//@ invariant let idx2I0_ge_idx := rel(idx,0) > rel(idx2,0) in let idx2I1_ge_idx := rel(idx,1) > rel(idx2,1) in (t0_ge_t1 && idx2I0_ge_idx && idx2I1_ge_idx) ==> (rel(determined,0) || rel(determined,1))
	//@ invariant let idx1I0_ge_idx := rel(idx,0) > rel(idx1,0) in let idx1I1_ge_idx := rel(idx,1) > rel(idx1,1) in (t0_le_t1 && idx1I0_ge_idx && idx1I1_ge_idx) ==> (rel(determined,0) || rel(determined,1))
	for ; idx < len(steps); idx++ {
		step := steps[idx]
		commitment, err := prefixTree.GetCommitment(label, step, RootHash)

		//@ assume err == nil
		//@ assume low(commitment == nil)

		if err != nil {
			if !determined {
				resultRes = 404
				resultErr = err
				determined = true
			}
			//@ assert false
		} else {
			incl := commitment != nil
			//@ assert low(incl)

			//@ ghost var old_determined bool = determined

			if !incl {
				//@ assert (t0_ge_t1 && rel(idx,0) == rel(idx2,0)) ==> rel(step <= t, 0)
				//@ assert (t0_le_t1 && rel(idx,1) == rel(idx1,1)) ==> rel(step <= t, 1)

				if step <= t && !determined {
					resultRes = -1
					resultErr = nil
					determined = true
				}

				//@ assert determined == (old_determined || step <= t)
				//@ assert rel(determined, 0) == (rel(old_determined, 0) || rel(step <= t, 0))
				//@ assert rel(determined, 1) == (rel(old_determined, 1) || rel(step <= t, 1))
				//@ assert (t0_ge_t1 && rel(idx,0) == rel(idx2,0)) ==> rel(determined, 0)
				//@ assert (t0_le_t1 && rel(idx,1) == rel(idx1,1)) ==> rel(determined, 1)
				//@ assert rel(old_determined, 0) ==> rel(determined, 0)
				//@ assert rel(old_determined, 1) ==> rel(determined, 1)

			} else {
				//@ assert (t0_ge_t1 && rel(idx,1) == rel(idx2,1)) ==> rel(t < step, 1)
				//@ assert (t0_le_t1 && rel(idx,0) == rel(idx1,0)) ==>  rel(t < step, 0)

				if t < step && !determined {
					resultRes = 1
					resultErr = nil
					determined = true
				}

				//@ assert determined == (old_determined || t < step)
				//@ assert rel(determined, 0) == (rel(old_determined, 0) || rel(t < step, 0))
				//@ assert rel(determined, 1) == (rel(old_determined, 1) || rel(t < step, 1))
				//@ assert (t0_ge_t1 && rel(idx,1) == rel(idx2,1)) ==> rel(determined, 1)
				//@ assert (t0_le_t1 && rel(idx,0) == rel(idx1,0)) ==> rel(determined, 0)
				//@ assert rel(old_determined, 0) ==> rel(determined, 0)
				//@ assert rel(old_determined, 1) ==>  rel(determined, 1)
			}
		}

		// == and > will cover >=, which is a direct implication
		// Gobra is not able to detect that, so we use the assume trick.
		// There is no soundnesss error as far as I can see

		//@ assert (t0_ge_t1 && rel(idx,0) == rel(idx2,0) && rel(idx,1) == rel(idx2,1)) ==> (rel(determined,0) || rel(determined,1))
		//@ assert (t0_le_t1 && rel(idx,0) == rel(idx1,0) && rel(idx,1) == rel(idx1,1)) ==> (rel(determined,0) || rel(determined,1))

		//@ assert (t0_ge_t1 && rel(idx,0) > rel(idx2,0) && rel(idx,1) > rel(idx2,1)) ==> (rel(determined,0) || rel(determined,1))
		//@ assert (t0_le_t1 && rel(idx,0) > rel(idx1,0) && rel(idx,1) > rel(idx1,1)) ==> (rel(determined,0) || rel(determined,1))

		// Workaround: Use ghost variables in order to prevent bugs.

		//@ idx_ge_K2_0 = rel(idx, 0) >= rel(idx2, 0)
		//@ idx_ge_K2_1 = rel(idx, 1) >= rel(idx2, 1)
		//@ idx_ge_K1_0 = rel(idx, 0) >= rel(idx1, 0)
		//@ idx_ge_K1_1 = rel(idx, 1) >= rel(idx1, 1)

		//@ assume (t0_ge_t1 && idx_ge_K2_0 && idx_ge_K2_1) ==> (rel(determined, 0) || rel(determined, 1))
		//@ assume (t0_le_t1 && idx_ge_K1_0 && idx_ge_K1_1) ==> (rel(determined, 0) || rel(determined, 1))
		// assert false
	}

	return resultRes, resultErr

}

type MonitoringMapEntry struct {
	Position uint64
	Version  uint32
}

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
// @ requires resp.Version != nil
// @ requires size > 0
// @ requires *resp.Version >=0
// @ requires resp.Full_tree_head.RootHash != nil
// @ requires resp.Full_tree_head.RootHash != nil ==> acc(resp.Full_tree_head.RootHash)
// @ requires low(size)
// @ requires query.Label != nil
// @ requires low(query.Label)
// @ requires rel(resp.Version, 0) != rel(resp.Version,1)
//
//	Ideal goal:
//	ensures rel(err==nil,0) != rel(err==nil,1) || rel(res,0) != rel(res,1)
func VerifyLatestKey(prefixTrees []*proofs.PrefixTree, prefixRootHash []*[sha256.Size]byte, size uint64, query SearchRequest, resp SearchResponse, monitor_map []MonitoringMapEntry, config *Configuration /*@, ghost p perm@*/) (res bool, err error) {
	t := resp.Version //Claimed greatest version
	tVal := uint64(*t)
	search_tree := MkImplicitBinarySearchTree(size)
	// assert acc(search_tree.Inv(), p)
	// Variables to track result and avoid early termination
	resultRes := true
	var resultErr error = nil
	//@ assert search_tree != nil
	//@ assert search_tree != nil ==> search_tree.Inv()
	frontiers := search_tree.FrontierNodes( /*@p@*/ )
	//@ assert len(frontiers) > 0
	//@ assert low(len(frontiers)) && forall j int :: j>= 0 && j < len(frontiers) ==> low(frontiers[j])
	//@ assume forall i int :: i >= 0 && i < len(frontiers) ==> frontiers[i]>=0 && frontiers[i] < uint64(len(prefixTrees))
	terminalLogEntry := -1
	//@assert low(terminalLogEntry) //This holds trivially
	determined := false

	//@ invariant acc(prefixTrees)
	//@ invariant forall i int :: i >= 0 && i < len(prefixTrees) ==> acc(&prefixTrees[i])
	//@ invariant forall i int :: {&prefixTrees[i]} i >= 0 && i < len(prefixTrees) ==> acc(prefixTrees[i])
	//@ invariant acc(frontiers)
	//@ invariant acc(resp.Full_tree_head.RootHash)
	//@ invariant acc(query.Label, p)
	//@ invariant forall i int :: i >= 0 && i < len(prefixTrees) ==> prefixTrees[i] != nil
	//@ invariant forall i int :: i >= 0 && i < len(frontiers) ==> frontiers[i]>=0 && frontiers[i] < uint64(len(prefixTrees))
	//@ invariant low(size) ==> low(len(frontiers)) && forall j int :: j>= 0 && j < len(frontiers) ==> low(frontiers[j])
	//@ invariant low(resultErr == nil) ==> low(err == nil)
	//@ invariant rel(resultRes,0) != rel(resultRes,1) || rel(resultErr==nil, 0) != rel(resultErr==nil,1) || (resultRes && resultErr == nil)
	//Too strong
	// invariant low(err == nil) && low(!determined) && low(greatest == 0) ==> low(resultRes) && low(tVal)
	// invariant frontier == size - 1 ==> rel(resultRes,0) != rel(resultRes,1) || rel(resultErr==nil, 0) != rel(resultErr==nil,1)
	for _, frontier := range frontiers {
		//@ assert frontier >= 0 && int(frontier) < len(prefixTrees)
		//@ assert acc(prefixTrees[frontier])
		Prefix_tree := prefixTrees[frontier]
		if err != nil {
			break
		}
		if prefixTrees[frontier] == nil {
			resultRes = false
			resultErr = err
			determined = true
			//break
		} else {
			rootHash := prefixRootHash[frontier]
			//@ assert acc(query.Label)
			if size == 0 || tVal >= size || frontier >= size {
				resultRes = false
				resultErr = errors.New("version out of bounds")
				determined = true
				//break
				//return false, errors.New("version out of bounds")
			}
			LtGtOrEq, err := CheckGreatest(Prefix_tree, query.Label, tVal, rootHash[:], size /*@,p@*/)
			if err != nil {
				resultRes = false
				resultErr = err
				determined = true
				//break
			} else if LtGtOrEq == 1 {
				// Greater version exists
				resultRes = false
				resultErr = errors.New("greater version exists")
				break
			} else if LtGtOrEq == 0 && terminalLogEntry == -1 {
				terminalLogEntry = int(frontier)
			}

			if frontier == size-1 {
				if LtGtOrEq != 0 {
					resultRes = false
					resultErr = errors.New("Greatest version is not the greatest in the last iteration")
					break
				}
			}
		}
		//@ assert frontier == size - 1 ==>  rel(resultRes,0) != rel(resultRes,1) || rel(resultErr==nil, 0) != rel(resultErr==nil,1)
	}

	// assert rel(resultRes,0) != rel(resultRes,1) || rel(resultErr==nil, 0) != rel(resultErr==nil,1) || (resultRes && resultErr == nil)

	// assert low(resultErr == nil) && low(determined) && low(greatest==0) ==> low(resultRes) && low(tVal)
	// Post-loop logic (only execute if no error occurred in the loop)

	if terminalLogEntry == -1 && err == nil {
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
	// assert false
	return resultRes, resultErr
}
