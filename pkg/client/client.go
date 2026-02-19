package client

import (
	"crypto/sha256"
	"errors"

	"github.com/felixlinker/keytrans-verification/pkg/proofs"
)

// ##(--hyperMode extended --enableExperimentalHyperFeatures)

/*@
//Helper functions


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

ghost
requires true
decreases
pure func TStarWrapper(steps []uint64, t1, t2 uint64) uint64 {
  return (t1 < 0 || t2 < 0) ? 0 :  //Cannot happen because we check this beforehand.
  			t1 == t2 ? 0 : t1 < t2 ? proofs.TStar_pure(t1, t2) : proofs.TStar_pure(t2, t1)
}

// TStarBetween captures: steps[tStarIdx] == TStar(min(t1,t2), max(t1,t2))
// AND min(t1,t2) < steps[tStarIdx] <= max(t1,t2)
ghost
decreases
pure func TStarBetween(tStarVal, t1, t2 uint64) bool {
  return (t1 < 0 || t2 < 0) ? true :  // Cannot happen for uint64, but needed as proof hint
    t1 == t2 ? true :
    t1 < t2 ?
      (tStarVal == proofs.TStar_pure(t1, t2) && t1 < tStarVal && tStarVal <= t2) :
      (tStarVal == proofs.TStar_pure(t2, t1) && t2 < tStarVal && tStarVal <= t1)
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


// Ghost seq params avoid needing to unfold IsLow (which loses low facts in hyper mode)


ghost
decreases
// this captures our assumption that GetCommitment is deterministic
// takes seq[byte] inputs so it remains pure (no heap permissions needed)
pure func GetCommitmentIsDeterministic(Label seq[byte], Version uint64, RootHash seq[byte]) *[]byte


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
ensures rel(t,0) > rel(t,1) || rel(t,0) < rel(t,1)
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
// @ requires label != nil
// @ requires acc(label)
// @ requires acc(RootHash)
// @ requires acc(steps)
// @ requires t >= 0
// @ requires prefixTree != nil ==> prefixTree.Inv()
// @ requires forall i int :: {steps[i]} 0 <= i && i < len(steps) ==> steps[i] >= 0
// @ requires 0<= tStarIdx && tStarIdx < len(steps)
// @ requires low(steps[tStarIdx])
// @ requires TStarBetween(steps[tStarIdx], rel(t, 0), rel(t, 1))
// Very basic postcondition
// @ ensures (res == 0 && err == nil) || (res == 404 && err != nil) || ((res == -1 || res == 1) && err == nil)
// Correct postcondition
// @ ensures err == nil && res==0 ==> low(t)
func CheckGreatest(prefixTree *proofs.PrefixTree, steps []uint64, label []byte, t uint64, RootHash []byte, size uint64 /*@, ghost tStarIdx int, ghost labelSeq seq[byte], ghost RootHashSeq seq[byte]@*/) (res int, err error) {

	resultRes := 0
	var resultErr error = nil
	var determined bool = false //The flag is used due to hyperproperty feature of gobra.
	idx := 0
	//@ ghost var tStarVisited bool = false
	//@ ghost var tStar uint64 = steps[tStarIdx]

	//@ non_incl_lemma := GetCommitmentIsDeterministic(labelSeq, tStar, RootHashSeq) != nil && tStar <= t
	//@ incl_lemma := GetCommitmentIsDeterministic(labelSeq, tStar, RootHashSeq) == nil && t < tStar

	//@ assert  tStarIdx < idx && !determined ==> non_incl_lemma || incl_lemma

	//@ invariant acc(RootHash)
	//@ invariant acc(label)
	//@ invariant acc(steps)
	//@ invariant forall i int :: {steps[i]} 0 <= i && i < len(steps) ==> steps[i] >= 0
	//@ invariant 0 <= idx && idx <= len(steps)
	//@ invariant  TStarBetween(steps[tStarIdx], rel(t, 0), rel(t, 1))
	//@ invariant determined ==> (resultRes == 404 && resultErr != nil) || ((resultRes == -1 || resultRes == 1) && resultErr == nil)
	//@ invariant !determined ==> resultRes == 0 && resultErr == nil
	//@ invariant tStarIdx < idx && !determined ==> non_incl_lemma || incl_lemma
	for ; idx < len(steps); idx++ {
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
				//@ assert low(incl)

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
			}
			/*@
			ghost if idx == tStarIdx{
				assert !determined ==> non_incl_lemma || incl_lemma
				tStarVisited = true
			}

			@*/

		}

	}
	/*@

		ghost if true {
		 	issue903worksaround2 := !determined && low(!determined)
			ghost if issue903worksaround2 {
				assert non_incl_lemma || incl_lemma


			}

		}

	@*/

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
// ensures err == nil && res ==> low(t)
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
	for _, frontier := range frontiers {
		if !determined {
			//@ assert frontier >= 0 && int(frontier) < len(prefixTrees)
			//@ assert acc(prefixTrees[frontier])
			Prefix_tree := prefixTrees[frontier]
			if prefixTrees[frontier] == nil {
				resultRes = false
				resultErr = err
				determined = true
			} else {
				rootHash := prefixRootHash[frontier]
				//@ assert acc(query.Label)
				if size == 0 || tVal >= size || frontier >= size {
					resultRes = false
					resultErr = errors.New("version out of bounds")
					determined = true
				}
				steps := proofs.FullBinaryLadderSteps_wrapper(tVal)

				//Postcondition from the FBLS
				//@ assert acc(steps)
				//@ ghost var labelSeq seq[byte] = getContent(query.Label)
				//@ ghost var rootHashSeq seq[byte] = getContent(rootHash[:])
				//TODO: replace me
				//@ ghost var tStarIdx int = 13

				// _, _, idx1, idx2 := EstablishTStarWitnesses(steps, tVal)

				LtGtOrEq, err := CheckGreatest(Prefix_tree, steps, query.Label, tVal, rootHash[:], size /*@, tStarIdx, labelSeq, rootHashSeq @*/)
				if err != nil {
					resultRes = false
					resultErr = err
					determined = true
				} else if LtGtOrEq == 1 {
					// Greater version exists
					resultRes = false
					resultErr = errors.New("greater version exists")
					determined = true
				} else if LtGtOrEq == 0 && terminalLogEntry == -1 {
					terminalLogEntry = int(frontier)
				}

				if frontier == size-1 {
					if LtGtOrEq != 0 {
						resultRes = false
						resultErr = errors.New("Greatest version is not the greatest in the last iteration")
						determined = true
						// assert (frontier == size - 1) ==> ( rel(!resultRes,0) || rel(!resultRes,1) || rel(resultErr!=nil, 0) || rel(resultErr!=nil,1))
					}
				}
			}
		}
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
