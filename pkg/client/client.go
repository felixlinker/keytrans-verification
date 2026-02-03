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

/*@
ghost
decreases
ensures res > 0
pure
func GetInt() (res int)
@*/

/*
// func deterministicFunc(label, view, version) (error)
// Use low or rel
*/

/*@
// We need a lemma for functional correctness. This consists of determinism

ghost
decreases
pure
func VersionExists(label []byte, version uint64, RootHash []byte) (r bool)
// return tree.Value == RootHash && tree.Contains(VRF(label, version))
@*/

/*
CheckGreatest verifies if t is the greatest version
 Returns:

	-1: Greatest version < t (found hole at or below t), the greatest version does not exist so far
	 0: t is the greatest version
	 1: Greatest version > t (found commitment above t), violates t being the greatest version
*/
//TODO: We need to somehow grab the value of the root from the tree and see if the hash root is equal
// @ requires noPerm < p
// @ requires label != nil
// @ requires t >= 0
// @ requires prefixTree != nil ==> prefixTree.Inv()
// @ requires acc(label)
// @ requires low(len(label)) && (forall i int :: {label[i]} 0<= i && i < len(label) ==> low(label[i]))
// @ requires acc(RootHash)
// @ requires low(len(RootHash)) && (forall i int :: {RootHash[i]} 0<= i && i < len(RootHash) ==>  low(RootHash[i]))
// @ requires rel(t,0) != rel(t,1)
// @ requires low(t>=0)
// @ ensures rel(err==nil, 0) != rel(err==nil, 1) || rel(res, 0) != rel(res, 1) || (res == -42 && err == nil)
func CheckGreatest(prefixTree *proofs.PrefixTree, label []byte, t uint64, RootHash []byte, size uint64 /*@, ghost p perm@*/) (res int, err error) {
	//steps/*, idx*/ := proofs.FullBinaryLadderSteps(t/*, rel(t,0)*/) //Das andere
	//steps2 /*, idx2*/ := proofs.FullBinaryLadderSteps(t/*, rel(t,1)*/)

	steps := proofs.FullBinaryLadderSteps_wrapper(t)

	//@ ghost var t0 uint64 = rel(t,0)
	//@ ghost var t1 uint64 = rel(t,1)
	//@ ghost var TStar uint64 = 0
	/*@
	ghost if t0 < t1{
		assert t0 >=0
		TStar = proofs.TStar_pure(t0,t1)
	}else if t1 < t0{
		assert t1 >= 0
		TStar = proofs.TStar_pure(t1,t0)
	}
	@*/

	//Postcondition from the FBLS
	//@ assert acc(steps)
	// assert forall t2 uint64 :: exists idx1 int :: t < t2 ==> 0 <= idx1 && idx1 < len(steps) && t < proofs.TStar_pure(t, t2) && proofs.TStar_pure(t, t2) <= t2 && proofs.TStar_pure(t, t2) == steps[idx1]
	// assert forall t2 uint64 :: exists idx2 int :: t > t2 && t2 >= 0  ==> 0 <= idx2 && idx2 < len(steps) && proofs.TStar_pure(t2, t) == steps[idx2] && t2 < proofs.TStar_pure(t2, t) && proofs.TStar_pure(t2, t) <= t

	// @ assert forall t2 uint64 :: {proofs.TStar_wrapper(steps,t, t2)} proofs.TStar_wrapper(steps,t, t2)
	// @ assert forall t2 uint64 :: {proofs.TStar_wrapper(steps,t2, t)} proofs.TStar_wrapper(steps,t2,t)

	// Replace it using rel(t,0), rel(t,1) and rel(steps,0), rel(steps,1)

	// assert exists idx2 int :: rel(t,0) > rel(t,1)  ==>  0 <= idx2 && idx2 < len(rel(steps,0)) && proofs.TStar_pure(rel(t,1), rel(t,0)) == rel(steps,0)[idx2]
	//@ assert proofs.TStar_wrapper(rel(steps,0), rel(t,0), rel(t,1))
	// assert  exists idx3 int :: rel(t,0) > rel(t,1) ==> 0 <= idx3 && idx3 < len(rel(steps,1)) && proofs.TStar_pure(rel(t,1), rel(t,0)) == rel(steps,1)[idx3]
	// assert proofs.TStar_wrapper(rel(steps,1),rel(t,0),rel(t,1))
	//@ assert rel(proofs.TStar_wrapper(rel(steps,1),rel(t,0),rel(t,1)), 1)

	// exists idx1 int :: rel(t,0) < rel(t,1) ==> 0 <= idx1 && idx1 < len(rel(steps,0)) && proofs.TStar_pure(rel(t,0), rel(t,1)) == rel(steps,0)[idx1]
	//@ assert proofs.TStar_wrapper(rel(steps,0), rel(t,1), rel(t,0))
	// exists idx4 int :: rel(t,0) < rel(t,1) ==> 0 <= idx4 && idx4 < len(rel(steps,1)) && proofs.TStar_pure(rel(t,0), rel(t,1)) == rel(steps,1)[idx4]
	// assert proofs.TStar_wrapper(rel(steps,1), rel(t,1), rel(t,0))
	//@ assert rel(proofs.TStar_wrapper(rel(steps,1),rel(t,1),rel(t,0)), 1)

	//Replace with rel(steps,0) and rel(steps,1) with bound
	// assume acc(rel(steps,1), p) // Will cause an error in this case, a java concurrency error...
	//@ idx1 := GetInt()
	//@ idx2 := GetInt()
	//@ idx3 := GetInt()
	//@ idx4 := GetInt()
	//@ assume rel(t,0) > rel(t,1) ==> 0 <= idx2 && idx2 < len(rel(steps,0)) && 0 <= idx3 && idx3 < len(rel(steps,1)) && rel(steps[idx3],1) == rel(steps[idx2],0) && rel(t,1) <= rel(steps[idx3],1) && rel(steps[idx3],1) < rel(t,0)
	//@ assume rel(t,0) < rel(t,1) ==> 0 <= idx1 && idx1 < len(rel(steps,0)) && 0 <= idx4 && idx4 < len(rel(steps,1)) && rel(steps[idx4],1) == rel(steps[idx1],0)&& rel(t,0) <= rel(steps[idx4],1) && rel(steps[idx4],1) < rel(t,1)

	//@ assert rel(t,0) > rel(t,1) ==> 0 <= idx2 && idx2 < len(rel(steps,0)) && 0 <= idx3 && idx3 < len(rel(steps,1)) && rel(steps[idx3],1) == rel(steps[idx2],0) && rel(t,1) <= rel(steps[idx2],0) && rel(steps[idx2],0) < rel(t,0)
	//@ assert rel(t,0) < rel(t,1) ==> 0 <= idx1 && idx1 < len(rel(steps,0)) && 0 <= idx4 && idx4 < len(rel(steps,1)) && rel(steps[idx4],1) == rel(steps[idx1],0)&& rel(t,0) <=rel(steps[idx1],0) && rel(steps[idx1],0) < rel(t,1)

	//Move existential quantifier to the right side of the implication

	//@ assert rel(t,0) < rel(t,1) ==> 0 <= idx1 && idx1 < len(rel(steps,0)) && 0 <= idx4 && idx4 < len(rel(steps,1)) && rel(steps[idx4],1) == rel(steps[idx1],0)&& rel(t,0) <= rel(steps[idx4],1) && rel(steps[idx4],1) < rel(t,1)
	//@ assert rel(t,0) < rel(t,1) ==> 0 <= idx1 && idx1 < len(rel(steps,0)) && 0 <= idx4 && idx4 < len(rel(steps,1)) && rel(steps[idx4],1) == rel(steps[idx1],0)&& rel(t,0) <=rel(steps[idx1],0) && rel(steps[idx1],0) < rel(t,1)

	resultRes := -42
	var resultErr error = nil
	var determined bool = false //The flag is used due to hyperproperty feature of gobra.
	//@ assert acc(steps)

	// step0 != step1 and idx0 == idx1 ==> differences, with assume
	// Fixed iteration observation ==> assumes ==> arbitrary loop iteration

	//Using pred to do low and acc sucks because it will always return an issue with permission error
	//Apparently, there will be an issue with acc(s1) && acc(s2) will lead to permission error than using line by line .....

	//@ invariant acc(RootHash)
	//@ invariant acc(label)
	//@ invariant acc(steps)
	//@ invariant low(len(RootHash))
	//@ invariant low(len(label))
	//@ invariant forall i int :: {RootHash[i]} 0<= i && i < len(RootHash) ==> low(RootHash[i])
	//@ invariant forall i int :: {label[i]} 0<= i && i < len(label) ==> low(label[i])
	//@ invariant forall i int :: {steps[i]} 0<= i && i < len(steps) ==> steps[i] >= 0
	//@ invariant rel(t, 0) != rel(t,1)
	// we need something for already diverged
	//@ invariant !determined ==> (resultRes == -42 && resultErr == nil)
	//@ invariant determined ==> (resultRes == 404 && resultErr != nil) || ((resultRes == -1 || resultRes == 1) && resultErr == nil)
	//@ invariant rel(determined, 0) != rel(determined, 1) ==> (determined ==> (resultRes == -1 || resultRes == 1) && resultErr == nil)
	//@ invariant (rel(resultRes, 0) != rel(resultRes, 1) || rel(resultErr==nil, 0) != rel(resultErr==nil, 1)) || (!determined && resultRes == -42 && resultErr == nil)
	//@ invariant (rel(determined,0) || rel(determined,1)) ==> (rel(resultErr==nil,0) != rel(resultErr==nil,1) || rel(resultRes,0) != rel(resultRes,1))
	for _, step := range steps {
		if !determined {
			commitment, err := prefixTree.GetCommitment(label, step, RootHash)
			// Assume injectivity and Functional correctness
			//@ assume !rel(determined, 0) && !rel(determined, 1) ==> rel(step, 0) == rel(step, 1) && err == nil && rel(commitment == nil, 0) == rel(commitment == nil, 1)

			if err != nil {
				//@ assert err != nil
				resultRes = 404
				resultErr = err
				determined = true
				/*@
				ghost if step == TStar{
					assert err != nil
					assert resultErr != nil
				}

				@*/
				//break
			} else {
				incl := commitment != nil
				//@ assert step == TStar ==> low(incl)
				//TODO: Analyse those assumes
				//@ assume step != TStar ==> !low(!incl && step <= t) && !low(incl && t < step)
				//I think this is actually the FBLS giving us that. This is the case which it continues.
				/*@
				ghost if step == TStar{
					//step is now between t0 and t1, so the path must differ
					ghost if t0 < t1{
						assert rel(t < step,0)
						assert !rel(t < step, 1)
						assert !rel(step <= t, 0)
						assert rel(step <=t , 1)
						ghost if incl{
							// Branch 2: incl && t < step
							assert rel(incl && t< step,0) != rel(incl && t < step, 1)
							}else {
								assert rel(!incl && step <= t, 0)!= rel(!incl && step <= t, 1)
						}
					} else {
							//Symmetric, now between t1 and t0
							assert !rel(t< step,0)
							assert rel(t < step, 1)
							assert rel(step <= t, 0)
							assert !rel(step <=t , 1)

							ghost if incl{
									assert rel(incl && t< step,0) != rel(incl && t < step, 1)
								} else{
									assert rel(!incl && step <= t ,0) != rel(!incl && step <=t, 1)
								}
							}
							assert rel(!incl && step <=t, 0) != rel(!incl && step <=t, 1) || rel(incl && t < step, 0) != rel(incl&& t < step,1)
					}
				@*/
				//@ assert step == TStar ==> rel(!incl && step <=t, 0) != rel(!incl && step <=t, 1) || rel(incl && t < step, 0) != rel(incl&& t < step,1)

				if !incl && step <= t { // Claimed Greatest is less than t
					resultRes = -1
					resultErr = nil
					determined = true
					/*@
					ghost if step == TStar{
						// Only one execution reaches here if my assumption is correct
						assert rel(resultRes,0)!= rel(resultRes,1)
						assert rel(resultRes,0) != rel(resultRes,1) || rel(resultErr==nil,0) != rel(resultErr==nil,1)
						}
					@*/
					//@ assert resultErr == nil
					//break
					//@ assert step == TStar && rel(resultErr==nil, 0) != rel(resultErr==nil, 1) ==> rel(resultRes,0) != rel(resultRes,1)
				} else if incl && t < step { // Greatest is greater than t
					resultRes = 1
					resultErr = nil
					determined = true
					/*@
					ghost if step == TStar{
						// Only one execution reaches here if my assumption is correct
						assert rel(resultRes,0)!= rel(resultRes,1)
						 assert rel(resultRes,0) != rel(resultRes,1) || rel(resultErr==nil,0) != rel(resultErr==nil,1)
					}
					@*/
					//@ assert resultErr == nil
					//break
					//@ assert step == TStar && rel(resultErr==nil, 0) != rel(resultErr==nil, 1) ==> rel(resultRes,0) != rel(resultRes,1)
				}
				//Neither branch taken
				// assert(resultErr == nil && !((!incl && step <= t) || (incl && t < step))) || rel(resultRes, 0) != rel(resultRes, 1)
			}
			//To avoid Early termination: if determined is true, we just continue looping without doing anything
		}
	}
	//@ assert !determined ==> resultRes == -42 && resultErr == nil
	//@ assert determined ==> rel(resultErr==nil, 0) != rel(resultErr==nil, 1) || rel(resultRes, 0) != rel(resultRes, 1)
	//@ assert (!rel(determined,0) && !rel(determined,1)) ==> (resultRes == -42 && resultErr == nil)
	//@ assert (rel(determined,0) || rel(determined,1)) ==> (rel(resultErr==nil,0) != rel(resultErr==nil,1) || rel(resultRes,0) != rel(resultRes,1))
	//@ assert (rel(resultErr==nil,0) != rel(resultErr==nil,1) || rel(resultRes,0) != rel(resultRes,1)) || (resultRes == -42 && resultErr == nil)
	//@ assert false
	//As TStar is in the ladder and rel(resultRes,0)!= rel(resultRes,1), this always hold given on the conditions.

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
	// invariant low(err == nil) && low(!determined) && low(greatest == 0) ==> low(resultRes) && low(tVal)
	//@ invariant rel(resultRes,0) != rel(resultRes,1) || rel(resultErr==nil, 0) != rel(resultErr==nil,1) || (resultRes && resultErr == nil)
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
			//determined = true
			break
		} else {
			rootHash := prefixRootHash[frontier]
			//@ assert acc(query.Label)
			if size == 0 || tVal >= size || frontier >= size {
				resultRes = false
				resultErr = errors.New("version out of bounds")
				break
				//return false, errors.New("version out of bounds")
			}
			LtGtOrEq, err := CheckGreatest(Prefix_tree, query.Label, tVal, rootHash[:], size /*@,p@*/)
			if err != nil {
				resultRes = false
				resultErr = err
				break
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

/*

	// ghost var commitment0 []byte = rel(commitment,0)
	// ghost var commitment1 []byte = rel(commitment,1)

	// assume acc(commitment0)
	// assume acc(commitment1)
	// assume low(len(label)) && (forall i int :: {label[i]} 0<= i && i < len(label) ==> low(label[i])) && low(step) && low(err == nil) ==> low((commitment != nil) == VersionExists(label, step, RootHash))
	// assume low(len(label)) && (forall i int :: {label[i]} 0<= i && i < len(label) ==> low(label[i])) && low(step) && low(err == nil) ==> low((commitment == nil) == !VersionExists(label, step, RootHash))
	//Maybe we only need this. We assume Merkle Binding

	// assume low(len(label)) && (forall i int :: {label[i]} 0<= i && i < len(label) ==> low(label[i])) && low(step) && low(err == nil) ==> low(commitment == nil)
	// assume low(len(label)) && (forall i int :: {label[i]} 0<= i && i < len(label) ==> low(label[i])) && low(step) && low(err == nil) ==> len(commitment0) == len(commitment1)
	//TODO: Error with the memory permission...
	// assume low(len(label)) && (forall i int :: {label[i]} 0<= i && i < len(label) ==> low(label[i])) && low(step) && low(err == nil) ==> (forall i int :: {commitment0[i], commitment1[i]} 0<= i && i < len(label) ==> commitment0[i] == commitment1[i])
// assert !low(t) ==> 0 <= idx1 && idx1 < len(rel(steps,0)) && 0 <= idx4 && idx4 < len(rel(steps,1)) && rel(steps[idx4],1) == rel(steps[idx1],0)
*/
