package client

import (
	"errors"

	"github.com/felixlinker/keytrans-verification/pkg/proofs"
)

// ##(--hyperMode extended --enableExperimentalHyperFeatures)

/*@
//Compare the bytes of the arrays
ghost
decreases
requires acc(r1, _)
requires acc(r2,_)
pure
func BytesEqual(r1 []byte, r2 []byte) bool {
	return len(r1) == len(r2) && forall i int :: 0<=i && i < len(r1) ==> r1[i] ==r2[i]
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
	//@ fold acc(resp.Inv(), p)

	//Here, we assume that the tree is already built

	//@ invariant acc(resp.Inv(), p)
	// invariant unfolding acc(resp.Search.Inv(), p/2) in 0 <= i && i <= len(resp.Search.Prefix_proofs)
	//@ invariant 0 <= i && i <= len(resp.Search.Prefix_proofs)
	//@ invariant acc(trees)
	for i := 0; i < len(resp.Search.Prefix_proofs); i++ {
		//@ unfold acc(resp.Inv(), p)
		prf := /*@ unfolding acc(resp.Search.Inv(), p/2) in @*/ resp.Search.Prefix_proofs[i]
		if tree, err := prf.ToTree(resp.Binary_ladder); err != nil {
			//@ fold acc(resp.Inv(), p)
			return nil, err
		} else {
			trees = append( /*@ perm(1/2), @*/ trees, tree)
		}
		//@ fold acc(resp.Inv(), p)
	}

	// TODO: Verify proof of inclusion in all trees
	monitoringMap := make([]MonitoringMapEntry, 0)
	decision, err := VerifyLatestKey(trees, st.Size, query, resp, monitoringMap, config)
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

/*@

// func deterministicFunc(label, view, version) (error)
// Use low or rel

@
*/

/*
CheckGreatest verifies if t is the greatest version
 Returns:

	-1: Greatest version < t (found hole at or below t), the greatest version does not exist so far
	 0: t is the greatest version
	 1: Greatest version > t (found commitment above t), violates t being the greatest version
*/

// @ requires noPerm < p
// @ requires acc(label, p)
// @ requires label != nil
// @ requires t >= 0
// @ requires prefixTree != nil
// @ requires low(label)
// @ requires low(prefixTree)
// @ requires low(RootHash)
// @ requires rel(t,0) != rel(t,1)
// @ ensures rel(err==nil, 0) != rel(err==nil, 1) || rel(res, 0) != rel(res, 1)
func CheckGreatest(prefixTree *proofs.PrefixTree, label []byte, t uint64, RootHash []byte, terminalLogEntry int, frontier uint64, size uint64 /*@, ghost p perm@*/) (res int, newTerminalLogEntry int, err error) {
	steps := proofs.FullBinaryLadderSteps_wrapper(t)
	//Postcondition from the FBLS
	//@ assert acc(steps)
	// assert forall t2 uint64 :: exists idx1 int :: t < t2 ==> 0 <= idx1 && idx1 < len(steps) && t < proofs.TStar_pure(t, t2) && proofs.TStar_pure(t, t2) <= t2 && proofs.TStar_pure(t, t2) == steps[idx1]
	// assert forall t2 uint64 :: exists idx2 int :: t > t2 && t2 >= 0  ==> 0 <= idx2 && idx2 < len(steps) && proofs.TStar_pure(t2, t) == steps[idx2] && t2 < proofs.TStar_pure(t2, t) && proofs.TStar_pure(t2, t) <= t

	// @ assert forall t2 uint64 :: {proofs.TStar_wrapper(steps,t, t2)} proofs.TStar_wrapper(steps,t, t2)
	// @ assert forall t2 uint64 :: {proofs.TStar_wrapper(steps,t2, t)} proofs.TStar_wrapper(steps,t2,t)

	// Replace it using rel(t,0), rel(t,1) and rel(steps,0), rel(steps,1)

	// assert exists idx2 int :: rel(t,0) > rel(t,1)  ==>  0 <= idx2 && idx2 < len(rel(steps,0)) && proofs.TStar_pure(rel(t,1), rel(t,0)) == rel(steps,0)[idx2]
	//@ assert proofs.TStar_wrapper(rel(steps,0), rel(t,0), rel(t,1))
	// refute len(rel(steps,0)) == len(rel(steps,1)) ==> exists idx int :: 0 <= idx && idx < len(rel(steps,0)) ==> rel(steps,0)[idx] != rel(steps,1)[idx]
	// assert  exists idx3 int :: rel(t,0) > rel(t,1) ==> 0 <= idx3 && idx3 < len(rel(steps,1)) && proofs.TStar_pure(rel(t,1), rel(t,0)) == rel(steps,1)[idx3]
	// assert proofs.TStar_wrapper(rel(steps,1),rel(t,0),rel(t,1))
	// exhale acc(rel(steps,1), 1/12)
	//@ assert rel(proofs.TStar_wrapper(rel(steps,1),rel(t,0),rel(t,1)), 1)

	// exists idx1 int :: rel(t,0) < rel(t,1) ==> 0 <= idx1 && idx1 < len(rel(steps,0)) && proofs.TStar_pure(rel(t,0), rel(t,1)) == rel(steps,0)[idx1]
	//@ assert proofs.TStar_wrapper(rel(steps,0), rel(t,1), rel(t,0))
	// exists idx4 int :: rel(t,0) < rel(t,1) ==> 0 <= idx4 && idx4 < len(rel(steps,1)) && proofs.TStar_pure(rel(t,0), rel(t,1)) == rel(steps,1)[idx4]
	// assert proofs.TStar_wrapper(rel(steps,1), rel(t,1), rel(t,0))
	//@ assert rel(proofs.TStar_wrapper(rel(steps,1),rel(t,1),rel(t,0)), 1)

	//Replace with rel(steps,0) and rel(steps,1) with bound
	// assume acc(rel(steps,1), p) // Will cause an error in this case, a java concurrency error...
	// TODO: I don't think there is any way to make this code provable besides digging into the Gobra code and fix the encoding.
	//@ inhale acc(rel(steps,1),1/12)
	//@ assert exists idx2, idx3 int :: rel(t,0) > rel(t,1) ==> 0 <= idx2 && idx2 < len(rel(steps,0)) && 0 <= idx3 && idx3 < len(rel(steps,1)) && rel(steps,1)[idx3] == rel(steps,0)[idx2] && rel(t,1) <= rel(steps,1)[idx3] && rel(steps,1)[idx3] < rel(t,0)
	//@ assert exists idx2, idx3 int :: rel(t,0) > rel(t,1) ==> 0 <= idx2 && idx2 < len(rel(steps,0)) && 0 <= idx3 && idx3 < len(rel(steps,1)) && rel(steps,1)[idx3] == rel(steps,0)[idx2] && rel(t,1) <= rel(steps,0)[idx2] && rel(steps,0)[idx2] < rel(t,0)

	//@ assert exists idx1, idx4 int :: rel(t,0) < rel(t,1) ==> 0 <= idx1 && idx1 < len(rel(steps,0)) && 0 <= idx4 && idx4 < len(rel(steps,1)) && rel(steps,1)[idx4] == rel(steps,0)[idx1]&& rel(t,0) <= rel(steps,1)[idx4] && rel(steps,1)[idx4] < rel(t,1)
	//@ assert exists idx1, idx4 int :: rel(t,0) < rel(t,1) ==> 0 <= idx1 && idx1 < len(rel(steps,0)) && 0 <= idx4 && idx4 < len(rel(steps,1)) && rel(steps,1)[idx4] == rel(steps,0)[idx1]&& rel(t,0) <=rel(steps,0)[idx1] && rel(steps,0)[idx1] < rel(t,1)

	//Move existential quantifier to the right side of the implication

	//@ assert rel(t,0) < rel(t,1) ==> exists idx1, idx4 int :: 0 <= idx1 && idx1 < len(rel(steps,0)) && 0 <= idx4 && idx4 < len(rel(steps,1)) && rel(steps,1)[idx4] == rel(steps,0)[idx1]&& rel(t,0) <= rel(steps,1)[idx4] && rel(steps,1)[idx4] < rel(t,1)
	//@ assert rel(t,0) < rel(t,1) ==> exists idx1, idx4 int :: 0 <= idx1 && idx1 < len(rel(steps,0)) && 0 <= idx4 && idx4 < len(rel(steps,1)) && rel(steps,1)[idx4] == rel(steps,0)[idx1]&& rel(t,0) <=rel(steps,0)[idx1] && rel(steps,0)[idx1] < rel(t,1)

	//@ assert !low(t) ==> exists idx1, idx4 int :: 0 <= idx1 && idx1 < len(rel(steps,0)) && 0 <= idx4 && idx4 < len(rel(steps,1)) && rel(steps,1)[idx4] == rel(steps,0)[idx1]

	resultRes := 0
	var resultErr error = nil

	// idx0 != idx1 and idx0 == idx1 ==> differences, with assume
	// Fixed iteration observation ==> assumes ==> arbitrary loop iteration

	//@ invariant acc(steps)
	//@ invariant 0 <= idx && idx <= len(steps)
	//@ invariant forall l int :: 0 <= l && l < len(steps) ==> steps[l] >= 0
	//@ invariant low(label)
	//@ invariant low(RootHash)
	// invariant exists idx int :: rel(steps,0)[idx] != rel(steps,1)[idx] //Unsound example, ignore for now I think
	//@ invariant !low(resultRes) || !low(resultErr==nil)
	for idx := 0; idx < len(steps); idx++ {
		step := steps[idx]
		commitment, err := prefixTree.GetCommitment(label, step, RootHash)
		// Assume hiding and binding.
		//@ assume low(label) && low(step) && rel(err==nil,0)==rel(err==nil, 1) ==> low(commitment) //Hiding
		//@ assume low(label) && low(step) && BytesEqual(rel(RootHash,0),rel(RootHash,1)) ==> BytesEqual(rel(commitment,0), rel(commitment,1)) && rel(err, 0) == rel(err,1) //Binding
		//@ assert rel(step,0) != rel(step,1) ==> !BytesEqual(rel(commitment,0), rel(commitment,1))
		//@ assert rel(step,0) == rel(step,1) && proofs.TStar_pure(rel(t,1), rel(t,0)) != step ==> BytesEqual(rel(commitment,0), rel(commitment,1))
		//@ assert rel(step,0) == rel(step,1) && proofs.TStar_pure(rel(t,1), rel(t,0)) == step ==> !BytesEqual(rel(commitment,0), rel(commitment,1))
		if err != nil {
			resultRes = 0
			resultErr = err
			//determined = true
			break
		} else {
			incl := commitment != nil
			//@ assert !BytesEqual(rel(commitment,0), rel(commitment,1)) ==> rel(incl,0) != rel(incl,1)
			//@ assert  BytesEqual(rel(commitment,0), rel(commitment,1)) ==> rel(incl, 0) == rel(incl,1)
			if !incl && step <= t { // Claimed Greatest is less than t
				resultRes = -1
				resultErr = nil
				//determined = true
				break
			} else if incl && t < step { // Greatest is greater than t
				//@ assert rel(incl,0) != rel(incl,1) || rel(t < step,0) != rel(t < step,1)
				resultRes = 1
				resultErr = nil
				//determined = true
				break
			}
		}
		//To avoid Early termination: if determined is true, we just continue looping without doing anything
	}

	// assert 1 == 2
	//Again, avoid early termination because of Gobra Hyperproperty mode
	LtGtOrEq := resultRes
	err = resultErr
	newTerminalLogEntry = terminalLogEntry

	//Final Result values
	finalRes := LtGtOrEq
	finalNewTerminalLogEntry := newTerminalLogEntry
	var finalErr error = nil

	if err != nil {
		finalRes = 0
		finalNewTerminalLogEntry = terminalLogEntry
		finalErr = err
	} else {
		// Check if LtGtOrEq == 1
		if LtGtOrEq == 1 {
			finalRes = 0
			finalNewTerminalLogEntry = terminalLogEntry
			finalErr = errors.New("not the greatest version as expected")
		} else {
			// Update terminal log entry if needed
			if LtGtOrEq == 0 && terminalLogEntry == -1 {
				finalNewTerminalLogEntry = int(frontier)
			}

			// Check frontier condition
			if frontier == size-1 {
				if LtGtOrEq != 0 {
					finalRes = 0
					finalErr = errors.New("t is not the greatest version as expected")
				}
				//Injectivity missing!
				//@ assert finalErr == nil && frontier == size-1 && finalRes == 0 && low(finalErr== nil) && low(frontier == size-1) && low(finalRes == 0)==> low(t)
			}
		}
	}
	//Final assert
	//@ assert rel(finalRes,0) != rel(finalRes,1) || rel(finalErr==nil,0) != rel(finalErr==nil,1)
	return finalRes, finalNewTerminalLogEntry, finalErr
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
// @ requires acc(config,p)
// @ requires forall i int :: i >= 0 && i < len(prefixTrees) ==> acc(&prefixTrees[i])
// @ requires forall i int :: {&prefixTrees[i]} i >= 0 && i < len(prefixTrees) ==> acc(prefixTrees[i].Inv(), p)
// @ requires forall i int :: i >= 0 && i < len(prefixTrees) ==> prefixTrees[i] != nil
// @ requires resp.Version != nil
// @ requires size > 0
// @ requires *resp.Version >=0
// @ requires resp.Full_tree_head.RootHash != nil
// @ requires low(size)
// @ requires low(query.Label)
// @ requires rel(resp.Version, 0) != rel(resp.Version,1)
// @ ensures rel(err==nil,0) != rel(err==nil,1) && rel(res,0) != rel(res,1)
func VerifyLatestKey(prefixTrees []*proofs.PrefixTree, size uint64, query SearchRequest, resp SearchResponse, monitor_map []MonitoringMapEntry, config *Configuration /*@, ghost p perm@*/) (res bool, err error) {
	t := resp.Version //Claimed greatest version
	tVal := uint64(*t)
	search_tree := MkImplicitBinarySearchTree(size)
	// assert acc(search_tree.Inv(), p)
	// Variables to track result and avoid early termination
	resultRes := true
	var greatest int = -2
	var resultErr error = nil
	if search_tree == nil {
		resultRes = false
		resultErr = errors.New("No search tree found")
		//return false, errors.New("No search tree found")
	}
	if query.Label == nil && err == nil {
		resultRes = false
		resultErr = errors.New("No search tree found")
		//return false, errors.New("Empty label :(")
	}
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
	//@ invariant acc(query.Label, p)
	//@ invariant forall i int :: i >= 0 && i < len(prefixTrees) ==> prefixTrees[i] != nil
	//@ invariant forall i int :: i >= 0 && i < len(frontiers) ==> frontiers[i]>=0 && frontiers[i] < uint64(len(prefixTrees))
	//@ invariant low(size) ==> low(len(frontiers)) && forall j int :: j>= 0 && j < len(frontiers) ==> low(frontiers[j])
	//@ invariant low(resultErr == nil) ==> low(err == nil)
	// invariant low(err == nil) && low(!determined) && low(greatest == 0) ==> low(resultRes) && low(tVal)
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
			//@ assert acc(query.Label)
			if size == 0 || tVal >= size || frontier >= size {
				resultRes = false
				resultErr = errors.New("version out of bounds")
				break
				//return false, errors.New("version out of bounds")
			}
			greatest, terminalLogEntry, err = CheckGreatest(Prefix_tree, query.Label, tVal, resp.Full_tree_head.RootHash, terminalLogEntry, frontier, size /*@,p@*/)
			if err != nil {
				resultRes = false
				resultErr = err
				//determined = true
				break
			}
		}
	}

	// assert low(resultErr == nil) && low(determined) && low(greatest==0) ==> low(resultRes) && low(tVal)
	// Post-loop logic (only execute if no error occurred in the loop)

	if terminalLogEntry == -1 && err == nil {
		resultRes = false
		resultErr = errors.New("Claimed Version is not found.")
	} else if frontiers[0] < uint64(terminalLogEntry) && config.Mode == 1 {
		entry := MonitoringMapEntry{
			Position: uint64(len(frontiers) - 1),
			Version:  *t,
		}
		monitor_map = append( /*@ perm(1/2), @*/ monitor_map, entry)
	}

	// assert false
	return resultRes, resultErr
}
