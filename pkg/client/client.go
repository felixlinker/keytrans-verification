package client

import (
	"crypto/sha256"
	"errors"

	"github.com/felixlinker/keytrans-verification/pkg/proofs"
)

// ##(--hyperMode extended)

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
func (st *UserState) VerifyLatest(query SearchRequest, resp SearchResponse /*@, ghost p perm @*/) (res *proofs.UpdateValue, err error) {
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
	//@ ghost var idx int
	//@ ghost var t2 uint64 =uint64(*resp.Version) + 1
	ladderIndices /*@, idx @*/ := proofs.FullBinaryLadderSteps(uint64(*resp.Version) /*@, t2 @*/)
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

	return nil, nil
}

//Lemma : Merkle Binding
// This Merkle binding theorem is needed for showing that the commitment is in the tree state
// It is also one of the important lemmas we need to show that the commitment we get is consistent
// We use the following paper to derive the following lemma
// Paper: https://arxiv.org/pdf/2501.10802
//TODO: If we can formally verify that using Gobra without using the paper, then we will have better ground to argue that the stuff is formally verified. Relying on the paper itself will be somehow risky

/*
@
ghost
opaque
decreases
pure
func CommitmentExistsInTree(RootHash []byte, label []byte, Version uint64) bool

// func deterministicFunc(label, view, version) (error)
// Use low or rel

@
*/
type PT interface {
	// Returns non-nil if we can prove that the prefix tree contains a key for the
	// label and version pair provided. Returns nil if we can prove that the
	// prefix tree does not contain a key for the label and version pair provided.
	// Returns error in any other case.
	//@ pred Mem()

	//ensures low(RootHash) ==> (rel(RootHash, 0) == rel(RootHash, 1))
	// ensures low(RootHash) && err == nil ==> low(res)
	//@ requires Label != nil && len(Label) >= 0
	//@ requires Version >= 0
	//@ ensures err == nil ==> res != nil == CommitmentExistsInTree(RootHash, Label, Version)
	//@ ensures low(RootHash) && low(Label) && low(Version) && err == nil ==> low(res)
	//@ ensures low(RootHash) && low(Label) && low(Version) ==> low(err == nil)
	//@ ensures err != nil ==> res == nil
	GetCommitment(Label []byte, Version uint64, RootHash []byte) (res []byte, err error)
}

type PTImpl struct {
	Tree       *proofs.PrefixTree
	VrfOutputs map[uint64][sha256.Size]byte // Cached VRF outputs for each version
}

func ToPrefixTree(Label []byte, frontier uint64) (prefixTree PT, err error) {
	//TODO
	return nil, nil
}

//Queries1 == Queries2 ==> Same results ==> deterministic

// CheckGreatest verifies if t is the greatest version
// Returns:
//
//	-1: Greatest version < t (found hole at or below t), the greatest version does not exist so far
//	 0: t is the greatest version
//	 1: Greatest version > t (found commitment above t), violates t being the greatest version
//
// @ requires acc(label)
// @ requires len(label) > 0
// @ requires label != nil
// @ requires t > 0
// @ requires prefixTree != nil
// Low conditions for determinism
// @ requires low(label)
// @ requires low(prefixTree)
// @ requires low(RootHash)
// Uniqueness of the FBLS
// Goal:
// @ ensures low(err == nil) && low(res == 0) ==> low(t)
func CheckGreatest(prefixTree PT, label []byte, t uint64, RootHash []byte) (res int, err error) {
	steps := proofs.FullBinaryLadderSteps_wrapper(t)
	//TODO: We need to get rid of these assumes
	//The following assert will return an error, so no assume false
	// assert 1 == 2

	//@ invariant acc(steps)
	//@ invariant 0 <= idx && idx <= len(steps)
	//@ invariant forall l int :: 0 <= l && l < len(steps) ==> steps[l] >= 0
	//@ invariant low(label)
	//@ invariant low(RootHash)
	//@ invariant low(idx)
	for idx := 0; idx < len(steps); idx++ {
		step := steps[idx]
		commitment, err := prefixTree.GetCommitment(label, step, RootHash)
		// assert 1 == 2
		if err != nil {
			return 0, err
		} else {
			incl := commitment != nil
			//@ assert low(incl)
			//@ assert low(step) && low(t)
			//@ assert low(step <= t)  // Should follow from low(step) && low(t)
			//@ assert low(t < step)

			if !incl && step <= t { //Claimed Greatest is less than t
				//@ assert low(commitment == nil)  // From PT postcondition
				//@ assert step <= t
				return -1, nil
			} else if incl && t < step { //Greatest is greater than t
				//@ assert low(commitment != nil)
				//@ assert step > t
				return 1, nil
			}
		}

	}

	return 0, nil
}

type MonitoringMapEntry struct {
	Position uint64
	Version  uint32
}

// Goal: ensures forall st, st2 *UserState :: forall query, query2 SearchRequest :: forall resp, resp2 SearchResponse :: query.Label === query2.Label && err != nil ==> st.VerifyLatestKey(query, resp, p).Value === st2.VerifyLatestKey(query2, resp2, p).Value

// @ requires acc(st)
// @ requires query.Inv()
// @ requires noPerm < p
// @ requires resp.Inv()
// @ requires size > 0
// @ requires acc(monitor_map)
// @ requires acc(resp.Version, _)
// @ requires acc(query.Label)
// @ requires len(query.Label) > 0
// @ requires resp.Full_tree_head.RootHash != nil
// ==============Hyperproperties=============
// @ requires low(size)
// @ requires low(query.Label)
// @ ensures low(err == nil) ==> low(res)
func (st *UserState) VerifyLatestKey(size uint64, query SearchRequest, resp SearchResponse, monitor_map []MonitoringMapEntry /*@, ghost p perm@*/) (res bool, err error) {
	t := resp.Version //Claimed greatest version
	tVal := uint64(*t)
	//@ t2 := tVal + 1
	//@ assert size >= 0
	search_tree := MkImplicitBinarySearchTree(size)
	// assert acc(search_tree.Inv(), p) //TODO: Memory permission needs to be done, otherwise assume false
	// Return tree
	if search_tree == nil {
		return false, errors.New("No search tree found")
	}
	//@ assert search_tree != nil
	//@ assume acc(search_tree.Inv(), p)
	frontiers := search_tree.FrontierNodes( /*@p@*/ )
	//@ assume low(len(frontiers)) && forall j uint64 :: j>= 0 && j < len(frontiers) ==> low(frontiers[j]) //TODO: Remove this assume
	terminalLogEntry := -1

	// assert 1 == 2
	//@ invariant acc(frontiers)
	//@ invariant acc(query.Label)
	//@ invariant low(len(frontiers))
	//@ invariant low(frontier)
	for _, frontier := range frontiers {
		Prefix_tree, err := ToPrefixTree(query.Label, frontier)
		if err != nil {
			return false, err
		} else {
			//ladder := st.CreateInclusionLadder(t, prefixtree_proof)
			//if LtGtOrEq, err := ladder.CompareToTheGreatest(query.Label, tVal); err != nil {
			LtGtOrEq, err := CheckGreatest(Prefix_tree, query.Label, tVal, resp.Full_tree_head.RootHash)
			if err != nil {
				return false, err
			} else {
				if LtGtOrEq == 1 {
					return false, errors.New("not the greatest version as expected")
				}
				if LtGtOrEq == 0 && terminalLogEntry == -1 {
					terminalLogEntry = int(frontier)
				}

				if frontier == size-1 {
					if LtGtOrEq != 0 {
						return false, errors.New("t is not the greatest version as expected")
					}
				}
			}
		}
	}
	if terminalLogEntry == -1 {
		return false, errors.New("Claimed Version is not found.")
	}
	if frontiers[0] < uint64(terminalLogEntry) {
		//TODO: Need also to check if it's in contact monitoring mode, omitted because it's not so important in the proof
		entry := MonitoringMapEntry{
			Position: uint64(len(frontiers) - 1),
			Version:  *t,
		}
		monitor_map = append( /*@ perm(1/2), @*/ monitor_map, entry)
	}

	//@ assert 1 == 2
	return true, nil
}
