package client

import (
	"errors"

	"github.com/felixlinker/keytrans-verification/pkg/proofs"
)

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

	ladderIndices := proofs.FullBinaryLadderSteps(uint64(*resp.Version))
	if len(resp.Binary_ladder) != len(ladderIndices) {
		//@ fold acc(resp.Inv(), p)
		return nil, errors.New("length of binary ladder does not match greatest version")
	}

	trees := make([]*proofs.PrefixTree, 0, len(resp.Search.Prefix_proofs))
	//@ fold acc(resp.Inv(), p)

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

// @ trusted
func (st *UserState) CreateInclusionLadder(targetVersion *uint32, vrfs proofs.VRFProof) (ladder proofs.Ladder) {
	Ladd := proofs.Ladder{
		Inclusions:    []proofs.VRFInput{},
		NonInclusions: []proofs.VRFInput{},
	}

	for labelVersion, value := range vrfs.Mapping {
		labelVersionKey := labelVersion.ToVRFInput()
		if value {
			Ladd.Inclusions = append(Ladd.Inclusions, labelVersionKey)
		} else {
			Ladd.NonInclusions = append(Ladd.NonInclusions, labelVersionKey)
		}
	}
	return ladder
}

type PT interface {
	// Returns non-nil if we can prove that the prefix tree contains a key for the
	// label and version pair provided. Returns nil if we can prove that the
	// prefix tree does not contain a key for the label and version pair provided.
	// Returns error in any other case.

	//@ requires Label != nil
	//@ requires len(Label) >= 0
	//@ requires Version >= 0
	//@ ensures err == nil ==> (res != nil || res == nil)
	//@ ensures err != nil ==> res == nil
	GetCommitment(Label []byte, Version uint64) (res []byte, err error)
}

// @ requires acc(label)
// @ requires len(label) > 0
// @ requires label != nil
// @ requires t != t2
// @ requires t >= 0 && t2 >= 0
// @ requires prefixTree != nil
func CheckGreatest(prefixTree PT, label []byte, t uint64 /*@, t2 uint64@*/) (res int, err error) {
	steps /*@, idx2 @*/ := proofs.FullBinaryLadderSteps(t /*@, t2@*/)

	//@ invariant acc(steps)
	//@ invariant idx >= 0 && idx <= len(steps)
	//@ invariant forall l uint64 :: l >= 0 && l < len(steps) ==> steps[l]>=0
	for idx := 0; idx < len(steps); idx++ {
		step := steps[idx]
		if commitment, err := prefixTree.GetCommitment(label, step); err != nil {
			return 0, err
		} else {
			incl := commitment != nil
			if !incl && step <= t { //Greatest is less than t
				return -1, nil
			} else if incl && t < step { //Greatest is greater than t
				return 1, nil
			} else if incl && step <= t {
				continue
			} else if !incl && t < step {
				continue
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
// @ requires acc(monitor_map)
// @ requires acc(resp.Version, _)
func (st *UserState) VerifyLatestKey(query SearchRequest, resp SearchResponse, monitor_map []MonitoringMapEntry /*@, ghost p perm@*/) (res *proofs.UpdateValue, err error) {
	t := resp.Version //Claimed greatest version
	tVal := uint64(*t)

	search_tree := MkImplicitBinarySearchTree(st.Size)
	//@ assume acc(search_tree, p)
	frontiers := search_tree.FrontierNodes( /*@p@*/ )
	terminalLogEntry := -1

	for _, frontier := range frontiers {
		prefixtree_proof := resp.Inclusion.VRFProofs[frontier]
		ladder := st.CreateInclusionLadder(t, prefixtree_proof)
		if LtGtOrEq, err := ladder.CompareToTheGreatest(query.Label, tVal); err != nil {
			return nil, err
		} else {
			if LtGtOrEq == 1 {
				return nil, errors.New("not the greatest version as expected")
			}
			if LtGtOrEq == 0 && terminalLogEntry == -1 {
				terminalLogEntry = int(frontier)
			}

			if frontier == st.Size-1 {
				if LtGtOrEq != 0 {
					return nil, errors.New("t is not the greatest version as expected")
				}
			}
		}
	}
	if terminalLogEntry == -1 {
		return nil, errors.New("Claimed Version is not found.")
	}
	if frontiers[0] < uint64(terminalLogEntry) {
		//TODO: Need also to check if it's in contact monitoring mode, omitted because it's not so important in the proof
		entry := MonitoringMapEntry{
			Position: uint64(len(frontiers) - 1),
			Version:  *t,
		}
		monitor_map = append( /*@ perm(1/2), @*/ monitor_map, entry)
	}

	return nil, nil
}

// TODO: Prove me
// @ requires query1.Label === query2.Label
// @ requires resp1.Full_tree_head.RootHash === resp2.Full_tree_head.RootHash
// @ requires resp1.Version != resp2.Version
// @ ensures err1 != nil || err2 != nil
func VerifylatestKeyWrapper(query1 SearchRequest, resp1 SearchResponse, query2 SearchRequest, resp2 SearchResponse) (err1 error, err2 error)
