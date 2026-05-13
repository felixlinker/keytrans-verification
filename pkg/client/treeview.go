package client

import (
	"errors"

	"github.com/felixlinker/keytrans-verification/pkg/proofs"
	"github.com/felixlinker/keytrans-verification/pkg/search"
	//@ "github.com/felixlinker/keytrans-verification/pkg/utils"
)

type UserState struct {
	Size                uint64 // 0 means no tree
	Full_subtrees       []*proofs.NodeValue
	Frontier_timestamps []uint64
}

/*@
pred (s *UserState) Inv() {
	acc(s) &&
	acc(s.Full_subtrees) &&
	// NodeValue is a fixed-size array and, thus, does not require further permissions
	acc(s.Frontier_timestamps) &&
	(s.Size == 0 ==> len(s.Full_subtrees) == 0)
}
@*/

// @ requires noPerm < p
// @ preserves acc(timestamps, p)
// @ ensures res ==> forall i, j int :: { timestamps[i], timestamps[j] } 0 <= i && i < j && j < len(timestamps) ==> timestamps[i] <= timestamps[j]
// @ decreases
func checkIncreasing(timestamps []uint64 /*@, ghost p perm @*/) (res bool) {
	res = true
	if len(timestamps) > 0 {
		tmp := timestamps[0]
		//@ invariant 0 <= k && k <= len(timestamps)
		//@ invariant acc(timestamps, p)
		//@ invariant res ==> forall i int :: { timestamps[i] } 0 <= i && i < k ==> timestamps[i] <= tmp
		//@ invariant res ==> forall i, j int :: { timestamps[i], timestamps[j] } 0 <= i && i < j && j < k ==> timestamps[i] <= timestamps[j]
		//@ decreases len(timestamps) - k
		for k := 0; k < len(timestamps); k++ {
			v := timestamps[k]
			if tmp > v {
				res = false
			}
			tmp = v
		}
	}

	return res
}

// @ requires  noPerm < p
// @ preserves st.Inv()
// @ preserves acc(newHead.Inv(), p)
// since we take the timestamps from `prf`, we need full permissions to then
// @ preserves acc(prf.Inv(), p)
// @ ensures err == nil ==> unfolding st.Inv() in st.Size == newHead.Size()
// @ ensures err == nil && low(newHead.Size()) ==> unfolding st.Inv() in low(st.Size)
// @ trusted
func (st *UserState) UpdateView(newHead FullTreeHead, prf proofs.CombinedTreeProof /*@, ghost p perm @*/) (err error) {
	//@ unfold acc(prf.Inv(), p)

	if !checkIncreasing(prf.Timestamps /*@, p/2 @*/) {
		//@ fold acc(prf.Inv(), p)
		return errors.New("timestamps not increasing")
	}
	if newHead.Tree_head.Tree_size == 0 {
		//@ fold acc(prf.Inv(), p)
		return errors.New("new tree cannot be empty")
	}

	// TODO: Verify proof of consistency

	//@ unfold st.Inv()
	origSize := st.Size
	origSubtrees := st.Full_subtrees
	origTimestamps := st.Frontier_timestamps

	oldFrontier := search.Frontier(origSize)
	newFrontier := search.Frontier(newHead.Tree_head.Tree_size)

	if st.Size == 0 {
		// copy timestamps from `prf`:
		timestamps := make([]uint64, len(prf.Timestamps))
		copy(timestamps, prf.Timestamps /*@, p/2 @*/)
		st.Frontier_timestamps = timestamps
		//TODO: This is rather for subtree implementation. We don't need it I think.
		subtrees := make([]*proofs.NodeValue, len(prf.Inclusion.Elements))
		copy(subtrees, prf.Inclusion.Elements)
		st.Full_subtrees = subtrees
	} else {
		pathToOldHead := search.PathToNode(origSize-1, newHead.Tree_head.Tree_size)

		i := 0
		//@ invariant 0 <= i && i <= len(pathToOldHead) && i <= len(oldFrontier)
		//@ invariant acc(pathToOldHead) && acc(oldFrontier)
		for ; i < len(pathToOldHead) && i < len(oldFrontier) && pathToOldHead[i] == oldFrontier[i]; i++ {
		}
		//Additional checks
		if i > len(st.Full_subtrees) || i > len(prf.Inclusion.Elements) {
			//@ fold st.Inv()
			//@ fold acc(prf.Inv(), p)
			return errors.New("consistency check failed: insufficient frontier data")
		}
		//TODO: As mentioned, these are tree implementations. Can be removed.
		for j := 0; j < i; j++ {
			if st.Full_subtrees[j] != prf.Inclusion.Elements[j] {
				//@ fold st.Inv()
				//@ fold acc(prf.Inv(), p)
				return errors.New("consistency check failed: frontier hash mismatch")
			}
		}

		// TODO: the following assume statements should not be needed!
		//@ assume i < len(st.Frontier_timestamps)
		//@ assume i < len(prf.Timestamps)
		// the following assert stmt is needed due to an incompleteness:
		//@ assert forall j int :: 0 <= j && j < len(prf.Timestamps) - i ==> &(prf.Timestamps[i:][j]) == &(prf.Timestamps[j+i])
		st.Frontier_timestamps = append( /*@ perm(p/2), @*/ st.Frontier_timestamps[:i], prf.Timestamps[i:]...)
	}

	if len(newFrontier) != len(st.Frontier_timestamps) {
		//Revert changes: The frontier does not match.
		st.Size = origSize
		st.Full_subtrees = origSubtrees
		st.Frontier_timestamps = origTimestamps
		//@ fold st.Inv()
		//@ fold acc(prf.Inv(), p)
		return errors.New("incorrect number of timestamps provided")
	}

	newSubtrees := make([]*proofs.NodeValue, len(prf.Inclusion.Elements))
	copy(newSubtrees, prf.Inclusion.Elements)
	st.Full_subtrees = newSubtrees

	st.Size = newHead.Tree_head.Tree_size

	//@ fold st.Inv()
	//@ fold acc(prf.Inv(), p)
	return nil
}
