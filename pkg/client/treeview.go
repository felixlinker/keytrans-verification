package client

import (
	"errors"

	"github.com/felixlinker/keytrans-verification/pkg/proofs"
)

// This file implements Section 4, "Updating Views of the Tree"

type ImplicitBinarySearchTree struct {
	Root  uint64
	Left  *ImplicitBinarySearchTree
	Right *ImplicitBinarySearchTree
}

/*@
pred (t *ImplicitBinarySearchTree) Inv() {
	acc(t) &&
	(t.Left != nil ==> t.Left.Inv()) &&
	(t.Right != nil ==> t.Right.Inv())
}

pred (t *ImplicitBinarySearchTree) InvLow() {
	acc(t) &&
	low(t.Root) &&
	low(t.Left != nil) &&
	low(t.Right != nil) &&
	(t.Left != nil ==> t.Left.InvLow()) &&
	(t.Right != nil ==> t.Right.InvLow())
}
@*/

// @ requires tree_size >= 0
// @ requires low(tree_size)
// @ ensures root >= 0
// @ ensures tree_size >1 ==> root < tree_size
// @ ensures low(root)
func RootNode(tree_size uint64) (root uint64) {
	var res uint64 = 0
	if tree_size >= 1 {
		var power uint64 = 1
		var prev uint64 = 1
		//@ invariant low(power) && low(tree_size) && low(prev)
		//@ invariant prev - 1 < tree_size
		//@ invariant power >=1 && prev >=1
		for power-1 < tree_size {
			prev = power
			power = power * 2
		}
		res = prev - 1
	}
	return res
}

// @ requires low(tree != nil)
// @ requires low(offset)
// @ requires low(tree != nil) && tree != nil ==> tree.InvLow()
// @ ensures low(tree != nil)
// @ ensures low(tree != nil) && tree != nil ==> tree.InvLow()
func (tree *ImplicitBinarySearchTree) OffSet(offset uint64) {
	if tree != nil {
		//@ unfold tree.InvLow()
		tree.Root += offset
		tree.Left.OffSet(offset)
		tree.Right.OffSet(offset)
		//@ fold tree.InvLow()
	}
	return
}

// @ requires  noPerm < p
// @ preserves acc(tree.Inv(), p)
// @ ensures   err == nil ==> acc(path)
func (tree *ImplicitBinarySearchTree) PathTo(node uint64 /*@, ghost p perm @*/) (path []uint64, err error) {
	//@ unfold acc(tree.Inv(), p)
	if tree.Root == node {
		path = []uint64{node}
	} else {
		var recurse *ImplicitBinarySearchTree
		if tree.Root < node {
			recurse = tree.Right
		} else { // tree.Root > node
			recurse = tree.Left
		}
		if recurse == nil {
			err = errors.New("not found")
		} else {
			path, err = recurse.PathTo(node /*@, p/2 @*/)
		}
		if err == nil {
			path = append( /*@ p, @*/ []uint64{tree.Root}, path...)
		}
	}
	//@ fold acc(tree.Inv(), p)
	return
}

// Currently, magic wands do not get correctly processed by the SIF plugin
// //@ requires  noPerm < p
// //@ preserves tree != nil ==> acc(tree.Inv(), p)
// //@ ensures   acc(path)
// //@ ensures   tree != nil ==> len(path) > 0
// func (tree *ImplicitBinarySearchTree) FrontierNodes( /*@ ghost p perm @*/ ) (path []uint64) {
// 	path = []uint64{}

// 	if tree == nil {
// 		return
// 	}

// 	t := tree
// 	//@ package acc(t.Inv(), p) --* acc(tree.Inv(), p)
// 	// temporarily unfold the invariant to obtain the knowledge that t cannot be nil:
// 	//@ assert unfolding acc(tree.Inv(), p) in t != nil

//		//@ invariant acc(path)
//		//@ invariant t != nil ==> acc(t.Inv(), p)
//		//@ invariant t != nil ==> acc(t.Inv(), p) --* acc(tree.Inv(), p)
//		//@ invariant t == nil ==> acc(tree.Inv(), p)
//		//@ invariant t == nil ==> len(path) > 0
//		for t != nil {
//			//@ unfold acc(t.Inv(), p)
//			path = append( /*@ p, @*/ path, t.Root)
//			//@ ghost oldT := t
//			t = t.Right
//			/*@
//			ghost if t == nil {
//				fold acc(oldT.Inv(), p)
//				apply acc(oldT.Inv(), p) --* acc(tree.Inv(), p)
//			} else {
//				package acc(t.Inv(), p) --* acc(tree.Inv(), p) {
//					fold acc(oldT.Inv(), p)
//					apply acc(oldT.Inv(), p) --* acc(tree.Inv(), p)
//				}
//			}
//			@*/
//		}
//		return
//	}
//
// @ requires  noPerm < p
// @ requires low(tree != nil)
// @ requires low(tree != nil) && tree != nil ==> tree.InvLow()
// @ ensures low(tree != nil)
// @ ensures low(tree != nil) && tree != nil ==> tree.InvLow()
// @ ensures   acc(path)
// @ ensures   tree != nil ==> len(path) > 0
// TODO: bounds postcondition needs InvLow to carry bound info
// ensures forall j int :: j >= 0 && j < len(path) ==> path[j] >= 0 && path[j] < bound
// @ ensures (low(len(path)) && forall i int :: 0<= i && i< len(path) ==>  low(path[i]))
func (tree *ImplicitBinarySearchTree) FrontierNodes( /*@ ghost p perm, ghost bound uint64 @*/ ) (path []uint64) {
	if tree != nil {
		//@ unfold tree.InvLow()
		path = []uint64{tree.Root}
		subtreePath := tree.Right.FrontierNodes( /*@ p, bound @*/ )
		path = append( /*@ perm(1/2), @*/ path, subtreePath...)
		//@ fold tree.InvLow()
	}
	return
}

// @ requires tree_size >= 0
// @ requires low(tree_size)
// @ ensures tree_size == 0 ==> tree == nil
// @ ensures tree_size != 0 ==> tree != nil
// @ ensures low(tree != nil)
// @ ensures low(tree != nil) && tree != nil ==> tree.InvLow()
func MkImplicitBinarySearchTree(tree_size uint64) (tree *ImplicitBinarySearchTree) {
	if tree_size == 0 {
		tree = nil
	} else if tree_size == 1 {
		root := RootNode(tree_size)
		tree = &ImplicitBinarySearchTree{root, nil, nil}
		//@ fold tree.InvLow()
	} else if tree_size > 1 {
		root := RootNode(tree_size)
		left := MkImplicitBinarySearchTree(root)
		right := MkImplicitBinarySearchTree(tree_size - root - 1)

		if right != nil {
			right.OffSet(root + 1)
		}
		tree = &ImplicitBinarySearchTree{root, left, right}
		//@ fold tree.InvLow()
	}
	return
}

type UserState struct {
	Size                uint64 // 0 means no tree
	Full_subtrees       []proofs.NodeValue
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
func checkIncreasing(timestamps []uint64 /*@, ghost p perm @*/) (res bool) {
	res = true
	if len(timestamps) > 0 {
		tmp := timestamps[0]
		//@ invariant 0 <= k && k <= len(timestamps)
		//@ invariant acc(timestamps, p)
		//@ invariant res ==> forall i int :: { timestamps[i] } 0 <= i && i < k ==> timestamps[i] <= tmp
		//@ invariant res ==> forall i, j int :: { timestamps[i], timestamps[j] } 0 <= i && i < j && j < k ==> timestamps[i] <= timestamps[j]
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
// @ preserves acc(new_head.Inv(), p)
// since we take the timestamps from `prf`, we need full permissions to then
// @ preserves acc(prf.Inv(), p)
// @ ensures err == nil ==> unfolding st.Inv() in st.Size == new_head.Size()
// @ ensures err == nil && low(new_head.Size()) ==> unfolding st.Inv() in low(st.Size)
// @ trusted
func (st *UserState) UpdateView(new_head FullTreeHead, prf proofs.CombinedTreeProof /*@, ghost p perm @*/) (err error) {
	//@ unfold acc(prf.Inv(), p)

	if !checkIncreasing(prf.Timestamps /*@, p/2 @*/) {
		//@ fold acc(prf.Inv(), p)
		return errors.New("timestamps not increasing")
	}
	if new_head.Tree_head.Tree_size == 0 {
		//@ fold acc(prf.Inv(), p)
		return errors.New("new tree cannot be empty")
	}

	// TODO: Verify proof of consistency

	//@ unfold st.Inv()
	origSize := st.Size
	origSubtrees := st.Full_subtrees
	origTimestamps := st.Frontier_timestamps

	oldSearchTree := MkImplicitBinarySearchTree(st.Size)
	newSearchTree := MkImplicitBinarySearchTree(new_head.Tree_head.Tree_size)
	oldFrontier := oldSearchTree.FrontierNodes( /*@ 1/2, st.Size @*/ )
	newFrontier := newSearchTree.FrontierNodes( /*@ 1/2, new_head.Tree_head.Tree_size @*/ )

	if st.Size == 0 {
		// copy timestamps from `prf`:
		timestamps := make([]uint64, len(prf.Timestamps))
		copy(timestamps, prf.Timestamps /*@, p/2 @*/)
		st.Frontier_timestamps = timestamps
		//TODO: This is rather for subtree implementation. We don't need it I think.
		subtrees := make([]proofs.NodeValue, len(prf.Inclusion.Elements))
		copy(subtrees, prf.Inclusion.Elements)
		st.Full_subtrees = subtrees
	} else {
		pathToOldHead, pathErr := newSearchTree.PathTo(st.Size - 1 /*@, 1/2 @*/)
		if pathErr != nil {
			//@ fold st.Inv()
			//@ fold acc(prf.Inv(), p)
			return pathErr
		}

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

	newSubtrees := make([]proofs.NodeValue, len(prf.Inclusion.Elements))
	copy(newSubtrees, prf.Inclusion.Elements)
	st.Full_subtrees = newSubtrees

	st.Size = new_head.Tree_head.Tree_size

	//@ fold st.Inv()
	//@ fold acc(prf.Inv(), p)
	return nil
}
