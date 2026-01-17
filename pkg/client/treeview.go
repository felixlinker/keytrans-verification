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


@*/

// Get the largest power of two smaller than tree_size
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

// @ requires  noPerm < p
// @ requires low(by)
// @ requires tree!= nil ==>acc(tree.Inv(), p)
// @ ensures tree!= nil ==>acc(tree.Inv(), p)
// @ ensures low(by)
// @ ensures tree == nil ==> low(tree)
// @ ensures tree != nil ==> (unfolding acc(tree.Inv(),p) in low(tree.Root))
// @ trusted
func (tree *ImplicitBinarySearchTree) OffSet(by uint64 /*@,ghost p perm @*/) {
	if tree != nil {
		//@ unfold acc(tree.Inv(),p)
		//@ assert low(by)
		tree.Root += by
		//@ assert tree.Left == nil ==> low(tree.Left)
		//@ assert tree.Left!= nil ==> acc(tree.Left.Inv(), p)
		tree.Left.OffSet(by /*@,p @*/)
		//@ assert tree.Right == nil ==> low(tree.Right)
		//@ assert tree.Right!= nil ==> acc(tree.Right.Inv(),p)
		tree.Right.OffSet(by /*@,p @*/)
		//@ fold acc(tree.Inv(),p)
	}
	//@ assert tree == nil ==> low(tree)
	return
}

// @ requires  noPerm < p
// @ preserves acc(tree.Inv(), p)
// @ ensures   err == nil ==> acc(path)
// @ trusted
func (tree *ImplicitBinarySearchTree) PathTo(node uint64 /*@, ghost p perm @*/) (path []uint64, err error) {
	//@ unfold acc(tree.Inv(), p)
	if tree.Root == node {
		path = []uint64{node}
	} else {
		var recurse *ImplicitBinarySearchTree
		if tree.Root < node {
			recurse = tree.Left
		} else { // tree.Root > node
			recurse = tree.Right
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
// @ preserves tree != nil ==> acc(tree.Inv(), p)
// @ ensures   acc(path)
// @ ensures   tree != nil ==> len(path) > 0
func (tree *ImplicitBinarySearchTree) FrontierNodes( /*@ ghost p perm @*/ ) (path []uint64) {
	if tree != nil {
		//@ unfold acc(tree.Inv(), p)
		path = []uint64{tree.Root}
		subtreePath := tree.Right.FrontierNodes( /*@ p @*/ )
		path = append( /*@ p, @*/ path, subtreePath...)
		//@ fold acc(tree.Inv(), p)
	}
	return
}

// @ requires noPerm < p
// @ requires tree_size >= 0
// @ requires low(tree_size)
// @ requires tree == nil ==> low(tree)
// @ ensures tree_size == 0 ==> tree == nil
// @ ensures tree_size != 0 ==> tree != nil
// @ ensures tree == nil ==> low(tree)
// @ ensures tree != nil ==> tree.Inv()
// @ ensures tree != nil ==> acc(tree.Inv(),p)
// @ ensures tree != nil ==> unfolding acc(tree.Inv(),p) in low(tree.Root)
func MkImplicitBinarySearchTree(tree_size uint64 /*@,ghost p perm@*/) (tree *ImplicitBinarySearchTree) {
	if tree_size == 0 {
		tree = nil
		//@ assert low(tree)
	} else if tree_size == 1 {
		root := RootNode(tree_size)
		//@ assert low(root)
		tree = &ImplicitBinarySearchTree{root, nil, nil}
		//@ fold tree.Inv()
		//@ assert acc(tree.Inv(), p)
		//@ assert unfolding acc(tree.Inv(),p) in low(tree.Root)
	} else if tree_size > 1 {
		root := RootNode(tree_size)
		left := MkImplicitBinarySearchTree(root /*@, p@*/)
		//@ assert left == nil ==> low(left)
		//@ assert left != nil ==> unfolding acc(left.Inv(),p) in low(left.Root)
		right := MkImplicitBinarySearchTree(tree_size - root - 1 /*@, p@*/)
		if right != nil {
			right.OffSet(root + 1 /*@, p@*/)
		}
		//@ assert right == nil ==> low(right)
		//@ assert right != nil ==> unfolding acc(right.Inv(),p) in low(right.Root)
		tree = &ImplicitBinarySearchTree{root, left, right}
		//@ fold acc(tree.Inv(),p)
		//@ assert unfolding acc(left.Inv(),p)  in low(tree.Root)
	}
	//@ assert tree == nil ==> low(tree)
	//@ assert tree != nil ==> unfolding acc(tree.Inv(),p) in low(tree.Root)

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
// @ trusted //TODO
func (st *UserState) UpdateView(new_head FullTreeHead, prf proofs.CombinedTreeProof /*@, ghost p perm @*/) (err error) {
	//@ unfold acc(prf.Inv(), p)
	if !checkIncreasing(prf.Timestamps /*@, p/2 @*/) {
		err = errors.New("timestamps not increasing")
		//@ fold acc(prf.Inv(), p)
		return
	} else if new_head.Tree_head.Tree_size == 0 {
		err = errors.New("new tree cannot be empty")
		//@ fold acc(prf.Inv(), p)
		return
	}

	// TODO: Verify proof of consistency

	//@ unfold st.Inv()
	oldSearchTree := MkImplicitBinarySearchTree(st.Size)
	newSearchTree := MkImplicitBinarySearchTree(new_head.Tree_head.Tree_size)
	oldFrontier := oldSearchTree.FrontierNodes( /*@ 1/2 @*/ )
	newFrontier := newSearchTree.FrontierNodes( /*@ 1/2 @*/ )
	if st.Size == 0 {
		// copy timestamps from `prf`:
		timestamps := make([]uint64, len(prf.Timestamps))
		copy(timestamps, prf.Timestamps /*@, p/2 @*/)
		st.Frontier_timestamps = timestamps
	} else if pathToOldHead, err := newSearchTree.PathTo(st.Size - 1 /*@, 1/2 @*/); err != nil {
		//@ fold st.Inv()
		//@ fold acc(prf.Inv(), p)
		return err
	} else {
		i := 0
		//@ invariant 0 <= i && i <= len(pathToOldHead) && i <= len(oldFrontier)
		//@ invariant acc(pathToOldHead) && acc(oldFrontier)
		for ; i < len(pathToOldHead) && i < len(oldFrontier) && pathToOldHead[i] == oldFrontier[i]; i++ {
		}

		// TODO: the following assume statements should not be needed!
		//@ assume i < len(st.Frontier_timestamps)
		//@ assume i < len(prf.Timestamps)
		// the following assert stmt is needed due to an incompleteness:
		//@ assert forall j int :: 0 <= j && j < len(prf.Timestamps) - i ==> &(prf.Timestamps[i:][j]) == &(prf.Timestamps[j+i])
		st.Frontier_timestamps = append( /*@ perm(p/2), @*/ st.Frontier_timestamps[:i], prf.Timestamps[i:]...)
	}
	//@ fold acc(prf.Inv(), p)

	if len(newFrontier) != len(st.Frontier_timestamps) {
		//@ fold st.Inv()
		// TODO: is it okay that we have already modified `st.Frontier_timestamps`?
		return errors.New("incorrect number of timestamps provided")
	}

	st.Size = new_head.Tree_head.Tree_size
	//@ fold st.Inv()
	return nil
}
