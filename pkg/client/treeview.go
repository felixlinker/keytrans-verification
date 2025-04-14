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
func RootNode(tree_size uint64) uint64 {
	var power uint64 = 1
	for power < tree_size {
		power = power << 1
	}
	return power >> 1
}

//@ preserves tree != nil ==> tree.Inv()
func (tree *ImplicitBinarySearchTree) OffSet(by uint64) {
	if tree == nil {
		return
	}

	//@ unfold tree.Inv()
	tree.Root += by
	tree.Left.OffSet(by)
	tree.Right.OffSet(by)

	//@ fold tree.Inv()
	return
}

//@ requires  noPerm < p
//@ preserves acc(tree.Inv(), p)
//@ ensures   err == nil ==> acc(path)
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

//@ requires  noPerm < p
//@ preserves tree != nil ==> acc(tree.Inv(), p)
//@ ensures   acc(path)
//@ ensures   tree != nil ==> len(path) > 0
func (tree *ImplicitBinarySearchTree) FrontierNodes( /*@ ghost p perm @*/ ) (path []uint64) {
	path = []uint64{}

	if tree == nil {
		return
	}

	t := tree
	//@ package acc(t.Inv(), p) --* acc(tree.Inv(), p)
	// temporarily unfold the invariant to obtain the knowledge that t cannot be nil:
	//@ assert unfolding acc(tree.Inv(), p) in t != nil

	//@ invariant acc(path)
	//@ invariant t != nil ==> acc(t.Inv(), p)
	//@ invariant t != nil ==> acc(t.Inv(), p) --* acc(tree.Inv(), p)
	//@ invariant t == nil ==> acc(tree.Inv(), p)
	//@ invariant t == nil ==> len(path) > 0
	for t != nil {
		//@ unfold acc(t.Inv(), p)
		path = append( /*@ p, @*/ path, t.Root)
		oldT := t
		_ = oldT
		t = t.Right
		/*@
		ghost if t == nil {
			fold acc(oldT.Inv(), p)
			apply acc(oldT.Inv(), p) --* acc(tree.Inv(), p)
		} else {
			package acc(t.Inv(), p) --* acc(tree.Inv(), p) {
				fold acc(oldT.Inv(), p)
				apply acc(oldT.Inv(), p) --* acc(tree.Inv(), p)
			}
		}
		@*/
	}
	return
}

// Currently, magic wands do not get correctly processed by the SIF plugin
// //@ requires  noPerm < p
// //@ preserves tree != nil ==> acc(tree.Inv(), p)
// //@ ensures acc(path) && (tree != nil ==> len(path) > 0)
// func (tree *ImplicitBinarySearchTree) FrontierNodesLoop(/*@ ghost p perm @*/) (path []uint64) {
// 	path = []uint64{}

// 	tmpTree := tree

// 	/*@
// 	ghost if tree != nil {
// 		package acc(tmpTree.Inv(), p) --* acc(tree.Inv(), p)
// 	}
// 	@*/

// 	//@ invariant acc(path)
// 	//@ invariant tree != nil && tmpTree == nil ==> acc(tree.Inv(), p)
// 	//@ invariant tmpTree != nil ==> acc(tmpTree.Inv(), p)
// 	//@ invariant tmpTree != nil ==> acc(tmpTree.Inv(), p) --* acc(tree.Inv(), p)
// 	//@ invariant tmpTree != tree ==> len(path) > 0
// 	for tmpTree != nil {
// 		//@ unfold acc(tmpTree.Inv(), p)
// 		path = append(/*@ perm(1/2), @*/ path, tmpTree.Root)
// 		oldTmpTree := tmpTree
// 		_ = oldTmpTree
// 		tmpTree = tmpTree.Right
// 		/*@
// 		ghost if tmpTree == nil {
// 			fold acc(oldTmpTree.Inv(), p)
// 			apply acc(oldTmpTree.Inv(), p) --* acc(tree.Inv(), p)
// 		} else {
// 			package acc(tmpTree.Inv(), p) --* acc(tree.Inv(), p) {
// 				fold acc(oldTmpTree.Inv(), p)
// 				apply acc(oldTmpTree.Inv(), p) --* acc(tree.Inv(), p)
// 			}
// 		}
// 		@*/
// 	}
// 	return path
// }

//@ ensures tree_size != 0 ==> tree != nil
//@ ensures tree != nil ==> tree.Inv()
func MkImplicitBinarySearchTree(tree_size uint64) (tree *ImplicitBinarySearchTree) {
	root := RootNode(tree_size)
	if tree_size == 0 {
		return nil
	} else if tree_size == 1 {
		tree = &ImplicitBinarySearchTree{root, nil, nil}
		//@ fold tree.Inv()
		return
	}

	left := MkImplicitBinarySearchTree(root)
	right := MkImplicitBinarySearchTree(tree_size - root - 1)
	if right != nil {
		right.OffSet(root + 1)
	}
	tree = &ImplicitBinarySearchTree{root, left, right}
	//@ fold tree.Inv()
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
	acc(s.Frontier_timestamps)
}
@*/

//@ requires noPerm < p
//@ preserves acc(timestamps, p)
//@ ensures res ==> forall i, j int :: { timestamps[i], timestamps[j] } 0 <= i && i < j && j < len(timestamps) ==> timestamps[i] <= timestamps[j]
func checkIncreasing(timestamps []uint64 /*@, ghost p perm @*/) (res bool) {
	if len(timestamps) == 0 {
		return true
	}

	tmp := timestamps[0]

	//@ invariant 0 <= k && k <= len(timestamps)
	//@ invariant acc(timestamps, p)
	//@ invariant forall i int :: { timestamps[i] } 0 <= i && i < k ==> timestamps[i] <= tmp
	//@ invariant forall i, j int :: { timestamps[i], timestamps[j] } 0 <= i && i < j && j < k ==> timestamps[i] <= timestamps[j]
	for k := 0; k < len(timestamps); k++ {
		v := timestamps[k]
		if tmp > v {
			return false
		}
		tmp = v
	}

	return true
}

//@ requires  noPerm < p
//@ preserves st.Inv()
//@ preserves acc(new_head.Inv(), p)
// since we take the timestamps from `prf`, we need full permissions to then
//@ preserves acc(prf.Inv(), p)
//@ ensures err == nil ==> unfolding st.Inv() in st.Size == new_head.Size()
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
