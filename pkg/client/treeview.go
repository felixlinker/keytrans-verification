package client

import (
	"errors"

	"github.com/felixlinker/keytrans-verification/pkg/proofs"
	//@ "github.com/felixlinker/keytrans-verification/pkg/utils"
)

// This file implements Section 4, "Updating Views of the Tree"

type ImplicitBinarySearchTree struct {
	Root  uint64
	Left  *ImplicitBinarySearchTree
	Right *ImplicitBinarySearchTree
}

/*@
pred (t *ImplicitBinarySearchTree) Inv() {
	acc(t) && 0 <= t.Root &&
	(t.Left != nil ==> t.Left.Inv()) &&
	(t.Right != nil ==> t.Right.Inv()) &&
	// valid ranges:
	(t.Left != nil ==> t.Left.Max() < t.Root) &&
	(t.Right != nil ==> t.Root < t.Right.Min())
}

ghost
requires t != nil ==> acc(t.Inv(), _)
ensures  0 <= res
decreases
pure func (t *ImplicitBinarySearchTree) Size() (res int) {
	return t == nil ? 0 : t.sizeRec()
}

ghost
requires acc(t.Inv(), _)
ensures  0 <= res
decreases acc(t.Inv(), _)
pure func (t *ImplicitBinarySearchTree) sizeRec() (res int) {
	return unfolding acc(t.Inv(), _) in 1 + (t.Left == nil ? 0 : t.Left.sizeRec()) + (t.Right == nil ? 0 : t.Right.sizeRec())
}

ghost
requires acc(t.Inv(), _)
ensures  0 <= res && res <= t.Max()
decreases acc(t.Inv(), _)
pure func (t *ImplicitBinarySearchTree) Min() (res uint64) {
	return unfolding acc(t.Inv(), _) in t.Left == nil ? t.Root : t.Left.Min()
}

ghost
requires acc(t.Inv(), _)
decreases acc(t.Inv(), _)
pure func (t *ImplicitBinarySearchTree) Max() uint64 {
	return unfolding acc(t.Inv(), _) in t.Right == nil ? t.Root : t.Right.Max()
}
@*/

// @ requires 0 <= treeSize
// @ ensures  0 <= root
// @ ensures  1 < treeSize ==> root < treeSize
// @ ensures  root == RootNodePure(treeSize)
// @ ensures  low(treeSize) ==> low(root)
// @ decreases
func RootNode(treeSize uint64) (root uint64) {
	var res uint64 = 0
	if treeSize >= 1 {
		var power uint64 = 1
		var prev uint64 = 1
		//@ ghost var i uint64 = 0

		//@ invariant 0 <= i
		//@ invariant prev - 1 < treeSize
		//@ invariant 1 <= power && 1 <= prev
		//@ invariant power == utils.PowOf2_pure(i)
		//@ invariant prev == (i == 0 ? 1 : utils.PowOf2_pure(i - 1))
		//@ invariant utils.Log2Floor_pure(power) == i
		//@ invariant utils.Log2Floor_pure(prev) == (i == 0 ? 0 : i - 1)
		//@ invariant prev <= treeSize
		//@ invariant low(treeSize) ==> low(power) && low(prev)
		//@ decreases treeSize - power
		for power-1 < treeSize {
			prev = power
			power = power * 2
			//@ i++
		}

		//@ utils.Log2FloorInbetween(i - 1, prev, treeSize, power)
		res = prev - 1
	}
	return res
}

/*@
ghost
decreases treeSize
pure func RootNodePure(treeSize uint64) (root uint64) {
	return treeSize == 0 ? 0 : utils.PowOf2_pure(utils.Log2Floor_pure(treeSize)) - 1
}
@*/

// @ preserves tree != nil ==> tree.Inv()
// @ requires  0 <= offset
// @ ensures   old(tree.Size()) == tree.Size()
// @ ensures   tree != nil ==> old(tree.Min()) + offset == tree.Min()
// @ ensures   tree != nil ==> old(tree.Max()) + offset == tree.Max()
// @ decreases tree.Size()
func (tree *ImplicitBinarySearchTree) OffSet(offset uint64) {
	if tree != nil {
		//@ unfold tree.Inv()
		tree.Root += offset
		tree.Left.OffSet(offset)
		tree.Right.OffSet(offset)
		//@ fold tree.Inv()
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
// @ preserves tree != nil ==> acc(tree.Inv(), p)
// @ ensures   acc(path)
// @ ensures   (tree == nil) == (0 == len(path))
// @ ensures   tree != nil ==> forall j int :: { path[j] } 0 <= j && j < len(path) ==> tree.Min() <= path[j] && path[j] <= tree.Max()
// ensures   tree != nil ==> unfolding acc(tree.Inv(), p) in low(tree.Root) ==> (low(len(path)) && forall i int :: { path[i] } 0 <= i && i < len(path) ==> low(path[i]))
// @ decreases tree.Size()
func (tree *ImplicitBinarySearchTree) FrontierNodes( /*@ ghost p perm @*/ ) (path []uint64) {
	if tree != nil {
		//@ unfold acc(tree.Inv(), p/2)
		path = []uint64{tree.Root}
		//@ assert low(len(path))
		//@ assert forall j int :: { path[j] } 0 <= j && j < len(path) && low(tree.Root) ==> low(path[j])
		// assert tree.Right == nil ==> low(tree.Right)
		// assert tree.Right != nil ==> unfolding tree.Right.Inv() in low(tree.Right.Root)
		subtreePath := tree.Right.FrontierNodes( /*@ p/4 @*/ )
		// assert low(len(subtreePath))
		// assert forall j int :: 0 <= j && j < len(subtreePath) ==> low(subtreePath[j])
		path = append( /*@ perm(1/2), @*/ path, subtreePath...)
		// assert low(len(path))
		// assert forall j int :: 0 <= j && j < len(path) ==> low(path[j])
		//@ fold acc(tree.Inv(), p/2)
	}
	return
}

// @ requires 0 <= treeSize
// @ ensures  tree != nil ==> tree.Inv() && tree.Min() == 0 && tree.Max() == treeSize - 1
// @ ensures  treeSize == uint64(tree.Size())
// @ ensures  (treeSize == 0) == (tree == nil)
// @ ensures  tree != nil ==> unfolding tree.Inv() in low(treeSize) ==> low(tree.Root)
// @ decreases treeSize
func MkImplicitBinarySearchTree(treeSize uint64) (tree *ImplicitBinarySearchTree) {
	if treeSize == 0 {
		tree = nil
	} else if treeSize == 1 {
		root := RootNode(treeSize)
		tree = &ImplicitBinarySearchTree{root, nil, nil}
		//@ fold tree.Inv()
		//@ assert tree.Size() == 1
	} else if treeSize > 1 {
		root := RootNode(treeSize)
		left := MkImplicitBinarySearchTree(root)
		right := MkImplicitBinarySearchTree(treeSize - root - 1)
		right.OffSet(root + 1)
		tree = &ImplicitBinarySearchTree{root, left, right}
		//@ fold tree.Inv()
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
	oldFrontier := oldSearchTree.FrontierNodes( /*@ 1/2 @*/ )
	newFrontier := newSearchTree.FrontierNodes( /*@ 1/2 @*/ )

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
