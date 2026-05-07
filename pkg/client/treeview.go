package client

import (
	"errors"
	"math"

	"github.com/felixlinker/keytrans-verification/pkg/proofs"
	//@ "github.com/felixlinker/keytrans-verification/pkg/utils"
)

// This file implements Section 4, "Updating Views of the Tree"
type ImplicitBinarySearchTree struct {
	size uint64
	tree *ImplicitBinarySearchNode
}

/*@
pred (t *ImplicitBinarySearchTree) Inv() {
	acc(t) && 0 <= t.size &&
	((t.tree == nil) == (t.size == 0)) &&
	(t.tree != nil ==>
		t.tree.Inv(0, t.size - 1) &&
		t.size == uint64(t.tree.Size(0, t.size - 1)))
}

ghost
requires acc(t.Inv(), _)
ensures  0 <= res
decreases
pure func (t *ImplicitBinarySearchTree) Size() (res uint64) {
	return unfolding acc(t.Inv(), _) in t.size
}
@*/

type ImplicitBinarySearchNode struct {
	Root  uint64
	Left  *ImplicitBinarySearchNode
	Right *ImplicitBinarySearchNode
}

/*@
pred (n *ImplicitBinarySearchNode) Inv(min, max uint64) {
	acc(n) && n.Root == RootNodePure(max + 1 - min) + min &&
	min <= n.Root && n.Root <= max &&
	((n.Left == nil) == (n.Root == min)) &&
	(n.Left != nil ==> n.Left.Inv(min, n.Root - 1)) &&
	((n.Right == nil) == (n.Root == max)) &&
	(n.Right != nil ==> n.Right.Inv(n.Root + 1, max))
}

ghost
requires n != nil ==> acc(n.Inv(min, max), _)
ensures  0 <= res
decreases
pure func (n *ImplicitBinarySearchNode) Size(min, max uint64) (res int) {
	return n == nil ? 0 : unfolding acc(n.Inv(min, max), _) in n.sizeRec(min, max)
}

ghost
requires acc(n.Inv(min, max), _)
ensures  0 < res
decreases acc(n.Inv(min, max), _)
pure func (n *ImplicitBinarySearchNode) sizeRec(min, max uint64) (res int) {
	return unfolding acc(n.Inv(min, max), _) in 1 + (n.Left == nil ? 0 : unfolding acc(n.Left.Inv(min, n.Root - 1), _) in n.Left.sizeRec(min, n.Root - 1)) + (n.Right == nil ? 0 : unfolding acc(n.Right.Inv(n.Root + 1, max), _) in n.Right.sizeRec(n.Root + 1, max))
}
@*/

// @ requires 0 <= treeSize && treeSize <= math.MaxUint64
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
		overflowed := false
		//@ ghost var i uint64 = 0

		//@ invariant 0 <= i
		//@ invariant overflowed ==> 0 < i && treeSize < 2*power
		//@ invariant prev - 1 < treeSize
		//@ invariant 1 <= power && power <= math.MaxUint64
		//@ invariant 1 <= prev && prev <= math.MaxUint64
		//@ invariant power == utils.PowOf2_pure(overflowed ? i-1 : i)
		//@ invariant prev == (i == 0 ? 1 : utils.PowOf2_pure(i - 1))
		//@ invariant utils.Log2Floor_pure(power) == (overflowed ? i-1 : i)
		//@ invariant utils.Log2Floor_pure(prev) == (i == 0 ? 0 : i - 1)
		//@ invariant prev <= treeSize
		//@ invariant low(treeSize) ==> low(power) && low(prev) && low(overflowed)
		//@ decreases treeSize - power
		for power-1 < treeSize && !overflowed {
			prev = power
			if power > math.MaxUint64/2 {
				overflowed = true
			} else {
				power = power * 2
			}
			//@ i++
		}

		//@ utils.Log2FloorInbetween(i - 1, prev, treeSize, overflowed ? power*2 : power)
		res = prev - 1
	}
	return res
}

/*@
ghost
ensures 1 <= treeSize ==> root < treeSize
decreases treeSize
pure func RootNodePure(treeSize uint64) (root uint64) {
	return treeSize == 0 ? 0 : utils.PowOf2_pure(utils.Log2Floor_pure(treeSize)) - 1
}
@*/

// @ requires  noPerm < p
// @ preserves acc(tree.Inv(), p)
// @ ensures   (err == nil) == (0 <= nodeVal && nodeVal < tree.Size())
// @ ensures   err == nil ==> acc(path)
// @ ensures   err == nil ==> forall i int :: { path[i] } 0 <= i && i < len(path) ==> 0 <= path[i] && path[i] < tree.Size()
// @ decreases
func (tree *ImplicitBinarySearchTree) PathTo(nodeVal uint64 /*@, ghost p perm @*/) (path []uint64, err error) {
	//@ unfold acc(tree.Inv(), p)
	if tree.tree == nil {
		err = errors.New("no paths exist in an empty tree")
	} else {
		path, err = tree.tree.pathTo(nodeVal /*@, 0, tree.size - 1, p/2 @*/)
	}
	//@ fold acc(tree.Inv(), p)
	return
}

// @ requires  noPerm < p
// @ preserves acc(node.Inv(min, max), p)
// @ requires  min <= max
// @ ensures   (err == nil) == (min <= nodeVal && nodeVal <= max)
// @ ensures   err == nil ==> acc(path)
// @ ensures   err == nil ==> forall i int :: { path[i] } 0 <= i && i < len(path) ==> min <= path[i] && path[i] <= max
// @ decreases max - min
func (node *ImplicitBinarySearchNode) pathTo(nodeVal uint64 /*@, ghost min, max uint64, ghost p perm @*/) (path []uint64, err error) {
	//@ unfold acc(node.Inv(min, max), p/2)
	if node.Root == nodeVal {
		path = []uint64{nodeVal}
	} else {
		var recurse *ImplicitBinarySearchNode
		//@ ghost var minRec, maxRec uint64 = min, max
		if node.Root < nodeVal {
			recurse = node.Right
			//@ minRec = node.Root + 1
		} else { // node.Root > nodeVal
			recurse = node.Left
			//@ maxRec = node.Root - 1
		}
		if recurse == nil {
			err = errors.New("not found")
		} else {
			path, err = recurse.pathTo(nodeVal /*@, minRec, maxRec, p/4 @*/)
		}
		if err == nil {
			path = append( /*@ perm(1/2), @*/ []uint64{node.Root}, path...)
		}
	}
	//@ fold acc(node.Inv(min, max), p/2)
	return
}

// @ requires  noPerm < p
// @ preserves acc(tree.Inv(), p)
// @ ensures   acc(path)
// @ ensures   uint64(len(path)) <= tree.Size()
// @ ensures   0 < tree.Size() ==> 0 < len(path)
// @ ensures   forall j int :: { path[j] } 0 <= j && j < len(path) ==> 0 <= path[j] && path[j] < tree.Size()
// @ ensures   0 < tree.Size() ==> path[len(path) - 1] == tree.Size() - 1
// @ ensures   low(tree.Size()) ==> low(len(path)) && forall i int :: { path[i] } 0 <= i && i < len(path) ==> low(path[i])
// @ decreases
func (tree *ImplicitBinarySearchTree) FrontierNodes( /*@ ghost p perm @*/ ) (path []uint64) {
	//@ unfold acc(tree.Inv(), p/2)
	if tree.tree != nil {
		path = tree.tree.frontierNodes( /*@ 0, tree.size - 1, p/4 @*/ )
	}
	//@ fold acc(tree.Inv(), p/2)
	return
}

// @ requires  noPerm < p
// @ preserves acc(node.Inv(min, max), p)
// @ ensures   acc(path)
// @ ensures   0 < len(path)
// @ ensures   uint64(len(path)) <= max - min + 1
// @ ensures   forall j int :: { path[j] } 0 <= j && j < len(path) ==> min <= path[j] && path[j] <= max
// @ ensures   path[len(path) - 1] == max
// @ ensures   low(min) && low(max) ==> low(len(path)) && forall i int :: { path[i] } 0 <= i && i < len(path) ==> low(path[i])
// @ decreases acc(node.Inv(min, max), p)
func (node *ImplicitBinarySearchNode) frontierNodes( /*@ ghost min, max uint64, ghost p perm @*/ ) (path []uint64) {
	//@ unfold acc(node.Inv(min, max), p/2)
	path = []uint64{node.Root}
	if node.Right != nil {
		subtreePath := node.Right.frontierNodes( /*@ node.Root + 1, max, p/4 @*/ )
		path = append( /*@ perm(1/2), @*/ path, subtreePath...)
	}
	//@ fold acc(node.Inv(min, max), p/2)
	return
}

// @ requires 0 <= treeSize && treeSize <= math.MaxUint64
// @ ensures  tree.Inv() && tree.Size() == treeSize
// @ decreases
func MkImplicitBinarySearchTree(treeSize uint64) (tree *ImplicitBinarySearchTree) {
	var root *ImplicitBinarySearchNode
	if treeSize != 0 {
		root = mkImplicitBinarySearchNode(0, treeSize-1)
	}
	tree = &ImplicitBinarySearchTree{treeSize, root}
	//@ fold tree.Inv()
	return
}

// @ requires  0 <= min && min <= max && max + 1 <= math.MaxUint64
// @ ensures   node != nil
// @ ensures   node.Inv(min, max)
// @ ensures   uint64(node.Size(min, max)) == max - min + 1
// @ decreases max - min
func mkImplicitBinarySearchNode(min, max uint64) (node *ImplicitBinarySearchNode) {
	root := RootNode(max+1-min) + min
	if min == max { // treeSize == 1
		node = &ImplicitBinarySearchNode{root, nil, nil}
		//@ fold node.Inv(min, max)
	} else { // min < max
		var left *ImplicitBinarySearchNode
		if root != min {
			left = mkImplicitBinarySearchNode(min, root-1)
		}
		var right *ImplicitBinarySearchNode
		if root != max {
			right = mkImplicitBinarySearchNode(root+1, max)
		}
		node = &ImplicitBinarySearchNode{root, left, right}
		//@ fold node.Inv(min, max)
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

	oldSearchTree := MkImplicitBinarySearchTree(st.Size)
	newSearchTree := MkImplicitBinarySearchTree(newHead.Tree_head.Tree_size)
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

	st.Size = newHead.Tree_head.Tree_size

	//@ fold st.Inv()
	//@ fold acc(prf.Inv(), p)
	return nil
}
