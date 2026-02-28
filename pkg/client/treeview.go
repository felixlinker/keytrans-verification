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


//TODO
decreases
//requires acc(tree.Inv(), _)
pure func (tree *ImplicitBinarySearchTree) IsLow() bool
@*/

/*


pred (t *ImplicitBinarySearchTree) LowInv(p perm) {
	noPerm < p && p < writePerm && acc(t, p) && low(t.Root) &&
	(t.Left != nil ==> t.Left.LowInv(p)) &&
	(t.Right != nil ==> t.Right.LowInv(p))
}


*/

// RootNode computes the largest power-of-two minus one that is less than tree_size.
// This gives the root position of an implicit binary search tree of the given size.
//
// Preconditions: tree_size >= 0 and low (public).
// Postconditions: root >= 0, root < tree_size (when tree_size > 1), root is low.
//
// Returns: root position of the implicit BST.
//
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

// OffSet adds a constant offset to every node's Root value in the tree.
// Used to shift a subtree's positions after constructing left/right children.
//
// Preconditions/Postconditions: preserves tree.Inv() when tree is non-nil.
//
// @ preserves tree!= nil ==> tree.Inv()
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

// PathTo returns the path from the root of the tree down to the given node.
// It performs a standard BST search, collecting each visited node's Root value.
//
// Preconditions: tree.Inv() must hold with at least permission p.
// Postconditions: on success, returns an owned path slice; tree.Inv() is preserved.
//
// Returns:
//   - path: ordered slice of node positions from root to target
//   - err: non-nil ("not found") if the node is not in the tree
//
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
// FrontierNodes returns the rightmost spine of the implicit BST — the root
// followed by all right children. These are the "frontier" log entries used
// by VerifyLatestKey and VerifyUpdateKey to check the greatest version.
//
// Preconditions: if tree is non-nil, tree.Inv() must hold and tree.Root must be low.
// Postconditions: preserves tree.Inv(), returns a non-empty path (when tree != nil)
// with all elements low and within [0, bound).
//
// Returns: path — the frontier node positions from root down the right spine.
//
// TODO: analyse if we need to have full permissions if we incooperate with low or can we use partial permission.
// @ requires  noPerm < p
// @ requires tree != nil ==> tree.Inv()
// @ requires tree == nil ==> low(tree)
// @ requires tree!= nil ==> unfolding tree.Inv() in low(tree.Root)
// @ ensures tree != nil ==> tree.Inv()
// @ ensures tree!= nil ==> unfolding tree.Inv() in low(tree.Root)
// @ ensures   acc(path)
// @ ensures   tree != nil ==> len(path) > 0
// @ ensures low(len(path))
// @ ensures forall j int :: j>= 0 && j < len(path) ==> low(path[j])
// @ ensures forall j int :: j >= 0 && j < len(path) ==> path[j] >= 0 && path[j] < bound
// @ ensures tree.IsLow() ==> low(len(path)) && forall i int :: 0<= i && i< len(path) &&  low(path[i])
// @ trusted
// TODO: There is no way to fix this issue now due to the hyperpredicate...
func (tree *ImplicitBinarySearchTree) FrontierNodes( /*@ ghost p perm, ghost bound uint64 @*/ ) (path []uint64) {
	if tree != nil {
		//@ unfold tree.Inv()
		path = []uint64{tree.Root}
		//@ assert low(len(path))
		//@ assert forall j int :: j>= 0 && j < len(path) ==> low(path[j])
		//@ assert tree.Right == nil ==> low(tree.Right)
		//@ assert tree.Right != nil ==> unfolding tree.Right.Inv() in low(tree.Right.Root)
		subtreePath := tree.Right.FrontierNodes( /*@ p, bound @*/ )
		//@ assert low(len(subtreePath))
		//@ assert forall j int :: j>= 0 && j < len(subtreePath) ==> low(subtreePath[j])
		path = append( /*@ p, @*/ path, subtreePath...)
		//@ assert low(len(path))
		// assert 1 == 2
		//@ assert forall j int :: j>= 0 && j < len(path) ==> low(path[j])
		//@ fold tree.Inv()
	}
	return
}

// MkImplicitBinarySearchTree constructs an implicit binary search tree for a
// transparency log of the given size. The root is the largest power-of-two minus
// one less than tree_size. Left and right subtrees are constructed recursively,
// with the right subtree offset by (root + 1).
//
// Preconditions: tree_size >= 0 and low (public).
// Postconditions: nil if tree_size==0; otherwise tree.Inv() holds with low root.
//
// Returns: the constructed tree (nil for empty).
//
// @ requires tree_size >= 0
// @ requires low(tree_size)
// @ ensures tree_size == 0 ==> tree == nil
// @ ensures tree_size != 0 ==> tree != nil
// @ ensures tree != nil ==> tree.Inv()
// @ ensures tree == nil ==> low(tree)
// @ ensures tree != nil ==> unfolding tree.Inv() in low(tree.Root)
func MkImplicitBinarySearchTree(tree_size uint64) (tree *ImplicitBinarySearchTree) {
	if tree_size == 0 {
		tree = nil
	} else if tree_size == 1 {
		root := RootNode(tree_size)
		tree = &ImplicitBinarySearchTree{root, nil, nil}
		//@ fold tree.Inv()
	} else if tree_size > 1 {
		root := RootNode(tree_size)
		left := MkImplicitBinarySearchTree(root)
		right := MkImplicitBinarySearchTree(tree_size - root - 1)

		if right != nil {
			right.OffSet(root + 1)
		}
		tree = &ImplicitBinarySearchTree{root, left, right}
		//@ fold tree.Inv()
	}
	return
}

// IsDistinguished checks if a log entry is distinguished per Section 7.2.
// An entry is distinguished iff the time span (right_ts - left_ts) is at least
// the reasonable monitoring window (rmw). Distinguished entries serve as public
// checkpoints for contact monitoring.
//
// Preconditions: all inputs must be low (public).
// Postconditions: result is low (public).
//
// Returns: true if the entry is distinguished.
//
// @ requires low(left_ts) && low(right_ts) && low(rmw)
// @ ensures low(res)
func IsDistinguished(left_ts, right_ts, rmw uint64) (res bool) {
	if right_ts >= left_ts {
		res = (right_ts - left_ts) >= rmw
	} else {
		res = false
	}
	return
}

// ComputeDistinguishedSet recursively walks the implicit BST and marks which
// positions are distinguished (time span >= rmw). Returns a bool slice indexed
// by tree position where true means the position is a distinguished checkpoint.
//
// Preconditions: tree.Inv() and timestamps must be readable, rmw must be low.
// Postconditions: preserves tree.Inv() and timestamps, result length and all
// elements are low (public).
//
// Returns: result — bool slice where result[pos] == true means pos is distinguished.
//
// @ requires noPerm < p
// @ requires acc(tree.Inv(), p) && acc(timestamps, p)
// @ requires low(rmw)
// @ ensures  acc(tree.Inv(), p) && acc(timestamps, p) && acc(result)
// @ ensures  low(len(result))
// @ ensures  forall j int :: 0 <= j && j < len(result) ==> low(result[j])
// @ trusted
func ComputeDistinguishedSet(tree *ImplicitBinarySearchTree, timestamps []uint64,
	rmw uint64 /*@, ghost p perm @*/) (result []bool) {
	if tree == nil {
		result = make([]bool, 0)
		return
	}
	//@ unfold acc(tree.Inv(), p)
	size := countNodes(tree)
	result = make([]bool, size)
	computeDistinguishedRec(tree, timestamps, rmw, 0, uint64(len(timestamps))-1, result)
	//@ fold acc(tree.Inv(), p)
	return
}

// @ trusted
func countNodes(tree *ImplicitBinarySearchTree) int {
	if tree == nil {
		return 0
	}
	return 1 + countNodes(tree.Left) + countNodes(tree.Right)
}

// @ trusted
func computeDistinguishedRec(tree *ImplicitBinarySearchTree, timestamps []uint64,
	rmw uint64, left_ts_idx, right_ts_idx uint64, result []bool) {
	if tree == nil {
		return
	}
	root := tree.Root
	if right_ts_idx < uint64(len(timestamps)) && left_ts_idx < uint64(len(timestamps)) {
		left_ts := timestamps[left_ts_idx]
		right_ts := timestamps[right_ts_idx]
		if IsDistinguished(left_ts, right_ts, rmw) {
			if int(root) < len(result) {
				result[root] = true
			}
			// Recurse into subtrees
			computeDistinguishedRec(tree.Left, timestamps, rmw, left_ts_idx, root, result)
			computeDistinguishedRec(tree.Right, timestamps, rmw, root, right_ts_idx, result)
		}
		// If not distinguished, nothing in the subtree is either
	}
}

// DirectPathRight returns positions on the direct path from root to `pos` that
// are >= pos, stopping after the first distinguished entry (Section 8.2, Step 2).
// Used by VerifyMonitor to determine which log entries to check for a given
// monitoring map entry.
//
// Preconditions: tree.Inv() and distinguished must be readable, pos and
// distinguished length/elements must be low (public).
// Postconditions: preserves tree.Inv() and distinguished, result length and
// elements are all low.
//
// Returns: result — positions on the right direct path to check during monitoring.
//
// @ requires noPerm < p
// @ requires acc(tree.Inv(), p) && acc(distinguished, p)
// @ requires low(pos) && low(len(distinguished))
// @ requires forall j int :: 0 <= j && j < len(distinguished) ==> low(distinguished[j])
// @ ensures  acc(tree.Inv(), p) && acc(distinguished, p) && acc(result)
// @ ensures  low(len(result)) && low(len(distinguished))
// @ ensures  forall j int :: 0 <= j && j < len(distinguished) ==> low(distinguished[j])
// @ ensures  forall j int :: 0 <= j && j < len(result) ==> low(result[j])
// @ trusted
func DirectPathRight(tree *ImplicitBinarySearchTree, pos uint64,
	distinguished []bool /*@, ghost p perm @*/) (result []uint64) {
	result = make([]uint64, 0)
	if tree == nil {
		return
	}
	path, err := tree.PathTo(pos /*@, p/2 @*/)
	if err != nil {
		return
	}
	// Filter: keep only positions >= pos
	for i := 0; i < len(path); i++ {
		if path[i] >= pos {
			result = append( /*@ perm(1/2), @*/ result, path[i])
			// Terminate after first distinguished entry
			if int(path[i]) < len(distinguished) && distinguished[path[i]] {
				break
			}
		}
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

// checkIncreasing verifies that a slice of timestamps is monotonically
// non-decreasing. Used by UpdateView to validate proof timestamps.
//
// Preconditions: timestamps must be readable with permission p.
// Postconditions: if true, all pairs satisfy timestamps[i] <= timestamps[j] for i < j.
//
// Returns: true if timestamps are non-decreasing, false otherwise.
//
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

// UpdateView advances the user's local view of the transparency tree to match
// new_head (Section 4). It validates that timestamps are increasing, verifies
// consistency between old and new frontiers, and updates the stored subtree
// hashes and frontier timestamps.
//
// Preconditions: st.Inv(), new_head.Inv(), and prf.Inv() must hold.
// Postconditions: on success, st.Size == new_head.Size(); if new_head.Size() is
// low then st.Size is also low. Preserves all invariants.
//
// Returns: err — non-nil if timestamps are invalid, tree is empty, or
// consistency check between old and new frontiers fails.
//
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
	oldSearchTree := MkImplicitBinarySearchTree(st.Size)
	newSearchTree := MkImplicitBinarySearchTree(new_head.Tree_head.Tree_size)
	oldFrontier := oldSearchTree.FrontierNodes( /*@ 1/2, st.Size @*/ )
	newFrontier := newSearchTree.FrontierNodes( /*@ 1/2, new_head.Tree_head.Tree_size @*/ )

	if st.Size == 0 {
		// copy timestamps from `prf`:
		timestamps := make([]uint64, len(prf.Timestamps))
		copy(timestamps, prf.Timestamps /*@, p/2 @*/)
		st.Frontier_timestamps = timestamps
		// Initialize Full_subtrees from proof's Inclusion.Elements
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

		// Verify consistency: old frontier hashes must match Full_subtrees
		if i > len(st.Full_subtrees) || i > len(prf.Inclusion.Elements) {
			//@ fold st.Inv()
			//@ fold acc(prf.Inv(), p)
			return errors.New("consistency check failed: insufficient frontier data")
		}
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
