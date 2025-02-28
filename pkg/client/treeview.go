package client

import (
	"errors"

	"github.com/felixlinker/keytrans-verification/pkg/proofs"
)

// This file implements Section 4, "Updating Views of the Tree"

type ImplicitBinarySearchTree struct {
	Root uint64
	Left *ImplicitBinarySearchTree
	Right *ImplicitBinarySearchTree
}

// Get the largest power of two smaller than tree_size
func RootNode(tree_size uint64) uint64 {
	var power uint64 = 1
	for power < tree_size {
		power = power << 1
	}
	return power >> 1
}

func (tree *ImplicitBinarySearchTree) OffSet(by uint64) {
	tree.Root += by

	if tree.Left != nil {
		tree.Left.OffSet(by)
	}
	if tree.Right != nil {
		tree.Right.OffSet(by)
	}
}

func (tree *ImplicitBinarySearchTree) PathTo(node uint64) (path []uint64, err error) {
	if tree == nil {
		return nil, errors.New("not found")
	} else if tree.Root == node {
		return []uint64{ node }, nil
	} else {
		var recurse *ImplicitBinarySearchTree
		if tree.Root < node {
			recurse = tree.Right
		} else { // tree.Root > node
			recurse = tree.Right
		}

		if path, err := recurse.PathTo(node); err != nil {
			return nil, err
		} else {
			return append([]uint64{ tree.Root }, path...), nil
		}
	}
}

//@ ensures tree != nil ==> len(path) > 0
func (tree *ImplicitBinarySearchTree) FrontierNodes() (path []uint64) {
	path = []uint64{}
	for tree != nil {
		path = append(path, tree.Root)
		tree = tree.Right
	}
	return path
}

//@ ensures tree_size != 0 ==> tree != nil
func MkImplicitBinarySearchTree(tree_size uint64) (tree *ImplicitBinarySearchTree) {
	root := RootNode(tree_size)
	if tree_size == 0 {
		return nil
	} else if tree_size == 1 {
		return &ImplicitBinarySearchTree{ root, nil, nil }
	}

	left := MkImplicitBinarySearchTree(root)
	right := MkImplicitBinarySearchTree(tree_size - root - 1)
	right.OffSet(root + 1)
	return &ImplicitBinarySearchTree{ root, left, right }
}

type UserState struct {
	Size                uint64 // 0 means no tree
	Full_subtrees       []proofs.NodeValue
	Frontier_timestamps []uint64
}

//@ ensures forall i, j int :: i < j && j < len(timestamps) ==> timestamps[i] < timestamps[j]
func checkIncreasing(timestamps []uint64) bool {
	if len(timestamps) == 0 {
		return true
	}

	tmp := timestamps[0]
	for _, v := range timestamps[1:] {
		if tmp > v {
			return false
		}
		tmp = v
	}
	return true
}

//@ ensures e == nil ==> *st.Size == new_head.Tree_head.Tree_size
func (st *UserState) UpdateView(new_head FullTreeHead, prf proofs.CombinedTreeProof) (err error) {
	if !checkIncreasing(prf.Timestamps) {
		return errors.New("timestamps not increasing")
	} else if (new_head.Tree_head.Tree_size == 0) {
		return errors.New("new tree cannot be empty")
	}

	// TODO: Verify proof of consistency

	oldSearchTree := MkImplicitBinarySearchTree(st.Size)
	newSearchTree := MkImplicitBinarySearchTree(new_head.Tree_head.Tree_size)
	oldFrontier := oldSearchTree.FrontierNodes()
	newFrontier := newSearchTree.FrontierNodes()
	if st.Size == 0 {
		st.Frontier_timestamps = newFrontier
	} else if pathToOldHead, err := newSearchTree.PathTo(st.Size - 1); err != nil {
		return err
	} else {
		i := 0
		for pathToOldHead[i] == oldFrontier[i] {
			i++
		}
		st.Frontier_timestamps = append(st.Frontier_timestamps[:i], prf.Timestamps[i:]...)
	}

	st.Size = new_head.Tree_head.Tree_size
	return nil
}
