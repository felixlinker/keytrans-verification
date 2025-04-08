package proofs

import (
	"crypto/sha256"
	"errors"

	"github.com/felixlinker/keytrans-verification/pkg/crypto"
)

type PrefixTree struct {
	Value   *[32]byte
	Leaf    *PrefixLeaf
	Left    *PrefixTree
	Right   *PrefixTree
}

func (tree *PrefixTree) GetChild(right bool) (sub_tree *PrefixTree) {
	if right {
		sub_tree = tree.Right
		if sub_tree == nil {
			sub_tree = &PrefixTree{}
			tree.Right = sub_tree
		}
	} else {
		sub_tree = tree.Left
		if sub_tree == nil {
			sub_tree = &PrefixTree{}
			tree.Left = sub_tree
		}
	}
	return sub_tree
}

func (tree *PrefixTree) InitializeAt(vrf_output [32]byte, depth uint8, sub_tree PrefixTree) {
	node := tree
	var i uint8
	for i = 0; i < depth; i++ {
		node = tree.GetChild(vrf_output[i / 8] >> (i % 8) != 0)
	}

	if sub_tree.Value != nil {
		node.Value = sub_tree.Value
	}
	if sub_tree.Leaf != nil {
		node.Leaf = sub_tree.Leaf
	}
	if sub_tree.Left != nil {
		node.Left = sub_tree.Left
	}
	if sub_tree.Right != nil {
		node.Right = sub_tree.Right
	}
}

func (prf PrefixProof) ToTree(fullLadder []BinaryLadderStep) (tree *PrefixTree, err error) {
	tree = &PrefixTree{ nil, nil, nil, nil }
	if len(fullLadder) < len(prf.Results) {
		return nil, errors.New("too many results")
	}

	var steps []CompleteBinaryLadderStep
	if steps, err = CombineResults(prf.Results, fullLadder); err != nil {
		return nil, err
	}

	for i, step := range(steps) {
		r := prf.Results[i]
		if r.Result_type == NonInclusionLeaf {
			if step.Result.Leaf == nil {
				return nil, errors.New("missing leaf")
			} else {
				tree.InitializeAt(step.Result.Leaf.Vrf_output, r.Depth, PrefixTree{
					Leaf: step.Result.Leaf,
				})
			}
		} else {
			leaf := PrefixLeaf{
				Vrf_output: crypto.VRF_proof_to_hash(step.Step.Proof),
				Commitment: step.Step.Commitment,
			}
			if r.Result_type == Inclusion {
				tree.InitializeAt(leaf.Vrf_output, r.Depth, PrefixTree{ Leaf: &leaf })
			} else if r.Result_type == NonInclusionParent {
				tree.InitializeAt(leaf.Vrf_output, r.Depth, PrefixTree{ Value: &[32]byte{} })
			} else {
				return nil, errors.New("illegal result type")
			}
		}
	}

	if remaining_values, err := tree.InitializeLeaves(prf.Elements); err != nil {
		return nil, err
	} else if len(remaining_values) > 0 {
		return nil, errors.New("too many proof elements")
	} else if _, err := tree.ComputeHash(); err != nil {
		return nil, err
	} else {
		return tree, nil
	}
}

func (tree *PrefixTree) InitializeLeaves(ordered_leaves []NodeValue) ([]NodeValue, error) {
	if tree == nil {
		return ordered_leaves, nil
	} else if tree.Left == nil && tree.Right == nil {
		if tree.Value != nil {
			return ordered_leaves, nil
		} else {
			if tree.Leaf != nil {
				input := append(tree.Leaf.Vrf_output[:], tree.Leaf.Commitment[:]...)
				digest := sha256.Sum256(input)
				tree.Value = &digest
				return ordered_leaves, nil
			} else {
				if len(ordered_leaves) > 0 {
					tree.Value = &ordered_leaves[0]
					return ordered_leaves[1:], nil
				} else {
					return nil, errors.New("missing node value")
				}
			}
		}
	} else if leaves, err := tree.Left.InitializeLeaves(ordered_leaves); err != nil {
		return nil, err
	} else if leaves, err = tree.Right.InitializeLeaves(leaves); err != nil {
		return nil, err
	} else {
		return leaves, nil
	}
}

func (tree *PrefixTree) ComputeHash() (hashContent []byte, err error) {
	hashContent = make([]byte, sha256.Size + 1)
	if tree == nil {
		return hashContent, nil
	} else if tree.Left == nil && tree.Right == nil {
		if tree.Value == nil {
			return hashContent, errors.New("leaf hashes not initialized")
		} else {
			return append([]byte{ 0x01 }, tree.Value[:]...), nil
		}
	} else if tree.Value != nil {
		return append([]byte{ 0x02 }, tree.Value[:]...), nil
	} else if leftContent, err := tree.Left.ComputeHash(); err != nil {
		return hashContent, err
	} else if rightContent, err := tree.Right.ComputeHash(); err != nil {
		return hashContent, err
	} else {
		digest := sha256.Sum256(append(leftContent, rightContent...))
		tree.Value = &digest
		return append([]byte{ 0x02 }, tree.Value[:]...), nil
	}
}
