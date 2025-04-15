package proofs

import (
	"crypto/sha256"
	"errors"
)

/*@
pred (t PrefixTree) Inv() {
	acc(t.Value) && acc(t.Leaf) && acc(t.Left) && acc(t.Right) &&
	(t.Value != nil || t.Leaf != nil || t.Left != nil || t.Right != nil) &&
	((t.Leaf != nil) ==> (t.Left == nil && t.Right == nil)) &&
	((t.Left != nil || t.Right != nil) ==> t.Leaf == nil) &&
	(t.Left != nil ==> t.Left.Inv()) &&
	(t.Right != nil ==> t.Right.Inv())
}
@*/

// Recursive prefix tree data structure
type PrefixTree struct {
	// Hash value of this node; must be computed if nil
	Value *[sha256.Size]byte
	// If set, this node is a leaf of the given value. Left and Right must be nil
	// in this case.
	Leaf *PrefixLeaf
	// Left subtree. May be nil even if Right is not nil.
	Left *PrefixTree
	// Right subtree. May be nil even if Left is not nil.
	Right *PrefixTree
}

// Get the left or right child of the given tree and initialize if necessary
func (tree *PrefixTree) getChild(right bool) (sub_tree *PrefixTree) {
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

// Insert the given prefix tree at the specified depth, following the provided
// vrf_output.
func (tree *PrefixTree) initializeAt(vrf_output [32]byte, depth uint8, sub_tree PrefixTree) {
	node := tree
	var i uint8
	for i = 0; i < depth; i++ {
		node = tree.getChild(vrf_output[i/8]>>(i%8) != 0)
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

func ToTreeRecursive(prefix []bool, steps []CompleteBinaryLadderStep, coPathNodes []NodeValue) (tree *PrefixTree, nextSteps []CompleteBinaryLadderStep, nextNodes []NodeValue, err error) {
	tree = nil
	nextSteps = steps
	nextNodes = coPathNodes
	err = nil

	if len(steps) == 0 {
		if len(coPathNodes) == 0 {
			err = errors.New("not enough co-path nodes")
			return
		} else {
			tree = &PrefixTree{ Value: &coPathNodes[0] }
			nextNodes = coPathNodes[1:]
			return
		}
	}

	step := steps[0]

	prefixMatches := false
	for i := 0; i < len(prefix); i++ {
		bit := 0x01 == step.Step.Vrf_output[i / 8] >> (i % 8)
		prefixMatches = prefixMatches && bit == prefix[i]
	}

	if prefixMatches {
		if int(step.Result.Depth) < len(prefix) {
			nextDepth := len(prefix) + 1
			nextBit := 0x01 == step.Step.Vrf_output[nextDepth / 8] >> (nextDepth % 8)
			if nextBit {
				// Go right
				if len(coPathNodes) == 0 {
					err = errors.New("not enough co-path nodes")
					return
				} else {
					left := &PrefixTree{ Value: &coPathNodes[0] }
					if right, recSteps, recNodes, e := ToTreeRecursive(append(prefix, true), steps, coPathNodes[1:]); e != nil {
						err = e
						return
					} else {
						tree = &PrefixTree{ Left: left, Right: right, }
						nextSteps = recSteps
						nextNodes = recNodes
						return
					}
				}
			} else {
				// Go left
				if left, recSteps, recNodes, e := ToTreeRecursive(append(prefix, false), steps, coPathNodes); e != nil {
					err = e
					return
				} else if right, recSteps2, recNodes2, e := ToTreeRecursive(append(prefix, false), recSteps, recNodes); e != nil {
					err = e
					return
				} else {
					tree = &PrefixTree{ Left: left, Right: right }
					nextSteps = recSteps2
					nextNodes = recNodes2
					return
				}
			}
		} else if int(step.Result.Depth) == len(prefix) {
			resultType := step.Result.Result_type
			if resultType == Inclusion {
				// TODO: Copy leaf
				tree = &PrefixTree{ Leaf: &step.Step }
				nextSteps = steps[1:]
				return
			} else if resultType == NonInclusionLeaf {
				if step.Result.Leaf == nil {
					err = errors.New("no leaf for inclusion proof given")
					return
				} else {
					// TODO: copy leaf
					tree = &PrefixTree{ Leaf: step.Result.Leaf }
					nextSteps = steps[1:]
					return
				}
			} else if resultType == NonInclusionParent {
				tree = &PrefixTree{Value: &[32]byte{}}
				nextSteps = steps[1:]
				return
			} else {
				err = errors.New("invalid result type")
				return
			}
		} else {
			err = errors.New("prefix tree construction invariant violated")
			return
		}
	} else if len(coPathNodes) == 0 {
		err = errors.New("not enough co-path nodes")
		return
	} else {
		tree = &PrefixTree{ Value: &coPathNodes[0] }
		nextNodes = coPathNodes[1:]
		return
	}
}

// Construct a prefix tree from a prefix proof and the provided binary ladder
// steps. We assume that the binary ladder steps are in the order that the
// binary ladder would request them.
func (prf PrefixProof) ToTree(fullLadder []BinaryLadderStep) (tree *PrefixTree, err error) {
	tree = &PrefixTree{nil, nil, nil, nil}
	if len(fullLadder) < len(prf.Results) {
		return nil, errors.New("too many results")
	}

	var steps []CompleteBinaryLadderStep
	if steps, err = CombineResults(prf.Results, fullLadder); err != nil {
		return nil, err
	}

	tree, _, _, err = ToTreeRecursive([]bool{}, steps, prf.Elements)
	return
}

// Set the hash values of unitialized subtrees, pulling them in left-to-right
// DFS order from the provided, ordered_values. Raises an error if number of
// ordered_values does not exactly match the required values.
func (tree *PrefixTree) SetMissingSubtrees(ordered_values []NodeValue) ([]NodeValue, error) {
	var err error
	values := ordered_values

	if tree == nil {
		return ordered_values, nil
	}

	if tree.Left == nil {
		if len(ordered_values) == 0 {
			return nil, errors.New("too few node values")
		}

		left := tree.getChild(false) // initialize left child
		left.Value = &values[0]
		values = values[1:]
	} else if values, err = tree.Left.SetMissingSubtrees(values); err != nil {
		return nil, err
	}

	if tree.Right == nil {
		if len(ordered_values) == 0 {
			return nil, errors.New("too few node values")
		}

		right := tree.getChild(true) // initialize right child
		right.Value = &values[0]
		values = values[1:]
	} else if values, err = tree.Right.SetMissingSubtrees(values); err != nil {
		return nil, err
	}

	return values, nil
}

func (tree *PrefixTree) HashContent() (hashContent []byte, err error) {
	hashContent = make([]byte, sha256.Size+1)
	if tree == nil {
		return hashContent, nil
	} else if tree.Left == nil && tree.Right == nil {
		if value /*@ @ @*/, err := tree.ComputeHash(); err != nil {
			return nil, err
		} else {
			return append( /*@ perm(1/2), @*/ []byte{0x01}, value[:]...), nil
		}
	} else {
		if leftContent, err := tree.Left.HashContent(); err != nil {
			return nil, err
		} else if rightContent, err := tree.Right.HashContent(); err != nil {
			return nil, err
		} else {
			hashContent = append( /*@ perm(1/2), @*/ []byte{0x02}, leftContent...)
			return append( /*@ perm(1/2), @*/ hashContent, rightContent...), nil
		}
	}
}

// Recursively compute all hashes of a prefix tree.
func (tree *PrefixTree) ComputeHash() (hash [sha256.Size]byte, err error) {
	if tree == nil {
		return [sha256.Size]byte{}, errors.New("cannot hash empty node")
	} else if tree.Value != nil {
		return *tree.Value, nil
	} else if tree.Left == nil && tree.Right == nil {
		if tree.Leaf == nil {
			return [sha256.Size]byte{}, errors.New("neither leaf nor value given for empty node")
		} else {
			// TODO: We would have to include length, too, to be compliant with TLS
			// encoding, but not so important right now because inputs are
			// fixed-length and this may get changed in the future
			value /*@ @ @*/ := sha256.Sum256(append( /*@ perm(1/2), @*/ tree.Leaf.Vrf_output[:], tree.Leaf.Commitment[:]...) /*@, perm(1/2) @*/)
			tree.Value = &value
			return value, nil
		}
	} else {
		if leftContent, err := tree.Left.HashContent(); err != nil {
			return [sha256.Size]byte{}, err
		} else if rightContent, err := tree.Right.HashContent(); err != nil {
			return [sha256.Size]byte{}, err
		} else {
			value /*@ @ @*/ := sha256.Sum256(append( /*@ perm(1/2), @*/ leftContent, rightContent...) /*@, perm(1/2) @*/)
			tree.Value = &value
			return value, nil
		}
	}
}
