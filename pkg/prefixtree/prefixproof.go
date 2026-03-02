package prefixtree

import (
	"bytes"
	"crypto/sha256"
	"errors"

	"github.com/felixlinker/keytrans-verification/pkg/crypto"
	"github.com/felixlinker/keytrans-verification/pkg/proofs"
)

/*@
pred (t *PrefixTree) Inv() {
	acc(t) && (t != nil ==> t.InvRec())
}

pred (t PrefixTree) InvRec() {
	acc(t.Value) && acc(t.Leaf) && acc(t.Left) && acc(t.Right) &&
	// Value dereference
	(t.Value != nil ==> acc(t.Value)) &&
	// Leaf content access
	(t.Leaf != nil ==> acc(t.Leaf)) &&
	// Recursive children
	(t.Left != nil ==> t.Left.Inv()) &&
	(t.Right != nil ==> t.Right.Inv()) &&
	// One of value, leaf, or both children must be defined
	(t.Value != nil || t.Leaf != nil || (t.Left != nil && t.Right != nil)) &&
	// If there's one children, there must be two
	(t.Left != nil) == (t.Right != nil) &&
	// Node is either a leaf or has children
	(t.Leaf != nil) != (t.Left != nil && t.Right != nil) &&
	// If a node's value is defined, its children's values must be defined
	((t.Value != nil && t.Left != nil && t.Right != nil) ==> (t.Left.GetValue() != nil && t.Right.GetValue() != nil))
}

@*/

// @ requires t != nil
// @ requires acc(t.Inv(), _)
// @ decreases
// @ pure
func (t *PrefixTree) GetValue() *[sha256.Size]byte {
	return /*@ unfolding acc(t.Inv(), _) in unfolding acc(t.InvRec(), _) in @*/ t.Value
}

// @ requires t != nil
// @ requires acc(t.Inv(), _)
// @ requires t.GetValue() != nil
// @ decreases
// @ pure
func (t *PrefixTree) GetValueArray() [sha256.Size]byte {
	return /*@ unfolding acc(t.Inv(), _) in unfolding acc(t.InvRec(), _) in @*/ *t.Value
}

// Recursive prefix tree data structure
type PrefixTree struct {
	// Hash value of this node; must be computed if nil
	Value *[sha256.Size]byte
	// If set, this node is a leaf of the given value. Left and Right must be nil
	// in this case.
	Leaf *proofs.PrefixLeaf
	// Left subtree. May be nil even if Right is not nil.
	Left *PrefixTree
	// Right subtree. May be nil even if Left is not nil.
	Right *PrefixTree
}

// Creates a prefix tree recursively from a list of binary ladder steps and
// nodes that give all copaths. The function assumes that steps is sorted
// ascending by steps.Step.Vrf_output and that coPathNodes is sorted ascending
// too. prefix will be initially empty and reflects the current position in the
// prefix tree.
// @ ensures err == nil ==> tree != nil && tree.Inv()
// @ trusted
func ToTreeRecursive(prefix []bool, steps []proofs.CompleteBinaryLadderStep, coPathNodes []proofs.NodeValue) (tree *PrefixTree, nextSteps []proofs.CompleteBinaryLadderStep, nextNodes []proofs.NodeValue, err error) {
	tree = nil
	nextSteps = steps
	nextNodes = coPathNodes
	err = nil

	// If there are no more steps to insert into the prefix tree, insert a copath
	// node at the current subtree.
	if len(steps) == 0 {
		if len(coPathNodes) == 0 {
			err = errors.New("not enough co-path nodes")
			return
		} else {
			tree = &PrefixTree{Value: &coPathNodes[0]}
			nextNodes = coPathNodes[1:]
			return
		}
	}

	step /*@@@*/ := steps[0]

	prefixMatches := true
	for i := 0; i < len(prefix); i++ {
		bit := (step.Step.Vrf_output[i/8]>>uint(i%8))&1 == 1
		prefixMatches = prefixMatches && bit == prefix[i]
	}

	if prefixMatches {
		// The current prefix is a prefix of step.Step.Vrf_output.
		if int(step.Result.Depth) < len(prefix) { // assume one-based depth; https://github.com/ietf-wg-keytrans/draft-protocol/issues/37
			// The server tells us that this depth does suffice to identify the
			// vrf output. Insert the result in one of its children.
			nextDepth := len(prefix) + 1
			nextBit := (step.Step.Vrf_output[nextDepth/8]>>uint(nextDepth%8))&1 == 1
			if nextBit {
				// Go right
				if len(coPathNodes) == 0 {
					err = errors.New("not enough co-path nodes")
					return
				} else {
					// As we must recurse right, the left child must be provided as a co
					// path node.
					left := &PrefixTree{Value: &coPathNodes[0]}
					if right, recSteps, recNodes, e := ToTreeRecursive(append( /*@ perm(1/2), @*/ prefix, true), steps, coPathNodes[1:]); e != nil {
						err = e
						return
					} else {
						tree = &PrefixTree{Left: left, Right: right}
						nextSteps = recSteps
						nextNodes = recNodes
						return
					}
				}
			} else {
				// Go left. Continue with the algorithm recursively to the right
				// afterwards. Either, the next step may be inserted there or it is
				// provided as a co path node.
				if left, recSteps, recNodes, e := ToTreeRecursive(append( /*@ perm(1/2), @*/ prefix, false), steps, coPathNodes); e != nil {
					err = e
					return
				} else if right, recSteps2, recNodes2, e := ToTreeRecursive(append( /*@ perm(1/2), @*/ prefix, true), recSteps, recNodes); e != nil {
					err = e
					return
				} else {
					tree = &PrefixTree{Left: left, Right: right}
					nextSteps = recSteps2
					nextNodes = recNodes2
					return
				}
			}
		} else if int(step.Result.Depth) == len(prefix) {
			// We are at the right depth to insert the search result. Insert it based
			// on the type of result.
			resultType := step.Result.Result_type
			if resultType == proofs.Inclusion {
				// TODO: Copy leaf
				tree = &PrefixTree{Leaf: &step.Step}
				nextSteps = steps[1:]
				return
			} else if resultType == proofs.NonInclusionLeaf {
				if step.Result.Leaf == nil {
					err = errors.New("no leaf for inclusion proof given")
					return
				} else {
					// TODO: copy leaf
					tree = &PrefixTree{Leaf: step.Result.Leaf}
					nextSteps = steps[1:]
					return
				}
			} else if resultType == proofs.NonInclusionParent {
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
		tree = &PrefixTree{Value: &coPathNodes[0]}
		nextNodes = coPathNodes[1:]
		return
	}
}

// ToTree constructs a prefix tree from a prefix proof and the provided binary
// ladder steps. We assume that the binary ladder steps are in the order that
// the binary ladder would request them.
// @ ensures err == nil ==> tree != nil && tree.Inv()
// @ ensures err != nil ==> tree != nil && tree.Inv() && tree.GetValue() != nil
// @ trusted
func ToTree(prf proofs.PrefixProof, fullLadder []proofs.BinaryLadderStep) (tree *PrefixTree, err error) {
	tree = &PrefixTree{}
	if len(fullLadder) < len(prf.Results) {
		return nil, errors.New("too many results")
	}

	var steps []proofs.CompleteBinaryLadderStep
	if steps, err = proofs.CombineResults(prf.Results, fullLadder); err != nil {
		return nil, err
	}

	if tree, _, _, err = ToTreeRecursive([]bool{}, steps, prf.Elements); err != nil {
		return
	}
	_, err = tree.ComputeHash()
	return
}

// @ requires tree != nil ==> tree.Inv()
// @ ensures  tree != nil ==> tree.Inv()
// @ ensures  err == nil && tree != nil ==> tree.GetValue() != nil
// @ trusted
func (tree *PrefixTree) HashContent() (hashContent []byte, err error) {
	hashContent = make([]byte, sha256.Size)
	if tree == nil {
		// Spec: absent node uses Hash.Nh (32) zero bytes
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
// @ requires tree != nil ==> tree.Inv()
// @ ensures  tree != nil ==> tree.Inv()
// @ ensures  tree != nil && err == nil ==> tree.GetValue() != nil && len(tree.GetValueArray()) == len(hash) && (forall i int :: { hash[i] } 0 <= i && i < len(hash) ==> (tree.GetValueArray())[i] == hash[i])
// @ trusted
func (tree *PrefixTree) ComputeHash() (hash [sha256.Size]byte, err error) {
	if tree == nil {
		return [sha256.Size]byte{}, errors.New("cannot hash empty node")
	} else if tree.Value != nil {
		return *tree.Value, nil
	} else if tree.Left == nil && tree.Right == nil {
		if tree.Leaf == nil {
			return [sha256.Size]byte{}, errors.New("neither leaf nor value given for empty node")
		} else {
			// Spec: leaf.value = Hash(0x01 || vrf_output || commitment)
			input := append( /*@ perm(1/2), @*/ []byte{0x01}, tree.Leaf.Vrf_output[:]...)
			input = append( /*@ perm(1/2), @*/ input, tree.Leaf.Commitment[:]...)
			value /*@ @ @*/ := sha256.Sum256(input /*@, perm(1/2) @*/)
			tree.Value = &value
			return value, nil
		}
	} else {
		// Spec: parent.value = Hash(0x02 || left.value || right.value)
		// where each child value is a Hash.Nh-byte (32-byte) hash.
		leftHash, leftErr := tree.Left.ComputeHash()
		if leftErr != nil {
			return [sha256.Size]byte{}, leftErr
		}
		rightHash, rightErr := tree.Right.ComputeHash()
		if rightErr != nil {
			return [sha256.Size]byte{}, rightErr
		}
		input := append( /*@ perm(1/2), @*/ []byte{0x02}, leftHash[:]...)
		input = append( /*@ perm(1/2), @*/ input, rightHash[:]...)
		value /*@ @ @*/ := sha256.Sum256(input /*@, perm(1/2) @*/)
		tree.Value = &value
		return value, nil
	}
}

//Lemma : Merkle Binding
// This Merkle binding theorem is needed for showing that the commitment is in the tree state
// It is also one of the important lemmas we need to show that the commitment we get is consistent
// We use the following paper to derive the following lemma
// Paper: https://arxiv.org/pdf/2501.10802

/*@
// this captures our assumption that GetCommitment is deterministic
ghost
decreases
// takes seq[byte] inputs so it remains pure (no heap permissions needed)
// returns bool: true = commitment exists (inclusion), false = no commitment (non-inclusion)
pure func GetCommitmentIsDeterministic(Label seq[byte], Version uint64, RootHash seq[byte]) bool
@*/

// GetCommitment searches the authenticated prefix tree for the commitment
// corresponding to the given (Label, Version) pair.
//
// Following the Authentikit pattern from "Logical Relations for Formally
// Verified Authenticated Data Structures" (Gregersen et al., CCS '25):
// This implements the "ideal" retrieve operation. The tree has already been
// constructed from proofs (ToTree) and its hashes computed (ComputeHash),
// which corresponds to the verifier's unauth checks at each level (Figure 3c).
// GetCommitment computes the VRF output for (Label, Version) and searches
// the prefix tree for a matching leaf.
//
// Returns:
//   - (commitment, nil) if a leaf with matching VRF output is found (inclusion)
//   - (nil, nil)         if no matching leaf exists (non-inclusion)
//   - (nil, error)       if the tree is in an invalid state
//
// @ requires Label != nil && len(Label) >= 0
// @ requires Version >= 0
// @ requires acc(Label)
// @ requires acc(RootHash)
// @ ensures acc(res)
// @ ensures acc(RootHash)
// @ ensures acc(Label)
// @ ensures err == nil ==> (res != nil) == GetCommitmentIsDeterministic(labelS, Version, rootHashS)
// @ trusted
func (tree *PrefixTree) GetCommitment(Label []byte, Version uint64, RootHash []byte /*@, ghost labelS seq[byte], ghost rootHashS seq[byte]@*/) (res []byte, err error) {
	if tree == nil {
		// Nil tree: non-inclusion (no commitments exist in an empty tree)
		return nil, nil
	}

	// Verify the tree's root hash matches the provided root hash.
	if tree.Value != nil {
		if !bytes.Equal(tree.Value[:], RootHash) {
			return nil, errors.New("root hash mismatch")
		}
	} else if value, hashErr := tree.ComputeHash(); hashErr != nil {
		return nil, hashErr
	} else if !bytes.Equal(value[:], RootHash) {
		return nil, errors.New("root hash mismatch")
	}

	// Compute the VRF output for the (Label, Version) pair.
	// The VRF output determines the path through the prefix tree.
	VRFInput := crypto.VrfInput{
		Label:   Label,
		Version: uint32(Version),
	}
	//@ fold VRFInput.Inv()
	vrfOutput := crypto.VRF_hash(nil, VRFInput)
	vrfOutputSlice := make([]byte, sha256.Size)
	for i := 0; i < sha256.Size; i++ {
		vrfOutputSlice[i] = vrfOutput[i]
	}

	// Search the prefix tree following the VRF output bits
	res, err = tree.SearchForCommitment(vrfOutputSlice, 0)
	return
}

// SearchForCommitment traverses the prefix tree following the bits of
// vrfOutput starting at the given depth. This corresponds to the ideal
// retrieve operation from the Authentikit pattern (Figure 3b in
// Gregersen et al.): descend left or right based on the path bits,
// and return the value at the matching leaf.
//
// @ preserves tree!= nil ==> tree.Inv()
// @ trusted
func (tree *PrefixTree) SearchForCommitment(vrfOutput []byte, depth int) ([]byte, error) {
	if tree == nil {
		return nil, nil
	}

	node := tree
	d := depth
	maxDepth := len(vrfOutput) * 8

	for d < maxDepth {
		if node == nil {
			// Path doesn't exist: non-inclusion
			return nil, nil
		}

		//@ unfold node.Inv()

		// Case 1: Leaf node — check if VRF output matches
		if node.Leaf != nil {
			if bytes.Equal(node.Leaf.Vrf_output[:], vrfOutput) {
				// Inclusion: return a copy of the commitment
				result := make([]byte, sha256.Size)
				for i := 0; i < sha256.Size; i++ {
					result[i] = node.Leaf.Commitment[i]
				}
				//@ fold node.Inv()
				return result, nil
			}
			// Non-inclusion: leaf exists but VRF output doesn't match
			//@ fold node.Inv()
			return nil, nil
		}

		// Case 2: Internal node with children — navigate based on bit
		if node.Left != nil && node.Right != nil {
			byteIdx := d / 8
			bitIdx := d % 8
			bit := (vrfOutput[byteIdx] >> bitIdx) & 1

			if bit == 1 {
				node = node.Right
			} else {
				node = node.Left
			}
			d++
			//@ fold node.Inv()
			continue
		}

		// Case 3: Copath node (has Value but no children/leaf) —
		// the tree was only partially expanded via the prefix proof,
		// so we cannot determine inclusion or non-inclusion.
		if node.Value != nil {
			//@ fold node.Inv()
			return nil, errors.New("cannot determine: reached copath node")
		}

		// Case 4: Invalid tree node (no leaf, no children, no value)
		//@ fold node.Inv()
		return nil, errors.New("invalid tree node state")
	}

	return nil, errors.New("exceeded maximum tree depth")
}
