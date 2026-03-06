package prefixtree

import (
	"crypto/sha256"
	"errors"

	"github.com/felixlinker/keytrans-verification/pkg/crypto"
	"github.com/felixlinker/keytrans-verification/pkg/proofs"
)

/*@
pred (t *PrefixTree) Inv() {
	acc(t) && (t != nil ==> t.InvRec())
}

//TODO: I think this is wrong.
// If there's one children, there must be two
// (t.Left != nil) == (t.Right != nil) &&
//  According to Figure 5 in the spec, there could be cases that only one child exists. So this invariant should not exist.


pred (t PrefixTree) InvRec() {
	acc(t.Value) && acc(t.Leaf) && acc(t.Left) && acc(t.Right) &&
	// One of value, leaf, or both children must be defined
	(t.Value != nil || t.Leaf != nil || (t.Left != nil && t.Right != nil)) &&
	// Node is either a leaf or has children
	(t.Leaf != nil) != (t.Left != nil && t.Right != nil) &&
	// If a node's value is defined, its children's values must be defined
	((t.Value != nil && t.Left != nil && t.Right != nil) ==> (t.Left.Value != nil && t.Right.Value != nil))
}

@*/

/*@
  ghost
  requires acc(arr, _)
  decreases
  pure
  func getContent(arr []byte) (res seq[byte]) {
    return GetByteContent(arr, 0)
  }

  ghost
  requires acc(arr, _)
  requires 0 <= idx && idx <= len(arr)
  decreases len(arr) - idx
  pure
  func GetByteContent(arr []byte, idx int) (res seq[byte]) {
    return idx == len(arr) ? seq[byte]{} : seq[byte]{arr[idx]} ++ GetByteContent(arr, idx + 1)
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

	prefixMatches := false
	for i := 0; i < len(prefix); i++ {
		bit := step.Step.Vrf_output[i/8]>>(i%8) == 0x01
		prefixMatches = prefixMatches && bit == prefix[i]
	}

	if prefixMatches {
		// The current prefix is a prefix of step.Step.Vrf_output.
		if int(step.Result.Depth) < len(prefix) { // assume one-based depth; https://github.com/ietf-wg-keytrans/draft-protocol/issues/37
			// The server tells us that this depth does suffice to identify the
			// vrf output. Insert the result in one of its children.
			nextDepth := len(prefix) + 1
			nextBit := step.Step.Vrf_output[nextDepth/8]>>(nextDepth%8) == 0x01
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
				} else if right, recSteps2, recNodes2, e := ToTreeRecursive(append( /*@ perm(1/2), @*/ prefix, false), recSteps, recNodes); e != nil {
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

// Construct a prefix tree from a prefix proof and the provided binary ladder
// steps. We assume that the binary ladder steps are in the order that the
// binary ladder would request them.
// @ ensures err == nil ==> tree != nil && tree.Inv() && tree.GetValue() != nil
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
// @ ensures  err != nil && tree != nil ==> tree.GetValue() != nil
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
// @ requires tree != nil ==> tree.Inv()
// @ ensures  tree != nil ==> tree.Inv()
// @ ensures  tree != nil && err != nil ==> tree.GetValue() != nil && len(tree.GetValueArray()) == len(hash) && (forall i int :: { hash[i] } 0 <= i && i < len(hash) ==> (tree.GetValueArray())[i] == hash[i])
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

//For looking up the key in the commitment
//If there is an error, then the server has not even mentioned the existence of the label,version
//So error
//Otherwise, it should be either nil or not nil.
//Here, we assume that the return value is deterministic.

// @ requires acc(commitmentMap)
// @ requires acc(Label, 1/2)
// @ requires acc(rootHash,1/2)
// @ requires labelS == getContent(Label)
// @ requires rootHashS == getContent(rootHash)
// @ ensures acc(commitmentMap)
// @ ensures acc(Label, 1/2)
// @ ensures acc(rootHash,1/2)
// @ ensures err == nil ==> (res != nil) == GetCommitmentIsDeterministic(labelS, Version, rootHashS)
// @ trusted
func LookUpCommitment(commitmentMap map[proofs.VRFInputKey]*[sha256.Size]byte, Label []byte, Version uint64, rootHash []byte /*@, ghost labelS seq[byte], ghost rootHashS seq[byte], @*/) (res *[sha256.Size]byte, err error) {
	key := proofs.VRFInputKey{Label: string(Label), Version: int(Version)}
	val, exists := commitmentMap[key]
	if !exists {
		return nil, errors.New("(label,version) not in commitment map")
	}
	return val, nil

}

//The commitment map which will be built when reading the response of the server
// Instead of building the whole tree using ToTree, we'll just use the answer from the server itself
// Similar to Brendan's implementation.

// @ requires acc(label)
// @ requires acc(results)
// @ requires acc(ladder)
// @ requires acc(ladderVersions)
// @ requires len(results) <= len(ladder)
// @ requires len(results) == len(ladderVersions)
// @ ensures acc(label)
// @ ensures acc(results)
// @ ensures acc(ladder)
// @ ensures acc(ladderVersions)
// @ ensures err == nil ==> acc(commitmentMap)
// @ trusted
func BuildcommitmentMap(label []byte, results []proofs.PrefixSearchResult, ladder []proofs.BinaryLadderStep, ladderVersions []uint64) (commitmentMap map[proofs.VRFInputKey]*[sha256.Size]byte, err error) {
	commitmentMap = make(map[proofs.VRFInputKey]*[32]byte)
	// Check fi the results and the ladders are having the same length
	//The prefixSearchResults are saying which versions are included and which are not!
	if len(results) > len(ladder) {
		return nil, errors.New("More results than the ladder steps")
	}
	// If the server is not the same as the ladder results,
	// this means some versions are missing or added more.
	// We'll have to return an error
	if len(results) != len(ladderVersions) {
		return nil, errors.New("result mismatch")
	}

	//Labels are in the original implementation []bytes
	//However, this would be extremely bad with Go as []bytes cannot be key in the map
	//So we convert the label into string.
	//There may be side effects, so maybe we need to think of better way to handle that
	labelStr := string(label)
	for i := 0; i < len(results); i++ {
		// Define (Label, version) as key
		key := proofs.VRFInputKey{Label: labelStr, Version: int(ladderVersions[i])}
		//Per spec, the order of results should preserve the ladder order.
		// Each BinaryLadderStep structure contains information related to one version of the label in the binary ladder for the target version,
		// listed in the same order that the versions are output by the algorithm in Section 5.

		if _, ok := commitmentMap[key]; ok {
			//The binary ladder should be distinct.
			//So if this case happens, so we need to return an error.
			return nil, errors.New("Duplicate (label,version) in the ladder")
		}
		resultType := results[i].Result_type
		if resultType == proofs.Inclusion {
			if ladder[i].Commitment == nil {
				return nil, errors.New("inclusion result but no commitment...")
			}
			commitmentMap[key] = ladder[i].Commitment
		} else if resultType == proofs.NonInclusionLeaf || resultType == proofs.NonInclusionParent {
			//If the status is not included
			//We can just return nil
			commitmentMap[key] = nil
		} else {
			return nil, errors.New("invalid result type")
		}
	}
	return commitmentMap, nil

}

// GetCommitmentMap abstracts the prefix tree as a map: given (Label, Version),
// returns the commitment if included, nil otherwise.
// The postcondition ties the result to GetCommitmentIsDeterministic.
// So instead of traversing from the root down to the leaf, the response has already provided the answer which versions are included or not
// The only thing we need to verify is the path from leaf to root, instead of building the tree
// and then trying to see if the commitment is in the tree or not.
// I don't think the first way is making too much sense in the first place.

// @ requires Label != nil && len(Label) >= 0
// @ requires Version >= 0
// @ requires acc(Label, 1/2)
// @ requires acc(RootHash, 1/2)
// @ requires acc(pk, 1/2)
// @ requires acc(proof_step, 1/2)
// @ ensures acc(res)
// @ ensures acc(RootHash)
// @ ensures acc(Label)
// @ ensures err == nil ==> (res != nil) == GetCommitmentIsDeterministic(labelS, Version, rootHashS)
// @ trusted
func GetCommitmentMap(pk []byte, step_proof []byte, Label []byte, Version uint64, RootHash []byte /*@, ghost labelS seq[byte], ghost rootHashS seq[byte]@*/) (res *[32]byte, err error) {
	return nil, nil
}

// @ requires Label != nil && len(Label) >= 0
// @ requires Version >= 0
// @ requires acc(Label, 1/2)
// @ requires acc(RootHash, 1/2)
// @ requires acc(pk, 1/2)
// @ requires acc(proof_step, 1/2)
// @ ensures acc(res)
// @ ensures acc(RootHash)
// @ ensures acc(Label)
// @ ensures err == nil ==> (res != nil) == GetCommitmentIsDeterministic(labelS, Version, rootHashS)
// @ trusted
func (tree *PrefixTree) GetCommitment(pk []byte, step_proof []byte, Label []byte, Version uint64, RootHash []byte /*@, ghost labelS seq[byte], ghost rootHashS seq[byte]@*/) (res *[32]byte, err error) {
	//1. Verify that the VRF_verify(pk, (label, version), step.Proof) is true

	VRF_input := crypto.VrfInput{
		Label:   Label,
		Version: uint32(Version),
	}
	//TODO: Here, we are using arbitrary pk. But it would be good to have pk in the first place as we're implementing a stub

	valid, VRF_output := crypto.VRF_verify(pk, VRF_input, step_proof)
	if !valid {
		return nil, errors.New("Verification of the VRF failed")

	}

	commitment, err := tree.SearchForCommitment(VRF_output)
	if err != nil {
		return nil, err
	}

	//2. Verify that the Result_type == {1,2,3}, 1 means included, 2,3 means not included
	//3. return commitment from the BinaryLadder type, can be nil
	return commitment, nil
}

// Here, the idea is to traverse through the VRF_output and see if the commitment is present.
// We do recursive search
// @trusted
func (tree *PrefixTree) SearchForCommitment(VRF_output [sha256.Size]byte) (commitment *[sha256.Size]byte, err error) {
	//Here, the tree is somehow empty. So we cannot argue on the tree anyway
	if tree == nil {
		return nil, errors.New("The tree is empty")
	}
	//Check if it's nil, if yes, then see if it's leaf. If not, then return error
	node := tree // The start is always root
	//sha256.Size is 32 with byte structure, so *8
	//We do iterative version.

	for d := 0; d < sha256.Size*8; d++ {
		//As the prefixtree will have different depth, we need to check the leaf value. If we have reached a leaf
		//In this case, Left and Right must be nil
		if node.Leaf != nil && node.Left == nil && node.Right == nil {
			//Check if the leaf value matches. If yes, then commitment
			if node.Leaf.Vrf_output == VRF_output {
				return &node.Leaf.Commitment, nil
			}
			//The VRF output doesn't match, so commitment definitely not included
			return nil, nil
		} else if node.Left != nil || node.Right != nil {
			//Consistent with ToTreeRecursive
			//Index d is used in bit representation, while the VRF_output is in byte.
			//So we need to do these ugly conversion.
			bit := (VRF_output[d/8] >> uint(d%8)) & 1
			if bit == 0 && node.Left != nil {
				node = node.Left
			} else if bit == 1 && node.Right != nil {
				node = node.Right
			} else if node.Value != nil {
				//The server is only providing the hash value of the copath node.
				//So we cannot go down to check if the value of the version is included or not.
				return nil, errors.New("Reached copath node, view incomplete, not able to verify")
			} else {
				return nil, errors.New("Either bit is pointing to the wrong direction ")
			}
		} else {
			return nil, errors.New("Undefined behavior")
		}

	}
	return nil, nil
}
