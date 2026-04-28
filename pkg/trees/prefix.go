package trees

import (
	"crypto/sha256"
	"errors"
	"slices"

	"github.com/felixlinker/keytrans-verification/pkg/crypto"
	"github.com/felixlinker/keytrans-verification/pkg/proofs"
)

func bits(searchKey [sha256.Size]byte) []bool {
	// TODO:
	return []bool{}
}

type PrefixTree interface {
	GetRoot() [sha256.Size]byte
	// TODO: Make return value *[...]...
	GetCommitment(label []byte, version uint64) ([sha256.Size]byte, bool, error)
}

type prefixLeaf struct {
	value      [sha256.Size]byte
	vrfOutput  [sha256.Size]byte
	commitment [sha256.Size]byte
}

func commitmentLeaf(pl *proofs.PrefixLeaf) (t *prefixLeaf) {
	if pl == nil {
		return nil
	}

	// Spec: leaf.value = Hash(0x01 || vrf_output || commitment)
	input := append( /*@ perm(1/2), @*/ []byte{0x01}, pl.Vrf_output[:]...)
	input = append( /*@ perm(1/2), @*/ input, pl.Commitment[:]...)
	value /*@ @ @*/ := sha256.Sum256(input /*@, perm(1/2) @*/)
	return &prefixLeaf{
		value:      value,
		vrfOutput:  pl.Vrf_output,
		commitment: pl.Commitment,
	}
}

type prefixTree struct {
	leaf  *prefixLeaf
	left  *prefixTree
	right *prefixTree
}

func nodeValueLeaf(nodeValue proofs.NodeValue) (t *prefixTree) {
	return &prefixTree{
		leaf: &prefixLeaf{
			value:      nodeValue,
			vrfOutput:  [sha256.Size]byte{},
			commitment: [sha256.Size]byte{},
		},
		left:  nil,
		right: nil,
	}
}

func (t *prefixTree) insertLeaf(steps []bool, depth uint8, leaf *prefixLeaf) {
	if depth == 0 {
		t.leaf = leaf
		t.left = nil
		t.right = nil
	} else if steps[0] {
		t.right.insertLeaf(steps[1:], depth-1, leaf)
	} else {
		t.left.insertLeaf(steps[1:], depth-1, leaf)
	}
}

func (t *prefixTree) fill(elements []proofs.NodeValue) (es []proofs.NodeValue, err error) {
	if t.leaf != nil {
		return elements, nil
	}

	if t.left != nil {
		if elements, err = t.left.fill(elements); err != nil {
			return nil, err
		}
	} else if len(elements) == 0 {
		return nil, errors.New("too few elements")
	} else {
		t.left = nodeValueLeaf(elements[0])
		elements = elements[1:]
	}

	if t.right != nil {
		if elements, err = t.right.fill(elements); err != nil {
			return nil, err
		}
	} else if len(elements) == 0 {
		return nil, errors.New("too few elements")
	} else {
		t.right = nodeValueLeaf(elements[0])
		elements = elements[1:]
	}

	return elements, err
}

func (t prefixTree) value() (r [sha256.Size]byte, err error) {
	r = [sha256.Size]byte{}
	if t.leaf != nil {
		return t.leaf.value, nil
	} else if t.left == nil || t.right == nil {
		return r, errors.New("incomplete tree")
	} else if left, errL := t.left.value(); errL != nil {
		return r, errL
	} else if right, errR := t.right.value(); errR != nil {
		return r, errR
	} else {
		input := append( /*@ perm(1/2), @*/ []byte{0x02}, left[:]...)
		input = append( /*@ perm(1/2), @*/ input, right[:]...)
		return sha256.Sum256(input /*@, perm(1/2) @*/), nil
	}
}

func (t prefixTree) getLeaf(searchKey []bool) (l *prefixLeaf) {
	if t.leaf != nil || len(searchKey) == 0 {
		return t.leaf
	} else if searchKey[0] {
		return t.right.getLeaf(searchKey[1:])
	} else {
		return t.left.getLeaf(searchKey[1:])
	}
}

func (t prefixTree) search(searchKey [sha256.Size]byte) (r [sha256.Size]byte, ok bool) {
	leaf := t.getLeaf(bits(searchKey))
	return leaf.commitment, slices.Equal(leaf.vrfOutput[:], searchKey[:])
}

type prefixDict struct {
	root       [sha256.Size]byte
	tree       prefixTree
	label      []byte
	vrfOutputs map[uint64][sha256.Size]byte
}

func Dict(label []byte, version uint64, prf proofs.PrefixProof, fullLadder []proofs.BinaryLadderStep) (d prefixDict, err error) {
	steps := proofs.FullBinaryLadderSteps(version)
	if len(steps) != len(fullLadder) || len(steps) != len(prf.Results) {
		return prefixDict{}, errors.New("not enough ladder steps or prefix search results")
	}

	t := prefixTree{}
	d = prefixDict{
		label:      label,
		vrfOutputs: make(map[uint64][32]byte, len(steps)),
	}

	for i := 0; i < len(fullLadder); i++ {
		ladderVersion := steps[i]
		leafData := fullLadder[i]
		result := prf.Results[i]
		// TODO: Should verify `result.result_type`, but I skip this for now as it seems to
		// be redundant information

		// TODO: Use server public key
		if searchKey, ok := crypto.VRF_verify([]byte{}, crypto.VrfInput{Label: label, Version: version}, leafData.Proof); !ok {
			return prefixDict{}, errors.New("VRF verification failed")
		} else {
			d.vrfOutputs[ladderVersion] = searchKey
			searchKeyBits := bits(searchKey)
			if ladderVersion <= version {
				t.insertLeaf(searchKeyBits, result.Depth, commitmentLeaf(&proofs.PrefixLeaf{Vrf_output: searchKey, Commitment: leafData.Commitment}))
			} else {
				t.insertLeaf(searchKeyBits, result.Depth, commitmentLeaf(result.Leaf))
			}
		}
	}

	remaining, err := t.fill(prf.Elements)
	if len(remaining) > 0 {
		return d, errors.New("too many elements provided")
	} else if err != nil {
		return d, err
	} else if root, err := t.value(); err != nil {
		return d, err
	} else {
		d.tree = t
		d.root = root
		return d, nil
	}
}

func (d prefixDict) GetRoot() [sha256.Size]byte {
	return d.root
}

func (d prefixDict) GetCommitment(label []byte, version uint64) (r [sha256.Size]byte, ok bool, err error) {
	r = [sha256.Size]byte{}
	if !slices.Equal(label, d.label) {
		return r, false, errors.New("wrong label")
	} else if searchKey, ok := d.vrfOutputs[version]; !ok {
		return r, false, errors.New("no proof for version")
	} else {
		r, ok = d.tree.search(searchKey)
		return r, ok, nil
	}
}
