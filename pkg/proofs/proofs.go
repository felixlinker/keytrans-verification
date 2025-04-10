package proofs

import (
	"bytes"
	"crypto/sha256"
	"errors"
	"slices"

	"github.com/felixlinker/keytrans-verification/pkg/crypto"
)

type NodeValue = [sha256.Size]byte

type UpdateValue struct {
	Value []byte
}

/*@
pred (u UpdateValue) Inv() {
	acc(u.Value)
}
@*/

type CommitmentValue struct {
	Opening []byte
	Label   []byte      // pseudonym; max length 2^8-1 bytes
	Update  UpdateValue // value associated with label, e.g., public key
}

type BinaryLadderStep struct {
	Proof      [sha256.Size]byte
	Commitment [sha256.Size]byte
}

type InclusionProof struct {
}

/*@
pred (i InclusionProof) Inv() {
	true
}
@*/

const (
	Reserved           = 0
	Inclusion          = 1
	NonInclusionLeaf   = 2
	NonInclusionParent = 3
)

// A leaf in a prefix tree
type PrefixLeaf struct {
	// Vrf_output for the search key and version pair stored at this leaf.
	Vrf_output [sha256.Size]byte
	// Commitment to the public key of the search key and version pair.
	Commitment [sha256.Size]byte
}

type PrefixSearchResult struct {
	Result_type int
	Leaf        *PrefixLeaf // only present when result_type == NonInclusionLeaf
	Depth       uint8
}

type PrefixProof struct {
	Results  []PrefixSearchResult
	Elements []NodeValue
}

type CombinedTreeProof struct {
	Timestamps    []uint64
	Prefix_proofs []PrefixProof
	Prefix_roots  []NodeValue
}

/*@
pred (c CombinedTreeProof) Inv() {
	acc(c.Timestamps) &&
	acc(c.Prefix_proofs) &&
	acc(c.Prefix_roots)
}
@*/

type CompleteBinaryLadderStep struct {
	Step   BinaryLadderStep
	Result PrefixSearchResult
}

//@ trusted
func CombineResults(results []PrefixSearchResult, steps []BinaryLadderStep) (completeSteps []CompleteBinaryLadderStep, err error) {
	completeSteps = make([]CompleteBinaryLadderStep, 0, len(results))
	if len(steps) < len(results) {
		return completeSteps, errors.New("not enough steps")
	}

	sortedSteps := make([]BinaryLadderStep, 0, len(results))
	copy(sortedSteps, steps[:len(results)])
	sortBinaryLadderSteps(sortedSteps)

	for i, step := range sortedSteps {
		completeSteps = append(completeSteps, CompleteBinaryLadderStep{
			Step:   step,
			Result: results[i],
		})
	}

	return completeSteps, nil
}

//@ trusted
//@ preserves acc(sortedSteps)
func sortBinaryLadderSteps(sortedSteps []BinaryLadderStep) {
	slices.SortFunc(sortedSteps, func(a, b BinaryLadderStep) int {
		hashA := crypto.VRF_proof_to_hash(a.Proof)
		hashB := crypto.VRF_proof_to_hash(b.Proof)
		return bytes.Compare(hashA[:], hashB[:])
	})
	return
}
