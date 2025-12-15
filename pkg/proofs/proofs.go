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
type VRFInput struct {
	Label   []byte
	Version int
}

type Ladder struct {
	Inclusions    []VRFInput
	NonInclusions []VRFInput
}

type VRFInputKey struct {
	Label   string //From Label converted to String, used for VRFProof mapping.
	Version int
}

type VRFProof struct {
	Mapping map[VRFInputKey]bool
}

type InclusionProof struct {
	VRFProofs []VRFProof // A list of mappings from label-version to the boolean, true => inclusion, false => inclusion
}

/*@
pred (i InclusionProof) Inv() {
	true
}
@*/

// Values for PrefixSearchResult.Result_type
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

/*@
pred (p *PrefixLeaf) Inv() {
     acc(p)
}
@*/

type PrefixSearchResult struct {
	Result_type int
	Leaf        *PrefixLeaf // only present when result_type == NonInclusionLeaf
	Depth       uint8
}

/*@
pred (p PrefixSearchResult) Inv() {
	(p.Result_type == Inclusion || p.Result_type == NonInclusionParent || p.Result_type == NonInclusionLeaf) &&
	p.Result_type == NonInclusionLeaf ==> p.Leaf.Inv()
}
@*/

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
	Step   PrefixLeaf
	Result PrefixSearchResult
}

// @ trusted
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
			Step: PrefixLeaf{
				Vrf_output: crypto.VRF_proof_to_hash(step.Proof),
				Commitment: step.Commitment,
			},
			Result: results[i],
		})
	}

	return completeSteps, nil
}

// @ trusted
// @ preserves acc(sortedSteps)
func sortBinaryLadderSteps(sortedSteps []BinaryLadderStep) {
	slices.SortFunc(sortedSteps, func(a, b BinaryLadderStep) int {
		hashA := crypto.VRF_proof_to_hash(a.Proof)
		hashB := crypto.VRF_proof_to_hash(b.Proof)
		return bytes.Compare(hashA[:], hashB[:])
	})
	return
}

// @ trusted
func (v VRFInput) ToVRFInputKey() VRFInputKey {
	return VRFInputKey{Label: string(v.Label), Version: v.Version}
}

// @ trusted
func (v VRFInputKey) ToVRFInput() VRFInput {
	return VRFInput{Label: []byte(v.Label), Version: v.Version}
}

// @ trusted
//
//	preserves acc(ladder, 1/2)
//	preserves acc(v, 1/2)
func (ladder Ladder) hasInclusion(v VRFInput) bool {
	for _, inclusion := range ladder.Inclusions {
		if bytes.Equal(inclusion.Label, v.Label) {
			return true
		}
	}
	return false
}

// @ trusted
func (ladder Ladder) hasNonInclusion(v VRFInput) bool {
	for _, nonInclusion := range ladder.NonInclusions {
		if bytes.Equal(nonInclusion.Label, v.Label) {
			return true
		}
	}
	return false
}

// @ trusted
// @ requires acc(label)
func (ladder Ladder) TerminateWithinGreatest(label []byte, targetVersion *uint64) bool {
	expected := FullBinaryLadderSteps(*targetVersion)

	for _, v := range expected {
		lad := VRFInput{
			Label:   label,
			Version: int(v),
		}
		if v <= *targetVersion && !(ladder.hasInclusion(lad)) {
			return false
		}
		if v > *targetVersion && !(ladder.hasNonInclusion(lad)) {
			return false
		}
	}
	return true
}

// @ requires *targetVersion >= 0
// ensures exists v :: int v > int(*targetVersion) ==> res == 1 && err == nil
// ensures exists v :: int v < int(*targetVersion) ==> res == -1 && err == nil
func (ladder Ladder) CompareToTheGreatest(label []byte, targetVersion *uint64) (res int, err error) { //-1, 0, 1, -2

	for _, v := range ladder.Inclusions {
		if v.Version > int(*targetVersion) && bytes.Equal(v.Label, label) {
			return 1, nil // > t
		}
	}
	for _, v := range ladder.NonInclusions {
		if v.Version < int(*targetVersion) && bytes.Equal(v.Label, label) {
			return -1, nil // < t
		}
	}
	//@ t2 := 0
	//@ assert *targetVersion > 0
	expected := FullBinaryLadderSteps(*targetVersion /*@, t2 @*/)

	for _, v := range expected {
		currentLabelVersion := VRFInput{
			Label:   label,
			Version: int(v),
		}
		if v <= *targetVersion && !(ladder.hasInclusion(currentLabelVersion)) {
			return -2, errors.New("server error: information missing") //Error
		}
		if v > *targetVersion && !(ladder.hasNonInclusion(currentLabelVersion)) {
			return -2, errors.New("server error: information missing") //Error
		}
	}
	return 0, nil // = t
}
