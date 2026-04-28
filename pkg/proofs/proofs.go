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
	Proof      []byte            // opaque proof[VRF.Np] — variable length per VRF scheme
	Commitment [sha256.Size]byte // optional<HashValue> - only use for versions that should exist
}

/*@
pred (s BinaryLadderStep) Inv() {
	acc(s.Proof)
}
@*/

type InclusionProof struct {
	Elements []NodeValue // HashValue elements — log-tree inclusion/consistency batch proof
}

/*@
pred (i InclusionProof) Inv() {
	acc(i.Elements)
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
	Inclusion     InclusionProof
}

/*@
pred (c CombinedTreeProof) Inv() {
	acc(c.Timestamps) &&
	acc(c.Prefix_proofs) &&
	acc(c.Prefix_roots) &&
	c.Inclusion.Inv()
}
@*/

type CompleteBinaryLadderStep struct {
	Step   PrefixLeaf
	Result PrefixSearchResult
}

// @ requires forall i int :: { &results[i] } 0 <= i && 0 < len(results) ==> acc(&results[i]) && acc(results[i].Inv())
// @ requires forall i int :: { &steps[i] } 0 <= i && 0 < len(steps) ==> acc(&steps[i]) && acc(steps[i].Inv())
// @ ensures acc(completeSteps)
// @ ensures len(completeSteps) == len(results)
func CombineResults(results []PrefixSearchResult, steps []BinaryLadderStep) (completeSteps []CompleteBinaryLadderStep, err error) {
	completeSteps = make([]CompleteBinaryLadderStep, len(results))
	if len(steps) != len(results) {
		return completeSteps, errors.New("steps mismatch")
	}

	// @ invariant 0 <= i && i <= len(results)
	// @ invariant len(completeSteps) == len(results)
	// @ invariant acc(completeSteps)
	// @ invariant forall i int :: { &results[i] } 0 <= i && 0 < len(results) ==> acc(&results[i]) && acc(results[i].Inv())
	// @ invariant forall j int :: { &steps[j] } 0 <= j && 0 < len(steps) ==> acc(&steps[j]) && acc(steps[j].Inv())
	for i := 0; i < len(results); i++ {
		// @ unfold acc(steps[i].Inv())
		completeSteps[i] = CompleteBinaryLadderStep{
			Step: PrefixLeaf{
				Vrf_output: crypto.VRF_proof_to_hash(steps[i].Proof),
				// TODO: This might be nil
				Commitment: steps[i].Commitment,
			},
			Result: results[i],
		}
		// @ fold acc(steps[i].Inv())
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
