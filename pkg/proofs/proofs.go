package proofs

import (
	"crypto/sha256"
)

type NodeValue = [sha256.Size]byte

type UpdateValue struct {
	Value []byte
}

type CommitmentValue struct {
	Opening []byte      // VRF proof
	Label   []byte      // pseudonym; max length 2^8-1 bytes
	Update  UpdateValue // value associated with label, e.g., public key
}

type BinaryLadderStep struct {
	Proof      [sha256.Size]byte
	Commitment []byte // TODO: Make array of
}

type InclusionProof struct {
}

const (
	Reserved           = 0
	Inclusion          = 1
	NonInclusionLeaf   = 2
	NonInclusionParent = 3
)

type PrefixLeaf struct {
	vrf_output [sha256.Size]byte
	commitment [sha256.Size]byte
}

type PrefixSearchResults struct {
	result_type int
	leaf        *PrefixLeaf // only present when result_type == NonInclusionLeaf
	depth       uint8
}

type PrefixProof struct {
	results  []PrefixSearchResults
	Elements []NodeValue
}

type CombinedTreeProof struct {
	Timestamps    []uint64
	Prefix_proofs []PrefixProof
	Prefix_roots  []NodeValue
}
