package proofs

import (
	"bytes"
	"crypto/sha256"

	"github.com/felixlinker/keytrans-verification/pkg/utils"
)

type NodeValue = [sha256.Size]byte

/*@
pred NodeValuesInv(vs []*NodeValue) {
	forall i int :: {&vs[i]} 0 <= i && i < len(vs) ==> acc(&vs[i]) && acc(vs[i])
}
@*/

type UpdateValue struct {
	Value []byte
}

/*@
pred (u *UpdateValue) Inv() {
	acc(u) && acc(u.Value)
}
@*/

// @ requires noPerm < p
// @ preserves acc(v.Inv(), p)
func (v *UpdateValue) Marshal( /*@ ghost p perm @*/ ) (r []byte) {
	// @ unfold acc(v.Inv(), p)
	buf := bytes.NewBuffer(nil)
	buf.Write(utils.Uint32(uint32(len(v.Value))))
	buf.Write(v.Value)
	// @ fold acc(v.Inv(), p)
	return buf.Bytes()
}

type BinaryLadderStep struct {
	Proof      []byte             // opaque proof[VRF.Np] — variable length per VRF scheme
	Commitment *[sha256.Size]byte // optional<HashValue> - only use for versions that should exist
}

/*@
pred (s *BinaryLadderStep) Inv() {
	acc(s) && acc(s.Proof) && (s.Commitment != nil ==> acc(s.Commitment))
}

pred BinaryLadderStepsInv(steps []*BinaryLadderStep) {
	forall i int :: {&steps[i]} 0 <= i && i < len(steps) ==> acc(&steps[i]) && acc(steps[i].Inv())
}
@*/

type InclusionProof struct {
	Elements []*NodeValue // HashValue elements — log-tree inclusion/consistency batch proof
}

/*@
pred (i *InclusionProof) Inv() {
	acc(i) && i.Elements != nil &&
	(forall j int :: 0 <= j && j < len(i.Elements) ==> acc(&i.Elements[j]) && acc(i.Elements[j]))
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
	Vrf_output []byte
	// Commitment to the public key of the search key and version pair.
	Commitment *[sha256.Size]byte
}

/*@
pred (l *PrefixLeaf) Inv() {
	acc(l) && acc(l.Vrf_output) && acc(l.Commitment)
}
@*/

type PrefixSearchResult struct {
	// NOTE: Real API also provides a result type, but this is not needed for
	// reconstruction, thus, dropped.
	// NOTE: I always expect a leaf and removed commitments from the binary ladder
	// This is an API change, that, however simplifies my life.
	Leaf  *PrefixLeaf
	Depth uint8
}

/*@
pred (p *PrefixSearchResult) Inv() {
	acc(p) && acc(p.Leaf.Inv())
}

pred PrefixSearchResultsInv(rs []*PrefixSearchResult) {
	forall i int :: {&rs[i]} 0 <= i && i < len(rs) ==> acc(&rs[i]) && acc(rs[i].Inv())
}
@*/

type PrefixProof struct {
	Results  []*PrefixSearchResult
	Elements []*NodeValue
}

/*@
pred (p *PrefixProof) Inv() {
	acc(p) && PrefixSearchResultsInv(p.Results) && NodeValuesInv(p.Elements)
}

pred PrefixProofsInv(ps []*PrefixProof) {
	forall i int :: {ps[i]} 0 <= i && i < len(ps) ==> acc(&ps[i]) && acc(ps[i].Inv())
}
@*/

type CombinedTreeProof struct {
	Timestamps    []uint64
	Prefix_proofs []*PrefixProof
	Prefix_roots  []*NodeValue
	Inclusion     *InclusionProof
}

/*@
pred (c *CombinedTreeProof) Inv() {
	acc(c) && acc(c.Timestamps) && PrefixProofsInv(c.Prefix_proofs) &&
	NodeValuesInv(c.Prefix_roots) && acc(c.Inclusion.Inv())
}
@*/
