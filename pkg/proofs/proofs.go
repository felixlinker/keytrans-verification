package proofs

// @ import "github.com/felixlinker/keytrans-verification/pkg/utils"

type NodeValue = []byte

/*@
pred NodeValuesInv(vs []NodeValue) {
	forall i int :: {vs[i]} 0 <= i && i < len(vs) ==> acc(&vs[i]) && acc(utils.BytesMem(vs[i]))
}
@*/

type BinaryLadderStep struct {
	Proof      []byte // opaque proof[VRF.Np] — variable length per VRF scheme
	Commitment []byte // optional<HashValue> - only use for versions that should exist
}

/*@
pred (s *BinaryLadderStep) Inv() {
	acc(s) && acc(utils.BytesMem(s.Proof)) && (s.Commitment != nil ==> acc(utils.BytesMem(s.Commitment)))
}

pred BinaryLadderStepsInv(steps []*BinaryLadderStep) {
	forall i int :: {&steps[i]} 0 <= i && i < len(steps) ==> acc(&steps[i]) && acc(steps[i].Inv())
}
@*/

type InclusionProof struct {
	Elements []NodeValue // HashValue elements — log-tree inclusion/consistency batch proof
}

/*@
pred (i *InclusionProof) Inv() {
	acc(i) && acc(NodeValuesInv(i.Elements))
}
@*/

// Values for PrefixSearchResult.Result_type
type PrefixSearchResultType byte

const (
	Reserved           PrefixSearchResultType = 0
	Inclusion          PrefixSearchResultType = 1
	NonInclusionLeaf   PrefixSearchResultType = 2
	NonInclusionParent PrefixSearchResultType = 3
)

// A leaf in a prefix tree
type PrefixLeaf struct {
	Depth      uint8
	NodeValue  []byte
	VrfOutput  []byte
	Commitment []byte
}

/*@
pred (l *PrefixLeaf) Inv() {
	acc(l) && (l.NodeValue != nil ==> utils.BytesMem(l.NodeValue)) &&
		(l.VrfOutput != nil ==> utils.BytesMem(l.VrfOutput)) &&
		(l.Commitment != nil ==> utils.BytesMem(l.Commitment))
}
@*/

/*@
pred PrefixLeavesInv(ls []*PrefixLeaf) {
	forall i int :: {ls[i]} 0 <= i && i < len(ls) ==> acc(&ls[i]) && acc(ls[i].Inv())

}
@*/

type PrefixProof struct {
	Leaves []*PrefixLeaf
}

/*@
pred (p *PrefixProof) Inv() {
	acc(p) && PrefixLeavesInv(p.Leaves)
}

pred PrefixProofsInv(ps []*PrefixProof) {
	forall i int :: {ps[i]} 0 <= i && i < len(ps) ==> acc(&ps[i]) && acc(ps[i].Inv())
}
@*/

type CombinedTreeProof struct {
	Timestamps    []uint64
	Prefix_proofs []*PrefixProof
	Prefix_roots  []NodeValue
	Inclusion     *InclusionProof
}

/*@
pred (c *CombinedTreeProof) Inv() {
	acc(c) && acc(c.Timestamps) && PrefixProofsInv(c.Prefix_proofs) &&
	NodeValuesInv(c.Prefix_roots) && acc(c.Inclusion.Inv())
}
@*/
