package proofs

import (
	"errors"

	"github.com/felixlinker/keytrans-verification/pkg/crypto"
	"github.com/felixlinker/keytrans-verification/pkg/utils"
	// @ "crypto/sha256"
)

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
	// Vrf_output for the search key and version pair stored at this leaf.
	Vrf_output []byte
	// Commitment to the public key of the search key and version pair.
	Commitment []byte
}

/*@
pred (l *PrefixLeaf) Inv() {
	acc(l) && len(l.Vrf_output) == 32 && acc(utils.BytesMem(l.Vrf_output)) && acc(utils.BytesMem(l.Commitment))
}
@*/

type PrefixSearchResult struct {
	ResultType PrefixSearchResultType
	Leaf       *PrefixLeaf
	Depth      uint8
}

/*@
pred (p *PrefixSearchResult) Inv() {
	acc(p) && (p.Leaf != nil ==> acc(p.Leaf.Inv()))
}

pred PrefixSearchResultsInv(rs []*PrefixSearchResult) {
	forall i int :: {rs[i]} 0 <= i && i < len(rs) ==> acc(&rs[i]) && acc(rs[i].Inv())
}
@*/

type PrefixProof struct {
	Results  []*PrefixSearchResult
	Elements []NodeValue
}

/*@
pred (p *PrefixProof) Inv() {
	acc(p) && PrefixSearchResultsInv(p.Results) && NodeValuesInv(p.Elements)
}

pred PrefixProofsInv(ps []*PrefixProof) {
	forall i int :: {ps[i]} 0 <= i && i < len(ps) ==> acc(&ps[i]) && acc(ps[i].Inv())
}
@*/

// @ requires noPerm < p
// @ preserves acc(PrefixProofsInv(prfs))
// @ preserves acc(BinaryLadderStepsInv(ladder), p) && acc(utils.BytesMem(pk), p) && acc(utils.BytesMem(label), p)
func PullLeaves(prfs []*PrefixProof, ladder []*BinaryLadderStep, pk []byte, label []byte, version uint64 /*@, ghost p perm @*/) (err error) {
	// @ invariant acc(PrefixProofsInv(prfs))
	// @ invariant acc(BinaryLadderStepsInv(ladder), p) && acc(utils.BytesMem(pk), p) && acc(utils.BytesMem(label), p)
	// @ invariant 0 <= i && i <= len(prfs)
	for i := 0; i < len(prfs) && err == nil; i++ {
		// @ unfold acc(PrefixProofsInv(prfs))
		err = pullLeaves(prfs[i], ladder, pk, label, version /*@, p @*/)
		// @ fold acc(PrefixProofsInv(prfs))
	}
	return
}

// @ requires noPerm < p
// @ preserves acc(prf.Inv())
// @ preserves acc(BinaryLadderStepsInv(ladder), p) && acc(utils.BytesMem(pk), p) && acc(utils.BytesMem(label), p)
func pullLeaves(prf *PrefixProof, ladder []*BinaryLadderStep, pk []byte, label []byte, version uint64 /*@, ghost p perm @*/) (err error) {
	// @ unfold acc(prf.Inv())
	if len(ladder) < len(prf.Results) {
		err = errors.New("too few binary ladder steps")
	} else {
		// @ invariant acc(prf) && PrefixSearchResultsInv(prf.Results) && NodeValuesInv(prf.Elements)
		// @ invariant 0 <= i && i <= len(prf.Results) && i <= len(ladder)
		// @ invariant acc(BinaryLadderStepsInv(ladder), p) && acc(utils.BytesMem(pk), p) && acc(utils.BytesMem(label), p)
		for i := 0; i < len(prf.Results) && i < len(ladder) && err == nil; i++ {
			// @ unfold PrefixSearchResultsInv(prf.Results)
			// @ unfold acc(prf.Results[i].Inv())
			if prf.Results[i].ResultType == Inclusion {
				// @ unfold acc(BinaryLadderStepsInv(ladder), p)
				// @ unfold acc(ladder[i].Inv(), p)
				if vrfOutput, ok := crypto.VRF_verify(pk, label, version, ladder[i].Proof /*@, p @*/); !ok {
					err = errors.New("VRF did not verify")
				} else if ladder[i].Commitment == nil {
					err = errors.New("binary ladder misses commitment")
				} else {
					// Copy commitment
					leaf /*@@@*/ := PrefixLeaf{
						Vrf_output: vrfOutput,
						Commitment: utils.Copy(ladder[i].Commitment /*@, p @*/),
					}
					prf.Results[i].Leaf = &leaf
					// @ fold acc(prf.Results[i].Leaf.Inv())
				}
				// @ fold acc(ladder[i].Inv(), p)
				// @ fold acc(BinaryLadderStepsInv(ladder), p)
			}
			// @ fold acc(prf.Results[i].Inv())
			// @ fold PrefixSearchResultsInv(prf.Results)
		}
	}
	// @ fold acc(prf.Inv())
	return
}

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
