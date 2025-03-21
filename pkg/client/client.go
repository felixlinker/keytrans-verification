package client

import (
	"errors"

	"github.com/felixlinker/keytrans-verification/pkg/crypto"
	"github.com/felixlinker/keytrans-verification/pkg/proofs"
)

type TreeHead struct {
	Tree_size uint64
	Signature []byte
}

/*@
pred (t TreeHead) Inv() {
	acc(t.Signature)
}
@*/

type FullTreeHead struct {
	Tree_head TreeHead
	// TODO: AuditorTreeHead auditor_tree_head
}

/*@
pred (f FullTreeHead) Inv() {
	f.Tree_head.Inv()
}

ghost
decreases
requires f.Inv()
pure func (f FullTreeHead) Size() uint64 {
	return unfolding f.Inv() in f.Tree_head.Tree_size
}
@*/

type SearchRequest struct {
	Last  *uint32
	Label []byte
	// TODO: optional<uint32> version
}

/*@
pred (s SearchRequest) Inv() {
	acc(s.Last) && acc(s.Label)
}
@*/

type SearchResponse struct {
	Full_tree_head FullTreeHead
	Version        *uint32 // version; only present for latest-key queries
	Binary_ladder  []proofs.BinaryLadderStep
	Search         proofs.CombinedTreeProof
	Inclusion      proofs.InclusionProof
	Opening        []byte             // TODO: For actual VRFs, this would be fixed size
	Value          proofs.UpdateValue // value associated with queried label
}

/*@
pred (s SearchResponse) Inv() {
	s.Full_tree_head.Inv() &&
	acc(s.Version) &&
	acc(s.Binary_ladder) &&
	s.Search.Inv() &&
	s.Inclusion.Inv() &&
	acc(s.Opening) &&
	s.Value.Inv()
}
@*/

//@ requires noPerm < p
//@ preserves st.Inv()
//@ preserves acc(query.Inv(), p) && acc(prf.Inv(), p)
//@ ensures err == nil ==> acc(res) && res.Inv()
func (st *UserState) VerifyLatest(query SearchRequest, prf SearchResponse /*@, ghost p perm @*/) (res *proofs.UpdateValue, err error) {
	//@ unfold acc(prf.Inv(), p)
	if err := st.UpdateView(prf.Full_tree_head, prf.Search /*@, p/2 @*/); err != nil {
		//@ fold acc(prf.Inv(), p)
		return nil, err
	} else if len(prf.Search.Prefix_roots) > 0 {
		//@ fold acc(prf.Inv(), p)
		return nil, errors.New("too many prefix roots")
	}

	vrfOutputs := make([][32]byte, len(prf.Binary_ladder))

	//@ invariant 0 <= i && i <= len(prf.Binary_ladder)
	//@ invariant acc(prf.Binary_ladder, p)
	//@ invariant acc(vrfOutputs) && len(vrfOutputs) == len(prf.Binary_ladder)
	for i := 0; i < len(prf.Binary_ladder); i++ {
		step := prf.Binary_ladder[i]
		vrfOutputs[i] = crypto.VRF_proof_to_hash(step.Proof)
	}

	//@ fold acc(prf.Inv(), p)
	return nil, nil
}
