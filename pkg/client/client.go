package client

import (
	"errors"

	"github.com/felixlinker/keytrans-verification/pkg/proofs"
)

type TreeHead struct {
	Tree_size uint64
	Signature []byte
}

type FullTreeHead struct {
	Tree_head TreeHead
	// TODO: AuditorTreeHead auditor_tree_head
}

type SearchRequest struct {
	Last  *uint32
	Label []byte
	// TODO: optional<uint32> version
}

type SearchResponse struct {
	Full_tree_head FullTreeHead
	Version        *uint32 // version; only present for latest-key queries
	Binary_ladder  []proofs.BinaryLadderStep
	Search         proofs.CombinedTreeProof
	Inclusion      proofs.InclusionProof
	Opening        []byte             // TODO: For actual VRFs, this would be fixed size
	Value          proofs.UpdateValue // value associated with queried label
}

func (st *UserState) VerifyLatest(query SearchRequest, proof SearchResponse) (*proofs.UpdateValue, error) {
	if err := st.UpdateView(proof.Full_tree_head, proof.Search); err != nil {
		return nil, err
	} else if len(proof.Search.Timestamps) > 0 {
		return nil, errors.New("too many timestamps")
	} else if len(proof.Search.Prefix_roots) > 0 {
		return nil, errors.New("too many prefix roots")
	} else {
		return nil, nil
	}
}
