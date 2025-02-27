package client

import (
	"errors"

	"github.com/felixlinker/keytrans-verification/pkg/proofs"
)

// This file implements Section 4.2, "Updating Views of the Tree / Algorithm"

type UserState struct {
	Size                *uint64
	Full_subtrees       []proofs.NodeValue
	Frontier_timestamps []uint64
}

func checkIncreasing(timestamps []uint64) bool {
	if len(timestamps) == 0 {
		return true
	}

	tmp := timestamps[0]
	for _, v := range timestamps[1:] {
		if tmp > v {
			return false
		}
		tmp = v
	}
	return true
}

//@ ensures e == nil ==> *st.Size == new_head.Tree_head.Tree_size
func (st *UserState) UpdateView(new_head FullTreeHead, proof proofs.CombinedTreeProof) (err error) {
	if len(proof.Prefix_proofs) > 0 {
		return errors.New("invalid proof")
	} else if len(proof.Prefix_roots) > 0 {
		return errors.New("invalid proof")
	} else if !checkIncreasing(proof.Timestamps) {
		return errors.New("timestamps not increasing")
	}

	// NOTE: blocked on https://github.com/ietf-wg-keytrans/draft-protocol/issues/16

	*(st.Size) = new_head.Tree_head.Tree_size

	return nil
}
