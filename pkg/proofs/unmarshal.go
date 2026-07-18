package proofs

import (
	"bytes"
	"crypto/sha256"
	"errors"
	"fmt"

	"github.com/felixlinker/keytrans-verification/pkg/utils"
)

// @ ensures err == nil ==> acc(NodeValuesInv(r))
func UnmarshalNodeValues(buf *bytes.Buffer) (r []*NodeValue, err error) {
	if lengthUint16, e := utils.ReadUint16(buf); e != nil {
		err = e
	} else {
		// @ assume 0 <= lengthUint16
		length := int(lengthUint16)
		r = make([]*NodeValue, 0, length)
		// @ fold acc(NodeValuesInv(r))

		// @ invariant acc(NodeValuesInv(r))
		for i := 0; i < length && err == nil; i++ {
			var val /*@@@*/ NodeValue
			if n, e := buf.Read(val[:]); n != len(val) || e != nil {
				err = utils.BufferError(e)
			} else {
				// @ unfold acc(NodeValuesInv(r))
				// @ assert forall i int :: {r[i], val} 0 <= i && i < len(r) ==> &(*r[i])[0] != &val[0] && r[i] != &val
				r = append( /*@ perm(1/2), @*/ r, &val)
				// @ fold acc(NodeValuesInv(r))
			}
		}
	}
	return
}

// @ requires acc(s)
// @ ensures err == nil ==> acc(s.Inv())
func (s *BinaryLadderStep) Unmarshal(buf *bytes.Buffer, withCommitment bool) (err error) {
	prf := make([]byte, 64)
	if n, e := buf.Read(prf); n != len(prf) || e != nil {
		err = utils.BufferError(e)
	} else {
		s.Proof = prf
		// @ fold acc(utils.BytesMem(s.Proof))
		s.Commitment = nil
		if withCommitment {
			var commitment /*@@@*/ [sha256.Size]byte
			if n, e := buf.Read(commitment[:]); n != len(commitment) || e != nil {
				return utils.BufferError(e)
			}
			s.Commitment = &commitment
			// @ assert acc(s.Commitment)
		}
		// @ fold acc(s.Inv())
	}
	return
}

// Unmarshal up to 2^8-1 binary ladder steps. Assumes that array length of steps
// is encoded as byte.
// @ ensures err == nil ==> BinaryLadderStepsInv(r)
func UnmarshalBinaryLadderSteps(buf *bytes.Buffer, version uint64) (r []*BinaryLadderStep, err error) {
	// @ assume 0 <= version
	ladder /*@, tmp @*/ := FullBinaryLadderSteps(version /*@, 0 @*/)
	r = make([]*BinaryLadderStep, 0, len(ladder))
	// @ fold BinaryLadderStepsInv(r)

	if steps, e := buf.ReadByte(); int(steps) != len(ladder) || e != nil {
		if e != nil {
			err = e
		} else {
			// @ assert int(steps) != len(ladder)
			msg := fmt.Sprintf("wrong number of binary ladder steps provided (version %d): got %d want %d", version, steps, len(ladder))
			err = errors.New(msg)
		}
	} else {
		// @ invariant 0 <= i && i <= len(ladder)
		// @ invariant BinaryLadderInv(ladder)
		// @ invariant BinaryLadderStepsInv(r)
		for i := 0; i < len(ladder) && err == nil; i++ {
			step /*@@@*/ := BinaryLadderStep{}
			// @ unfold BinaryLadderInv(ladder)
			if e := step.Unmarshal(buf, ladder[i] <= version); e != nil {
				err = e
			} else {
				// @ assert acc(step.Inv())
				// @ unfold BinaryLadderStepsInv(r)
				// // @ assert forall i int :: {r[i].Inv(), (&step).Inv()} 0 <= i && i < len(r) ==> unfolding acc(r[i].Inv()) in unfolding acc((&step).Inv()) in r[i] != &step
				r = append( /*@ perm(1/2), @*/ r, &step)
				// TODO:
				// @ inhale BinaryLadderStepsInv(r)
				// // @ fold BinaryLadderStepsInv(r)
			}
			// @ fold BinaryLadderInv(ladder)
		}
	}
	return
}

// @ requires acc(prf)
// @ ensures err == nil ==> acc(prf.Inv())
func (prf *InclusionProof) Unmarshal(buf *bytes.Buffer) (err error) {
	if values, e := UnmarshalNodeValues(buf); e != nil {
		err = e
	} else {
		prf.Elements = values
		// @ fold acc(prf.Inv())
	}
	return
}

// @ requires acc(l)
// @ ensures err == nil ==> acc(l.Inv())
func (l *PrefixLeaf) Unmarshal(buf *bytes.Buffer) (err error) {
	// length of output is same for all cipher suites
	output /*@@@*/ := make([]byte, sha256.Size)
	var commitment /*@@@*/ [sha256.Size]byte
	if n, e := buf.Read(output); n != len(output) || e != nil {
		return utils.BufferError(e)
	} else if n, e := buf.Read(commitment[:]); n != len(commitment) || e != nil {
		return utils.BufferError(e)
	} else {
		l.Vrf_output = output
		l.Commitment = &commitment
		// @ fold acc(l.Inv())
	}
	return
}

// @ requires acc(p)
// @ ensures err == nil ==> acc(p.Inv())
func (p *PrefixSearchResult) Unmarshal(buf *bytes.Buffer) (err error) {
	if resultType, e := buf.ReadByte(); e != nil {
		err = e
	} else {
		p.ResultType = PrefixSearchResultType(resultType)
		p.Leaf = nil
		if p.ResultType == NonInclusionLeaf {
			leaf /*@@@*/ := PrefixLeaf{}
			if e := leaf.Unmarshal(buf); e != nil {
				err = e
			} else {
				p.Leaf = &leaf
			}
		}

		if err == nil {
			if depth, e := buf.ReadByte(); e != nil {
				err = e
			} else {
				p.Depth = depth
			}
		}
		// @ fold acc(p.Inv())
	}
	return
}

// @ ensures err == nil ==> acc(PrefixSearchResultsInv(r))
func UnmarshalPrefixSearchResults(buf *bytes.Buffer) (r []*PrefixSearchResult, err error) {
	if lengthByte, e := buf.ReadByte(); e != nil {
		err = e
	} else {
		length := int(uint8(lengthByte))
		// @ assume 0 <= length
		r = make([]*PrefixSearchResult, 0, length)
		// @ fold acc(PrefixSearchResultsInv(r))

		// @ invariant acc(PrefixSearchResultsInv(r))
		for i := 0; i < length && err == nil; i++ {
			result /*@@@*/ := PrefixSearchResult{}
			if e := result.Unmarshal(buf); e != nil {
				err = e
			} else {
				// @ unfold acc(PrefixSearchResultsInv(r))
				r = append( /*@ perm(1/2), @*/ r, &result)
				// TODO:
				// @ inhale acc(PrefixSearchResultsInv(r))
			}
		}
	}
	return
}

// @ requires acc(p)
// @ ensures err == nil ==> acc(p.Inv())
func (p *PrefixProof) Unmarshal(buf *bytes.Buffer) (err error) {
	if results, e := UnmarshalPrefixSearchResults(buf); e != nil {
		err = e
	} else if values, e := UnmarshalNodeValues(buf); e != nil {
		err = e
	} else {
		p.Results = results
		p.Elements = values
		// @ fold acc(p.Inv())
	}
	return
}

// @ ensures err == nil ==> acc(PrefixProofsInv(r))
func UnmarshalPrefixProofs(buf *bytes.Buffer) (r []*PrefixProof, err error) {
	if lengthByte, e := buf.ReadByte(); e != nil {
		err = e
	} else {
		length := int(uint8(lengthByte))
		// @ assume 0 <= length
		r = make([]*PrefixProof, 0, length)
		// @ fold acc(PrefixProofsInv(r))

		// @ invariant acc(PrefixProofsInv(r))
		for i := 0; i < length && err == nil; i++ {
			prf /*@@@*/ := PrefixProof{}
			if e := prf.Unmarshal(buf); e != nil {
				err = e
			} else {
				// @ unfold acc(PrefixProofsInv(r))
				r = append( /*@ perm(1/2), @*/ r, &prf)
				// TODO:
				// @ inhale acc(PrefixProofsInv(r))
			}
		}
	}
	return
}

// @ requires acc(c)
// @ ensures err == nil ==> acc(c.Inv())
func (c *CombinedTreeProof) Unmarshal(buf *bytes.Buffer) (err error) {
	incPrf /*@@@*/ := InclusionProof{}
	if timestamps, e := utils.ReadUint64s(buf); e != nil {
		err = e
	} else if prefixProofs, e := UnmarshalPrefixProofs(buf); e != nil {
		err = e
	} else if prefixRoots, e := UnmarshalNodeValues(buf); e != nil {
		err = e
	} else if e := incPrf.Unmarshal(buf); e != nil {
		err = e
	} else {
		c.Timestamps = timestamps
		c.Prefix_proofs = prefixProofs
		c.Prefix_roots = prefixRoots
		c.Inclusion = &incPrf
		// @ fold acc(c.Inv())
	}
	return
}
