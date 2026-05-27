package trees

import (
	"bytes"
	"crypto/sha256"
	"errors"

	"github.com/felixlinker/keytrans-verification/pkg/crypto"
	"github.com/felixlinker/keytrans-verification/pkg/proofs"
	"github.com/felixlinker/keytrans-verification/pkg/utils"
)

type Lookups struct {
	label       []byte
	version     uint64
	vrfOutputs  map[uint64][]byte
	commitments map[uint64][]byte
}

/*@
pred SliceMapInv(m map[uint64][]byte) {
	acc(m) && (forall k uint64 :: k elem m ==> acc(m[k]))
}

pred (ls *Lookups) Inv() {
	acc(ls) && acc(ls.label) && acc(SliceMapInv(ls.vrfOutputs)) && acc(SliceMapInv(ls.commitments))
}
@*/

// Auxiliary map functions to speed up verification

// @ requires acc(v)
// @ preserves acc(SliceMapInv(m))
func mapSet(k uint64, v []byte, m map[uint64][]byte) {
	// @ unfold acc(SliceMapInv(m))
	m[k] = v
	// @ fold acc(SliceMapInv(m))
}

// @ requires noPerm < p
// @ preserves acc(SliceMapInv(m), p)
// @ ensures ok ==> acc(r)
func mapGet(m map[uint64][]byte, k uint64 /*@, ghost p perm @*/) (r []byte, ok bool) {
	var tmp []byte
	// @ unfold acc(SliceMapInv(m), p)
	if tmp, ok = m[k]; ok {
		copy(r, tmp /*@, p @*/)
	}
	// @ fold acc(SliceMapInv(m), p)
	return
}

// @ requires noPerm < p
// @ requires 0 <= version
// @ preserves acc(label, p) && acc(pk, p) && acc(proofs.BinaryLadderStepsInv(fullLadder), p)
// @ ensures err == nil ==> acc(ls.Inv())
func MkLookups(label []byte, version uint64, pk []byte, fullLadder []*proofs.BinaryLadderStep /*@, ghost p perm @*/) (ls *Lookups, err error) {
	ls = nil
	err = nil
	steps /*@, idx @*/ := proofs.FullBinaryLadderSteps(version /*@, version @*/)
	if len(steps) != len(fullLadder) {
		err = errors.New("wrong number of binary ladder steps")
	} else {
		vrfOutputs := make(map[uint64][]byte, len(steps))
		commitments := make(map[uint64][]byte, len(steps)/2)
		// @ fold acc(SliceMapInv(vrfOutputs))
		// @ fold acc(SliceMapInv(commitments))
		// @ unfold acc(proofs.BinaryLadderInv(steps))

		// @ invariant 0 <= i && i <= len(fullLadder)
		// @ invariant acc(label, p) && acc(pk, p) && acc(steps) && acc(SliceMapInv(vrfOutputs)) && acc(SliceMapInv(commitments))
		// @ invariant len(steps) == len(fullLadder)
		// @ invariant acc(proofs.BinaryLadderStepsInv(fullLadder), p)
		for i := 0; i < len(fullLadder) && err == nil; i++ {
			// @ unfold acc(proofs.BinaryLadderStepsInv(fullLadder), p)
			// @ unfold acc(fullLadder[i].Inv(), p)
			ladderVersion := steps[i]
			leafData := fullLadder[i]

			if searchKey, ok := crypto.VRF_verify(pk, label, ladderVersion, leafData.Proof /*@, p @*/); !ok {
				err = errors.New("VRF verification failed")
			} else {
				var k []byte
				copy(k, searchKey /*@, perm(1/2) @*/)
				mapSet(ladderVersion, k, vrfOutputs)

				if ladderVersion <= version {
					if leafData.Commitment == nil {
						err = errors.New("missing commitment")
					} else {
						var c []byte
						copy(c, utils.FromDigest(*leafData.Commitment) /*@, perm(1/2) @*/)
						mapSet(ladderVersion, c, commitments)
					}
				}
			}
			// @ fold acc(fullLadder[i].Inv(), p)
			// @ fold acc(proofs.BinaryLadderStepsInv(fullLadder), p)
		}

		ls = &Lookups{
			version:     version,
			vrfOutputs:  vrfOutputs,
			commitments: commitments,
		}
		copy(ls.label, label /*@, p/2 @*/)
		// @ fold acc(ls.Inv())
	}
	return
}

// Check that the prefix tree has a greatest version for the respective label
// that is consistent with the claimed greatest version. This is the case
// whenever err == nil. Furthermore, if r != nil, the greatest version of the
// key is committed to by the respectively returned value.
// @ requires noPerm < p
// @ preserves acc(ls.Inv(), p)
// @ requires acc(t.Inv(), p)
// @ ensures noPerm < tp && tp <= p && acc(t.Inv(), tp)
// @ ensures r != nil && err != nil ==> acc(r, tp)
func (ls *Lookups) CheckPrefixTree(t *Prefix /*@, ghost p perm @*/) (r *[sha256.Size]byte, err error /*@, ghost tp perm @*/) {
	// @ unfold acc(ls.Inv(), p)
	// @ assume 0 <= ls.version
	steps /*@, idx @*/ := proofs.FullBinaryLadderSteps(ls.version /*@, ls.version @*/)
	// @ fold acc(ls.Inv(), p)
	// @ unfold acc(proofs.BinaryLadderInv(steps))

	done := false
	// @ ghost tp = p
	// @ invariant 0 <= i && i <= len(steps)
	// @ invariant acc(steps) && acc(ls.Inv(), p) && noPerm < tp && tp <= p && acc(t.Inv(), tp)
	// @ invariant r != nil ==> acc(r, tp)
	for i := 0; i < len(steps) && err == nil && !done; i++ {
		lookup := steps[i]
		// @ unfold acc(ls.Inv(), p)
		if searchKey, ok := mapGet(ls.vrfOutputs, lookup /*@, p @*/); !ok {
			err = errors.New("vrfOutputs incomplete")
		} else {
			if c, ok := t.Search(searchKey /*@, tp @*/); !ok {
				err = errors.New("failed expected prefix tree lookup")
			} else {
				if lookup <= ls.version {
					if c == nil {
						r = nil
						done = true
						// r == nil && err == nil means that the prefix tree has a greatest
						// version smaller than the expected one, which can be consistent with
						// a greatest version lookup.
					} else if cExpected, ok := mapGet(ls.commitments, lookup /*@, p @*/); !ok {
						err = errors.New("commitments incomplete")
					} else if !bytes.Equal(cExpected, utils.FromDigest(*c) /*@, p, p @*/) {
						err = errors.New("failed expected prefix tree lookup")
					} else if lookup == ls.version {
						r = c
					}
				} else if c != nil {
					err = errors.New("inclusion but expected non-inclusion")
				}
			}
		}
		// @ tp = tp/2
		// @ fold acc(ls.Inv(), p)
	}
	return
}
