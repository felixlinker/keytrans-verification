package search

// TODO: Move this module to proofs

import (
	"bytes"
	"errors"

	"github.com/felixlinker/keytrans-verification/pkg/crypto"
	"github.com/felixlinker/keytrans-verification/pkg/proofs"
	"github.com/felixlinker/keytrans-verification/pkg/trees/misc"
	"github.com/felixlinker/keytrans-verification/pkg/trees/prefix"
	"github.com/felixlinker/keytrans-verification/pkg/utils"
)

// ##(--hyperMode extended)

type Lookups struct {
	label       []byte
	version     uint64
	vrfOutputs  map[uint64][]byte
	commitments map[uint64][]byte
}

/*@
pred (ls *Lookups) Inv() {
	acc(ls) && acc(utils.BytesMem(ls.label)) && acc(misc.SliceMapInv(ls.vrfOutputs)) && acc(misc.SliceMapInv(ls.commitments))
}
@*/

// @ requires noPerm < p
// @ requires 0 <= version
// @ preserves acc(utils.BytesMem(label), p) && acc(utils.BytesMem(pk), p) && acc(proofs.BinaryLadderStepsInv(fullLadder), p)
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
		// @ fold acc(misc.SliceMapInv(vrfOutputs))
		// @ fold acc(misc.SliceMapInv(commitments))
		// @ unfold acc(proofs.BinaryLadderInv(steps))

		// @ invariant 0 <= i && i <= len(fullLadder)
		// @ invariant acc(utils.BytesMem(label), p) && acc(utils.BytesMem(pk), p) && acc(steps) && acc(misc.SliceMapInv(vrfOutputs)) && acc(misc.SliceMapInv(commitments))
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
				misc.MapSet(ladderVersion, utils.Copy(searchKey /*@, perm(1/2) @*/), vrfOutputs)

				if ladderVersion <= version {
					if leafData.Commitment == nil {
						err = errors.New("missing commitment")
					} else {
						c := utils.Copy(leafData.Commitment /*@, p @*/)
						misc.MapSet(ladderVersion, c, commitments)
					}
				}
			}
			// @ fold acc(fullLadder[i].Inv(), p)
			// @ fold acc(proofs.BinaryLadderStepsInv(fullLadder), p)
		}

		ls = &Lookups{
			label:       utils.Copy(label /*@, p/2 @*/),
			version:     version,
			vrfOutputs:  vrfOutputs,
			commitments: commitments,
		}
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
// @ preserves acc(t.Inv(), p)
// @ ensures r != nil && err != nil ==> utils.BytesMem(r)
func (ls *Lookups) CheckPrefixTree(t *prefix.Tree /*@, ghost p perm @*/) (r []byte, err error) {
	// @ unfold acc(ls.Inv(), p)
	// @ assume 0 <= ls.version
	steps /*@, idx @*/ := proofs.FullBinaryLadderSteps(ls.version /*@, ls.version @*/)
	// @ fold acc(ls.Inv(), p)
	// @ unfold acc(proofs.BinaryLadderInv(steps))

	done := false
	// @ invariant 0 <= i && i <= len(steps)
	// @ invariant acc(steps) && acc(ls.Inv(), p) && acc(t.Inv(), p)
	// @ invariant r != nil ==> utils.BytesMem(r)
	for i := 0; i < len(steps) && err == nil && !done; i++ {
		lookup := steps[i]
		// @ unfold acc(ls.Inv(), p)
		if searchKey, ok := misc.MapGet(ls.vrfOutputs, lookup /*@, p @*/); !ok {
			err = errors.New("vrfOutputs incomplete")
		} else {
			if c, ok := t.Search(searchKey /*@, p @*/); !ok {
				err = errors.New("failed expected prefix tree lookup")
			} else {
				if lookup <= ls.version {
					if c == nil {
						r = nil
						done = true
						// r == nil && err == nil means that the prefix tree has a greatest
						// version smaller than the expected one, which can be consistent with
						// a greatest version lookup.
					} else if cExpected, ok := misc.MapGet(ls.commitments, lookup /*@, p @*/); !ok {
						err = errors.New("commitments incomplete")
					} else {
						// @ unfold acc(utils.BytesMem(cExpected), p)
						// @ unfold acc(utils.BytesMem(c), perm(1/2))
						equal := bytes.Equal(cExpected, c /*@, p, perm(1/2) @*/)
						// @ fold acc(utils.BytesMem(c), perm(1/2))
						// @ fold acc(utils.BytesMem(cExpected), p)
						if !equal {
							err = errors.New("failed expected prefix tree lookup")
						} else if lookup == ls.version {
							r = c
						}
					}
				} else if c != nil {
					err = errors.New("inclusion but expected non-inclusion")
				}
			}
		}
		// @ fold acc(ls.Inv(), p)
	}
	return
}
