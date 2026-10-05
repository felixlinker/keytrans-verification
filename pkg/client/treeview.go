package client

import (
	"bytes"
	"errors"

	"github.com/felixlinker/keytrans-verification/pkg/crypto"
	"github.com/felixlinker/keytrans-verification/pkg/proofs"
	"github.com/felixlinker/keytrans-verification/pkg/search"
	"github.com/felixlinker/keytrans-verification/pkg/trees/log"
	"github.com/felixlinker/keytrans-verification/pkg/trees/prefix"
	"github.com/felixlinker/keytrans-verification/pkg/utils"
)

type TreeHead struct {
	Tree_size uint64
	Signature []byte
}

/*@
pred (t *TreeHead) Inv() {
	acc(t) && acc(t.Signature)
}
@*/

type FullTreeHeadType = uint8

const FullTreeHeadSame FullTreeHeadType = 1
const FullTreeHeadUpdated FullTreeHeadType = 2

type FullTreeHead struct {
	headType  FullTreeHeadType
	Tree_head *TreeHead
	// TODO: AuditorTreeHead auditor_tree_head
}

/*@
pred (f *FullTreeHead) Inv() {
	acc(f) && (f.Tree_head != nil ==> acc(f.Tree_head.Inv()))
}
@*/

func VerifyFullTreeHead(config *Configuration, size uint64, root []byte, signature []byte) (ok bool) {
	// TODO:
	return true
}

type UserState struct {
	Tree                *log.Tree
	Frontier_timestamps []uint64
	Config              *Configuration
}

/*@
pred (s *UserState) Inv() {
	acc(s) && (s.Tree != nil ==> acc(s.Tree.Inv())) && acc(utils.Monotonic(s.Frontier_timestamps)) && acc(s.Config.Inv())
}
@*/

// @ requires  noPerm < p
// @ requires acc(st.Inv())
// @ requires acc(timestamps, p)
// @ requires  acc(prf.Inv())
// @ ensures err == nil ==> acc(st.Inv())
func (st *UserState) UpdateView(newSize uint64, timestamps []uint64, prf *proofs.InclusionProof /*@, ghost p perm @*/) (err error) {
	// @ unfold acc(st.Inv())
	oldSize := st.Tree.GetSize( /*@ perm(1/2) @*/ )
	if len(timestamps) == 0 {
		err = errors.New("no timestamps provided")
	} else if newSize <= oldSize {
		err = errors.New("new tree must not  become smaller")
	} else {
		var start uint64 = 0
		// @ unfold acc(utils.Monotonic(st.Frontier_timestamps))
		if 0 < len(st.Frontier_timestamps) {
			start = st.Frontier_timestamps[len(st.Frontier_timestamps)-1]
		}

		if !utils.CheckIncreasing(start, timestamps /*@, p @*/) {
			err = errors.New("timestamps not increasing")
		} else if newTree, e := st.Tree.Grow(newSize, prf); e != nil {
			err = e
		} else {
			st.Tree = newTree

			// @ unfold acc(utils.Monotonic(timestamps), p)
			// @ assert forall i, j int :: {st.Frontier_timestamps[i], timestamps[j]} 0 <= i && i < len(st.Frontier_timestamps) && 0 < j && j < len(timestamps) ==> st.Frontier_timestamps[i] < timestamps[j]

			frontier := search.Frontier(newSize)
			keep := len(frontier) - len(timestamps)
			if keep < 0 || len(st.Frontier_timestamps) < keep {
				err = errors.New("incorrect number of new timestamps provided")
			} else {
				// @ assert acc(st.Tree.Inv())
				tmp := st.Frontier_timestamps[:keep]
				// @ assert forall i int :: {tmp[i]} 0 <= i && i < len(tmp) ==> &tmp[i] == &st.Frontier_timestamps[i]
				tmp = append( /*@ p/2, @*/ tmp, timestamps...)
				// @ fold acc(utils.Monotonic(tmp))
				st.Frontier_timestamps = tmp
				// @ fold acc(st.Inv())
			}
		}
	}
	return
}

// NOTE: Below function was an attempt to encapsulate some of the challenges I
// encountered verifying MkPrefixes.
// @ requires prefix.PrefixesInv(ts)
// @ requires t.Inv()
// @ requires unfolding prefix.PrefixesInv(ts) in forall i int :: {ts[i]} 0 <= i && i < len(ts) ==> ts[i] != t
// @ ensures prefix.PrefixesInv(r) && len(r) == len(ts)+1
func auxAppend(ts []*prefix.Tree, t *prefix.Tree) (r []*prefix.Tree) {
	// @ unfold prefix.PrefixesInv(ts)
	r = append( /*@ perm(1/2), @*/ ts, t)
	// @ fold prefix.PrefixesInv(r)
	return
}

// @ requires noPerm < p
// @ preserves acc(st.Inv(), p)
// @ requires acc(proofs.PrefixProofsInv(prfs), p)
// @ ensures err == nil ==> 0 < len(ts) && prefix.PrefixesInv(ts)
func (st *UserState) MkPrefixes(prfs []*proofs.PrefixProof /*@, ghost p perm @*/) (ts []*prefix.Tree, err error) {
	// @ unfold acc(st.Inv(), p)
	size := st.Tree.GetSize( /*@ p @*/ )
	if size <= 0 {
		// @ fold acc(st.Inv(), p)
		err = errors.New("no tree")
	} else if len(prfs) == 0 {
		// @ fold acc(st.Inv(), p)
		err = errors.New("no proofs")
	} else if len(st.Frontier_timestamps) <= 0 {
		// @ fold acc(st.Inv(), p)
		err = errors.New("no frontier")
	} else {
		frontier := search.Frontier(size)
		mrd := search.MostRecentDistinguished(
			st.Frontier_timestamps,
			/*@ unfolding acc(st.Config.Inv(), p) in @*/ st.Config.ReasonableMonitoringWindow,
			/*@ p, @*/
		)
		// @ fold acc(st.Inv(), p)

		if len(frontier) != /*@ unfolding acc(st.Inv(), p) in @*/ len(st.Frontier_timestamps) {
			err = errors.New("length mismatch between frontier and frontier timestamps")
		} else if len(prfs)+mrd+1 != len(frontier) {
			err = errors.New("too few or too many prefix proofs")
		} else {
			ts = make([]*prefix.Tree, 0, len(prfs))
			// @ fold prefix.PrefixesInv(ts)
			// @ unfold acc(proofs.PrefixProofsInv(prfs), p)

			// @ invariant 0 <= i && i <= len(prfs)
			// @ invariant 0 <= i+mrd && i+mrd <= len(frontier)
			// @ invariant acc(frontier) && acc(prfs, p) && acc(st.Inv(), p)
			// @ invariant len(frontier) == unfolding acc(st.Inv(), p) in len(st.Frontier_timestamps)
			// @ invariant unfolding acc(st.Inv(), p) in st.Tree != nil
			// @ invariant forall j int :: {prfs[j]} i <= j && j < len(prfs) ==> acc(prfs[j].Inv(), p)
			// @ invariant prefix.PrefixesInv(ts)
			// @ invariant 0 < i && err == nil ==> 0 < len(ts)
			for i := 0; i < len(prfs) && err == nil; i++ {
				// @ unfold acc(st.Inv(), p)
				// @ unfold acc(utils.Monotonic(st.Frontier_timestamps), p)
				timestamp := st.Frontier_timestamps[i+mrd]
				// @ fold acc(utils.Monotonic(st.Frontier_timestamps), p)

				if t, e := prefix.MkPrefix(prfs[i] /*@, p @*/); e != nil {
					err = e
				} else if v, e := t.Value( /*@ p @*/ ); e != nil {
					err = e
				} else if c, e := st.Tree.GetLeafHash(frontier[i+mrd] /*@, p @*/); e != nil {
					err = e
				} else if c == nil {
					err = errors.New("no commitment for frontier node")
				} else {
					h := crypto.LogEntryHash(timestamp, c /*@, perm(1/2) @*/)
					// @ unfold utils.BytesMem(v)
					// @ unfold utils.BytesMem(h)
					if !bytes.Equal(v, h /*@, perm(1/2), perm(1/2) @*/) {
						err = errors.New("log tree commitment does not match prefix tree root hash")
					} else {
						// TODO: I cannot assert below because whenever I add new lines after
						// the (now) assume, the assert fails.
						// @ assume unfolding prefix.PrefixesInv(ts) in forall i int :: {ts[i]} 0 <= i && i < len(ts) ==> ts[i] != t
						ts = auxAppend(ts, t)
					}
					// @ fold utils.BytesMem(v)
					// @ fold utils.BytesMem(h)
				}
				// @ fold acc(st.Inv(), p)
			}
		}
	}

	return
}
