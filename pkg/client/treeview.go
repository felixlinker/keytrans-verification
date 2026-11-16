package client

import (
	"bytes"
	"errors"

	"github.com/felixlinker/keytrans-verification/pkg/crypto"
	"github.com/felixlinker/keytrans-verification/pkg/proofs"
	"github.com/felixlinker/keytrans-verification/pkg/search"
	"github.com/felixlinker/keytrans-verification/pkg/trees/log"
	"github.com/felixlinker/keytrans-verification/pkg/trees/prefix"
	//@ "github.com/felixlinker/keytrans-verification/pkg/utils"
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

ghost
requires acc(s.Inv(), _)
ensures  0 <= r
decreases
pure func (s *UserState) NumTimestamps() (r int) {
	return unfolding acc(s.Inv(), _) in len(s.Frontier_timestamps)
}

ghost
requires acc(s.Inv(), _)
decreases
pure func (s *UserState) HasTree() bool {
	return unfolding acc(s.Inv(), _) in s.Tree != nil
}
@*/

// retained returns the log entries that the user retained from their previous
// view of the tree: the log entries along its frontier, with their timestamps.
// @ trusted
func (st *UserState) retained() (entries []knownEntry, err error) {
	size := st.Tree.GetSize( /*@ perm(1/2) @*/ )
	if size == 0 {
		return nil, nil
	}
	frontier := search.Frontier(size)
	if len(frontier) != len(st.Frontier_timestamps) {
		return nil, errors.New("length mismatch between frontier and frontier timestamps")
	}
	for i := 0; i < len(frontier); i++ {
		entries = append( /*@ perm(1/2), @*/ entries, knownEntry{pos: frontier[i], ts: st.Frontier_timestamps[i]})
	}
	return
}

// UpdateView consumes, through `r`, the timestamps needed to update the user's
// view of the tree from its current size to `newSize`, and grows the log tree
// with the consistency proof `prf`. It returns the grown log tree.
//
// NOTE: log.Tree.Grow modifies st.Tree in place, so st.Tree must not be relied
// upon if this function or any later verification step fails.
// @ trusted
func (st *UserState) UpdateView(r *ProofReader, newSize uint64, prf *proofs.InclusionProof) (newTree *log.Tree, err error) {
	oldSize := st.Tree.GetSize( /*@ perm(1/2) @*/ )
	if newSize == 0 {
		return nil, errors.New("tree must not be empty")
	} else if newSize < oldSize {
		return nil, errors.New("new tree must not become smaller")
	} else if prf == nil {
		return nil, errors.New("no inclusion proof provided")
	}

	updateView(r, oldSize)
	if err = r.Err(); err != nil {
		return nil, err
	}
	return st.Tree.Grow(newSize, prf)
}

// checkLeaves verifies that the log tree's leaf for each log entry whose
// prefix tree root was computed from a prefix proof matches that entry.
//
// The log tree stores hashes in its leaves, which correspond to the hash of a
// log entry. A log entry consists of a timestamp and a prefix tree root hash.
// Thus, a log entry commits to the prefix tree's root hash under the entry's
// timestamp. Hence, we recompute the log entry's hash and compare it against
// what the log stores.
// @ trusted
func checkLeaves(tree *log.Tree, entries []knownEntry) (err error) {
	for i := 0; i < len(entries) && err == nil; i++ {
		if !entries[i].proved {
			continue
		}
		c, e := tree.GetLeafHash(entries[i].pos /*@, perm(1/2) @*/)
		if e != nil {
			err = e
		} else if c == nil {
			err = errors.New("no commitment for log entry")
		} else {
			h := crypto.LogEntryHash(entries[i].ts, entries[i].root /*@, perm(1/2) @*/)
			if !bytes.Equal(c, h /*@, perm(1/2), perm(1/2) @*/) {
				err = errors.New("log tree commitment does not match prefix tree root hash")
			}
		}
	}
	return
}

// frontierTimestamps returns the timestamps of the log entries along the
// frontier of the tree that `r` is for, all of which must be known.
// @ trusted
func frontierTimestamps(r *ProofReader) (ts []uint64) {
	frontier := search.Frontier(r.n)
	ts = make([]uint64, len(frontier))
	for i := 0; i < len(frontier); i++ {
		ts[i] = r.GetTimestamp(frontier[i])
	}
	return
}

// NOTE: Below function was an attempt to encapsulate some of the challenges I
// encountered verifying MkPrefixes.
// @ requires prefix.PrefixesInv(ts)
// @ requires t.Inv()
// @ ensures prefix.PrefixesInv(r) && len(r) == len(ts)+1
func auxAppend(ts []*prefix.Tree, t *prefix.Tree) (r []*prefix.Tree) {
	// @ unfold prefix.PrefixesInv(ts)
	/*@
	assert forall i int :: {ts[i]} 0 <= i && i < len(ts) ==> ts[i] != t by contra {
		// existential elimination (requires Gobra `7fa4f86` or newer):
		var j int :| 0 <= j && j < len(ts) && ts[j] == t
		unfold ts[j].Inv()
		unfold t.Inv()
	}
	@*/
	r = append( /*@ perm(1/2), @*/ ts, t)
	// @ fold prefix.PrefixesInv(r)
	return
}
