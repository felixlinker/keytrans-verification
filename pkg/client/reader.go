package client

import (
	"bytes"
	"errors"

	"github.com/felixlinker/keytrans-verification/pkg/proofs"
	"github.com/felixlinker/keytrans-verification/pkg/trees/prefix"
)

// ##(--hyperMode extended --enableExperimentalHyperFeatures)

// The fields of a CombinedTreeProof carry no indication of which log entry each
// timestamp or PrefixProof belongs to. Instead, elements are provided in the
// order in which the algorithm being executed requests them, and the user
// treats the `timestamps` and `prefix_proofs` fields as queues. See Section
// "Combined Tree" of draft-ietf-keytrans-protocol.
//
// ProofReader implements these queue semantics. Algorithms request data for a
// log entry by position; the reader returns already-known data for that
// position without consuming anything, and otherwise consumes the next element
// of the corresponding queue and associates it with the position.
//
// The first error is recorded and turns every subsequent call into a no-op, so
// algorithms need not check for errors after every call. Callers check Err().

// knownEntry is the data associated with one log entry.
type knownEntry struct {
	pos uint64
	ts  uint64
	// root is the prefix tree root value, or nil if not (yet) known.
	root []byte
	// provided is true if ts was consumed from the proof's `timestamps` field,
	// and false if it was retained from a previous query.
	provided bool
	// proved is true if root was computed from a consumed PrefixProof.
	proved bool
}

type ProofReader struct {
	n   uint64 // Size of the tree that the proof is for.
	prf *proofs.CombinedTreeProof

	tsNext  int // Index of the next unconsumed element of prf.Timestamps.
	prfNext int // Index of the next unconsumed element of prf.Prefix_proofs.

	known []knownEntry // Sorted by strictly increasing pos.
	err   error
}

/*@
pred (r *ProofReader) Inv() {
	acc(r) && acc(r.prf) && acc(r.prf.Timestamps) && acc(r.known) &&
	0 <= r.tsNext && r.tsNext <= len(r.prf.Timestamps) &&
	0 <= r.prfNext && r.prfNext <= len(r.prf.Prefix_proofs)
}
@*/

// NewProofReader returns a reader over `prf`, a proof for a tree of size `n`.
// `retained` holds the log entries retained from a previous query, sorted by
// position.
// @ trusted
func NewProofReader(prf *proofs.CombinedTreeProof, n uint64, retained []knownEntry) (r *ProofReader) {
	r = &ProofReader{n: n, prf: prf}
	if prf == nil {
		r.err = errors.New("no proof provided")
		return
	}
	for i := 0; i < len(retained) && r.err == nil; i++ {
		e := retained[i]
		if e.pos >= n {
			r.err = errors.New("retained log entry is outside of the tree")
		} else if 0 < i && retained[i-1].pos >= e.pos {
			r.err = errors.New("retained log entries are not sorted")
		} else if 0 < i && retained[i-1].ts >= e.ts {
			r.err = errors.New("retained timestamps are not monotonic")
		} else {
			e.provided = false
			e.proved = false
			r.known = append( /*@ perm(1/2), @*/ r.known, e)
		}
	}
	return
}

// Err returns the first error encountered by the reader, if any.
// @ trusted
func (r *ProofReader) Err() error {
	return r.err
}

// find returns the index of the first known entry whose position is greater
// than or equal to `x`, and whether that entry's position equals `x`.
// @ trusted
func (r *ProofReader) find(x uint64) (i int, found bool) {
	for i = 0; i < len(r.known); i++ {
		if r.known[i].pos >= x {
			return i, r.known[i].pos == x
		}
	}
	return i, false
}

// GetTimestamp returns the timestamp of log entry `x`, consuming the next
// element of `timestamps` if it is not already known.
//
// Timestamps must be strictly increasing by position, matching the
// utils.Monotonic predicate that UserState retains its timestamps under.
// @ trusted
func (r *ProofReader) GetTimestamp(x uint64) (ts uint64) {
	if r.err != nil {
		return 0
	}
	if x >= r.n {
		r.err = errors.New("requested log entry is outside of the tree")
		return 0
	}
	i, found := r.find(x)
	if found {
		return r.known[i].ts
	}
	if r.tsNext >= len(r.prf.Timestamps) {
		r.err = errors.New("too few timestamps")
		return 0
	}
	ts = r.prf.Timestamps[r.tsNext]
	r.tsNext++

	if 0 < i && r.known[i-1].ts >= ts {
		r.err = errors.New("timestamps are not monotonic")
		return 0
	} else if i < len(r.known) && ts >= r.known[i].ts {
		r.err = errors.New("timestamps are not monotonic")
		return 0
	}

	e := knownEntry{pos: x, ts: ts, provided: true}
	tail := append( /*@ perm(1/2), @*/ []knownEntry{e}, r.known[i:]...)
	r.known = append( /*@ perm(1/2), @*/ r.known[:i], tail...)
	return ts
}

// GetPrefixProof consumes the next element of `prefix_proofs`, which is a
// proof from the prefix tree of log entry `x`, and returns the prefix tree
// reconstructed from it. If the timestamp of `x` is not already known, it is
// consumed as well, since it is needed to compute the log entry's leaf value.
//
// All proofs from the same log entry must produce the same prefix tree root.
// The leaves of the proof must already be populated (see proofs.PullLeaves).
// @ trusted
func (r *ProofReader) GetPrefixProof(x uint64) (t *prefix.Tree) {
	if r.err != nil {
		return nil
	}
	if r.prfNext >= len(r.prf.Prefix_proofs) {
		r.err = errors.New("too few prefix proofs")
		return nil
	}
	prf := r.prf.Prefix_proofs[r.prfNext]
	r.prfNext++

	t, err := prefix.MkPrefix(prf /*@, perm(1/2) @*/)
	if err != nil {
		r.err = err
		return nil
	}
	root, err := t.Value( /*@ perm(1/2) @*/ )
	if err != nil {
		r.err = err
		return nil
	}

	r.GetTimestamp(x)
	if r.err != nil {
		return nil
	}
	i, _ := r.find(x)
	if r.known[i].root != nil && !bytes.Equal(r.known[i].root, root) {
		r.err = errors.New("conflicting prefix tree roots for the same log entry")
		return nil
	}
	r.known[i].root = root
	r.known[i].proved = true
	return t
}

// Finish verifies that the proof has been fully consumed and associates the
// elements of `prefix_roots` with the log entries whose timestamp was provided
// but whose prefix tree root is not yet known, in order of position. It
// returns all known log entries, sorted by position.
// @ trusted
func (r *ProofReader) Finish() (entries []knownEntry) {
	if r.err != nil {
		return nil
	}
	if r.tsNext != len(r.prf.Timestamps) {
		r.err = errors.New("unexpected additional timestamps")
		return nil
	} else if r.prfNext != len(r.prf.Prefix_proofs) {
		r.err = errors.New("unexpected additional prefix proofs")
		return nil
	}

	next := 0
	for i := 0; i < len(r.known); i++ {
		if r.known[i].provided && r.known[i].root == nil {
			if next >= len(r.prf.Prefix_roots) {
				r.err = errors.New("too few prefix roots")
				return nil
			}
			r.known[i].root = r.prf.Prefix_roots[next]
			next++
		}
	}
	if next != len(r.prf.Prefix_roots) {
		r.err = errors.New("unexpected additional prefix roots")
		return nil
	}
	return r.known
}
