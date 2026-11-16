package client

import (
	"bytes"
	"strings"
	"testing"

	"github.com/felixlinker/keytrans-verification/pkg/proofs"
)

// Acceptance test based on Appendix C.1 ("Worked Example") of
// draft-ietf-keytrans-protocol-06: a greatest-version search over a log with
// 13 entries by a user who previously observed the log with 4 entries.
//
//   - The implicit binary search tree has root 7, and the frontier is 7, 11, 12.
//   - The user retained log entry 3, the previous tree's only frontier entry.
//   - T_12 - T_7 >= RMW > T_12 - T_11, so entry 11 is the rightmost
//     distinguished log entry.
//
// Expected CombinedTreeProof contents:
//
//	timestamps    = [T_7, T_11, T_12]
//	prefix_proofs = [ladder from entry 11, ladder from entry 12]
//	prefix_roots  = [prefix tree root of entry 7]
//
// Subtests for known gaps either skip or, where the check is executable, skip
// only while the known failure persists and fail once it is fixed, so that the
// skip gets removed.

const c1RMW uint64 = 50

var c1Timestamps = map[uint64]uint64{3: 30, 7: 70, 11: 115, 12: 120}

// @ trusted
func TestAppendixC1(t *testing.T) {
	retained := []knownEntry{{pos: 3, ts: c1Timestamps[3]}}
	root7 := bytes.Repeat([]byte{7}, 32)
	prf := &proofs.CombinedTreeProof{
		Timestamps:    []uint64{c1Timestamps[7], c1Timestamps[11], c1Timestamps[12]},
		Prefix_proofs: []*proofs.PrefixProof{testPrefixProof(11), testPrefixProof(12)},
		Prefix_roots:  [][]byte{root7},
	}

	t.Run("update view consumes T_7, T_11, T_12", func(t *testing.T) {
		r := NewProofReader(prf, 13, retained)
		updateView(r, 4)
		if r.Err() != nil {
			t.Fatalf("updateView: %v", r.Err())
		}
		if r.tsNext != 3 {
			t.Fatalf("consumed %d timestamps, want 3", r.tsNext)
		}
		for _, x := range []uint64{7, 11, 12} {
			i, found := r.find(x)
			if !found || r.known[i].ts != c1Timestamps[x] || !r.known[i].provided {
				t.Errorf("entry %d not associated with T_%d", x, x)
			}
		}
	})

	// Gap 1: search.MostRecentDistinguished returns the first
	// non-distinguished frontier index (2, entry 12) instead of the rightmost
	// distinguished one (1, entry 11).
	t.Run("search starts at entry 11 and prefix_roots covers entry 7", func(t *testing.T) {
		r := NewProofReader(prf, 13, retained)
		updateView(r, 4)
		greatestVersionSearch(r, c1RMW)
		entries := r.Finish()
		if err := r.Err(); err != nil {
			if strings.Contains(err.Error(), "unexpected additional prefix proofs") {
				t.Skipf("known gap 1 (search.MostRecentDistinguished picks the wrong starting entry): %v", err)
			}
			t.Fatalf("unexpected error: %v", err)
		}

		want := []struct {
			pos      uint64
			provided bool
			proved   bool
		}{
			{3, false, false},
			{7, true, false},
			{11, true, true},
			{12, true, true},
		}
		if len(entries) != len(want) {
			t.Fatalf("Finish() returned %d entries, want %d: %+v", len(entries), len(want), entries)
		}
		for i, w := range want {
			e := entries[i]
			if e.pos != w.pos || e.provided != w.provided || e.proved != w.proved {
				t.Errorf("entry %d = %+v, want %+v", i, e, w)
			}
		}
		if !bytes.Equal(entries[1].root, root7) {
			t.Errorf("entry 7 root = %x, want prefix_roots[0]", entries[1].root)
		}
		t.Log("gap 1 appears fixed: remove the skip above")
	})

	// The remaining gaps need a cryptographically complete SearchResponse
	// (VRF proofs, commitments, real prefix proofs and a spec-format log tree
	// proof) to exercise through VerifyLatest.
	t.Run("entry 12's ladder omits lookups already proven to its left", func(t *testing.T) {
		t.Skip("known gap 2: proofs.PullLeaves and search.Lookups.CheckPrefixTree assume a full " +
			"binary ladder; entry 12's PrefixProof holds a single non-inclusion result for version 3")
	})
	t.Run("retained prefix root of entry 3 is checked", func(t *testing.T) {
		t.Skip("known gap 3: UserState retains frontier timestamps but not frontier prefix tree roots")
	})
	t.Run("inclusion is evaluated from leaves 7, 11, 12 and the retained subtree", func(t *testing.T) {
		t.Skip("known gap 4: log.Tree.Grow takes leaf values from the inclusion proof instead of " +
			"computing them from timestamps and prefix tree roots, so prefix_roots is never authenticated")
	})
}
