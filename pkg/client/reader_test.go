package client

import (
	"bytes"
	"strings"
	"testing"

	"github.com/felixlinker/keytrans-verification/pkg/proofs"
)

// testPrefixProof returns a PrefixProof for a prefix tree consisting of a
// single leaf; different values of `b` give different roots.
//
// @ trusted
func testPrefixProof(b byte) *proofs.PrefixProof {
	return &proofs.PrefixProof{
		Results: []*proofs.PrefixSearchResult{{
			ResultType: proofs.Inclusion,
			Leaf: &proofs.PrefixLeaf{
				Vrf_output: bytes.Repeat([]byte{b}, 32),
				Commitment: bytes.Repeat([]byte{b}, 32),
			},
			Depth: 0,
		}},
	}
}

// @ trusted
func expectErr(t *testing.T, r *ProofReader, substr string) {
	t.Helper()
	if r.Err() == nil {
		t.Fatalf("expected error containing %q, got none", substr)
	} else if !strings.Contains(r.Err().Error(), substr) {
		t.Fatalf("expected error containing %q, got %q", substr, r.Err())
	}
}

// @ trusted
func TestProofReaderTimestamps(t *testing.T) {
	t.Run("known timestamps are not consumed again", func(t *testing.T) {
		r := NewProofReader(&proofs.CombinedTreeProof{Timestamps: []uint64{70, 110}}, 13, nil)
		if ts := r.GetTimestamp(7); ts != 70 {
			t.Fatalf("GetTimestamp(7) = %d, want 70", ts)
		}
		if ts := r.GetTimestamp(7); ts != 70 || r.tsNext != 1 {
			t.Fatalf("second GetTimestamp(7) = %d with %d consumed, want 70 with 1", ts, r.tsNext)
		}
		if ts := r.GetTimestamp(11); ts != 110 {
			t.Fatalf("GetTimestamp(11) = %d, want 110", ts)
		}
	})

	t.Run("retained timestamps are not consumed", func(t *testing.T) {
		retained := []knownEntry{{pos: 3, ts: 30}}
		r := NewProofReader(&proofs.CombinedTreeProof{Timestamps: []uint64{70}}, 13, retained)
		if ts := r.GetTimestamp(3); ts != 30 || r.tsNext != 0 {
			t.Fatalf("GetTimestamp(3) = %d with %d consumed, want 30 with 0", ts, r.tsNext)
		}
	})

	t.Run("non-monotonic timestamps are rejected", func(t *testing.T) {
		retained := []knownEntry{{pos: 3, ts: 30}}
		r := NewProofReader(&proofs.CombinedTreeProof{Timestamps: []uint64{20}}, 13, retained)
		r.GetTimestamp(7)
		expectErr(t, r, "not monotonic")
	})

	t.Run("too few timestamps", func(t *testing.T) {
		r := NewProofReader(&proofs.CombinedTreeProof{}, 13, nil)
		r.GetTimestamp(7)
		expectErr(t, r, "too few timestamps")
	})

	t.Run("errors are sticky", func(t *testing.T) {
		r := NewProofReader(&proofs.CombinedTreeProof{Timestamps: []uint64{70}}, 13, nil)
		r.GetTimestamp(13) // outside of the tree
		if ts := r.GetTimestamp(7); ts != 0 || r.tsNext != 0 {
			t.Fatalf("GetTimestamp after error = %d with %d consumed, want 0 with 0", ts, r.tsNext)
		}
		expectErr(t, r, "outside of the tree")
	})
}

// @ trusted
func TestProofReaderPrefixProofs(t *testing.T) {
	t.Run("a prefix proof consumes the timestamp of its log entry", func(t *testing.T) {
		prf := &proofs.CombinedTreeProof{
			Timestamps:    []uint64{70},
			Prefix_proofs: []*proofs.PrefixProof{testPrefixProof(1)},
		}
		r := NewProofReader(prf, 13, nil)
		if tree := r.GetPrefixProof(7); tree == nil {
			t.Fatalf("GetPrefixProof(7): %v", r.Err())
		}
		if r.tsNext != 1 || r.prfNext != 1 {
			t.Fatalf("consumed %d timestamps and %d proofs, want 1 and 1", r.tsNext, r.prfNext)
		}
	})

	t.Run("proofs from the same log entry must agree", func(t *testing.T) {
		prf := &proofs.CombinedTreeProof{
			Timestamps:    []uint64{70},
			Prefix_proofs: []*proofs.PrefixProof{testPrefixProof(1), testPrefixProof(1), testPrefixProof(2)},
		}
		r := NewProofReader(prf, 13, nil)
		r.GetPrefixProof(7)
		r.GetPrefixProof(7)
		if r.Err() != nil {
			t.Fatalf("consistent proofs rejected: %v", r.Err())
		}
		r.GetPrefixProof(7)
		expectErr(t, r, "conflicting prefix tree roots")
	})

	t.Run("too few prefix proofs", func(t *testing.T) {
		r := NewProofReader(&proofs.CombinedTreeProof{Timestamps: []uint64{70}}, 13, nil)
		r.GetPrefixProof(7)
		expectErr(t, r, "too few prefix proofs")
	})
}

// @ trusted
func TestProofReaderFinish(t *testing.T) {
	root := func(b byte) []byte { return bytes.Repeat([]byte{b}, 32) }

	t.Run("prefix roots fill provided entries without a root, by position", func(t *testing.T) {
		prf := &proofs.CombinedTreeProof{
			// Requested in the order 11, 3, 7; entry 3 is retained.
			Timestamps:    []uint64{110, 70},
			Prefix_proofs: []*proofs.PrefixProof{testPrefixProof(1)},
			Prefix_roots:  [][]byte{root(7)},
		}
		r := NewProofReader(prf, 13, []knownEntry{{pos: 3, ts: 30}})
		r.GetTimestamp(11)
		r.GetTimestamp(3)
		r.GetPrefixProof(7) // consumes timestamp 70 for entry 7
		r.GetPrefixProof(11)
		expectErr(t, r, "too few prefix proofs")

		r = NewProofReader(prf, 13, []knownEntry{{pos: 3, ts: 30}})
		r.GetTimestamp(11)
		r.GetTimestamp(3)
		r.GetPrefixProof(11)
		r.GetTimestamp(7)
		entries := r.Finish()
		if r.Err() != nil {
			t.Fatalf("Finish(): %v", r.Err())
		}
		if len(entries) != 3 || entries[0].pos != 3 || entries[1].pos != 7 || entries[2].pos != 11 {
			t.Fatalf("Finish() entries = %+v, want positions 3, 7, 11", entries)
		}
		if entries[0].root != nil {
			t.Errorf("retained entry 3 was given a prefix root")
		}
		if !bytes.Equal(entries[1].root, root(7)) || entries[1].proved {
			t.Errorf("entry 7 = %+v, want root from prefix_roots", entries[1])
		}
		if !entries[2].proved {
			t.Errorf("entry 11 = %+v, want root from its prefix proof", entries[2])
		}
	})

	t.Run("leftover elements are rejected", func(t *testing.T) {
		cases := []struct {
			name   string
			prf    *proofs.CombinedTreeProof
			substr string
		}{
			{"timestamps", &proofs.CombinedTreeProof{Timestamps: []uint64{70}}, "additional timestamps"},
			{"prefix proofs", &proofs.CombinedTreeProof{Prefix_proofs: []*proofs.PrefixProof{testPrefixProof(1)}}, "additional prefix proofs"},
			{"prefix roots", &proofs.CombinedTreeProof{Prefix_roots: [][]byte{root(1)}}, "additional prefix roots"},
		}
		for _, tc := range cases {
			t.Run(tc.name, func(t *testing.T) {
				r := NewProofReader(tc.prf, 13, nil)
				r.Finish()
				expectErr(t, r, tc.substr)
			})
		}
	})

	t.Run("missing prefix roots are rejected", func(t *testing.T) {
		r := NewProofReader(&proofs.CombinedTreeProof{Timestamps: []uint64{70}}, 13, nil)
		r.GetTimestamp(7)
		r.Finish()
		expectErr(t, r, "too few prefix roots")
	})
}
