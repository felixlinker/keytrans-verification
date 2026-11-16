package client

import (
	"bytes"
	"testing"

	"github.com/felixlinker/keytrans-verification/pkg/proofs"
	"github.com/felixlinker/keytrans-verification/pkg/trees/log"
)

// @ trusted
func testLeaves(n int) []proofs.NodeValue {
	out := make([]proofs.NodeValue, n)
	for i := range out {
		out[i] = bytes.Repeat([]byte{byte(i + 1)}, 32)
	}
	return out
}

// @ trusted
func prunedProof(t *testing.T, size uint64, cacheSize uint64) *proofs.InclusionProof {
	t.Helper()

	tree := log.FullTree(testLeaves(int(size)))
	tree.Prune(cacheSize)
	prf, err := tree.ProofFromPruned(cacheSize)
	if err != nil {
		t.Fatalf("ProofFromPruned(size=%d, cacheSize=%d): %v", size, cacheSize, err)
	}
	return prf
}

// updateViewTo runs UpdateView from st's current view to `size`, providing
// exactly `timestamps`, and fails unless all of them are consumed.
//
// @ trusted
func updateViewTo(t *testing.T, st *UserState, size uint64, timestamps []uint64, prf *proofs.InclusionProof) *log.Tree {
	t.Helper()

	retained, err := st.retained()
	if err != nil {
		t.Fatalf("retained(): %v", err)
	}
	r := NewProofReader(&proofs.CombinedTreeProof{Timestamps: timestamps}, size, retained)
	tree, err := st.UpdateView(r, size, prf)
	if err != nil {
		t.Fatalf("UpdateView(%d -> %d) with timestamps %v: %v", st.Tree.GetSize(), size, timestamps, err)
	} else if r.tsNext != len(timestamps) {
		t.Fatalf("UpdateView(%d -> %d) consumed %d of %d timestamps", st.Tree.GetSize(), size, r.tsNext, len(timestamps))
	}
	return tree
}

// When a user who has seen a tree of size `from` updates to size `to`, the
// draft (Section "Updating Views of the Tree") provides the timestamps of the
// log entries on the direct path of entry `from-1` whose index is >= `from`,
// followed by the rest of the new frontier. These are not always a suffix of
// the new frontier: for 5 -> 8 they are entries [5, 7], while the new frontier
// is just [7].
//
// @ trusted
func TestUpdateViewTimestamps(t *testing.T) {
	tests := []struct {
		name       string
		from, to   uint64
		initial    []uint64 // timestamps of frontier(from) = entries [3, 4]
		timestamps []uint64 // timestamps provided by the update
	}{
		{name: "5 to 5", from: 5, to: 5, initial: []uint64{30, 40}, timestamps: nil},
		{name: "5 to 6", from: 5, to: 6, initial: []uint64{30, 40}, timestamps: []uint64{50}},
		{name: "5 to 8", from: 5, to: 8, initial: []uint64{30, 40}, timestamps: []uint64{50, 70}},
	}

	for _, tc := range tests {
		t.Run(tc.name, func(t *testing.T) {
			st := &UserState{}
			st.Tree = updateViewTo(t, st, tc.from, tc.initial, prunedProof(t, tc.from, 0))
			st.Frontier_timestamps = tc.initial

			updateViewTo(t, st, tc.to, tc.timestamps, prunedProof(t, tc.to, tc.from))
		})
	}
}
