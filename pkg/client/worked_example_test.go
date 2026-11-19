package client

// Tests for Appendix C.1 "Worked Example" of draft-ietf-keytrans-protocol-06:
// https://datatracker.ietf.org/doc/html/draft-ietf-keytrans-protocol-06#name-worked-example

import (
	"bytes"
	"crypto/sha256"
	"fmt"
	"slices"
	"testing"

	"github.com/felixlinker/keytrans-verification/pkg/crypto"
	"github.com/felixlinker/keytrans-verification/pkg/proofs"
	"github.com/felixlinker/keytrans-verification/pkg/search"
	"github.com/felixlinker/keytrans-verification/pkg/trees/log"
)

const (
	exTreeSize     uint64 = 13
	exPrevTreeSize uint64 = 4
	exTarget       uint64 = 2
)

type exScenario struct {
	name       string
	timestamps []uint64 // T_0 .. T_12
	rmw        uint64
}

// Each scenario satisfies T_12 - T_7 >= RMW and T_12 - T_11 < RMW.
var exScenarios = []exScenario{
	{"evenly spaced, RMW at T_12 - T_7", exEvenTimestamps(), 5000},
	{"evenly spaced, RMW just above T_12 - T_11", exEvenTimestamps(), 1001},
	{"repeated timestamps", []uint64{10, 10, 20, 20, 30, 30, 30, 40, 50, 50, 60, 95, 95}, 50},
	{"large gap before entry 11", []uint64{1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 900, 901}, 2},
}

// @ trusted
func exEvenTimestamps() []uint64 {
	ts := make([]uint64, exTreeSize)
	for i := range ts {
		ts[i] = 1_700_000_000_000 + 1000*uint64(i)
	}
	return ts
}

// exLeaves returns the log tree leaf values: Hash(LogEntry{T_i, PT_i}).
// @ trusted
func exLeaves(timestamps []uint64) []proofs.NodeValue {
	leaves := make([]proofs.NodeValue, len(timestamps))
	for i, ts := range timestamps {
		prefixRoot := crypto.Sum(fmt.Appendf(nil, "prefix tree root %d", i))
		leaves[i] = crypto.LogEntryHash(ts, prefixRoot)
	}
	return leaves
}

// exLeafPair returns the value of the parent of two leaves, computed directly
// from the draft (Hash(0x00 || left || 0x00 || right) with SHA-256) rather than
// with the log package under test.
// @ trusted
func exLeafPair(left, right []byte) []byte {
	input := append(append([]byte{0x00}, left...), append([]byte{0x00}, right...)...)
	sum := sha256.Sum256(input)
	return sum[:]
}

// "the root is entry 7, the right child of entry 7 is entry 11, and the right
// child of entry 11 is entry 12, making entries 7, 11, and 12 the frontier."
// "...the contents of log entry 3 (the previous tree's only frontier entry)"
// @ trusted
func TestExampleFrontier(t *testing.T) {
	if got, want := search.Frontier(exTreeSize), []uint64{7, 11, 12}; !slices.Equal(got, want) {
		t.Errorf("Frontier(%d) = %v; want %v", exTreeSize, got, want)
	}
	if got, want := search.Frontier(exPrevTreeSize), []uint64{3}; !slices.Equal(got, want) {
		t.Errorf("Frontier(%d) = %v; want %v", exPrevTreeSize, got, want)
	}
}

// "The direct path of entry 3 in the new tree consists only of entry 7, so the
// timestamps provided are that of entry 7, followed by the timestamps of the
// remainder of the frontier: timestamps = [T_7, T_11, T_12]."
// @ trusted
func TestExampleUpdateViewEntries(t *testing.T) {
	got := search.YoungerToMostRecent(exPrevTreeSize-1, exTreeSize)
	if want := []uint64{7, 11, 12}; !slices.Equal(got, want) {
		t.Errorf("YoungerToMostRecent(%d, %d) = %v; want %v", exPrevTreeSize-1, exTreeSize, got, want)
	}
}

// "entry 11 is the rightmost distinguished log entry. (Entry 7 is also
// distinguished: the bounding timestamps used to evaluate it are 0 and T_12.)"
// The search then starts at entry 11, so exactly two PrefixProofs (entries 11
// and 12) are provided.
// @ trusted
func TestExampleRightmostDistinguished(t *testing.T) {
	frontier := search.Frontier(exTreeSize)
	for _, sc := range exScenarios {
		t.Run(sc.name, func(t *testing.T) {
			ts := []uint64{sc.timestamps[7], sc.timestamps[11], sc.timestamps[12]}
			idx := search.MostRecentDistinguished(ts, sc.rmw)
			if idx != 1 {
				t.Fatalf("MostRecentDistinguished(%v, %d) = %d; want 1 (entry %d)",
					ts, sc.rmw, idx, frontier[1])
			}
			if got := len(frontier) - idx; got != 2 {
				t.Errorf("number of search binary ladders = %d; want 2", got)
			}
		})
	}
}

// "The versions looked up by a search binary ladder for target version 2 are,
// in order: 0, 1, 3, 2. VRF proofs for exactly these versions are provided in
// SearchResponse.binary_ladder."
// @ trusted
func TestExampleBinaryLadder(t *testing.T) {
	got := proofs.FullBinaryLadderSteps(exTarget)
	if want := []uint64{0, 1, 3, 2}; !slices.Equal(got, want) {
		t.Errorf("FullBinaryLadderSteps(%d) = %v; want %v", exTarget, got, want)
	}
}

// "[inclusion] contains, in left-to-right order: the head value of the subtree
// with leaves 4 and 5, the value of leaf 6, the head value of the subtree with
// leaves 8 and 9, and the value of leaf 10."
//
// Leaves 7, 11 and 12 are not in `inclusion`: the user computes them from
// `timestamps` and the prefix tree root hashes (from `prefix_proofs` for
// entries 11 and 12, from `prefix_roots` for entry 7).
// @ trusted
func TestExampleInclusionProof(t *testing.T) {
	for _, sc := range exScenarios {
		t.Run(sc.name, func(t *testing.T) {
			leaves := exLeaves(sc.timestamps)
			want := [][]byte{
				exLeafPair(leaves[4], leaves[5]),
				leaves[6],
				exLeafPair(leaves[8], leaves[9]),
				leaves[10],
			}

			server := log.FullTree(leaves)
			server.Prune(exPrevTreeSize)
			prf, err := server.ProofFromPruned(exPrevTreeSize)
			if err != nil {
				t.Fatalf("ProofFromPruned(%d): %v", exPrevTreeSize, err)
			}
			if !slices.EqualFunc(prf.Elements, want, bytes.Equal) {
				t.Errorf("inclusion has %d elements %x;\nwant %d elements %x",
					len(prf.Elements), prf.Elements, len(want), want)
			}
		})
	}
}

// The user verifies "that the first timestamp is greater than or equal to the
// timestamp of the rightmost log entry they retained, and that each subsequent
// timestamp is greater than or equal to the one prior", then retains the
// timestamps of the new frontier (entries 7, 11 and 12).
//
// The inclusion proof here is whatever the log package produces for the
// transition, so that this test isolates the timestamp handling of UpdateView
// from the shape of the inclusion proof (see TestExampleInclusionProof).
// @ trusted
func TestExampleUpdateViewTimestamps(t *testing.T) {
	for _, sc := range exScenarios {
		t.Run(sc.name, func(t *testing.T) {
			st, prf := exReturningUser(t, sc)
			provided := []uint64{sc.timestamps[7], sc.timestamps[11], sc.timestamps[12]}
			if err := st.UpdateView(exTreeSize, provided, prf); err != nil {
				t.Fatalf("UpdateView: %v", err)
			}
			if !slices.Equal(st.Frontier_timestamps, provided) {
				t.Errorf("Frontier_timestamps = %v; want %v", st.Frontier_timestamps, provided)
			}
			if got := st.Tree.GetSize(); got != exTreeSize {
				t.Errorf("tree size = %d; want %d", got, exTreeSize)
			}
		})
	}

	t.Run("T_7 earlier than retained T_3 is rejected", func(t *testing.T) {
		sc := exScenarios[0]
		st, prf := exReturningUser(t, sc)
		provided := []uint64{sc.timestamps[7], sc.timestamps[11], sc.timestamps[12]}
		provided[0] = sc.timestamps[3] - 1
		if err := st.UpdateView(exTreeSize, provided, prf); err == nil {
			t.Errorf("UpdateView accepted T_7 < T_3")
		}
	})

	t.Run("decreasing frontier timestamps are rejected", func(t *testing.T) {
		sc := exScenarios[0]
		st, prf := exReturningUser(t, sc)
		provided := []uint64{sc.timestamps[7], sc.timestamps[11], sc.timestamps[12]}
		provided[1], provided[2] = provided[2], provided[1]
		if err := st.UpdateView(exTreeSize, provided, prf); err == nil {
			t.Errorf("UpdateView accepted T_11 > T_12")
		}
	})
}

// exReturningUser returns the state of a user who last observed the tree at
// size 4, and the log's inclusion proof for growing it to size 13.
// @ trusted
func exReturningUser(t *testing.T, sc exScenario) (*UserState, *proofs.InclusionProof) {
	t.Helper()
	leaves := exLeaves(sc.timestamps)

	retained := log.FullTree(leaves[:exPrevTreeSize])
	retained.Prune(0)

	server := log.FullTree(leaves)
	server.Prune(exPrevTreeSize)
	prf, err := server.ProofFromPruned(exPrevTreeSize)
	if err != nil {
		t.Fatalf("ProofFromPruned(%d): %v", exPrevTreeSize, err)
	}

	st := &UserState{
		Tree:                retained,
		Frontier_timestamps: []uint64{sc.timestamps[3]},
		Config:              &Configuration{ReasonableMonitoringWindow: sc.rmw},
	}
	return st, prf
}
