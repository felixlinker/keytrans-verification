package proofs

import (
	"testing"
)

// @ trusted
func TestTStar(t *testing.T) {
	tests := []struct {
		t1   uint64
		t2   uint64
		want uint64
	}{
		{t1: 7, t2: 8, want: 8},
		{t1: 7, t2: 9, want: 9},
		{t1: 7, t2: 10, want: 9},
		{t1: 7, t2: 11, want: 11},
		{t1: 7, t2: 12, want: 11},
		{t1: 7, t2: 13, want: 11},
		{t1: 7, t2: 14, want: 11},
		{t1: 7, t2: 15, want: 15},

		{t1: 10, t2: 11, want: 11},
		{t1: 10, t2: 12, want: 11},
		{t1: 10, t2: 13, want: 11},
		{t1: 10, t2: 14, want: 11},
		{t1: 10, t2: 15, want: 15},

		{t1: 0, t2: 15, want: 1},
		{t1: 0, t2: 1, want: 1},
		{t1: 8, t2: 9, want: 9},
		{t1: 8, t2: 14, want: 11},
		{t1: 9, t2: 10, want: 10},
		{t1: 9, t2: 11, want: 11},
		{t1: 8, t2: 16, want: 15},
		{t1: 7, t2: 16, want: 15},
		{t1: 1, t2: 2, want: 2},
		{t1: 2, t2: 3, want: 3},
		{t1: 15, t2: 16, want: 16},
		{t1: 16, t2: 17, want: 17},
		{t1: 17, t2: 18, want: 18},
		{t1: 0, t2: 17, want: 1},
		{t1: 15, t2: 17, want: 17},
		{t1: 15, t2: 31, want: 31},
		{t1: 0, t2: 1231223121, want: 1},
	}

	for _, tc := range tests {
		got := TStar(tc.t1, tc.t2)
		if got != tc.want {
			t.Errorf("TStar(%d, %d) = %d; want %d", tc.t1, tc.t2, got, tc.want)
		}
	}
}

// @ trusted
func TestFullBinaryLadderSteps(t *testing.T) {
	tests := []struct {
		target uint64
		want   []uint64
	}{
		{target: 0, want: []uint64{0, 1}},
		{target: 1, want: []uint64{0, 1, 3, 2}},
		{target: 2, want: []uint64{0, 1, 3, 2}},
		{target: 3, want: []uint64{0, 1, 3, 7, 5, 4}},
		{target: 7, want: []uint64{0, 1, 3, 7, 15, 11, 9, 8}},
		{target: 15, want: []uint64{0, 1, 3, 7, 15, 31, 23, 19, 17, 16}},
		{target: 8, want: []uint64{0, 1, 3, 7, 15, 11, 9, 8}},
		{target: 10, want: []uint64{0, 1, 3, 7, 15, 11, 9, 10}},
		{target: 11, want: []uint64{0, 1, 3, 7, 15, 11, 13, 12}},
		{target: 9, want: []uint64{0, 1, 3, 7, 15, 11, 9, 10}},
	}

	for _, tc := range tests {
		got := FullBinaryLadderSteps(tc.target)
		if len(got) != len(tc.want) {
			t.Errorf("FullBinaryLadderSteps(%d) = %v; want %v", tc.target, got, tc.want)
		} else {
			for i := range got {
				if got[i] != tc.want[i] {
					t.Errorf("FullBinaryLadderSteps(%d) = %v; want %v", tc.target, got, tc.want)
					break
				}
			}
		}
	}
}

// referenceBinaryLadder ports base_binary_ladder from
// draft-ietf-keytrans-protocol-06, Appendix "Binary Ladder", for n < 1<<32.
// @ trusted
func referenceBinaryLadder(n uint64) []uint64 {
	out := []uint64{}
	for {
		value := uint64(1)<<len(out) - 1
		out = append(out, value)
		if value > n {
			break
		}
	}
	lower, upper := out[len(out)-2], out[len(out)-1]
	for lower+1 < upper {
		value := (lower + upper) / 2
		out = append(out, value)
		if value <= n && value < 1<<32 {
			lower = value
		} else {
			upper = value
		}
	}
	filtered := []uint64{}
	for _, v := range out {
		if v < 1<<32 {
			filtered = append(filtered, v)
		}
	}
	return filtered
}

// "The greatest possible version is 2^32-1. Any lookup for a greater version is
// skipped and the algorithm above continues as if the lookup resulted in a
// non-inclusion proof."
// @ trusted
func TestFullBinaryLadderStepsMaxVersion(t *testing.T) {
	maxVersion := MaxVersion()
	if maxVersion != 1<<32-1 {
		t.Fatalf("MaxVersion() = %d; want %d", maxVersion, uint64(1<<32-1))
	}

	// For the greatest possible version, every power of two minus one up to
	// and including 2^32-1 is included and nothing else is looked up.
	powers := []uint64{}
	for k := 0; k <= 32; k++ {
		powers = append(powers, uint64(1)<<k-1)
	}

	if ref := referenceBinaryLadder(maxVersion); len(ref) != len(powers) {
		t.Fatalf("referenceBinaryLadder(%d) = %v; want %v", maxVersion, ref, powers)
	} else {
		for i := range ref {
			if ref[i] != powers[i] {
				t.Fatalf("referenceBinaryLadder(%d) = %v; want %v", maxVersion, ref, powers)
			}
		}
	}

	targets := []uint64{
		1<<31 - 1, 1 << 31, 1<<31 + 1,
		maxVersion - 2, maxVersion - 1, maxVersion,
		maxVersion + 1, 1 << 40, 1<<64 - 1,
	}
	for target := uint64(0); target < 1024; target++ {
		targets = append(targets, target)
	}

	for _, target := range targets {
		got := FullBinaryLadderSteps(target)
		// Beyond MaxVersion, the reference ladder is that of MaxVersion. (The
		// port itself would overflow there, unlike the Python original.)
		want := powers
		if target <= maxVersion {
			want = referenceBinaryLadder(target)
		}
		if len(got) != len(want) {
			t.Errorf("FullBinaryLadderSteps(%d) = %v; want %v", target, got, want)
			continue
		}
		for i := range got {
			if got[i] != want[i] {
				t.Errorf("FullBinaryLadderSteps(%d) = %v; want %v", target, got, want)
				break
			}
			if got[i] > maxVersion {
				t.Errorf("FullBinaryLadderSteps(%d) looks up version %d > MaxVersion", target, got[i])
				break
			}
		}
	}
}
