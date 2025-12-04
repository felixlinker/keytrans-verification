package proofs

import (
	"testing"
)

func TestTStar(t *testing.T) {
	tests := []struct {
		t1   uint64
		t2   uint64
		want uint64
	}{
		{t1: 0, t2: 15, want: 1},
		{t1: 0, t2: 1, want: 1},
		{t1: 8, t2: 9, want: 9},
		{t1: 8, t2: 14, want: 11},
		{t1: 9, t2: 10, want: 10},
		{t1: 8, t2: 16, want: 15},
		{t1: 7, t2: 16, want: 15},
		{t1: 1, t2: 2, want: 2},
		{t1: 2, t2: 3, want: 3},
		{t1: 15, t2: 16, want: 16},
		{t1: 16, t2: 17, want: 17},
		{t1: 17, t2: 18, want: 18},
		{t1: 0, t2: 17, want: 1},
		{t1: 15, t2: 17, want: 17},
		{t1: 0, t2: 1231223121, want: 1},
	}

	for _, tc := range tests {
		got := TStar(tc.t1, tc.t2)
		if got != tc.want {
			t.Errorf("TStar(%d, %d) = %d; want %d", tc.t1, tc.t2, got, tc.want)
		}
	}
}

func TestTStar_combined(t *testing.T) {
	tests := []struct {
		t1   uint64
		t2   uint64
		want uint64
	}{
		{t1: 0, t2: 15, want: 1},
		{t1: 0, t2: 1, want: 1},
		{t1: 8, t2: 9, want: 9},
		{t1: 8, t2: 14, want: 11},
		{t1: 9, t2: 10, want: 10},
		{t1: 8, t2: 16, want: 15},
		{t1: 7, t2: 16, want: 15},
		{t1: 1, t2: 2, want: 2},
		{t1: 2, t2: 3, want: 3},
		{t1: 15, t2: 16, want: 16},
		{t1: 16, t2: 17, want: 17},
		{t1: 17, t2: 18, want: 18},
		{t1: 0, t2: 17, want: 1},
		{t1: 0, t2: 1231223121, want: 1},
	}

	for _, tc := range tests {
		got := TStar_combined(tc.t1, tc.t2, false, true)
		if got != tc.want {
			t.Errorf("TStar(%d, %d) = %d; want %d", tc.t1, tc.t2, got, tc.want)
		}
	}
}

func TestFullBinaryLadderSteps(t *testing.T) {
	tests := []struct {
		target uint32
		want   []uint32
	}{
		{target: 0, want: []uint32{0, 1}},
		{target: 1, want: []uint32{0, 1, 3, 2}},
		{target: 15, want: []uint32{0, 1, 3, 7, 15, 31, 23, 19, 17, 16}},
		{target: 8, want: []uint32{0, 1, 3, 7, 15, 11, 9, 8}},
		{target: 10, want: []uint32{0, 1, 3, 7, 15, 11, 9, 10}},
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

func TestFullBinaryLadderStepsRecurse(t *testing.T) {
	tests := []struct {
		target uint64
		want   []uint64
	}{
		{target: 0, want: []uint64{0, 1}},
		{target: 1, want: []uint64{0, 1, 3, 2}},
		{target: 15, want: []uint64{0, 1, 3, 7, 15, 31, 23, 19, 17, 16}},
		{target: 8, want: []uint64{0, 1, 3, 7, 15, 11, 9, 8}},
		{target: 10, want: []uint64{0, 1, 3, 7, 15, 11, 9, 10}},
	}

	for _, tc := range tests {
		got := FullBinaryLadderSteps_recurse(tc.target)
		if len(got) != len(tc.want) {
			t.Errorf("FullBinaryLadderSteps_recurse(%d) = %v; want %v", tc.target, got, tc.want)
		} else {
			for i := range got {
				if got[i] != tc.want[i] {
					t.Errorf("FullBinaryLadderSteps_recurse(%d) = %v; want %v", tc.target, got, tc.want)
					break
				}
			}
		}
	}
}
