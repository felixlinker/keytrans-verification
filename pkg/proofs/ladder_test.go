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

func TestFullBinaryLadderSteps(t *testing.T) {
	tests := []struct {
		target uint64
		want   []uint64
	}{
		{target: 0, want: []uint64{0, 1}},
		{target: 1, want: []uint64{0, 1, 3, 2}},
		{target: 2, want: []uint64{0, 1, 3, 2}},
		{target: 3, want: []uint64{0, 1, 3, 7, 5, 4}},
		{target: 15, want: []uint64{0, 1, 3, 7, 15, 31, 23, 19, 17, 16}},
		{target: 8, want: []uint64{0, 1, 3, 7, 15, 11, 9, 8}},
		{target: 10, want: []uint64{0, 1, 3, 7, 15, 11, 9, 10}},
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

/*
func TestFullBinaryLadderStepsRecurse(t *testing.T) {
	tests := []struct {
		target        uint64
		want          []uint64
		inclusion     []uint64
		non_inclusion []uint64
	}{
		{target: 0, want: []uint64{0, 1}, inclusion: []uint64{0}, non_inclusion: []uint64{1}},
		{target: 1, want: []uint64{0, 1, 3, 2}, inclusion: []uint64{0, 1}, non_inclusion: []uint64{3, 2}},
		{target: 2, want: []uint64{0, 1, 3, 2}, inclusion: []uint64{0, 1, 2}, non_inclusion: []uint64{3}},
		{target: 3, want: []uint64{0, 1, 3, 7, 5, 4}, inclusion: []uint64{0, 1, 3}, non_inclusion: []uint64{7, 5, 4}},
		{target: 15, want: []uint64{0, 1, 3, 7, 15, 31, 23, 19, 17, 16}, inclusion: []uint64{0, 1, 3, 7, 15}, non_inclusion: []uint64{31, 23, 19, 17, 16}},
		{target: 16, want: []uint64{0, 1, 3, 7, 15, 31, 23, 19, 17, 16}, inclusion: []uint64{0, 1, 3, 7, 15, 16}, non_inclusion: []uint64{31, 23, 19, 17}},
		{target: 8, want: []uint64{0, 1, 3, 7, 15, 11, 9, 8}, inclusion: []uint64{0, 1, 3, 7, 8}, non_inclusion: []uint64{15, 11, 9}},
		{target: 10, want: []uint64{0, 1, 3, 7, 15, 11, 9, 10}, inclusion: []uint64{0, 1, 3, 7, 9, 10}, non_inclusion: []uint64{15, 11}},
	}

	for _, tc := range tests {
		got, incl, non_incl := FullBinaryLadderSteps_recurse(tc.target)
		if len(got) != len(tc.want) {
			t.Errorf("FullBinaryLadderSteps_recurse(%d) = %v; want %v", tc.target, got, tc.want)
		} else if len(incl) != len(tc.inclusion) {
			t.Errorf("FullBinaryLadderSteps_recurse(%d) = %v; want %v", tc.target, incl, tc.inclusion)
		} else if len(non_incl) != len(tc.non_inclusion) {
			t.Errorf("FullBinaryLadderSteps_recurse(%d) = %v; want %v", tc.target, non_incl, tc.non_inclusion)

		} else {
			for i := range got {
				if got[i] != tc.want[i] {
					t.Errorf("FullBinaryLadderSteps_recurse(%d) = %v; want %v", tc.target, got, tc.want)
					break
				}
			}
			for j := range incl {
				if incl[j] != tc.inclusion[j] {
					t.Errorf("FullBinaryLadderSteps_recurse(%d) = %v; want %v", tc.target, incl, tc.inclusion)
					break

				}
			}
			for k := range non_incl {
				if non_incl[k] != tc.non_inclusion[k] {
					t.Errorf("FullBinaryLadderSteps_recurse(%d) = %v; want %v", tc.target, non_incl, tc.non_inclusion)
					break
				}
			}
		}
	}
}
*/
