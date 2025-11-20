package proofs

import (
	"testing"
)

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
