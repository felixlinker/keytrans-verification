package utils

// Tests for TStar and FullBinaryLadderSteps have been moved to
// pkg/proofs/ladder_test.go to avoid an import cycle
// (utils_test -> proofs -> crypto -> utils).

/*
func TestFullBinaryLadderSteps_cursed(t *testing.T) {
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
		got := FBLS_cursed(tc.target)
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
