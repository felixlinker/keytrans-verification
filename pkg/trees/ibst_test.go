package trees

import "testing"

func TestFrontier(t *testing.T) {
	tests := []struct {
		size uint64
		want []uint64
	}{
		{size: 14, want: []uint64{7, 11, 13}},
		{size: 15, want: []uint64{7, 11, 13, 14}},
	}

	for _, tc := range tests {
		got := Frontier(tc.size)
		errF := func() {
			t.Errorf("Frontier(%d) = %v; want %v", tc.size, got, tc.want)
		}

		if len(got) != len(tc.want) {
			errF()
		} else {
			for i := range got {
				if got[i] != tc.want[i] {
					errF()
				}
			}
		}
	}
}
