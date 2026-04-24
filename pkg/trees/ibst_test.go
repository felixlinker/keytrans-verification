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
					break
				}
			}
		}
	}
}

func TestPathToFrontier(t *testing.T) {
	tests := []struct {
		n    uint64
		size uint64
		want []uint64
	}{
		{n: 0, size: 14, want: []uint64{0, 1, 3, 7}},
		// {n: 5, size: 14, want: []uint64{5, 3, 7}},
		// {n: 10, size: 14, want: []uint64{10, 9, 11, 7}},
		// {n: 12, size: 14, want: []uint64{12, 13, 11, 7}},
	}

	for _, tc := range tests {
		got := PathToRoot(tc.n, tc.size)
		errF := func() {
			t.Errorf("PathToRoot(%d, %d) = %v; want %v", tc.n, tc.size, got, tc.want)
		}

		if len(got) != len(tc.want) {
			errF()
		} else {
			for i := range got {
				if got[i] != tc.want[i] {
					errF()
					break
				}
			}
		}
	}
}
