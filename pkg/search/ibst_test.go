package search

import "testing"

// @ trusted
func TestFrontier(t *testing.T) {
	tests := []struct {
		size uint64
		want []uint64
	}{
		{size: 4, want: []uint64{3}},
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

// @ trusted
func TestPathToNode(t *testing.T) {
	tests := []struct {
		n    uint64
		size uint64
		want []uint64
	}{
		{n: 0, size: 14, want: []uint64{7, 3, 1, 0}},
		{n: 5, size: 14, want: []uint64{7, 3, 5}},
		{n: 10, size: 14, want: []uint64{7, 11, 9, 10}},
		{n: 12, size: 14, want: []uint64{7, 11, 13, 12}},
	}

	for _, tc := range tests {
		got := PathToNode(tc.n, tc.size)
		errF := func() {
			t.Errorf("PathToNode(%d, %d) = %v; want %v", tc.n, tc.size, got, tc.want)
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

// @ trusted
func TestPathToMostRecent(t *testing.T) {
	tests := []struct {
		n    uint64
		size uint64
		want []uint64
	}{
		{n: 0, size: 9, want: []uint64{0, 1, 3, 7, 8}},
		{n: 0, size: 14, want: []uint64{0, 1, 3, 7, 11, 13}},
		{n: 5, size: 14, want: []uint64{5, 3, 7, 11, 13}},
		{n: 10, size: 14, want: []uint64{10, 9, 11, 13}},
		{n: 12, size: 14, want: []uint64{12, 13}},
	}

	for _, tc := range tests {
		got := PathToMostRecent(tc.n, tc.size)
		errF := func() {
			t.Errorf("NodesToMostRecent(%d, %d) = %v; want %v", tc.n, tc.size, got, tc.want)
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
