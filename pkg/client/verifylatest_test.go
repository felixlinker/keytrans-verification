package client

//Uncomment this if you want to use Gobra.

import (
	"testing"
)

func TestRootNode_SpecCompilance(t *testing.T) {
	tests := []struct {
		name     string
		treeSize uint64
		wantRoot uint64
	}{

		{"size 0", 0, 0},
		{"size 1", 1, 0},
		{"size 2", 2, 1},

		//Pow of 2
		{"size 4", 4, 3},
		{"size 8", 8, 7},
		{"size 16", 16, 15},

		//Not pow of 2
		{"size 3", 3, 1},
		{"size 5", 5, 3},
		{"size 6", 6, 3},
		{"size 7", 7, 3},
		{"size 9", 9, 7},
		{"size 14", 14, 7},
		{"size 15", 15, 7},
		{"size 50", 50, 31},
	}

	for _, tc := range tests {
		t.Run(tc.name, func(t *testing.T) {
			got := RootNode(tc.treeSize)
			if got != tc.wantRoot {
				t.Errorf("RootNode(%d) = %d; want %d", tc.treeSize, got, tc.wantRoot)
			}
		})
	}
}
