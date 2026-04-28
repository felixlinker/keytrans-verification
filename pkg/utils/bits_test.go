package utils

import (
	"testing"
)

func equalBools(a []bool, b []bool) bool {
	if len(a) != len(b) {
		return false
	}

	for i := range a {
		if a[i] != b[i] {
			return false
		}
	}

	return true
}

func TestByteBits(t *testing.T) {
	tests := []struct {
		b    byte
		want []bool
	}{
		{b: 0x00, want: []bool{false, false, false, false, false, false, false, false}},
		{b: 0xff, want: []bool{true, true, true, true, true, true, true, true}},
		{b: 0x80, want: []bool{true, false, false, false, false, false, false, false}},
		{b: 0x01, want: []bool{false, false, false, false, false, false, false, true}},
		{b: 0xa5, want: []bool{true, false, true, false, false, true, false, true}},
		{b: 0x3c, want: []bool{false, false, true, true, true, true, false, false}},
	}

	for _, tc := range tests {
		got := ByteBits(tc.b)
		if !equalBools(got, tc.want) {
			t.Errorf("ByteBits(%08b) = %v; want %v", tc.b, got, tc.want)
		}
	}
}
