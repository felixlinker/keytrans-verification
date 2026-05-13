package utils

import "testing"

// @ trusted
func TestLog2Floor(t *testing.T) {
	tests := []struct {
		base uint64
		want uint64
	}{
		{base: 1, want: 0},
		{base: 2, want: 1},
		{base: 3, want: 1},
		{base: 4, want: 2},
		{base: 5, want: 2},
		{base: 7, want: 2},
		{base: 8, want: 3},
		{base: 9, want: 3},
		{base: 15, want: 3},
		{base: 16, want: 4},
		{base: 17, want: 4},
		{base: 31, want: 4},
		{base: 32, want: 5},
		{base: 33, want: 5},
		{base: 63, want: 5},
		{base: 64, want: 6},
	}

	for _, tc := range tests {
		got := Log2Floor(tc.base)
		if got != tc.want {
			t.Errorf("Log2Floor(%d) = %d; want %d", tc.base, got, tc.want)
		}
	}
}

// @ trusted
func TestPowOf2(t *testing.T) {
	tests := []struct {
		exp  uint64
		want uint64
	}{
		{exp: 0, want: 1},
		{exp: 1, want: 2},
		{exp: 2, want: 4},
		{exp: 3, want: 8},
		{exp: 4, want: 16},
		{exp: 5, want: 32},
		{exp: 6, want: 64},
		{exp: 7, want: 128},
		{exp: 8, want: 256},
		{exp: 16, want: 65536},
		{exp: 32, want: 4294967296},
		{exp: 63, want: 9223372036854775808},
	}

	for _, tc := range tests {
		got := PowOf2(tc.exp)
		if got != tc.want {
			t.Errorf("PowOf2(%d) = %d; want %d", tc.exp, got, tc.want)
		}
	}
}

// @ trusted
func TestLargestSmallerPower(t *testing.T) {
	tests := []struct {
		size uint64
		want uint64
	}{
		{size: 1, want: 1},
		{size: 2, want: 2},
		{size: 3, want: 2},
		{size: 4, want: 4},
		{size: 5, want: 4},
		{size: 7, want: 4},
		{size: 8, want: 8},
		{size: 9, want: 8},
		{size: 15, want: 8},
		{size: 16, want: 16},
		{size: 17, want: 16},
		{size: 31, want: 16},
		{size: 32, want: 32},
		{size: 33, want: 32},
		{size: 63, want: 32},
		{size: 64, want: 64},
	}

	for _, tc := range tests {
		got := LargestSmallerPower(tc.size)
		if got != tc.want {
			t.Errorf("LargestSmallerPower(%d) = %d; want %d", tc.size, got, tc.want)
		}
	}
}

// @ trusted
func TestTrueLargestSmallerPower(t *testing.T) {
	tests := []struct {
		size uint64
		want uint64
	}{
		{size: 1, want: 0},
		{size: 2, want: 1},
		{size: 3, want: 2},
		{size: 4, want: 2},
		{size: 5, want: 4},
		{size: 7, want: 4},
		{size: 8, want: 4},
		{size: 9, want: 8},
		{size: 15, want: 8},
		{size: 16, want: 8},
		{size: 17, want: 16},
		{size: 31, want: 16},
		{size: 32, want: 16},
		{size: 33, want: 32},
		{size: 63, want: 32},
		{size: 64, want: 32},
	}

	for _, tc := range tests {
		got := TrueLargestSmallerPower(tc.size)
		if got != tc.want {
			t.Errorf("LargestSmallerPower(%d) = %d; want %d", tc.size, got, tc.want)
		}
	}
}
