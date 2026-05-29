package utils

import (
	"crypto/sha256"
	"fmt"
	"math/rand"
	"slices"
	"testing"
)

var byteBitsTests = []struct {
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

// @ trusted
func TestByteBit(t *testing.T) {
	for _, tc := range byteBitsTests {
		for i, want := range tc.want {
			got := byteBit(tc.b, i)
			if got != want {
				t.Errorf("byteBit(%08b, %d) = %v; want %v", tc.b, i, got, want)
			}
		}
	}
}

// @ trusted
func equalBoolSlices(a [][]bool, b [][]bool) bool {
	if len(a) != len(b) {
		return false
	}

	for i := range a {
		if !slices.Equal(a[i], b[i]) {
			return false
		}
	}

	return true
}

// @ trusted
func TestByteBits(t *testing.T) {
	for _, tc := range byteBitsTests {
		got := ByteBits(tc.b)
		if !slices.Equal(got, tc.want) {
			t.Errorf("ByteBits(%08b) = %v; want %v", tc.b, got, tc.want)
		}
	}
}

// @ trusted
func TestBits(t *testing.T) {
	for run := 0; run < 5; run++ {
		t.Run(fmt.Sprintf("run%d", run), func(t *testing.T) {
			bytes := make([]byte, sha256.Size)
			want := make([]bool, 0, sha256.Size*8)
			r := rand.New(rand.NewSource(int64(run)))

			for i := range bytes {
				tc := byteBitsTests[r.Intn(len(byteBitsTests))]
				bytes[i] = tc.b
				want = append(want, tc.want...)
			}

			got := Bits(bytes)
			if !slices.Equal(got, want) {
				t.Errorf("Bits(%v) = %v; want %v", bytes, got, want)
			}
		})
	}
}

var flippedTailsTests = []struct {
	name  string
	input []bool
	start int
	want  [][]bool
}{
	{
		name:  "provided example",
		input: []bool{true, false, true},
		start: 1,
		want: [][]bool{
			[]bool{true, true},
			[]bool{true, false, false},
		},
	},
	{
		name:  "all tails from start zero",
		input: []bool{false, false, true, true},
		start: 0,
		want: [][]bool{
			[]bool{true},
			[]bool{false, true},
			[]bool{false, false, false},
			[]bool{false, false, true, false},
		},
	},
	{
		name:  "only final tail",
		input: []bool{true, true, false, false},
		start: 3,
		want: [][]bool{
			[]bool{true, true, false, true},
		},
	},
}

// @ trusted
func TestFlippedTails(t *testing.T) {
	for _, tc := range flippedTailsTests {
		t.Run(tc.name, func(t *testing.T) {
			got := FlippedTails(tc.input, tc.start)
			if !equalBoolSlices(got, tc.want) {
				t.Errorf("FlippedTails(%v, %d) = %v; want %v", tc.input, tc.start, got, tc.want)
			}
		})
	}
}
