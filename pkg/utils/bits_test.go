package utils

import (
	"crypto/sha256"
	"fmt"
	"math/rand"
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
	for _, tc := range byteBitsTests {
		got := ByteBits(tc.b)
		if !equalBools(got, tc.want) {
			t.Errorf("ByteBits(%08b) = %v; want %v", tc.b, got, tc.want)
		}
	}
}

func TestBits(t *testing.T) {
	for run := 0; run < 5; run++ {
		t.Run(fmt.Sprintf("run%d", run), func(t *testing.T) {
			var bytes [sha256.Size]byte
			want := make([]bool, 0, sha256.Size*8)
			r := rand.New(rand.NewSource(int64(run)))

			for i := range bytes {
				tc := byteBitsTests[r.Intn(len(byteBitsTests))]
				bytes[i] = tc.b
				want = append(want, tc.want...)
			}

			got := Bits(bytes)
			if !equalBools(got, want) {
				t.Errorf("Bits(%v) = %v; want %v", bytes, got, want)
			}
		})
	}
}
