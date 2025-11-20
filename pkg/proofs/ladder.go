package proofs

import (
	"math"
)

func TStar(t1 uint32, t2 uint32) (t_star uint32) {
	return uint32(tStar(float64(t1+1), float64(t2+1), true) - 1)
}

func tStar(t1 float64, t2 float64, pick_lowest bool) (t_star float64) {
	if t1 >= t2 {
		panic("invariant violated")
	}

	i_low := math.Floor(math.Log2(t1))
	i_high := math.Floor(math.Log2(t2))
	if i_high-i_low > 0 {
		if pick_lowest {
			return math.Pow(2, i_low+1)
		} else {
			return math.Pow(2, i_high)
		}
	} else {
		low := math.Pow(2, i_low)
		return low + tStar(t1-low, t2-low, false)
	}
}

func FullBinaryLadderSteps(target uint32) (r []uint32) {
	//@ assume 0 <= target // see https://github.com/viperproject/gobra/issues/192
	r = make([]uint32, 0)
	var i uint32 = 1

	//@ invariant acc(r)
	//@ invariant 0 <= i - 1
	//@ invariant i-1 <= target || 1 <= len(r)
	for i-1 <= target {
		r = append( /*@ perm(1/2), @*/ r, i-1)
		//@ old_i := i
		i = i << 1
		//@ assume i == old_i * 2 // Gobra currently does not axiomatize left and right shifts
	}
	// i is now the smallest power of two s.t. i-1 is larger than target
	//@ assert target < i - 1

	x_in := r[len(r)-1]
	x_out := i - 1
	r = append( /*@ perm(1/2), @*/ r, x_out) // this will be the first proof of non-inclusion

	//@ invariant acc(r)
	for x_in+1 < x_out {
		next := x_in + (x_out-x_in)/2
		r = append( /*@ perm(1/2), @*/ r, next)
		if next <= target {
			x_in = next
		} else {
			x_out = next
		}
	}
	return r
}
