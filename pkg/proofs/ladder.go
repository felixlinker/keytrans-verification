package proofs

import (
	"math"
)

// @ ghost
// @ requires t1 >= 0
// @ requires t2 >= t1
// @ pure
func TStar(t1 uint32, t2 uint32) (t_star uint32) {
	return uint32(tStar(float64(t1+1), float64(t2+1), true) - float64(1))
}

// @ ghost
// @ requires int(t1) > 0
// @ requires int(t2) >= int(t1)
// @ ensures t_star > 0
// @ decreases t2
//
//	pure
func tStar(t1 float64, t2 float64, pick_lowest bool) (t_star float64) {
	if t1 >= t2 {
		//@ assert false
		panic("invariant violated")
	}
	// @ assert t1 < t2
	//@ assert false

	i_low := math.Floor(math.Log2(t1))
	i_high := math.Floor(math.Log2(t2))

	if i_high-i_low > 0.0 {
		if pick_lowest {
			return math.Pow(2.0, i_low+1.0)
		} else {
			return math.Pow(2.0, i_high)
		}
	} else {
		low_ := math.Pow(2.0, i_low)
		//@ assert int(low_) > 0
		//@ assert t1- low_ < t1
		//@ assert t2-low_ < t2
		return low_ + tStar(t1-low_, t2-low_, false)
	}
}

// @ preserves acc(r)
// @ requires target >=0
//
//	ensures forall t1 uint32 :: t1 <= target ==> TStar(t1,target) elem r
//	ensures forall t2 uint32 :: t2 > target ==> TStar(target, t2) elem r
func FullBinaryLadderSteps(target uint32) (r []uint32) {
	//@ assume 0 <= target // see https://github.com/viperproject/gobra/issues/192
	r = make([]uint32, 0)
	var i uint32 = 1

	//@ invariant acc(r)
	//@ invariant 0 <= i - 1
	//@ invariant i-1 <= target || 1 <= len(r)
	//@
	for i-1 <= target {
		r = append( /*@ perm(1/2), @*/ r, i-1)
		//@ old_i := i
		i = i * 2
		//@ assert i == (2 * old_i)  // Gobra currently does not axiomatize left and right shifts
		//@ assert old_i <= i
	}
	// i is now the smallest power of two s.t. i-1 is larger than target
	//@ assert len(r) > 0

	x_in := r[len(r)-1]
	x_out := i - 1
	r = append( /*@ perm(1/2), @*/ r, x_out) // this will be the first proof of non-inclusion

	//@ invariant acc(r)
	// invariant x_in <= target
	// invariant x_out > target
	for x_in+1 < x_out {
		next := x_in + (x_out-x_in)/2
		//@ assert x_in <= next
		//@ assert next < x_out
		r = append( /*@ perm(1/2), @*/ r, next)
		if next <= target {
			x_in = next
		} else {
			x_out = next
		}
	}
	return r
}
