package proofs

// ===========================================================================
// ===========================================================================
/*@
//Log2Floor function
ghost
requires n > 0
ensures r >= 0
ensures n >= 1 ==> IntPow2(r) <= n && IntPow2(r+1) > n && r < n
ensures n == 1 ==> r == 0
decreases n
pure
func Log2Floor_pure(n uint64) (r uint64) {
    return n < 2 ? 0 : 1 + Log2Floor_pure(n / 2)
}


ghost
requires n>0
ensures IntPow2(Log2Floor_pure(n)+1) > n
ensures IntPow2(Log2Floor_pure(n)) <=n
decreases n
pure
func Log2FloorUpperBound(n uint64) uint64{
	return n < 2 ? 0:  Log2FloorUpperBound(n/2) + IntPow2Positive(Log2Floor_pure(n/2)+1)
}


ghost
requires n > 0
ensures IntPow2(Log2Floor_pure(n)) <= n
ensures n < IntPow2(Log2Floor_pure(n) + 1)
decreases
pure func Log2FloorBounds(n uint64) uint64 {
    return Log2FloorUpperBound(n)
}


@*/
// ==================================================================================
// =============================IntPow2==============================================

/*@
ghost
requires exp >= 0
ensures r > 0
decreases exp
pure
func IntPow2(exp uint64) (r uint64) {
  return exp == 0 ? 1 : 2 * IntPow2(exp - 1)
}


ghost
requires exp1 >= 0
requires exp1 < exp2
ensures IntPow2(exp1) < IntPow2(exp2)
decreases exp2
pure
func IntPow2IncLemma(exp1 uint64, exp2 uint64) (r bool){
	return exp2 == exp1 + 1 ? true : (IntPow2IncLemma(exp1, exp2-1))
}


ghost
requires n>= 0
ensures IntPow2(n) >= 1
decreases n
pure
func IntPow2Positive(n uint64) uint64{
	return n==0 ? 1 : IntPow2Positive(n-1)
}

ghost
requires n >= 0
ensures IntPow2(n) <= IntPow2(n+1)
decreases n
pure
func IntPow2LeqSucc(n uint64) uint64{
	return IntPow2Positive(n)
}

ghost
requires a >= 0
requires b >= 0
requires a <= b
ensures IntPow2(a) <= IntPow2(b)
decreases b - a
pure
func IntPow2Monotonic(a uint64, b uint64) uint64{
	return a == b ? 0 : IntPow2Monotonic(a, b - 1) + IntPow2LeqSucc(b - 1)
}


ghost
requires i_low >= 0
requires i_high >= 0
requires i_high > i_low
ensures IntPow2(i_low +1) <= IntPow2(i_high)
decreases
pure
func IntPow2GapLemma(i_low uint64, i_high uint64) uint64{
	return IntPow2Monotonic(i_low+1, i_high)
}

@*/
// ==================================================================================
// ============================================================================

// ==================================================================================
// ====================================================================================
/*@

ghost
requires t1 >= 0
requires t2 > t1
ensures t1 < r
ensures r <= t2
decreases
pure
func TStar_pure(t1 uint64, t2 uint64) (r uint64){
	return tStar_pure(t1 +1, t2+1, true)- 1
}

@*/
// =============================Core Lemma==============================================
//Here, we need to tell Gobra that IntPow2(i_low +1) <= IntPow2(i_high)
// We need to consider the case if t1 == low_, i.e. low_ is a power of 2
//Here, we need to consider the case if low_ is a power of 2. If yes, then we cannot recurse due to the issue of Log2Floor is expecting a value > 0. So we need to handle that case manually.
/*@

ghost
requires t1 > 0
requires t2 > t1
ensures r >= 1
ensures t1 < r && r<=t2
decreases t1,t2
pure
func tStar_pure(t1 uint64, t2 uint64, pick_lowest bool) (r uint64) {
    return let i_low := Log2Floor_pure(t1) in
           let i_high := Log2Floor_pure(t2) in
           let low_ := IntPow2(i_low) in
		   let bound_t1 := Log2FloorBounds(t1) in
		   let bound_t2 := Log2FloorBounds(t2) in
		   let i_low_positive := IntPow2Positive(i_low) in
           i_high > i_low ?
           		(pick_lowest ?
					let apply_gap := IntPow2GapLemma(i_low, i_high) in
						IntPow2(i_low + 1) :
					let apply_gap := IntPow2GapLemma(i_low, i_high) in
						IntPow2(i_high)) :
				(t1 == low_ ?
					let apply_bounds := Log2FloorBounds(t2 - low_) in
					low_ + IntPow2(Log2Floor_pure(t2-low_)):
					low_ + tStar_pure(t1 - low_,t2 - low_, false))

}
@*/

/*@
ghost
ensures res > 0
decreases
pure
func GetInt() (res uint64)

@*/

// @ requires base > 0
// @ ensures r >= 0
// @ ensures IntPow2(r) <= base
// @ ensures base < IntPow2(r+1)
// @ ensures r == Log2Floor_pure(base)
// @ decreases base
func Log2Floor(base uint64) (r uint64) {
	if base <= 1 {
		//@ assert Log2Floor_pure(base) == 0
		return 0
	} else {
		//@ assert base > 1
		//@ assert Log2Floor_pure(base) == 1 + Log2Floor_pure(base / 2)
		return 1 + Log2Floor(base/2)
	}
}

// @ requires exp >= 0
// @ ensures r == IntPow2(exp)
// @ decreases
func PowOf2(exp uint64) (r uint64) {
	var i uint64
	r = 1
	//@ invariant i >= 0 && i<= exp
	//@ invariant r == IntPow2(i)
	//@ decreases exp - i
	for i = 0; i < exp; i += 1 {
		r = r * 2
	}
	return r
}

// TStar returns a value r such that t1 < r <= t2
// @ requires t1 >= 0
// @ requires t2 > t1
// @ trusted
func TStar(t1 uint64, t2 uint64) (t_star uint64) {
	return tStar(t1+1, t2+1, true) - 1
}

// @ trusted
func tStar(t1 uint64, t2 uint64, pick_lowest bool) (t_star uint64) {
	i_low := Log2Floor(t1)
	i_high := Log2Floor(t2)

	if i_high > i_low {
		if pick_lowest {
			return PowOf2(i_low + 1)
		} else {
			return PowOf2(i_high)
		}
	} else {
		// i_high == i_low (same log bucket)
		low_ := PowOf2(i_low)

		if t1 == low_ {
			// t1 is exactly a power of 2, so t1 - low_ = 0
			// In float version: log2(0) = -Inf, so i_high - i_low > 0 is always true
			// Since pick_lowest = false in recursion, it returns 2^i_high
			// where i_high = floor(log2(t2 - low_))
			return low_ + PowOf2(Log2Floor(t2-low_))
		}

		// t1 > low_, safe to recurse normally
		return low_ + tStar(t1-low_, t2-low_, false)
	}
}

// @ trusted
func TStar_combined(t1 uint64, t2 uint64, pick_lowest bool, shift_interval bool) (t_star uint64) {
	if shift_interval {
		//@ assert shift_interval
		return TStar_combined(t1+1, t2+1, true, false) - 1
	} else {
		i_low := Log2Floor(t1)
		i_high := Log2Floor(t2)

		if i_high > i_low {
			if pick_lowest {
				return PowOf2(i_low + 1)
			} else {
				return PowOf2(i_high)
			}
		} else {
			low_ := PowOf2(i_low)

			if t1 == low_ {
				return low_ + PowOf2(Log2Floor(t2-low_))
			}

			// t1 > low_, safe to recurse normally
			return low_ + tStar(t1-low_, t2-low_, false)
		}
	}
}

// @ requires target >=0
// @ ensures acc(r)
func FullBinaryLadderSteps(target uint32 /*@, ghost idx uint64 @*/) (r []uint32) {
	//@ assume 0 <= target // see https://github.com/viperproject/gobra/issues/192
	r = make([]uint32, 0)
	var i uint32 = 1
	// @ k := 0

	//@ invariant acc(r)
	//@ invariant 0 <= i - 1
	//@ invariant i-1 <= target || 1 <= len(r)
	for i-1 <= target {
		r = append( /*@ perm(1/2), @*/ r, i-1)
		//@ old_i := i
		i = i * 2
		// @ k = k+1
		//@ assert i == (2 * old_i)  // Gobra currently does not axiomatize left and right shifts
	}
	// i is now the smallest power of two s.t. i-1 is larger than target
	//@ assert len(r) > 0

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

// @ requires target > 0
// @ requires t2 > 0
// @ ensures acc(r)
//
// ensures target < t2 ==> tStar_pure(target+1, t2+1, true )-1 == r[idx]
func FullBinaryLadderSteps_recurse(target uint64 /*@, ghost t2 uint64@*/) (r []uint64 /*@, ghost idx uint64@*/) {
	r = make([]uint64, 0)
	var i uint64 = 1
	//Find the index and the t_star from the array
	//@ var found uint64
	//@ idx = 0
	//@ var continue_searching bool = true

	//@ assume t2 > target

	// t_star := tStar_pure(target+1, t2+1, true) - 1

	r, x_in, x_out /*@, idx_@*/ := ExponentialJump(target, r, i /*@,idx@*/)

	/*@
		ghost
		if t2 >= x_out{
			found := x_out
			idx := idx_
			continue_searching := false
		}
	@*/

	res /*@, found_, idx_, t2_ @*/ := BinarySearchStep(target, r, x_in, x_out /*@, found, idx, t2, continue_searching @*/)
	/*@
	ghost
	if continue_searching {
		found := found_
		idx:= idx_
		continue_searching := false
	}
	@*/

	//The end goal
	//	assert t_star == found
	// assert t_star == r[idx]
	return res /*@, idx@*/
}

// @ requires acc(r)
// @ requires target >= 0
// @ ensures acc(res)
// @ preserves i-1 >= 0
// @ preserves i-1 <= target || 1 <= len(r)
// @ ensures x_out > target
func ExponentialJump(target uint64, r []uint64, i uint64 /*@, ghost idx uint64@*/) (res []uint64, x_in uint64, x_out uint64 /*@, ghost index uint64@*/) {
	if i-1 <= target {

		r = append( /*@ perm(1/2), @*/ r, i-1)
		//@ idx = idx + 1
		return ExponentialJump(target, r, 2*i /*@, idx +1@*/)
	}
	x_out = i - 1

	if len(r) > 0 {
		x_in = r[len(r)-1]
		r = append( /*@ perm(1/2), @*/ r, i-1)
		//@ idx = idx + 1
		return r, x_in, x_out /*@, idx@*/
	}
	return r, 0, x_out /*@, idx@*/
}

// @ requires acc(r)
// @ ensures acc(res)
// @ ensures t2 == t2_
func BinarySearchStep(target uint64, r []uint64, x_in uint64, x_out uint64 /*@, ghost idx uint64, ghost found uint64, ghost t2 uint64, ghost continue_searching bool@*/) (res []uint64 /*@, ghost index uint64, ghost found_element uint64, ghost t2_ uint64 @*/) {
	if x_in+1 >= x_out {
		return r /*@, idx, found, t2@*/
	}
	next := x_in + (x_out-x_in)/2
	r = append( /*@ perm(1/2), @*/ r, next)
	/*@
		ghost
		if t2 <= next && continue_searching{
			found = next
			idx = idx + 1
		}
	@*/
	if next <= target {
		return BinarySearchStep(target, r, next, x_out /*@, found, idx, t2, continue_searching@*/)
	} else {
		return BinarySearchStep(target, r, x_in, next /*@, found, idx,t2,continue_searching@*/)
	}
}

// @ requires target > 0
func FullBinaryLadderSteps_wrapper(target uint64) (r []uint64, incl []uint64, non_incl []uint64) {

	//@ t2 := GetInt()

	//@ assume t2 != target && t2 > 0
	//@ assume t2 > target

	res /*@, idx1@*/ := FullBinaryLadderSteps_recurse(target /*@, t2 @*/)

	// assume forall t2 uint64 :: t2 < target ==> tStar_pure(t2, target, true) elem r
	// assume forall t2 uint64 :: target < t2 ==> tStar_pure(target, t2, true) elem r
	return res, incl, non_incl
}
