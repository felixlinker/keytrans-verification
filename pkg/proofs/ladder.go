package proofs

/*@
ghost
requires n > 0
ensures r >= 0
ensures n >= 1 ==> IntPow2(r) <= n && IntPow2(r+1) > n && r < n
ensures n == 1 ==> r == 0
decreases n
pure
func Log2Floor_pure(n uint64) (r uint64) {
    return n <= 1 ? 0 : 1 + Log2Floor_pure(n / 2)
}

@*/

// Don't think we can do with <= 1 due to correctness, but let's see what will happen lol

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
func IntPow2Lemma(exp1 uint64, exp2 uint64) (r bool){
	return exp2 == exp1 + 1 ? true : (IntPow2Lemma(exp1, exp2-1))
}

@*/

/*@
ghost
decreases
pure
func max(v1 uint64, v2 uint64) (r uint64){
	return v1 > v2? v1 : v2
}
@*/

/*@
ghost
requires t1 > 0
requires t2 > t1
ensures r >= 1
ensures t1 < r // && r <= t2
decreases t1,t2
pure
func tStar_pure(t1 uint64, t2 uint64, pick_lowest bool) (r uint64) {
    return let i_low := Log2Floor_pure(t1) in
           let i_high := Log2Floor_pure(t2) in
           let low_ := IntPow2(i_low) in
           i_high > i_low ?
           pick_lowest ? IntPow2(i_low + 1) : let apply_lemma := IntPow2Lemma(i_low+1, i_high+1) in IntPow2(i_high) :
            low_ + tStar_pure(max(t1 - low_,1), max(t2 - low_,2), false)
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

// @ requires t1 >= 0
// @ requires t2 > t1
// @ ensures t_star >= 0
func TStar(t1 uint64, t2 uint64) (t_star uint64) {
	return tStar(t1+1, t2+1, true) - 1
}

// @ ensures max(v1,v2) == r
// @ decreases
func max_element(v1 uint64, v2 uint64) (r uint64) {
	if v1 > v2 {
		return v1
	} else {
		return v2
	}
}

// @ requires t1 > 0
// @ requires t2 > t1
// @ ensures t_star > 0
// @ ensures t_star == tStar_pure(t1, t2, pick_lowest)
// @ decreases t1, t2
func tStar(t1 uint64, t2 uint64, pick_lowest bool) (t_star uint64) {
	i_low := Log2Floor(t1)
	i_high := Log2Floor(t2)
	//@ assert i_low >=0
	//@ assert i_high>= 0
	if i_high-i_low > 0 && pick_lowest {
		//@ assert pick_lowest
		return PowOf2(i_low + 1)
	} else if i_high-i_low > 0 && !pick_lowest {
		//@ assert !pick_lowest
		return PowOf2(i_high)
	} else {
		//@ assert i_high <= i_low
		low_ := PowOf2(i_low)
		//@ assert low_ > 0
		//@ assert t1- low_ < t1
		//@ assert t2-low_ < t2
		//@ assert t1 >= low_
		//@ assert t2 >= low_
		return low_ + tStar(max_element(t1-low_, 1), max_element(t2-low_, 2), false)
	}
}

// @ trusted
func TStar_combined(t1 uint64, t2 uint64, pick_lowest bool, shift_interval bool) (t_star uint64) {
	if shift_interval {
		//@ assert shift_interval
		return TStar_combined(t1+1, t2+1, true, false) - 1
	} else {
		//@ assert !shift_interval
		i_low := Log2Floor(t1)
		i_high := Log2Floor(t2)
		//@ assert i_low >=0
		//@ assert i_high>= 0

		if i_high-i_low > 0 && pick_lowest {
			//@ assert i_high > i_low
			//@ assert pick_lowest
			return PowOf2(i_low + 1)
		} else if i_high-i_low > 0 && !pick_lowest {
			//@ assert i_high > i_low
			//@ assert !pick_lowest
			return PowOf2(i_high)
		} else {
			//@ assert i_high <= i_low
			low_ := PowOf2(i_low)
			//@ assert low_ > 0
			//@ assert t1- low_ < t1
			//@ assert t2-low_ < t2
			return low_ + TStar_combined(t1-low_, t2-low_, false, false)
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
// ensure target < t2 ==> tStar_pure(target, t2, true ) == r[idx]
//
//	ensure t2 < target ==> tStar_pure(t2,target, true)== r[idx]
func FullBinaryLadderSteps_recurse(target uint64 /*@, ghost t2 uint64@*/) (r []uint64 /*@, ghost idx uint64@*/) {
	r = make([]uint64, 0)
	var i uint64 = 1
	//Find the index and the t_star from the array
	//@ var found uint64
	//@ idx = 0

	//@ assume t2 > target

	//@ t_star := tStar_pure(target+1, t2+1, true) - 1

	r, x_in, x_out /*@, idx_@*/ := ExponentialJump(target, r, i /*@,idx@*/)

	/*
		ghost
		if t2 > x_out{
			found = x_out
		}
	*/

	// Else, we need to investigate more into the BinarySearchStep
	// We need to check the value of t2, and find the number smaller equal than t2 of the non-incl
	res /*@, found_, idx_, t2_ @*/ := BinarySearchStep(target, r, x_in, x_out /*@, found, idx, t2@*/)

	//The end goal
	//	assert t_star == found_
	// assert t_star == r[idx_]
	return res /*@, idx_@*/
}

// @ requires acc(r)
// @ ensures acc(res)
// @ preserves i-1 >= 0
// @ preserves i-1 <= target || 1 <= len(r)
func ExponentialJump(target uint64, r []uint64, i uint64 /*@, ghost idx uint64@*/) (res []uint64, x_in uint64, x_out uint64 /*@, ghost index uint64@*/) {
	if i-1 <= target {
		r = append( /*@ perm(1/2), @*/ r, i-1)
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
func BinarySearchStep(target uint64, r []uint64, x_in uint64, x_out uint64 /*@, ghost idx uint64, ghost found uint64, ghost t2 uint64@*/) (res []uint64 /*@, ghost index uint64, ghost found_element uint64, ghost t2_ uint64 @*/) {
	if x_in+1 >= x_out {
		return r /*@, idx, found, t2@*/
	}
	next := x_in + (x_out-x_in)/2
	r = append( /*@ perm(1/2), @*/ r, next)

	if next <= target {
		return BinarySearchStep(target, r, next, x_out /*@, found, idx, t2@*/)
	} else {
		/*@
		ghost
		if t2 <= next{
			found = next
			idx = idx + 1
		}
		@*/
		return BinarySearchStep(target, r, x_in, next /*@, found, idx,t2@*/)
	}
}

// @ requires target > 0
func FullBinaryLadderSteps_wrapper(target uint64) (r []uint64, incl []uint64, non_incl []uint64) {

	//@ t2 := GetInt()

	//@ assume t2 != target && t2 > 0
	//@ assume t2 > target

	res /*@, t_star12@*/ := FullBinaryLadderSteps_recurse(target /*@, t2 @*/)

	// assume forall t2 uint64 :: t2 < target ==> tStar_pure(t2, target, true) elem incl
	// assume forall t2 uint64 :: target < t2 ==> tStar_pure(target, t2, true) elem non_incl
	return res, incl, non_incl
}
