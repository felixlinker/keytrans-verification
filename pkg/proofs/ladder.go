package proofs

// ===========================================================================================
// =====================================Log2Floor Lemmas======================================
/*@
// Function: Computes Log2Floor(n)
ghost
ensures r >= 0
ensures n >= 1 ==> IntPow2(r) <= n && IntPow2(r+1) > n && r < n
ensures n == 1 ==> r == 0
decreases n
pure
func Log2Floor_pure(n uint64) (r uint64) {
    return n < 2 ? 0 : 1 + Log2Floor_pure(n / 2)
}


// Lemma: Log2Floor is upper bounded
ghost
requires n>0
ensures IntPow2(Log2Floor_pure(n)+1) > n
ensures IntPow2(Log2Floor_pure(n)) <=n
decreases n
pure
func Log2FloorUpperBound(n uint64) uint64{
	return n < 2 ? 0:  Log2FloorUpperBound(n/2) + IntPow2Positive(Log2Floor_pure(n/2)+1)
}


//Lemma: The element in the Log2Floor_pure is bounded

ghost
requires n > 0
ensures IntPow2(Log2Floor_pure(n)) <= n
ensures n < IntPow2(Log2Floor_pure(n) + 1)
decreases
pure func Log2FloorBounds(n uint64) uint64 {
    return Log2FloorUpperBound(n)
}


//Lemma: Monotonicity of the Log2Floor_pure function

ghost
requires a > 0
requires b > 0
requires a <= b
ensures Log2Floor_pure(a) <= Log2Floor_pure(b)
ensures a <= b/2 ==> Log2Floor_pure(a) < Log2Floor_pure(b)
decreases b
pure
func Log2FloorMonotonic(a uint64, b uint64) uint64 {
	return a == b ? 0 :
		(b < 2 ? 0 :
		(a < 2 ? Log2FloorBounds(b):
		Log2FloorMonotonic(a/2,b/2)))
}

//Lemma: When there is no gap, i.e. the log2Floor are equal, establish equality (triangle inequality)

ghost
requires target >= 0
requires t2 > target
requires Log2Floor_pure(t2 + 1) <=  Log2Floor_pure(target + 1)
ensures Log2Floor_pure(t2 + 1) == Log2Floor_pure(target + 1)
decreases
pure
func Log2FloorEqWhenNotGap_Upper(target uint64, t2 uint64) uint64{
	return Log2FloorMonotonic(target + 1, t2 + 1)
}

//Lemma: When there is no gap, i.e. the log2Floor are equal, establish equality (triangle inequality)
ghost
requires target > 0
requires t2 >= 0
requires t2 < target
requires Log2Floor_pure(t2 + 1) >=  Log2Floor_pure(target + 1)
ensures Log2Floor_pure(t2 + 1) == Log2Floor_pure(target + 1)
decreases
pure
func Log2FloorEqWhenNotGap_Lower(target uint64, t2 uint64) uint64{
	return Log2FloorMonotonic(t2 + 1, target + 1)
}



@*/
// ==================================================================================
// =============================IntPow2 Lemmas ======================================

/*@
// Function: Computes 2^(exp)
ghost
requires exp >= 0
ensures r > 0
decreases exp
pure
func IntPow2(exp uint64) (r uint64) {
  return exp == 0 ? 1 : 2 * IntPow2(exp - 1)
}

// Lemma: Power of 2 always positive

ghost
requires n >= 0
ensures IntPow2(n) > 0
ensures IntPow2(n) < IntPow2(n+1)
decreases n
pure
func IntPow2Positive(n uint64) uint64 {
	return n==0 ? 1 : IntPow2Positive(n-1)
}

// Lemma: Weaker version of IntPow2IncLemma
ghost
requires a >= 0
requires b >= 0
requires a <= b
ensures IntPow2(a) <= IntPow2(b)
ensures a < b ==> IntPow2(a) < IntPow2(b)
decreases b - a
pure
func IntPow2Monotonic(a uint64, b uint64) uint64 {
	return a == b ? 0 : IntPow2Monotonic(a, b - 1) + IntPow2Positive(b - 1)
}

// Lemma: Used to convince Gobra that the i_low < i_high ==> IntPow2(i_low +1) <= IntPow2(i_high)
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
// ============================================================================
// ============================================================================
/*@
// Main Lemma: t1 < r <= t2, which is what we want to show
ghost
requires t1 >= 0
requires t2 > t1
ensures t1 < r
ensures r <= t2
decreases
pure
func TStar_pure(t1 uint64, t2 uint64) (r uint64){
	return tStar_pure(t1 +1, t2+1)- 1
}

@*/
// =============================Core Lemma======================================
/*@
// Core Lemma: Shows that tPure function indicates t1<r <= t2
ghost
requires t1 > 0
requires t2 > t1
ensures r >= 1
ensures t1 < r && r<=t2
decreases
pure
func tStar_pure(t1 uint64, t2 uint64) (r uint64) {
	return let i_low := Log2Floor_pure(t1) in tStarRec_pure(t1, t2, IntPow2(i_low), IntPow2(i_low + 1))
}

ghost
requires x_in <= t1
requires t1 < x_out
requires 0 < t1
requires t1 < t2
ensures r > t1
ensures r <= t2
decreases x_out-x_in
pure
func tStarRec_pure(t1 uint64, t2 uint64, x_in uint64, x_out uint64) (r uint64) {
	return x_out <= t2 ?
		x_out :
		(let next := x_in + (x_out - x_in) / 2 in
			next <= t1 ?
				tStarRec_pure(t1, t2, next, x_out) :
				tStarRec_pure(t1, t2, x_in, next))
}
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
// @ ensures t_star >= 1
// @ ensures t_star == TStar_pure(t1,t2)
func TStar(t1 uint64, t2 uint64) (t_star uint64) {
	return tStar(t1+1, t2+1) - 1
}

// @ requires t1>0
// @ requires t2 > t1
// @ ensures t_star == tStar_pure(t1,t2)
func tStar(t1 uint64, t2 uint64) (t_star uint64) {
	i_low := Log2Floor(t1)
	return tStarRec(t1, t2, PowOf2(i_low), PowOf2(i_low+1))
}

// @ requires 0 < t1
// @ requires t1 < t2
// @ requires x_in <= t1
// @ requires t1 < x_out
// @ ensures r == tStarRec_pure(t1, t2, x_in, x_out)
func tStarRec(t1 uint64, t2 uint64, x_in uint64, x_out uint64) (r uint64) {
	if x_out <= t2 {
		return x_out
	} else {
		next := x_in + (x_out-x_in)/2
		if next <= t1 {
			return tStarRec(t1, t2, next, x_out)
		} else {
			return tStarRec(t1, t2, x_in, next)
		}
	}
}

// @ requires 0 < target && target < t2
// @ ensures acc(r)
// @ ensures 0 < len(r) && 0 <= idx && idx < len(r)
// @ ensures r[idx] == tStar_pure(target, t2)
func fullBinaryLadderSteps(target uint64 /*@, ghost t2 uint64@*/) (r []uint64 /*@, ghost idx int @*/) {
	r = make([]uint64, 0)
	var i uint64 = 1

	// Denotes the length of the array r.
	// @ ghost var k uint64 = 0
	// @ invariant acc(r)
	// @ invariant len(r) == int(k)
	// @ invariant 0 <= k && k <= target
	// @ invariant i == IntPow2(k) && k == Log2Floor_pure(i)
	// @ invariant k > 1 ==> let apply_mon := Log2FloorMonotonic(k - 1, target) in k - 1 <= Log2Floor_pure(target)
	//@ invariant len(r) > 0 ==> r[k-1] == i / 2
	for i-1 < target {
		r = append( /*@ perm(1/2), @*/ r, i)
		i = i * 2
		// @ k = k+1
	}
	// i is now the smallest power of two s.t. i-1 is larger than target

	var x_in uint64 = 1
	if len(r) > 0 {
		x_in = r[len(r)-1]
	}

	x_out := i
	r = append( /*@ perm(1/2), @*/ r, x_out) // this will be the first proof of non-inclusion

	// @ assert let apply_mon := Log2FloorMonotonic(target, i) in Log2Floor_pure(target) < k + 1
	// @ assert k + 1 <= x_out
	// @ assert let apply_mon := Log2FloorMonotonic(k + 1, x_out) in k <= Log2Floor_pure(x_out)
	// @ ghost target_idx := len(r) - 1

	res /*@, search_idx @*/ := BinarySearchStep(target, r, x_in, x_out /*@, t2, target_idx, x_out @*/)

	return res /*@, search_idx @*/
}

// @ requires 0 <= target && target < t2
// @ ensures acc(r) && 0 < len(r)
// @ ensures 0 <= idx && idx < len(r)
// ensures r[idx] == TStar_pure(target, t2)
func FullBinaryLadderSteps(target uint64 /*@, ghost t2 uint64 @*/) (r []uint64 /*@, ghost idx int @*/) {
	steps /*@, r_idx @*/ := fullBinaryLadderSteps(target + 1 /*@, t2 + 1 @*/)
	// @ invariant acc(steps)
	// @ invariant 0 <= i && i < len(steps)
	for i := range steps {
		steps[i] = steps[i] - 1
	}
	return steps /*@, r_idx @*/
}

// @ requires 0 < len(r) && acc(r)
// @ requires 0 < target && target < t2
// @ requires 0 < x_in && x_in <= target && target < x_out
// @ requires 0 < acc_idx && acc_idx < len(r)
// @ requires x_out <= t2 ? x_out <= acc_x_out && acc_x_out <= t2 : acc_x_out == x_out
// @ requires acc_x_out <= t2 ==> r[acc_idx] == tStarRec_pure(target, t2, x_in, acc_x_out)
// @ ensures acc(res) && 0 <= idx && idx < len(res)
// @ ensures res[idx] == tStarRec_pure(target, t2, x_in, acc_x_out)
// @ decreases x_out - x_in
func BinarySearchStep(target uint64, r []uint64, x_in uint64, x_out uint64 /*@, ghost t2 uint64, ghost acc_idx int, ghost acc_x_out uint64 @*/) (res []uint64 /*@, ghost idx int @*/) {
	// @ rec_idx := acc_idx
	if x_in+1 >= x_out {
		return r /*@, rec_idx @*/
	}

	next := x_in + (x_out-x_in)/2
	r = append( /*@ perm(1/2), @*/ r, next)
	rec_x_in := x_in
	rec_x_out := x_out
	if next <= target {
		rec_x_in = next
	} else {
		rec_x_out = next
		/*@
		ghost if rec_x_out <= t2 && acc_x_out > t2 {
			rec_idx = len(r) - 1
		}
		@*/
	}

	// @ rec_acc_x_out := acc_x_out <= t2 ? acc_x_out : rec_x_out
	return BinarySearchStep(target, r, rec_x_in, rec_x_out /*@, t2, rec_idx, rec_acc_x_out @*/)
}

/*@
ghost
ensures res > 0
decreases
pure
func GetInt() (res uint64)
@*/

// @ requires target > 0
// ensures forall t2 uint64 :: t2 < target && t2 >=0 ==> isInLadder(TStar_pure(t2, target), target)
// ensures forall t2 uint64 :: target < t2 && target >= 0 ==> isInLadder(TStar_pure(target, t2), target)
func FullBinaryLadderSteps_wrapper(target uint64) (r1 []uint64, r2 []uint64) {

	//@ t2 := GetInt()

	//@ assume t2 != target
	//@ assume t2 > target
	res /*@, j @*/ := fullBinaryLadderSteps(target /*@, t2 @*/)

	// assert isInLadder(TStar_pure(target, t2), target)

	//@ assume t2 < target
	res2 /*@, k @*/ := fullBinaryLadderSteps(target /*@, t2 @*/)
	// assert isInLadder(TStar_pure(t2, target), target)
	return res, res2
}

// ==============================================================================================
// ==============================================================================================

//Use it as a reference, we don't need this algorithm anymore

// @ requires target >=0
// @ ensures acc(r)
func FullBinaryLadderSteps_iterative(target uint64 /*@, ghost idx uint64 @*/) (r []uint64) {
	//@ assume 0 <= target // see https://github.com/viperproject/gobra/issues/192
	r = make([]uint64, 0)
	var i uint64 = 1
	// @ ghost var k uint64 = 0

	//@ invariant acc(r)
	//@ invariant 0 <= i - 1
	//@ invariant i-1 <= target || 1 <= len(r)
	//@ invariant i >= 1
	//@ invariant k >= 0
	//@ invariant i == IntPow2(k)
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
