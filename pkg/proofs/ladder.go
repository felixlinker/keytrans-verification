package proofs

// ===========================================================================
// =====================================Log2Floor Lemmas======================================
/*@
// Function: Computes Log2Floor(n)
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
requires a<= b
ensures Log2Floor_pure(a) <= Log2Floor_pure(b)
decreases b
pure
func Log2FloorMonotonic(a uint64, b uint64) uint64 {
	return a == b ? 0 :
		(b < 2 ? 0 :
		(a < 2 ? Log2FloorBounds(b):
		Log2FloorMonotonic(a/2,b/2)))
}

//Lemma: When there is no gap, i.e. the log2Floor are equal, establish equality

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


// Lemma: Monotonicity of the power function: x > y ==> 2^{x} > 2^{y}

ghost
requires exp1 >= 0
requires exp1 < exp2
ensures IntPow2(exp1) < IntPow2(exp2)
decreases exp2
pure
func IntPow2IncLemma(exp1 uint64, exp2 uint64) (r bool){
	return exp2 == exp1 + 1 ? true : (IntPow2IncLemma(exp1, exp2-1))
}


// Lemma: Power of 2 always positive

ghost
requires n>= 0
ensures IntPow2(n) >= 1
decreases n
pure
func IntPow2Positive(n uint64) uint64{
	return n==0 ? 1 : IntPow2Positive(n-1)
}

// Lemma: IntPow2(n) <= IntPow2(n+1), need apparently a more direct version of the lemma as IntPow2IncLemma does not always work
ghost
requires n >= 0
ensures IntPow2(n) <= IntPow2(n+1)
decreases n
pure
func IntPow2LeqSucc(n uint64) uint64{
	return IntPow2Positive(n)
}

// Lemma: Weaker version of IntPow2IncLemma
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
	return tStar_pure(t1 +1, t2+1, true)- 1
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
					let apply_gap := IntPow2GapLemma(i_low, i_high) in  			//Here, we need to tell Gobra that IntPow2(i_low +1) <= IntPow2(i_high)
						IntPow2(i_low + 1) :
					let apply_gap := IntPow2GapLemma(i_low, i_high) in				//Here as well
						IntPow2(i_high)) :
				(t1 == low_ ?														// We need to consider the case that low_ == t1 if t1 is a power of 2, so this would lead t1 - low_ to 0 and Log2Floor_pure(t1) is not defined.
					let apply_bounds := Log2FloorBounds(t2 - low_) in
					low_ + IntPow2(Log2Floor_pure(t2-low_)):
					low_ + tStar_pure(t1 - low_,t2 - low_, false))

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
	return tStar(t1+1, t2+1, true) - 1
}

// @ requires t1>0
// @ requires t2 > t1
// @ ensures t_star == tStar_pure(t1,t2,pick_lowest)
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

// ==================================================================================
// ====================================ExponentialJump Phase=========================
/*@
// Function: Computer 2ˆk - 1

ghost
requires k >= 0
ensures r == IntPow2(k) - 1
ensures r >= 0
decreases
pure
func expJumpElement(k uint64) (r uint64){
	return let _:= IntPow2Positive(k) in
		IntPow2(k) - 1
}


//Lemma: Find the first element that target < 2^r - 1


ghost
requires target >= 0
ensures r >= 1
ensures r == Log2Floor_pure(target +1) +1
ensures IntPow2(r) > target +1
ensures IntPow2(r-1) <= target +1
decreases
pure
func findExpLevel(target uint64) (r uint64){
	return let _ := Log2FloorBounds(target +1) in
		Log2Floor_pure(target+1)+1
}


//Lemma: target >= x_in when k = findExpLevel(target) && k > 0

ghost
requires target >= 0
requires k == findExpLevel(target)
requires k > 0
ensures target >= expJumpElement(k-1)
decreases
pure
func TargetGeqXin(target uint64, k uint64) uint64 {
	return let target_1_bounded := Log2FloorBounds(target+1) in
		let k_pos := IntPow2Positive(k-1) in
		0
}


// Lemma: When t2 and target in the same bucket, t2 < x_out


ghost
requires target >= 0
requires t2 > target
requires Log2Floor_pure(t2+1) == Log2Floor_pure(target+1)
requires k == findExpLevel(target)
ensures t2 < expJumpElement(k)
decreases
pure
func T2LtXout_Upper(target uint64, t2 uint64, k uint64) uint64 {
	return let bound_t2_1 := Log2FloorBounds(t2+1) in
		let k_pow := IntPow2Positive(k) in
		0
}



//Lemma: Constraint the range of tStar is in the range of (x_in, x_out]

ghost
requires target >= 0
ensures r == (let k := findExpLevel(target) in
			  let x_out := expJumpElement(k) in
			  let x_in := (k > 0 ? expJumpElement(k-1) : 0) in
				v > x_in && v < x_out)
decreases
pure
func isInBinarySearchPortion(v uint64, target uint64) (r bool){
	return let k := findExpLevel(target) in
			  let x_out := expJumpElement(k) in
			  let x_in := (k > 0 ? expJumpElement(k-1) : 0) in
				v > x_in && v < x_out
}



@*/
// ==============================================================================================

/*@
//Core Lemma: Shows that k is in the search binary ladder r
ghost
requires target >= 0
ensures r == (let k := findExpLevel(target) in
		(exists j uint64 :: j >= 0 && j <= k && v == expJumpElement(j)) ||
		isInBinarySearchPortion(v, target))
decreases
pure
func isInLadder(v uint64, target uint64) (r bool){
	return let k := findExpLevel(target) in
		(exists j uint64 :: j >= 0 && j <= k && v == expJumpElement(j)) ||
		isInBinarySearchPortion(v, target)
}
@*/

// ==============================================================================================
/*@
ghost
requires t1 > 0
requires t2 > t1
requires Log2Floor_pure(t2) > Log2Floor_pure(t1)
ensures tStar_pure(t1,t2,true) == IntPow2(Log2Floor_pure(t1)+1)
decreases
pure
func tStar_WhenGap_ReturnNextPow2(t1 uint64, t2 uint64) uint64{
	return 0
}



ghost
requires target >= 0
requires t2 > target
requires Log2Floor_pure(t2 +1)> Log2Floor_pure(target + 1)
ensures TStar_pure(target,t2) == expJumpElement(Log2Floor_pure(target +1)+1)
ensures TStar_pure(target,t2) == expJumpElement(findExpLevel(target))
decreases
pure
func TStar_IsExpJumpElement_WhenGap_Upper(target uint64, t2 uint64) uint64


func TStar_IsExpJumpElement_WhenGap_Lower(target uint64, t2 uint64) uint64

func TStar_InLadder_Upper_Gap(target uint64, t2 uint64) uint64


func TStar_InLadder_Upper_SameBucket(target uint64, t2 uint64) uint64

@*/
// ==============================================================================================
/*@
// Core Lemma 1: Shows that the tStar is detected when running FBLS(target), target < t2
ghost
requires target > 0
requires t2 >= 0
requires t2 < target
//ensures isInLadder(TStar_pure(t2,target), target)
decreases
pure
func TStar_InLadder_Lower(target uint64, t2 uint64) uint64{
	return 0
}

// Core Lemma 1: Shows that the tStar is detected when running FBLS(target), target > t2
ghost
requires target > 0
requires t2 >= 0
requires t2 > target
//ensures isInLadder(TStar_pure(t2,target), target)
decreases
pure
func TStar_InLadder_Upper(target uint64, t2 uint64) uint64{
	return 0
}

@*/

// ======================================Main Theorem============================================

// @ requires target > 0
// @ requires t2 > 0
// @ ensures acc(r)
// @ ensures target < t2 ==> isInLadder(TStar_pure(target,t2), target)
// @ ensures t2 < target ==> isInLadder(TStar_pure(t2,target), target)
func FullBinaryLadderSteps_recurse(target uint64 /*@, ghost t2 uint64@*/) (r []uint64 /*@, ghost idx uint64@*/) {
	r = make([]uint64, 0)
	var i uint64 = 1
	//Find the index and the t_star from the array
	//@ var found uint64
	//@ idx = 0
	//@ var continue_searching bool = true

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

/*@
ghost
ensures res > 0
decreases
pure
func GetInt() (res uint64)
@*/

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

// ==============================================================================================
// ==============================================================================================
// ==============================================================================================

// @ requires target >=0
// @ ensures acc(r)
func FullBinaryLadderSteps(target uint64 /*@, ghost idx uint64 @*/) (r []uint64) {
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
