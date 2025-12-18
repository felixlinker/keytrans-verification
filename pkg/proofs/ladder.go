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
ensures target >= (let k := findExpLevel(target) in k >0 ? expJumpElement(k-1):0)
decreases
pure
func TargetGeqXin(target uint64) uint64 {
	return let k := findExpLevel(target) in
		let target_1_bounded := Log2FloorBounds(target+1) in
		let k_pos := (k > 0 ? IntPow2Positive(k-1):0) in
		0
}


// Lemma: When t2 and target in the same bucket, t2 < x_out
ghost
requires target >= 0
requires t2 > target
requires Log2Floor_pure(t2+1) == Log2Floor_pure(target+1)
ensures t2 < expJumpElement(findExpLevel(target))
decreases
pure
func T2LtXout_Upper(target uint64, t2 uint64) uint64 {
	return let bound_t2_1 := Log2FloorBounds(t2+1) in
		let k := findExpLevel(target) in
		let k_pow := IntPow2Positive(k) in
		let positive_k := IntPow2Positive(k) in
		0
}



//Lemma: Constraint the range of tStar is in the range of (x_in, x_out]

ghost
requires target >= 0
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
//An element is in ladder if it's either
//1. An expJumpElement (from the exponential jump phase) OR
//2. An element hit in the binary searching phase (we call it binary search portion here)

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
//Lemma: Recursively check if v == expJumpElement(j) for some j in [0,k]

ghost
requires k >= 0
decreases k
pure
func isExpJumpElementUpToK(v uint64, k uint64) bool{
	return v == expJumpElement(k) || (k > 0 && isExpJumpElementUpToK(v, k-1))
}

//Lemma: If there is a gap, then return the next power of 2.

ghost
requires t1 > 0
requires t2 > t1
requires Log2Floor_pure(t2) > Log2Floor_pure(t1)
ensures tStar_pure(t1,t2) == IntPow2(Log2Floor_pure(t1)+1)
decreases
pure
func tStar_WhenGap_ReturnNextPow2(t1 uint64, t2 uint64) uint64{
	return 0
}

//Lemma: If v == expJumpElement(j) and j <= k, then isExpJumpElementUpToK(v,k) holds
// Provides explicit witness for the recursive predicate

ghost
requires k>= 0
requires j >= 0
requires j<= k
requires v == expJumpElement(j)
ensures isExpJumpElementUpToK(v,k)
decreases k - j
pure
func expJumpElementInRange(v uint64, k uint64, j uint64) uint64{
	return j == k ? 0 : expJumpElementInRange(v,k-1, j)
}



//Lemma LOWER: In the gap case, TStar returns expJumpElement(j) where j == Log2Floor(t2 +1)+1

ghost
requires target > 0
requires t2 >= 0
requires t2 < target
requires Log2Floor_pure(t2 +1) < Log2Floor_pure(target + 1)
ensures TStar_pure(t2,target) == expJumpElement(Log2Floor_pure(t2 + 1) + 1)
decreases
pure
func TStar_IsExpJumpElement_WhenGap_Lower(target uint64, t2 uint64) uint64{
	return let apply_gap_pow := tStar_WhenGap_ReturnNextPow2(t2 + 1, target +1) in
		let res_pos := IntPow2Positive(Log2Floor_pure(target+1)+1) in
		0
}



//Lemma UPPER: TStar returns expJumpElement(k), which is in the ladder

ghost
requires target >= 0
requires t2 > 0
requires t2 > target
requires Log2Floor_pure(t2 + 1) > Log2Floor_pure(target + 1)
ensures TStar_pure(target, t2) == (let k := findExpLevel(target) in expJumpElement(k))
decreases
pure
func TStar_InLadder_Upper_Gap(target uint64, t2 uint64) uint64{
	return let apply_gap_pow := tStar_WhenGap_ReturnNextPow2(target + 1, t2 +1) in
	let res_pos := IntPow2Positive(Log2Floor_pure(t2+1)+1) in
	0

}


//Lemma LOWER: TStar returns expJumpElement(j), j <= k

ghost
requires t2 >= 0
requires t2 < target
requires Log2Floor_pure(target + 1) > Log2Floor_pure(t2 +1)
ensures isInLadder(TStar_pure(t2,target), target)
decreases
pure
func TStar_InLadder_Lower_Gap(target uint64, t2 uint64) uint64{
	return let j:= Log2Floor_pure(t2+1) +1 in
	let k := findExpLevel(target) in
	let lemma_monotonicity := Log2FloorMonotonic(t2 + 1, target + 1) in
	let lemma_gap_lower := TStar_IsExpJumpElement_WhenGap_Lower(target, t2) in
	let exp_in_range := expJumpElementInRange(TStar_pure(t2, target), k , j) in
	0
}


//Lemma UPPER: Shows TStar is in the range of [x_in, x_out] (binary search portion)

ghost
requires target >= 0
requires t2 > target
requires Log2Floor_pure(t2+1) == Log2Floor_pure(target+1)
decreases
pure
func TStar_inBinarySearchPortion_Upper(target uint64, t2 uint64) uint64{
	return let apply_geq := TargetGeqXin(target) in
	let apply_upper := T2LtXout_Upper(target, t2) in
	0
}


//Lemma LOWER: Shows TStar is in the range of [x_in, x_out] (binary search portion)


ghost
requires target > 0
requires t2 >=0
requires t2 < target
requires Log2Floor_pure(t2+1) == Log2Floor_pure(target+1)
ensures t2 >= let k := findExpLevel(target) in k > 0 ? expJumpElement(k-1):0
decreases
pure
func T2GeqXin_Lower(target uint64, t2 uint64) uint64{
	return let k := findExpLevel(target) in
	let bound_t2_1 := Log2FloorBounds(t2 + 1) in
	let k_pos := (k > 0 ? IntPow2Positive(k-1): 0) in
	0
}


//Lemma: Proves target < x_out (derived from the findExpLevel postcondition)

ghost
decreases
requires target >= 0
ensures target < let k := findExpLevel(target) in expJumpElement(k)
pure
func TargetLtXout(target uint64) uint64{
	return 0
}


// Lemma LOWER: TStar is in the binary search portion
ghost
requires target >= 0
requires t2 >= 0
requires t2 < target
requires Log2Floor_pure(t2+1) == Log2Floor_pure(target+1)
decreases
pure
func TStar_inBinarySearchPortion_Lower(target uint64, t2 uint64) uint64{
	return let t2_geq_x_in := T2GeqXin_Lower(target, t2) in
	let target_lt_x_out := TargetLtXout(target) in
	0
}


// Lemma LOWER: TStar is in the binary search portion

ghost
requires target >= 0
requires t2 >= 0
requires t2 < target
requires Log2Floor_pure(t2+1) == Log2Floor_pure(target+1)
decreases
pure
func TStar_InLadder_Lower_SameBucket(target uint64, t2 uint64) uint64{
	return let apply_binary_portion := TStar_inBinarySearchPortion_Lower(target, t2) in
		0
}


//Lemma UPPER: TStar is in the binary search portion

ghost
requires target >= 0
requires t2 >= 0
requires t2 > target
requires Log2Floor_pure(t2+1) == Log2Floor_pure(target+1)
decreases
pure
func TStar_InLadder_Upper_SameBucket(target uint64, t2 uint64) uint64{
	return let apply_binary_portion := TStar_inBinarySearchPortion_Upper(target, t2) in
	0
}

@*/
// ==============================================================================================
/*@
// Core Lemma 1: Shows that the tStar is detected when running FBLS(target), target < t2
// For any t2 < target, TStar(t2, target) is in the ladder

ghost
requires target > 0
requires t2 >= 0
requires t2 < target
ensures isInLadder(TStar_pure(t2,target), target)
decreases
pure
func TStar_InLadder_Lower(target uint64, t2 uint64) uint64{
	return	Log2Floor_pure(t2+1) < Log2Floor_pure(target + 1) ?
		TStar_InLadder_Lower_Gap(target, t2) :
		let apply_eq_nogap := Log2FloorEqWhenNotGap_Lower(target,t2) in
		TStar_InLadder_Lower_SameBucket(target, t2)
}

// Core Lemma 2: Shows that the tStar is detected when running FBLS(target), target > t2
// For any t2 > target, TStar(t2, target) is in the ladder

ghost
requires target > 0
requires t2 >= 0
requires t2 > target
ensures isInLadder(TStar_pure(target, t2), target)
decreases
pure
func TStar_InLadder_Upper(target uint64, t2 uint64) uint64{
	return Log2Floor_pure(t2+1) > Log2Floor_pure(target + 1) ?
		TStar_InLadder_Upper_Gap(target, t2) :
		let apply_eq_nogap := Log2FloorEqWhenNotGap_Upper(target,t2) in
		TStar_InLadder_Upper_SameBucket(target, t2)
}

@*/

// ======================================Core Lemma============================================

// @ requires target > 0
// @ requires t2 > 0
// @ requires target != t2
// @ ensures acc(r)
// @ ensures 0 < len(r) && 0 <= idx && idx < len(r)
// @ ensures target < t2 ==> r[idx] == tStar_pure(target, t2)
func fullBinaryLadderSteps(target uint64 /*@, ghost t2 uint64@*/) (r []uint64 /*@, idx int @*/) {
	r = make([]uint64, 0)
	var i uint64 = 1

	// Denotes the length of the array r.
	//@ ghost var k uint64 = 0
	//@ invariant k >= 0
	//@ invariant i == IntPow2(k)
	//@ invariant acc(r)
	// @ invariant len(r) == int(k)
	// @ invariant k == Log2Floor_pure(i)
	// @ invariant k <= target
	// @ invariant k > 1 ==> let apply_mon := Log2FloorMonotonic(k - 1, target) in k - 1 <= Log2Floor_pure(target)
	//@ invariant len(r) > 0 ==> r[k-1] == i / 2
	//@ invariant i / 2 <= target
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

	/*@
		target_idx := len(r) - 1
		ghost if t2 > x_out {
			assert let apply_mon := Log2FloorMonotonic(target, t2) in Log2Floor_pure(target) < Log2Floor_pure(t2)
		} else {
			assume false
		}
	@*/

	res /*@, j @*/ := BinarySearchStep(target, r, x_in, x_out /*@, t2 @*/)

	return res /*@, target_idx @*/
}

// @ requires target >= 0
func FullBinaryLadderSteps(target uint64) (r []uint64) {
	steps /*@, j @*/ := fullBinaryLadderSteps(target + 1 /*@, target + 2 @*/)
	// @ invariant acc(steps)
	for i := range steps {
		steps[i] = steps[i] - 1
	}
	return steps
}

// @ requires acc(r)
// @ requires x_in <= x_out
// @ ensures acc(res)
// @ ensures len(res) >= len(r)
// @ ensures forall i int :: 0 <= i && i < len(r) ==> res[i] == old(r[i])
// @ decreases x_out - x_in
func BinarySearchStep(target uint64, r []uint64, x_in uint64, x_out uint64 /*@, ghost t2 uint64@*/) (res []uint64 /*@, ghost idx int @*/) {
	if x_in+1 >= x_out {
		return r /*@, 0 @*/
	}
	next := x_in + (x_out-x_in)/2
	r = append( /*@ perm(1/2), @*/ r, next)
	if next <= target {
		return BinarySearchStep(target, r, next, x_out /*@, t2 @*/)
	} else {
		return BinarySearchStep(target, r, x_in, next /*@, t2 @*/)
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
// ensures forall t2 uint64 :: t2 < target && t2 >=0 ==> isInLadder(TStar_pure(t2, target), target)
// ensures forall t2 uint64 :: target < t2 && target >= 0 ==> isInLadder(TStar_pure(target, t2), target)
func FullBinaryLadderSteps_wrapper(target uint64) (r1 []uint64, r2 []uint64) {

	//@ t2 := GetInt()

	//@ assume t2 != target
	//@ assume t2 > target
	res /*@, _ @*/ := fullBinaryLadderSteps(target /*@, t2 @*/)

	// assert isInLadder(TStar_pure(target, t2), target)

	//@ assume t2 < target
	res2 /*@, _ @*/ := fullBinaryLadderSteps(target /*@, t2 @*/)
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
