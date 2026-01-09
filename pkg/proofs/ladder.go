package proofs

// ##(--hyperMode extended)

//TODO: Lemmas kombinieren, simplifizieren.

// ===========================================================================================
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


ghost
requires x >= 1
requires n >= 0
requires IntPow2(n) <= x
requires x < IntPow2(n+1)
ensures Log2Floor_pure(x) == n
decreases x
pure
func Log2Floor_equal(x uint64, n uint64) uint64{
	return x < 2 ?
		// Base case: x== 1 && IntPow2(n) < 1 IntPow2(n+1)
		// n == 0
		0 :
		//Inductive case: x >= 2, x >=1
		// By I.H. Log2Floor(x/2) == n - 1
		Log2Floor_equal(x/2, n-1)
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
requires n>= 0
ensures IntPow2(n) >= 1
decreases n
pure
func IntPow2Positive(n uint64) uint64{
	return n==0 ? 1 : IntPow2Positive(n-1)
}


// Lemma: Weaker version of IntPow2IncLemma, i.e. forall a b :: IntPow2(a) <= IntPow2(b)
ghost
requires a >= 0
requires b >= 0
requires a <= b
ensures IntPow2(a) <= IntPow2(b)
decreases b - a
pure
func IntPow2Monotonic(a uint64, b uint64) uint64{
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
	//return tStar_pure_orig(t1 +1, t2+1, true)- 1
	return tStar_pure(t1 + 1, t2 +1 )-1
}


// Function: New TStar_pure, not using any booleans and recursion only.
// The reason why we can prove the whole stuff smoothly
ghost
requires 0 < t1
requires t1 < t2
ensures r > t1
ensures r <= t2
decreases
pure
func tStar_pure(t1 uint64, t2 uint64) (r uint64){
	return let i_low := Log2Floor_pure(t1) in
				tStarRec_pure(t1, t2, IntPow2(i_low), IntPow2(i_low+1))
}


//Function: Similar to the version we have for the binary search version
//The goal is to prove the equality of the binary search with TStar
// Essential for proving the properties.

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
// =============================Core Lemma======================================
/*@
// Core Lemma: Shows that tPure function indicates t1<r <= t2
// Original function, not used right now.
// Used for sightseeing and keep in memory which makes me suffer for months
ghost
requires t1 > 0
requires t2 > t1
ensures r >= 1
ensures t1 < r && r<=t2
decreases t1,t2
pure
func tStar_pure_orig(t1 uint64, t2 uint64, pick_lowest bool) (r uint64) {
    return let i_low := Log2Floor_pure(t1) in
           let i_high := Log2Floor_pure(t2) in
           let low_ := IntPow2(i_low) in
		   let bound_t1 := Log2FloorBounds(t1) in
		   let bound_t2 := Log2FloorBounds(t2) in
		   let i_low_positive := IntPow2Positive(i_low) in
           i_high > i_low ?
           		(let apply_gap := IntPow2GapLemma(i_low, i_high) in (pick_lowest ?
						IntPow2(i_low + 1) :
						IntPow2(i_high))) :
				(t1 == low_ ?														// We need to consider the case that low_ == t1 if t1 is a power of 2, so this would lead t1 - low_ to 0 and Log2Floor_pure(t1) is not defined.
					let apply_bounds := Log2FloorBounds(t2 - low_) in
					low_ + IntPow2(Log2Floor_pure(t2-low_)):
					low_ + tStar_pure_orig(t1 - low_,t2 - low_, false))

}
@*/

// @ requires base > 0
// =========Hyperproperties=====
// @ requires low(base)
// @ ensures low(r)
// =============================
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
// =========Hyperproperties=====
// @ requires low(t1) && low(t2)
// @ ensures low(t_star)
// =============================
// @ ensures t_star >= 1
// @ ensures t_star == TStar_pure(t1,t2)
// @ decreases
func TStar(t1 uint64, t2 uint64) (t_star uint64) {
	return tStar(t1+1, t2+1) - 1
}

// Older version of tStar, will not be used in the newer version
// @ requires t1 > 0
// @ requires t2 > t1
// =========Hyperproperties=====
// @ requires low(t1) && low(t2) && low(pick_lowest)
// @ ensures low(t_star)
// =============================
// @ ensures t_star == tStar_pure_orig(t1,t2,pick_lowest)
func tStar_orig(t1 uint64, t2 uint64, pick_lowest bool) (t_star uint64) {
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
			// This is also adapted in the proof of TStar_pure, which concludes the proof of t1 < r <= t2
			return low_ + PowOf2(Log2Floor(t2-low_))
		}

		// t1 > low_, safe to recurse normally
		return low_ + tStar_orig(t1-low_, t2-low_, false)
	}
}

// @ requires t1>0
// @ requires t2 > t1
// =========Hyperproperties=====
// @ requires low(t1) && low(t2)
// @ ensures low(t_star)
// =============================
// @ ensures t_star > t1 && t_star <= t2
// @ ensures tStar_pure(t1, t2) == t_star
// @ decreases
func tStar(t1 uint64, t2 uint64) (t_star uint64) {
	i_low := Log2Floor(t1)
	return tStarRec(t1, t2, PowOf2(i_low), PowOf2(i_low+1))
}

// @ requires t1 > 0
// @ requires t2 > t1
// @ requires t1 >= x_in
// @ requires t1 < x_out
// =========Hyperproperties=====
// @ requires low(t1) && low(t2) && low(x_in) && low(x_out)
// @ ensures low(r)
// =============================
// @ ensures r > t1 && r <= t2
// @ ensures r == tStarRec_pure(t1,t2,x_in, x_out)
// @ decreases x_out - x_in
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


//Function: Find the first element that target < 2^r - 1
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

// ==================================================================================
// ==================================================================================

// The element v is on path, i.e. v == next(x_in,x_out)
ghost
requires x_out > x_in
decreases x_out - x_in
pure
func isOnPath (v uint64, target uint64, x_in uint64, x_out uint64) bool{
	return x_in +1 >= x_out ? false :
		let next := x_in + (x_out - x_in)/2 in
			v == next ||
			(next <= target ?
				isOnPath(v,target, next, x_out):
				isOnPath(v,target, x_in, next))
}

//Lemma: When Log2Floor(t2) > Log2Floor(t1) ==> IntPow2(Log2Floor(t1)+1) <= t2

ghost
requires t1 >0
requires t2 > 0
requires Log2Floor_pure(t2) > Log2Floor_pure(t1)
ensures IntPow2(Log2Floor_pure(t1)+1) <= t2
decreases
pure
func GapImpliesPow2Bound(t1 uint64, t2 uint64) uint64{
	return let _:= Log2FloorBounds(t2) in
		let _:= IntPow2Monotonic(Log2Floor_pure(t1), Log2Floor_pure(t2)) in
		let _:= IntPow2Positive(Log2Floor_pure(t1)+1) in
		0
}


//Lemma: tStarRec returns the element of the bound because it's easy
ghost
decreases
requires x_in <= t1 && t1 < x_out
requires t1 > 0 && t1 < t2
requires x_out <= t2
ensures tStarRec_pure(t1,t2,x_in,x_out) == x_out
pure
func tStarRec_returns_expJumpBound(t1 uint64, t2 uint64, x_in uint64, x_out uint64) uint64{
	return 0
}



//Problem: For index-1 started stuff
//Solution: Make the 1 digit shifted!
ghost
requires x_in >= 1
requires x_out > x_in
requires v >= 1
requires target >= 1
requires isOnPath(v,target, x_in, x_out)
ensures isOnPath(v-1,target-1, x_in-1, x_out-1)
decreases x_out - x_in
pure
func isOnPath_shift(v uint64, target uint64, x_in uint64, x_out uint64) uint64{
	return x_in +1 >= x_out ? 0 :
		let next := x_in + (x_out - x_in)/2 in
			//next_shifted = x_in - 1 + (x_out-1 - x_in+1)/2 == next - 1
			v == next ? 0 : 			// v - 1 == next - 1 = next_shifted
			(next <= target ?
				isOnPath_shift(v,target, next, x_out):
				isOnPath_shift(v,target, x_in, next))
}

@*/
// ==============================================================================================
// =======================================On Path Lemmas=========================================

/*@
//Lemma: t2 is way more larger than x_out, so we return x_out in this case
// Easy case
ghost
requires target >= 0
requires t2 > target
requires Log2Floor_pure(t2 + 1) > Log2Floor_pure(target + 1)
ensures TStar_pure(target, t2) == expJumpElement(findExpLevel(target))
decreases
pure
func TStar_Gap_Upper(target uint64, t2 uint64) uint64{
	return let i_low := Log2Floor_pure(target+1) in
		let x_out := IntPow2(i_low+1) in
		let _:= GapImpliesPow2Bound(target+1, t2+1) in
		let _:= tStarRec_returns_expJumpBound(target+1, t2 +1, IntPow2(i_low), x_out) in
		0

}


//Lemma : t2 is way more smaller than x_in, so we return x_in in this case
// Also easy case
ghost
requires target >0
requires t2 >= 0
requires target > t2
requires Log2Floor_pure(target + 1) > Log2Floor_pure(t2 + 1)
ensures TStar_pure(t2,target) == expJumpElement(findExpLevel(t2))
decreases
pure
func TStar_Gap_Lower(target uint64, t2 uint64) uint64{
	return let i_low := Log2Floor_pure(t2+1) in
		let x_in := IntPow2(i_low+1) in
		let _:= GapImpliesPow2Bound(t2+1, target+1) in
		let _:= tStarRec_returns_expJumpBound(t2+1, target +1, IntPow2(i_low), x_in) in
		0

}



//Lemma: Assume same bucket UPPER: Generally speaking, we need to show TStar(target, t2) is on path torwards target
ghost
//annoying case 2.0
requires target >= 0
requires t2 > target
requires Log2Floor_pure(t2 + 1) == Log2Floor_pure(target + 1)
ensures let k:= findExpLevel(target) in
		let x_in := expJumpElement(k-1) in
		let x_out := expJumpElement(k) in
		isOnPath(TStar_pure(target,t2), target, x_in, x_out)
decreases
pure
func TStar_OnPath_Upper(target uint64, t2 uint64) uint64{
	return let i_low := Log2Floor_pure(t2+1) in
		let x_in := IntPow2(i_low) in
		let x_out := IntPow2(i_low+1) in
		// t1_arg = target + 1, t2_arg = t2 + 1, target_arg = target + 1
		// we need target = t2_arg
		//One can also strengthen the args using bounds and int2positive
		let _ := tStarRec_isOnPath_target(target + 1, t2 +1,target +1, x_in, x_out) in
		//Denotes tStarRec is on path when target is t1 or t2
		let _ := isOnPath_shift(tStar_pure(target+1, t2+1), target +1, x_in, x_out ) in
		//in index 1
		0
}


//Lemma: Assume same bucket LOWER: Generally speaking, we need to show TStar(t2, target) is on path torwards target
//Issue: shifted index by one, annoying case
//Solution: tStarRec_isOnPath_target solves this issue (additional lemma)
ghost
requires t2 >= 0
requires target > t2
requires Log2Floor_pure(t2 + 1) == Log2Floor_pure(target + 1)
ensures let k:= findExpLevel(target) in
		let x_in := expJumpElement(k-1) in
		let x_out := expJumpElement(k) in
		isOnPath(TStar_pure(t2,target), target, x_in, x_out)
decreases
pure
func TStar_OnPath_Lower(target uint64, t2 uint64) uint64{
	return let i_low := Log2Floor_pure(t2+1) in
	let x_in := IntPow2(i_low) in
	let x_out := IntPow2(i_low+1) in
	// t1_arg = t2 + 1, t2_arg = target + 1, target_arg = target + 1
	// we need target = t2_arg
	let _ := tStarRec_isOnPath_target(t2 + 1, target +1,target +1, x_in, x_out) in
	//Denotes tStarRec is on path when target is t1 or t2
	let _ := isOnPath_shift(tStar_pure(t2 +1, target+1), target +1, x_in, x_out ) in
	//in index 1
	0
}


//Shows that v is on path of the left side of the binary search steps
ghost
requires x_out > x_in
requires x_in + 1 < x_out
requires next == x_in + (x_out - x_in)/2
requires next > target
requires v != next
requires isOnPath(v,target,x_in,x_out)
ensures isOnPath(v,target,x_in,next)
decreases
pure
func isOnPath_subpath_left(v uint64, target uint64, x_in uint64,x_out uint64, next uint64) uint64{
	return 0
}



//Shows that v is on path of the right side of the binary search steps
ghost
requires x_out > x_in
requires x_in + 1 < x_out
requires next == x_in + (x_out - x_in)/2
requires next <= target
requires v != next
requires isOnPath(v,target,x_in,x_out)
ensures isOnPath(v,target,next,x_out)
decreases
pure
func isOnPath_subpath_right(v uint64, target uint64, x_in uint64,x_out uint64, next uint64) uint64{
	return 0
}
// ==============================================================================================
// ==============================================================================================



//tStarRec returns a midpoint on path when t2 < x_out given same bucket
// The is generally the step case where we go left or right
ghost
requires t1 > 0
requires t1 < t2
requires x_in <= t1 && t1 < x_out // Constraints on t1
requires t2 < x_out
ensures isOnPath(tStarRec_pure(t1,t2,x_in,x_out), t1, x_in, x_out)
decreases x_out - x_in
pure
func tStarRec_isOnPath(t1 uint64, t2 uint64, x_in uint64, x_out uint64) uint64{
	return x_in + 1 >= x_out ? 0 : //Base case: will not be handled here
		let next := x_in + (x_out-x_in)/2 in
		 //t2 < x_out ==> x_out <= t2 is false
		 // we take the recursive branch
		(next <= t1 ?
			// Go right: when next <= target
			tStarRec_isOnPath(t1,t2,next, x_out):
			// Go left: next > target
			// Need to check t2 < next
			(t2 < next ?
				// t2 >= next means tStarRec will return next a midpoint
				tStarRec_isOnPath(t1,t2,x_in,next) : 0))
}


//Lemma: Ensures that the next is on the path, i.e. v == next in isOnPath
ghost
requires target >= 0
requires x_in +1 < x_out
ensures let next := x_in + (x_out-x_in)/2 in isOnPath(next, target, x_in, x_out)
decreases x_out - x_in
pure
func midOnPath(target uint64, x_in uint64, x_out uint64) uint64{
	return 0
}


//Important lemma: returns next when t1 < next <= t2
// 2 steps
// 1. tStarRec(t1,t2,x_in,x_out) == tStarRec(t1,t2,x_in,next)
// 2. tStarRec(t1,t2,x_in,x_out) == next
ghost
requires t1 > 0
requires t1 < t2
requires x_in <= t1 && t1 < x_out
requires t2 < x_out
requires x_in +1 < x_out
requires let next := x_in + (x_out - x_in) / 2 in next > t1
requires let next := x_in + (x_out - x_in) / 2 in next <= t2
ensures let next := x_in + (x_out - x_in) / 2 in tStarRec_pure(t1,t2,x_in,x_out) == next 			//It exactly says that tStarRec RETURNS the value!
decreases x_out - x_in
pure
func tStarRec_returns_mid(t1 uint64, t2 uint64, x_in uint64, x_out uint64) uint64{
	return let next := x_in + (x_out - x_in) / 2 in
		let _:= tStarRec_returns_expJumpBound(t1,t2,x_in,next) in 0
}


// Lemma: Base case of the tStarRec_isOnPath
// Here, we have already found target == t1 and target == t2
//Problem: We need to show that tStarRec is on path of the target
ghost
requires t1 > 0
requires t1 < t2
requires x_in <= t1 && t1 < x_out // Constraints on t1
requires t2 < x_out
requires target == t1 || target == t2
ensures isOnPath(tStarRec_pure(t1,t2,x_in,x_out), target, x_in, x_out)
decreases x_out - x_in
pure
func tStarRec_isOnPath_target(t1 uint64, t2 uint64, target uint64, x_in uint64, x_out uint64) uint64{
	return x_in + 1 >= x_out ? 0 : //Base case
		let next := x_in + (x_out-x_in)/2 in
		(next <= t1 ?
			tStarRec_isOnPath_target(t1,t2,target,next, x_out):
			// Go left: next > target
			// Need to check t2 < next
			(t2 < next ?
				// t2 >= next means tStarRec will return next a midpoint
				tStarRec_isOnPath_target(t1,t2,target,x_in,next):
				//t1 < next <= t2
				// So v == mid is true, so isOnPath returns true
				let _ := tStarRec_returns_mid(t1, t2, x_in, x_out) in
				midOnPath(target, x_in, x_out)))
}

//Lemma: Link k with findExpLevel(target)
ghost
decreases
requires target >= 0
requires k > 0
requires IntPow2(k - 1) <= target + 1
requires IntPow2(k) > target + 1
ensures k == findExpLevel(target)
func findExpTarget_link_loop(target uint64, k uint64){
	// given IntPow2(k - 1) <= target + 1 < IntPow2(k)
	// By equal lemma: Log2Floor(target+1) == k - 1
	// So findExpLevel(target) == Log2Floor(target+1) +1 == k -1+1==k
	// Q.E.D
	Log2Floor_equal(target + 1, k - 1)
}


@*/

// ============================================================================================
// ======================================Core Lemma============================================

// @ requires target >= 0
// @ requires t2 >= 0
// @ requires t2 != target
// =========Hyperproperties=====
//
//	requires low(target) && low(t2)
//	ensures low(idx)
//
// =============================
// @ ensures acc(r)
// @ ensures 0<=idx && idx < len(r)
// @ ensures target < t2 ==> r[idx] == TStar_pure(target,t2)
// @ ensures t2 < target ==> r[idx] == TStar_pure(t2,target)
// @ ensures forall i uint64 :: 0<= i && i < len(r) ==> r[i] >= 0
// @ trusted //TODO
func FullBinaryLadderSteps(target uint64 /*@, ghost t2 uint64@*/) (r []uint64 /*@, ghost idx int@*/) {
	r = make([]uint64, 0)
	var i uint64 = 1
	// Denotes the length of the array r.
	//@ ghost var k uint64 = 0
	//@ ghost var foundTStar = false

	//@ invariant acc(r)
	//@ invariant k >= 0
	//@ invariant i == IntPow2(k)
	//@ invariant len(r) == int(k)
	//@ invariant forall j uint64 :: 0 <= j && j < len(r) ==> r[j] == expJumpElement(j)
	//@ invariant k == 0 || IntPow2(k - 1) <= target + 1 //Important invariant for the findExpTarget_link_loop in below
	//@ invariant low(i)
	for i-1 <= target {
		r = append( /*@ perm(1/2), @*/ r, i-1)
		i = i * 2
		//@ k = k+1
		//@ assert i-1 == expJumpElement(k)
	}

	// i is now the smallest power of two s.t. i-1 is larger than target
	//@ assert i > target
	var x_in uint64 = 0
	if len(r) > 0 {
		x_in = r[len(r)-1]
	}
	//@ assert x_in == expJumpElement(k-1)

	x_out := i - 1
	//@ assert x_out == expJumpElement(k)
	r = append( /*@ perm(1/2), @*/ r, x_out) // this will be the first proof of non-inclusion
	//@ assert r[int(k)] == expJumpElement(k)

	//@ findExpTarget_link_loop(target,k)
	//@ assert k == findExpLevel(target)

	/*@
	ghost if t2 > target{
		if Log2Floor_pure(t2 +1) > Log2Floor_pure(target +1){
			TStar_Gap_Upper(target, t2)
			idx = int(k)
			foundTStar = true 			// GAP case: we have found our TStar
		} else{
			//In this case, the element is on the binary search path between target and t2
			Log2FloorEqWhenNotGap_Upper(target, t2)
			TStar_OnPath_Upper(target, t2)
		}
	} else if t2 < target{
		if Log2Floor_pure(target +1) > Log2Floor_pure(t2 +1){
			TStar_Gap_Lower(target, t2)
			ghost var gapIdx uint64 = Log2Floor_pure(t2 + 1) + 1 	//The index consists of the lower exponential jump of t2.
			idx = int(gapIdx)
			foundTStar = true 			//GAP case
		} else {
			Log2FloorEqWhenNotGap_Lower(target, t2)
			TStar_OnPath_Lower(target, t2)
		}
	}
	@*/

	r /*@, idx @*/ = BinarySearchStep(target, r, x_in, x_out /*@, t2,k , idx, foundTStar@*/)

	return r /*@, idx@*/
}

// @ requires acc(r)
// @ requires x_in < x_out
//@ requires x_in >= 0
// @ requires target >= 0
// @ requires t2 >= 0
// @ requires k >=1
// @ requires 0 <= currIdx && currIdx < len(r)
// @ requires len(r) >= int(k) + 1
// @ requires forall i uint64 :: 0 <= i && i < k ==> r[i] == expJumpElement(i)
// @ requires r[k] == expJumpElement(k)
//@ requires forall l uint64 :: 0<= l && l < len(r) ==> r[l] >= 0
// The elements are on path of the binary search as soon as t2 and target are in the same bucket!
// ============= Case 1: t2 > target =============
// Either we have found TStar and the index shows that the element is TStar

// @ requires t2 > target && Log2Floor_pure(t2+1) > Log2Floor_pure(target+1) ==> (foundTStar && r[currIdx] == TStar_pure(target, t2))

// Or we are on path if they are still in the same bucket

// @ requires t2 > target && !(Log2Floor_pure(t2+1) > Log2Floor_pure(target+1)) ==> (foundTStar ==> r[currIdx] == TStar_pure(target, t2)) &&  (!foundTStar ==> isOnPath(TStar_pure(target, t2), target, x_in, x_out))
// ============= Case 1: t2 < target =============
// @ requires t2 < target && Log2Floor_pure(target+1) > Log2Floor_pure(t2+1) ==> (foundTStar && r[currIdx] == TStar_pure(t2, target))
// @ requires t2 < target && !(Log2Floor_pure(target+1) > Log2Floor_pure(t2+1)) ==> (foundTStar ==> r[currIdx] == TStar_pure( t2, target)) &&  (!foundTStar ==> isOnPath(TStar_pure(t2, target), target, x_in, x_out))
// @ requires k == findExpLevel(target)
// =========Hyperproperties=====
// @ requires low(target)
// @ requires low(r)
// @ requires low(x_in) && low(x_out)
// @ requires low(t2) && low(k) && low(currIdx) && low(foundTStar)
// @ ensures low(res)
// @ ensures low(resIdx)
// =============================
// @ ensures acc(res)
// @ ensures len(res) >= len(r)
// @ ensures 0<= resIdx && resIdx < len(res)
// @ ensures target < t2 ==> res[resIdx] == TStar_pure(target, t2)
// @ ensures t2 < target ==> res[resIdx] == TStar_pure(t2,target)
// @ ensures forall l uint64 :: 0<= l && l < len(res) ==> res[l] >= 0
// @ decreases x_out - x_in
// @ trusted //TODO
func BinarySearchStep(target uint64, r []uint64, x_in uint64, x_out uint64 /*@, ghost t2 uint64, ghost k uint64, ghost currIdx int, ghost foundTStar bool@*/) (res []uint64 /*@, ghost resIdx int@*/) {
	if x_in+1 >= x_out {
		return r /*@, currIdx@*/
	}
	next := x_in + (x_out-x_in)/2
	// @ assert low(next)
	//@ thisIdx := len(r)  //Keep track of the last element
	r = append( /*@ perm(1/2), @*/ r, next)

	//Assign gap case
	/*@
	ghost if t2 > target && !(Log2Floor_pure(t2 + 1) > Log2Floor_pure(target + 1)){
		if next == TStar_pure(target, t2){
			currIdx = thisIdx
			foundTStar = true
		}
	} else if t2 < target && !(Log2Floor_pure(target + 1) > Log2Floor_pure(t2 + 1)){
				if next == TStar_pure(t2, target){
			currIdx = thisIdx
			foundTStar = true
		}
	}
	@*/
	if next <= target {
		/*@
		ghost
		if !foundTStar{
			if t2 > target && !(Log2Floor_pure(t2 + 1) > Log2Floor_pure(target + 1)){
				isOnPath_subpath_right(TStar_pure(target, t2), target, x_in, x_out, next)
			}
			if t2 < target && !(Log2Floor_pure(target + 1) > Log2Floor_pure(t2 + 1)){
				isOnPath_subpath_right(TStar_pure(t2, target), target, x_in, x_out, next)
			}
		}
		@*/
		return BinarySearchStep(target, r, next, x_out /*@, t2,k, currIdx, foundTStar@*/)
	} else {
		/*@
		ghost
		if !foundTStar{
			if t2 > target && !(Log2Floor_pure(t2 + 1) > Log2Floor_pure(target + 1)){
				isOnPath_subpath_left(TStar_pure(target, t2), target, x_in, x_out, next)
			}
			if t2 < target && !(Log2Floor_pure(target + 1) > Log2Floor_pure(t2 + 1)){
				isOnPath_subpath_left(TStar_pure(t2, target), target, x_in, x_out, next)
		}}
		@*/
		return BinarySearchStep(target, r, x_in, next /*@, t2,k, currIdx, foundTStar@*/)
	}
}

/*@
ghost
ensures res > 0
decreases
pure
func GetInt() (res uint64)
@*/

// @ requires target >= 0
// @ requires low(target)
// @ ensures low(r1)
// @ ensures acc(r1)
// @ ensures forall t2 uint64 :: exists idx1 uint64 :: target < t2 ==> 0 <= idx1 && idx1 < len(r1) && TStar_pure(target, t2) == r1[idx1]
// @ ensures forall t2 uint64 :: exists idx2 uint64 ::target > t2 && t2 >= 0  ==> 0 <= idx2 && idx2 < len(r1) && TStar_pure(t2, target) == r1[idx2]
// @ trusted //TODO
func FullBinaryLadderSteps_wrapper(target uint64) (r1 []uint64) {
	//@ t2 := GetInt()
	//@ assume t2 != target
	//@ assume t2 >= 0 && low(t2)
	res /*@, idx @*/ := FullBinaryLadderSteps(target /*@, t2 @*/)
	//@ assert target < t2 ==>  TStar_pure(target, t2) == res[idx]
	//@ assert exists idx1 uint64 :: target < t2 ==> 0 <= idx1 && idx1 < len(res) && TStar_pure(target, t2) == res[idx1]
	//@ assume forall t2 uint64 :: exists idx1 uint64 :: target < t2 ==> 0 <= idx1 && idx1 < len(res) && TStar_pure(target, t2) == res[idx1]
	//@ assert target > t2 ==>  TStar_pure(t2, target) == res[idx]
	//@ assert exists idx1 uint64 :: target > t2 && t2 >= 0 ==> 0 <= idx1 && idx1 < len(res) && TStar_pure(t2,target) == res[idx1]
	//@ assume forall t2 uint64 :: exists idx1 uint64 :: target > t2 && t2 >= 0 ==> 0 <= idx1 && idx1 < len(res) && TStar_pure(t2,target) == res[idx1]
	return res
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
