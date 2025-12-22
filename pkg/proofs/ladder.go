package proofs

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


ghost
requires 0 < t1
requires t1 < t2
ensures r > t1
ensures r <= t2
decreases
pure
func tStar_pure(t1 uint64, t2 uint64) (r uint64){
	return let i_low := Log2Floor_pure(t1) in tStarRec_pure(t1, t2, IntPow2(i_low), IntPow2(i_low+1))
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
// @ decreases
func TStar(t1 uint64, t2 uint64) (t_star uint64) {
	return tStar(t1+1, t2+1) - 1
}

// Older version of tStar, will not be used in the newer version
// @ requires t1 > 0
// @ requires t2 > t1
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



// The element v is on path, i.e. v == mid(x_in,x_out)
ghost
requires x_in >=0
requires x_out > x_in
decreases x_out - x_in
pure
func isOnPath (v uint64, target uint64, x_in uint64, x_out uint64) bool{
	return x_in +1 >= x_out ? false :
		let mid := x_in + (x_out - x_in)/2 in
			v == mid ||
			(mid <= target ?
				isOnPath(v,target, mid, x_out):
				isOnPath(v,target, x_in, mid))
}
@*/
// ==============================================================================================
// =======================================On Path Lemmas=========================================

/*@
//TODO
ghost
requires target >= 0
requires t2 > target
requires Log2Floor_pure(t2 + 1) > Log2Floor_pure(target + 1)
ensures TStar_pure(target, t2) == expJumpElement(findExpLevel(target))
decreases
pure
func TStar_Gap_Upper(target uint64, t2 uint64) uint64


//TODO
ghost
requires t2 >= 0
requires target > t2
requires Log2Floor_pure(target + 1) > Log2Floor_pure(t2 + 1)
ensures TStar_pure(t2,target) == expJumpElement(findExpLevel(t2))
decreases
pure
func TStar_Gap_Lower(target uint64, t2 uint64) uint64


//TODO
ghost
requires target >= 0
requires t2 > target
requires Log2Floor_pure(t2 + 1) == Log2Floor_pure(target + 1)
ensures let k:= findExpLevel(target) in
		let x_in := expJumpElement(k-1) in
		let x_out := expJumpElement(k) in
		isOnPath(TStar_pure(target,t2), target, x_in, x_out)
decreases
pure
func TStar_OnPath_Upper(target uint64, t2 uint64) uint64
@*/
// ==============================================================================================

// ======================================Core Lemma============================================

// @ requires target > 0
// @ requires t2 > 0
// @ requires target != t2
// @ ensures acc(r)
//
//	 ensures 0<=idx && idx < len(r)
//
//		ensures target < t2 ==> r[idx] == TStar_pure(target,t2)
//		ensures t2 < target ==> r[idx] == TStar_pure(t2,target)
func FullBinaryLadderSteps(target uint64 /*@, ghost t2 uint64@*/) (r []uint64 /*@, ghost idx int@*/) {
	r = make([]uint64, 0)
	var i uint64 = 1
	// Denotes the length of the array r.
	//@ ghost var k uint64 = 0

	//@ invariant acc(r)
	//@ invariant k >= 0
	//@ invariant i == IntPow2(k)
	//@ invariant len(r) == int(k)
	//@ invariant forall j uint64 :: 0 <= j && j < len(r) ==> r[j] == expJumpElement(j)
	for i-1 <= target {
		r = append( /*@ perm(1/2), @*/ r, i-1)
		i = i * 2
		//@ k = k+1
		//@ assert i-1 == expJumpElement(k)
	}

	// i is now the smallest power of two s.t. i-1 is larger than target
	//@ assert i > target
	// assert k > Log2Floor_pure(target)
	var x_in uint64 = 0
	if len(r) > 0 {
		x_in = r[len(r)-1]
		//@ assert x_in == expJumpElement(k-1)
	}

	x_out := i - 1
	//@ assert x_out == expJumpElement(k)
	r = append( /*@ perm(1/2), @*/ r, x_out) // this will be the first proof of non-inclusion
	//@ assert r[int(k)] == expJumpElement(k)
	// assert k == findExpLevel(target)

	/*@
		ghost
		if t2 > i {
			Log2FloorMonotonic(i, t2)
			Log2FloorMonotonic(target, i)
			assert Log2Floor_pure(t2) >= Log2Floor_pure(i)
			assert Log2Floor_pure(i) >= Log2Floor_pure(target)
			assume Log2Floor_pure(t2) > Log2Floor_pure(target)
			assert t2 > target
			idx = len(r) - 1
			assert r[idx] == i-1
			//assert TStar_pure(target, t2) == i - 1
			//assert r[idx] == TStar_pure(target,t2)
		}
	@*/
	res /*@, index@*/ := BinarySearchStep(target, r, x_in, x_out /*@, t2, idx@*/)

	// Main core theorem to PROVE postcondition >.<
	/*@
	ghost
	if i <= t2{
		//idx = index
		assume false
	}
	@*/

	r = res

	return r /*@, idx@*/
}

// @ requires acc(r)
// @ requires x_in <= x_out
// @ requires target >= 0
// @ requires t2 >= 0
// @ ensures acc(res)
//
//	ensures target < t2 ==> res[resIdx] == TStar_pure(target, t2)
//	ensures t2 < target ==> res[resIdx] == TStar_pure(t2,target)
//
// @ decreases x_out - x_in
func BinarySearchStep(target uint64, r []uint64, x_in uint64, x_out uint64 /*@, ghost t2 uint64, ghost currIdx int@*/) (res []uint64 /*@, ghost resIdx int@*/) {
	if x_in+1 >= x_out {
		return r /*@, currIdx@*/
	}
	next := x_in + (x_out-x_in)/2
	r = append( /*@ perm(1/2), @*/ r, next)
	if next <= target {
		return BinarySearchStep(target, r, next, x_out /*@, t2, currIdx@*/)
	} else {
		return BinarySearchStep(target, r, x_in, next /*@, t2, currIdx@*/)
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
func FullBinaryLadderSteps_wrapper(target uint64) (r1 []uint64, r2 []uint64) {

	//@ t2 := GetInt()

	//@ assume t2 != target
	//@ assume t2 > target
	res /*@, idx@*/ := FullBinaryLadderSteps(target /*@, t2 @*/)

	// assert isInLadder(TStar_pure(target, t2), target)

	//@ assume t2 < target
	res2 /*@, idx2@*/ := FullBinaryLadderSteps(target /*@, t2 @*/)
	//  assert isInLadder(TStar_pure(t2, target), target)
	return res, res2
}

// @ requires target > 0
// @ requires t2 > 0
// @ requires target != t2
// @ ensures acc(r)
// @ ensures idx >= 0 && idx < len(r)
//
//	ensures target < t2 ==> r[idx] == TStar_pure(target,t2)
//	ensures t2 < target ==> r[idx] == TStar_pure(t2,target)
func FBLS_cursed(target uint64 /*@, ghost t2 uint64 @*/) (r []uint64 /*@, ghost idx int @*/) {
	r = make([]uint64, 0)

	k := Log2Floor(target+1) + 1
	//@ assert k == findExpLevel(target)
	//@ ghost var foundTStar bool = false

	var j uint64 = 0
	//@ idx = 0

	//@ invariant acc(r)
	//@ invariant j >= 0 && j <= k
	//@ invariant len(r) == int(j)
	//@ invariant forall i uint64 :: 0 <= i && i < len(r) ==> r[i] == expJumpElement(i)
	for j < k {
		element := PowOf2(j) - 1
		r = append( /*@ perm(1/2), @*/ r, element)
		//@ assert element == expJumpElement(j)
		j = j + 1
	}

	//@ assert len(r) == int(k)
	x_out := PowOf2(k) - 1
	//@ assert x_out == expJumpElement(k)

	x_in := PowOf2(k-1) - 1
	//@ assert x_in == expJumpElement(k-1)

	r = append( /*@ perm(1/2), @*/ r, x_out)
	//@ assert r[k] == expJumpElement(k)

	/*@
	ghost if t2 > target{
		if Log2Floor_pure(t2 +1) > Log2Floor_pure(target +1){
			TStar_Gap_Upper(target, t2)
			idx = int(k)
			foundTStar = true // GAP case: we have found our TStar
		} else{
			//In this case, the element is on the binary search path between target and t2
			Log2FloorEqWhenNotGap_Upper(target, t2)
			TStar_OnPath_Upper(target, t2)
		}
	} else{
		if Log2Floor_pure(target +1) > Log2Floor_pure(t2 +1){
			TStar_Gap_Lower(target, t2)
			ghost var gapIdx uint64 = Log2Floor_pure(t2 + 1) + 1 	//The index consists of the lower exponential jump of t2.
			idx = int(gapIdx)
			foundTStar = true 		//GAP case
		} else {
			assume true
		}
	}
	@*/

	r /*@, idx @*/ = BinarySearchStep(target, r, x_in, x_out /*@, t2, idx@*/)
	//@ assert acc(r)
	//@ assume idx >= 0 && idx < len(r)
	return r /*@, idx@*/

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
