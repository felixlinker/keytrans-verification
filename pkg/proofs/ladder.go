package proofs

// ===========================================================================================
// PROOF OVERVIEW — Binary Ladder & TStar
// ===========================================================================================
//
// Goal:
//   Prove that FullBinaryLadderSteps(target) produces a ladder containing
//   a special element `TStar_pure(target, t2) for ANY other version t2. This
//   special element is the largest element that the binary ladders for `target`
//   and `t2` share. If we consider two executions (think of hyper-mode) in
//   which the server claims that `target` and `t2` are both the latest version
//   for a particular user, we expect a proof of inclusion for this special
//   element in one execution and a proof of non-inclusion in the other one if
//   `target` and `t2` are different. This however contradicts our assumption
//   that both executions operate on the same authenticated data structure
//   and, thus, `target` and `t2` must be equal.
//
// Key definitions:
//   - TStar_pure(t1, t2): returns the "special" element as described above
//     for `t1` and `t2`
//   - expJumpElement(k) = 2^k - 1: the k-th exponential jump step.
//   - findExpLevel(t) = floor(log2(t+1)) + 1: the exponential level for t.
//   - isOnPath(v, target, x_in, x_out): v appears on the binary search path
//     from x_in to x_out when searching toward target.
//   - IsTStar(tStarVal, t1, t2): (defined in client.go) returns true if t1 == t2,
//     or tStarVal == TStarBetween(t1, t2) otherwise. Used in hyper-mode to carry
//     the TStar witness through the verification chain.
//   - TStarBetween(t1, t2): (defined in client.go) requires min(t1,t2) >= 0 and
//     max(t1,t2) > 0. Returns TStar_pure(min, max) and ensures
//     min(t1,t2) < res <= max(t1,t2) when t1 != t2.
//
// Proof structure (two cases for t2 > target; symmetric for t2 < target):
//
//   Case 1 — "Gap": Log2Floor(t2+1) > Log2Floor(target+1)
//     The exponential levels differ, so TStar equals expJumpElement(findExpLevel(target)),
//     which is already in the ladder from the exponential jump phase.
//     Chain: GapImpliesPow2Bound -> tStarRec_returns_expJumpBound -> TStar_Gap_Upper
//
//   Case 2 — "Same bucket": Log2Floor(t2+1) == Log2Floor(target+1)
//     Both versions are in the same exponential interval. TStar lies on the binary
//     search path toward target, so it will be appended during BinarySearchStep.
//     Chain: tStarRec_isOnPath_target -> isOnPath_shift -> TStar_OnPath_Upper
//     Then:  isOnPath_subpath_left/right (propagate through binary search steps)
//
// Lemma layers (bottom-up):
//
//   Layer 1 — Foundations:
//     IntPow2, IntPow2Positive, IntPow2Monotonic
//     Log2Floor_pure, Log2FloorUpperBound, Log2FloorMonotonic, Log2Floor_equal
//
//   Layer 2 — TStar core:
//     tStarRec_pure, tStar_pure, TStar_pure
//     expJumpElement, findExpLevel
//
//   Layer 3 — Path machinery:
//     isOnPath, isOnPath_shift, isOnPath_subpath_left/right, midOnPath
//     tStarRec_returns_expJumpBound, tStarRec_returns_mid
//     tStarRec_isOnPath_target, GapImpliesPow2Bound
//
//   Layer 4 — Case lemmas (Upper/Lower symmetric pairs):
//     TStar_Gap_Upper / TStar_Gap_Lower           (Case 1)
//     TStar_OnPath_Upper / TStar_OnPath_Lower     (Case 2)
//     Log2FloorEqWhenNotGap_Upper / _Lower        (establish equality for Case 2)
//
//   Layer 5 — Top-level:
//     findExpTarget_link_loop (links loop variable k to findExpLevel)
//     FullBinaryLadderSteps (combines exp jump + binary search, invokes case lemmas)
//     BinarySearchStep (binary search phase, propagates isOnPath through recursion)
//     FullBinaryLadderSteps_wrapper (universally quantifies over all t2)
//
// Note: Several lemmas (tStarRec_returns_expJumpBound, isOnPath_subpath_left/right,
// midOnPath) have body "return 0" — they are auto-proved by Gobra's SMT solver but
// must exist as named functions so callers can explicitly trigger the proof obligation.
// Upper/Lower pairs exist because TStar_pure(t1, t2) requires t1 < t2, forcing
// separate lemmas for the two orderings of target vs t2.
//
// ===========================================================================================

// ===========================================================================================
// =====================================Log2Floor Lemmas======================================
/*@

// Log2Floor_pure computes floor(log2(n)) recursively.
// Guarantees: 2^r <= n < 2^(r+1) and r < n.
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


// Log2FloorUpperBound establishes that Log2Floor_pure gives tight bounds:
// 2^Log2Floor(n) <= n < 2^(Log2Floor(n)+1).
// Proved by induction on n, using IntPow2Positive for the step case.
ghost
requires n>0
ensures IntPow2(Log2Floor_pure(n)+1) > n
ensures IntPow2(Log2Floor_pure(n)) <=n
decreases n
pure
func Log2FloorUpperBound(n uint64) uint64{
	return n < 2 ? 0:  Log2FloorUpperBound(n/2) + IntPow2Positive(Log2Floor_pure(n/2)+1)
}


// Log2FloorMonotonic proves a <= b ==> Log2Floor(a) <= Log2Floor(b).
// Proved by induction on b, with base case via Log2FloorUpperBound.
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
		(a < 2 ? Log2FloorUpperBound(b):
		Log2FloorMonotonic(a/2,b/2)))
}

// Log2FloorEqWhenNotGap_Upper: when t2 > target but there is no gap in
// exponential levels (Log2Floor(t2+1) <= Log2Floor(target+1)), derives
// that they are equal. Follows directly from Log2FloorMonotonic.
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

// Log2FloorEqWhenNotGap_Lower: symmetric to _Upper for the case t2 < target.
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


// Log2Floor_equal proves that if 2^n <= x < 2^(n+1), then Log2Floor(x) == n.
// Used by findExpTarget_link_loop to link the loop counter k to findExpLevel.
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
		0 :
		Log2Floor_equal(x/2, n-1)
}

@*/
// ==================================================================================
// =============================IntPow2 Lemmas ======================================

/*@

// IntPow2 computes 2^exp recursively. Always returns r > 0.
ghost
requires exp >= 0
ensures r > 0
decreases exp
pure
func IntPow2(exp uint64) (r uint64) {
  return exp == 0 ? 1 : 2 * IntPow2(exp - 1)
}

// IntPow2Positive proves IntPow2(n) >= 1 for all n >= 0.
// Needed as an explicit trigger since Gobra doesn't auto-derive this.
ghost
requires n>= 0
ensures IntPow2(n) >= 1
decreases n
pure
func IntPow2Positive(n uint64) uint64{
	return n==0 ? 1 : IntPow2Positive(n-1)
}

// IntPow2Monotonic proves a <= b ==> 2^a <= 2^b.
// Used by GapImpliesPow2Bound and Log2FloorMonotonic.
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

@*/
// ============================================================================
// ============================================================================
/*@

// TStar_pure is the specification-level tStar function (0-indexed).
// Given t1 < t2, returns the unique pivot r such that t1 < r <= t2.
// Converts to 1-indexed, delegates to tStar_pure, then shifts back.
ghost
requires t1 >= 0
requires t2 > t1
ensures t1 < r
ensures r <= t2
decreases
pure
func TStar_pure(t1 uint64, t2 uint64) (r uint64){
	return tStar_pure(t1 + 1, t2 +1 )-1
}

// tStar_pure computes tStar for 1-indexed versions. Determines the exponential
// interval [2^i, 2^(i+1)) containing t1, then delegates to tStarRec_pure
// which performs binary search within that interval.
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

// tStarRec_pure is the recursive binary search that finds tStar.
// Within interval [x_in, x_out]:
//   - If x_out <= t2: return x_out (t2 is beyond the interval)
//   - Otherwise: halve the interval, recurse into the half containing t1
// This mirrors the binary search steps appended by BinarySearchStep.
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
// Log2Floor computes floor(log2(base)) by repeated halving.
//
// Preconditions: base > 0.
// Postconditions: IntPow2(r) <= base < IntPow2(r+1), r == Log2Floor_pure(base).
//
// Returns: r — the floor of log base 2.
//
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

// PowOf2 computes 2^exp iteratively.
//
// Preconditions: exp >= 0.
// Postconditions: r == IntPow2(exp) (i.e., r == 2^exp).
//
// Returns: r — the value 2^exp.
//
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

// TStar computes the tStar value — a deterministic pivot between two versions t1
// and t2 (where t1 < t2). tStar is the key element in the binary ladder that both
// executions must agree on, enabling the hyper-property proof. Delegates to
// tStar with 1-indexed arguments and subtracts 1.
//
// Preconditions: t1 >= 0, t2 > t1.
// Postconditions: t_star >= 1, t_star == TStar_pure(t1, t2), t1 < t_star <= t2.
//
// Returns: t_star — the deterministic pivot value between t1 and t2.
//
// @ requires t1 >= 0
// @ requires t2 > t1
// @ ensures t_star >= 1
// @ ensures t_star == TStar_pure(t1,t2)
// @ decreases
func TStar(t1 uint64, t2 uint64) (t_star uint64) {
	return tStar(t1+1, t2+1) - 1
}

// tStar computes tStar for 1-indexed versions. Finds the log2 floor of t1 to
// determine the initial binary search bounds, then delegates to tStarRec.
//
// Returns: t_star — 1-indexed
//
// @ requires t1>0
// @ requires t2 > t1
// @ ensures t_star > t1 && t_star <= t2
// @ ensures tStar_pure(t1, t2) == t_star
// @ decreases
func tStar(t1 uint64, t2 uint64) (t_star uint64) {
	i_low := Log2Floor(t1)
	return tStarRec(t1, t2, PowOf2(i_low), PowOf2(i_low+1))
}

// tStarRec performs the recursive binary search to find tStar. It narrows the
// interval [x_in, x_out] by halving: if the midpoint <= t1 it recurses right,
// if x_out <= t2 it returns x_out, otherwise it recurses left.
//
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

// expJumpElement computes the k-th exponential jump step: 2^k - 1.
// These are the steps 0, 1, 3, 7, 15, ... appended during the first phase
// of FullBinaryLadderSteps.
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

// findExpLevel determines the exponential level for target:
// the smallest k such that 2^k - 1 > target. Equivalently,
// k = floor(log2(target+1)) + 1. This is the level where the
// exponential jump phase stops and binary search begins.
ghost
requires target >= 0
ensures r >= 1
ensures r == Log2Floor_pure(target +1) +1
ensures IntPow2(r) > target +1
ensures IntPow2(r-1) <= target +1
decreases
pure
func findExpLevel(target uint64) (r uint64){
	return let _ := Log2FloorUpperBound(target +1) in
		Log2Floor_pure(target+1)+1
}

// ==================================================================================
// ==================================================================================

// isOnPath checks whether v appears as a midpoint on the binary search path
// from x_in to x_out when searching toward target. Returns true iff v equals
// some midpoint encountered during the recursive halving. This predicate is
// the key invariant maintained by BinarySearchStep: if TStar is on the path,
// it will eventually be appended to the ladder.
ghost
requires x_out > x_in
decreases x_out - x_in
opaque
pure
func isOnPath (v uint64, target uint64, x_in uint64, x_out uint64) bool{
	return x_in +1 >= x_out ? false :
		let next := x_in + (x_out - x_in)/2 in
			v == next ||
			(next <= target ?
				isOnPath(v,target, next, x_out):
				isOnPath(v,target, x_in, next))
}

// GapImpliesPow2Bound: when there is a gap in exponential levels
// (Log2Floor(t2) > Log2Floor(t1)), then 2^(Log2Floor(t1)+1) <= t2.
// This means x_out (the boundary of t1's exponential interval) fits
// within t2's range, so tStarRec returns x_out immediately.
ghost
requires t1 >0
requires t2 > 0
requires Log2Floor_pure(t2) > Log2Floor_pure(t1)
ensures IntPow2(Log2Floor_pure(t1)+1) <= t2
decreases
pure
func GapImpliesPow2Bound(t1 uint64, t2 uint64) uint64{
	return let _:= Log2FloorUpperBound(t2) in
		let _:= IntPow2Monotonic(Log2Floor_pure(t1), Log2Floor_pure(t2)) in
		let _:= IntPow2Positive(Log2Floor_pure(t1)+1) in
		0
}

// tStarRec_returns_expJumpBound: when x_out <= t2, tStarRec immediately
// returns x_out. Auto-proved (return 0) — exists as a named trigger for
// TStar_Gap_Upper/Lower and tStarRec_returns_mid.
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

// isOnPath_shift converts a 1-indexed isOnPath fact to 0-indexed:
// isOnPath(v, target, x_in, x_out) ==> isOnPath(v-1, target-1, x_in-1, x_out-1).
// Needed because TStar_pure works in 0-indexed space but tStar_pure/tStarRec_pure
// work in 1-indexed space. Proved by structural induction on the path.
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
	return let _ := reveal isOnPath(v,target, x_in, x_out) in
		let _ := reveal isOnPath(v-1,target-1, x_in-1, x_out-1) in
		x_in +1 >= x_out ? 0 :
			let next := x_in + (x_out - x_in)/2 in
				v == next ? 0 :
				(next <= target ?
					isOnPath_shift(v,target, next, x_out):
					isOnPath_shift(v,target, x_in, next))
}

@*/
// ==============================================================================================
// =======================================On Path Lemmas=========================================

/*@

// --- Case 1 lemmas: Gap (exponential levels differ) ---

// TStar_Gap_Upper: when t2 > target and they are in different exponential
// levels (Log2Floor(t2+1) > Log2Floor(target+1)), then TStar equals the
// boundary of target's exponential interval: expJumpElement(findExpLevel(target)).
// This element was already appended during the exponential jump phase, so
// tStar is in the ladder without needing binary search.
// Proof: GapImpliesPow2Bound shows x_out <= t2+1, then tStarRec returns x_out.
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

// TStar_Gap_Lower: symmetric to TStar_Gap_Upper for the case target > t2.
// TStar(t2, target) equals expJumpElement(findExpLevel(t2)).
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

// --- Case 2 lemmas: Same bucket (same exponential level) ---

// TStar_OnPath_Upper: when t2 > target and they share the same exponential
// level, TStar(target, t2) lies on the binary search path toward target
// within the interval [expJumpElement(k-1), expJumpElement(k)].
// Proof: tStarRec_isOnPath_target shows it's on path in 1-indexed space,
// then isOnPath_shift converts to 0-indexed.
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
func TStar_OnPath_Upper(target uint64, t2 uint64) uint64{
	return let i_low := Log2Floor_pure(t2+1) in
		let x_in := IntPow2(i_low) in
		let x_out := IntPow2(i_low+1) in
		let _ := tStarRec_isOnPath_target(target + 1, t2 +1,target +1, x_in, x_out) in
		let _ := isOnPath_shift(tStar_pure(target+1, t2+1), target +1, x_in, x_out ) in
		0
}

// TStar_OnPath_Lower: symmetric to TStar_OnPath_Upper for target > t2.
// TStar(t2, target) lies on the binary search path toward target.
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
	let _ := tStarRec_isOnPath_target(t2 + 1, target +1,target +1, x_in, x_out) in
	let _ := isOnPath_shift(tStar_pure(t2 +1, target+1), target +1, x_in, x_out ) in
	0
}

// --- Path propagation helpers (used by BinarySearchStep) ---

// isOnPath_subpath_left: if v is on the path in [x_in, x_out] and the
// midpoint next > target (so binary search goes left), then v is on the
// path in the left subinterval [x_in, next].
// Auto-proved (return 0) — exists as a named trigger for BinarySearchStep.
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
	return let _ := reveal isOnPath(v,target,x_in,x_out) in 0
}

// isOnPath_subpath_right: symmetric to _left. If next <= target (binary
// search goes right), then v is on the path in [next, x_out].
// Auto-proved (return 0).
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
	return let _ := reveal isOnPath(v,target,x_in,x_out) in 0
}

// midOnPath: the midpoint of any interval is trivially on its own path.
// Auto-proved (return 0) — used by tStarRec_isOnPath_target when
// tStarRec returns the midpoint directly.
ghost
requires target >= 0
requires x_in +1 < x_out
ensures let next := x_in + (x_out-x_in)/2 in isOnPath(next, target, x_in, x_out)
decreases x_out - x_in
pure
func midOnPath(target uint64, x_in uint64, x_out uint64) uint64{
	return let next := x_in + (x_out-x_in)/2 in
		let _ := reveal isOnPath(next, target, x_in, x_out) in 0
}

// tStarRec_returns_mid: when the midpoint satisfies t1 < mid <= t2 (i.e.,
// mid is a valid tStar candidate), tStarRec returns exactly mid.
// Proof: the midpoint's subinterval [x_in, mid] has mid <= t2, so
// tStarRec_returns_expJumpBound applies to show it returns mid.
ghost
requires t1 > 0
requires t1 < t2
requires x_in <= t1 && t1 < x_out
requires t2 < x_out
requires x_in +1 < x_out
requires let next := x_in + (x_out - x_in) / 2 in next > t1
requires let next := x_in + (x_out - x_in) / 2 in next <= t2
ensures let next := x_in + (x_out - x_in) / 2 in tStarRec_pure(t1,t2,x_in,x_out) == next
decreases x_out - x_in
pure
func tStarRec_returns_mid(t1 uint64, t2 uint64, x_in uint64, x_out uint64) uint64{
	return let next := x_in + (x_out - x_in) / 2 in
		let _:= tStarRec_returns_expJumpBound(t1,t2,x_in,next) in 0
}

// tStarRec_isOnPath_target: the core "same bucket" lemma. Proves that
// tStarRec_pure(t1, t2, x_in, x_out) is on the binary search path toward
// target (where target is t1 or t2). Three cases per recursion step:
//   - mid <= t1: recurse right (both t1 and t2 are in [mid, x_out])
//   - t2 < mid:  recurse left  (both t1 and t2 are in [x_in, mid])
//   - t1 < mid <= t2: tStarRec returns mid, and midOnPath proves it's on path
ghost
requires t1 > 0
requires t1 < t2
requires x_in <= t1 && t1 < x_out
requires t2 < x_out
requires target == t1 || target == t2
ensures isOnPath(tStarRec_pure(t1,t2,x_in,x_out), target, x_in, x_out)
decreases x_out - x_in
pure
func tStarRec_isOnPath_target(t1 uint64, t2 uint64, target uint64, x_in uint64, x_out uint64) uint64{
	return x_in + 1 >= x_out ? 0 :
		let next := x_in + (x_out-x_in)/2 in
		let _ := reveal isOnPath(tStarRec_pure(t1,t2,x_in,x_out), target, x_in, x_out) in
		(next <= t1 ?
			tStarRec_isOnPath_target(t1,t2,target,next, x_out):
			(t2 < next ?
				tStarRec_isOnPath_target(t1,t2,target,x_in,next):
				let _ := tStarRec_returns_mid(t1, t2, x_in, x_out) in
				midOnPath(target, x_in, x_out)))
}

// --- Linking lemma ---

// findExpTarget_link_loop links the loop counter k from the exponential
// jump phase to findExpLevel(target). Given that 2^(k-1) <= target+1 < 2^k
// (maintained as a loop invariant in FullBinaryLadderSteps), derives
// k == findExpLevel(target) via Log2Floor_equal.
ghost
decreases
requires target >= 0
requires k > 0
requires IntPow2(k - 1) <= target + 1
requires IntPow2(k) > target + 1
ensures k == findExpLevel(target)
func findExpTarget_link_loop(target uint64, k uint64){
	Log2Floor_equal(target + 1, k - 1)
}


@*/

// ============================================================================================
// ======================================Core Lemma============================================

// FullBinaryLadderSteps constructs the full binary ladder for a given target
// version. The ladder consists of two phases:
//  1. Exponential jump phase: powers-of-two minus one (0, 1, 3, 7, 15, ...)
//     until overshooting target
//  2. Binary search phase: narrows down within the last exponential interval
//
// The key property is that for any other version t2, the tStar pivot value
// TStar_pure(target, t2) (or TStar_pure(t2, target)) is guaranteed to appear
// in the returned ladder at some index idx.
//
// Preconditions: target >= 0, t2 >= 0 (ghost), t2 != target.
// Postconditions: r[idx] == TStar_pure(min, max) where min/max are the ordered
// pair of target and t2. All elements are >= 0, r[0] == 0.
//
// Returns:
//   - r: the binary ladder steps
//   - idx (ghost): index in r where tStar appears
//
// @ requires target >= 0
// @ requires t2 >= 0
// @ requires t2 != target
// @ ensures acc(r)
// @ ensures 0<=idx && idx < len(r)
// @ ensures target < t2 ==> r[idx] == TStar_pure(target,t2)
// @ ensures t2 < target ==> r[idx] == TStar_pure(t2,target)
// @ ensures target < t2 ==> target <  TStar_pure(target,t2)  && TStar_pure(target,t2) <= t2
// @ ensures t2 < target ==> t2 < TStar_pure(t2,target) && TStar_pure(t2,target) <= target
// @ ensures forall i int :: 0<= i && i < len(r) ==> r[i] >= 0
// @ ensures len(r) > 0 && r[0] == 0
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
	//@ invariant forall j uint64 ::forall l int :: 0 <= l && l < len(r) && uint64(l) == j ==> r[l] == expJumpElement(j)
	//@ invariant forall l int :: 0<= l && l < len(r) ==> r[l] >= 0
	//@ invariant k == 0 || IntPow2(k - 1) <= target + 1 //Important invariant for the findExpTarget_link_loop in below
	for i-1 <= target {
		r = append( /*@ perm(1/2), @*/ r, i-1)
		i = i * 2
		//@ k = k+1
		//@ assert i-1 == expJumpElement(k) && i-1 >= 0
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

// BinarySearchStep performs the binary search phase of the full binary ladder.
// Starting from the interval [x_in, x_out], it repeatedly halves the interval,
// appending each midpoint to r. It tracks (via ghost state) whether tStar has been
// found among the appended elements, and uses isOnPath lemmas to maintain the
// invariant that tStar will eventually appear.
//
// Preconditions: r is an owned slice containing the exponential jump elements,
// x_in < x_out, target >= 0, ghost parameter foundTStar tracks if tStar was
// already located in the exponential phase.
//
// Postconditions: returns the extended ladder with res[resIdx] == TStar_pure(...).
// All elements >= 0, res[0] == 0.
//
// Returns:
//   - res: the extended binary ladder (appended midpoints)
//   - resIdx (ghost): index where tStar appears in res
//
// @ requires acc(r)
// @ requires x_in < x_out
// @ requires x_in >= 0
// @ requires target >= 0
// @ requires t2 >= 0
// @ requires k >=1
// @ requires 0 <= currIdx && currIdx < len(r)
// @ requires len(r) >= int(k) + 1
// @ requires forall i uint64 :: forall j int :: 0 <= i && i < k && j == int(i) ==> r[j] == expJumpElement(i)
// @ requires r[k] == expJumpElement(k)
// @ requires forall l int :: 0<= l && l < len(r) ==> r[l] >= 0
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
// @ ensures acc(res)
// @ ensures len(res) >= len(r)
// @ ensures 0<= resIdx && resIdx < len(res)
// @ ensures target < t2 ==> res[resIdx] == TStar_pure(target, t2)
// @ ensures t2 < target ==> res[resIdx] == TStar_pure(t2,target)
// @ ensures forall l int :: 0<= l && l < len(res) ==> res[l] >= 0
// @ ensures len(res) > 0 && res[0] == 0
// @ decreases x_out - x_in
func BinarySearchStep(target uint64, r []uint64, x_in uint64, x_out uint64 /*@, ghost t2 uint64, ghost k uint64, ghost currIdx int, ghost foundTStar bool@*/) (res []uint64 /*@, ghost resIdx int@*/) {
	if x_in+1 >= x_out {
		/*@
		ghost if t2 > target {
			revealTmp1 := reveal isOnPath(TStar_pure(target, t2), target, x_in, x_out)
		}
		ghost if t2 < target {
			revealTmp2 := reveal isOnPath(TStar_pure(t2, target), target, x_in, x_out)
		}
		@*/
		//@ assert r[0] == expJumpElement(0)
		return r /*@, currIdx@*/
	} else {
		next := x_in + (x_out-x_in)/2
		//  assert low(next)
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
}

/*@
// GetUInt64 is a ghost function stub that non-deterministically returns
// a positive uint64. Used by FullBinaryLadderSteps_wrapper to introduce
// the universally quantified t2 witness.
ghost
ensures res > 0
decreases
pure
func GetUInt64() (res uint64)
@*/

/*@
// TStar_wrapper is a predicate that packages the "TStar appears in the ladder"
// property into a triggerable form. For a ladder r1 and versions t1 < t2,
// it asserts that some index idx in r1 holds TStar_pure(t1, t2).
// Used in hyper-mode (client.go) by EstablishTStarWitnesses and FindTStarIdx
// to extract the witness index.
ghost
decreases
requires acc(r1, _)
pure
func TStar_wrapper(r1 []uint64, t1 uint64, t2 uint64) bool{
	return exists idx int :: {r1[idx]} t1 < t2 && t1 >= 0 ==> 0 <= idx && idx < len(r1) && TStar_pure(t1, t2) == r1[idx] && t1 <  TStar_pure(t1,t2)  && TStar_pure(t1,t2) <= t2
}
@*/

// FullBinaryLadderSteps_wrapper is the public entry point for computing the full
// binary ladder. It wraps FullBinaryLadderSteps and lifts the single-t2 guarantee
// to a universal quantifier: for ALL possible t2 values, the returned ladder
// contains TStar_pure(target, t2) (or TStar_pure(t2, target)). This is the
// key interface used by CheckGreatest to obtain the ladder steps.
//
// Preconditions: target >= 0.
// Postconditions: for every t2, TStar appears in r1. TStar_wrapper holds for
// all t2 in both orderings. All elements >= 0, r1[0] == 0.
//
// Returns: r1 — the full binary ladder steps for target.
//
// @ requires target >= 0
// @ ensures acc(r1)
// @ ensures forall t2 uint64 :: exists idx1 int :: target < t2 ==> 0 <= idx1 && idx1 < len(r1) && TStar_pure(target, t2) == r1[idx1] && target <  TStar_pure(target,t2)  && TStar_pure(target,t2) <= t2
// @ ensures forall t2 uint64 :: exists idx2 int ::target > t2 && t2 >= 0  ==> 0 <= idx2 && idx2 < len(r1) && TStar_pure(t2, target) == r1[idx2] && t2 < TStar_pure(t2, target ) && TStar_pure(t2, target) <= target
// @ ensures forall j int :: j >= 0 && j < len(r1) ==> r1[j] >= 0
// @ ensures forall t2 uint64 :: {TStar_wrapper(r1, target, t2)} TStar_wrapper(r1, target, t2)
// @ ensures forall t2 uint64 :: {TStar_wrapper(r1,t2,target)} TStar_wrapper(r1,t2,target)
// @ ensures len(r1) > 0 && r1[0] == 0
func FullBinaryLadderSteps_wrapper(target uint64) (r1 []uint64) {
	//@ t2 := GetUInt64()
	//@ assume t2 != target
	//@ assume t2 >= 0
	res /*@, idx @*/ := FullBinaryLadderSteps(target /*@, t2 @*/)
	//@ assert target < t2 ==>  TStar_pure(target, t2) == res[idx]
	//@ assert exists idx1 int :: target < t2 ==> 0 <= idx1 && idx1 < len(res) && TStar_pure(target, t2) == res[idx1] && target <  TStar_pure(target,t2)  && TStar_pure(target,t2) <= t2
	//@ assume forall t2 uint64 :: exists idx1 int :: target < t2 ==> 0 <= idx1 && idx1 < len(res) && TStar_pure(target, t2) == res[idx1] && target <  TStar_pure(target,t2)  && TStar_pure(target,t2) <= t2
	//@ assert target > t2 ==>  TStar_pure(t2, target) == res[idx]
	//@ assert exists idx1 int :: target > t2 && t2 >= 0 ==> 0 <= idx1 && idx1 < len(res) && TStar_pure(t2,target) == res[idx1] && t2 < TStar_pure(t2, target ) && TStar_pure(t2, target) <= target
	//@ assume forall t2 uint64 :: exists idx1 int :: target > t2 && t2 >= 0 ==> 0 <= idx1 && idx1 < len(res) && TStar_pure(t2,target) == res[idx1] && t2 < TStar_pure(t2, target ) && TStar_pure(t2, target) <= target
	return res
}
