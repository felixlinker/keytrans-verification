package proofs

import "github.com/felixlinker/keytrans-verification/pkg/utils"

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

// Core Lemma: Shows that tPure function indicates t1<r <= t2
ghost
requires t1 > 0
requires t2 > t1
ensures r >= 1
ensures t1 < r && r <= t2
decreases
pure
func tStar_pure(t1 uint64, t2 uint64) (r uint64) {
	return let i_low := utils.Log2Floor_pure(t1) in tStarRec_pure(t1, t2, utils.PowOf2_pure(i_low), utils.PowOf2_pure(i_low + 1))
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

// TStar returns a value r such that t1 < r <= t2
// @ requires t1 >= 0
// @ requires t2 > t1
// @ ensures t_star >= 1
// @ ensures t_star == TStar_pure(t1,t2)
func TStar(t1 uint64, t2 uint64) (t_star uint64) {
	return tStar(t1+1, t2+1) - 1
}

// @ requires t1 > 0
// @ requires t2 > t1
// @ ensures t_star == tStar_pure(t1, t2)
func tStar(t1 uint64, t2 uint64) (t_star uint64) {
	i_low := utils.Log2Floor(t1)
	return tStarRec(t1, t2, utils.PowOf2(i_low), utils.PowOf2(i_low+1))
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

// Construct a binary ladder, but on the interval [1, ...] so that reasoning
// about logarithms and powers of two becomes simpler.
// @ requires 0 < target && 0 < t2 && target != t2
// @ ensures acc(r)
// @ ensures 0 < len(r) && 0 < idx && idx < len(r)
// @ ensures forall i int :: 0 <= i && i < len(r) ==> 0 < r[i]
// @ ensures target < t2 ==> r[idx] == tStar_pure(target, t2)
// @ ensures t2 < target ==> r[idx] == tStar_pure(t2, target)
func fullBinaryLadderSteps(target uint64 /*@, ghost t2 uint64@*/) (r []uint64 /*@, ghost idx int @*/) {
	r = make([]uint64, 0)
	var i uint64 = 1

	/*@
	ghost if t2 < target {
		assert let _ := utils.Log2FloorMonotonic(t2, target) in utils.Log2Floor_pure(t2) <= utils.Log2Floor_pure(target)
	}
	@*/

	// Denotes the length of the array r.
	// @ ghost var k uint64 = 0
	// @ ghost var jump_idx int = 0
	// @ invariant acc(r)
	// @ invariant len(r) == int(k)
	// @ invariant 0 <= k && k <= target
	// @ invariant i == utils.PowOf2_pure(k) && k == utils.Log2Floor_pure(i)
	// @ invariant k > 1 ==> k - 1 <= utils.Log2Floor_pure(target)
	// @ invariant forall j int :: 0 <= j && j < len(r) ==> 0 < r[j]
	// @ invariant len(r) > 0 ==> r[k-1] == i / 2
	// @ invariant 0 <= jump_idx
	// @ invariant 0 == jump_idx ==> i / 2 <= t2
	// @ invariant jump_idx != 0 ==> t2 < target && jump_idx < len(r) && r[jump_idx] == tStar_pure(t2, target)
	for i-1 < target {
		r = append( /*@ perm(1/2), @*/ r, i)

		/*@
		assert i == utils.PowOf2_pure(k)
		ghost if jump_idx == 0 && t2 < i {
			assert let _ := utils.Log2FloorMonotonic(i / 2, t2) in utils.Log2Floor_pure(i / 2) <= utils.Log2Floor_pure(t2)
			assert let _ := utils.Log2FloorMonotonic(t2, i) in utils.Log2Floor_pure(t2) <= utils.Log2Floor_pure(i)
			assert i == tStar_pure(t2, target)
			jump_idx = len(r) - 1
		}
		@*/

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

	// @ assert let _ := utils.Log2FloorMonotonic(target, i) in utils.Log2Floor_pure(target) < k + 1
	// @ assert k + 1 <= x_out
	// @ assert let _ := utils.Log2FloorMonotonic(k + 1, x_out) in k <= utils.Log2Floor_pure(x_out)

	// Initialize the variables so that the recursive invariant on
	// BinarySearchStep is established right-away when we already found t*.

	// @ ghost target_idx := jump_idx != 0 ? jump_idx        : len(r) - 1
	// @ ghost acc_x_in   := jump_idx != 0 ? r[jump_idx] / 2 : x_in
	// @ ghost acc_x_out  := jump_idx != 0 ? r[jump_idx]     : x_out
	// @ found            := jump_idx != 0 || x_out <= t2

	res /*@, search_idx @*/ := BinarySearchStep(target, r, x_in, x_out /*@, t2, target_idx, acc_x_in, acc_x_out, found @*/)
	// In the case t2 < target && jump_idx == 0, we must hint to gobra with
	// assertion below that acc_x_in is indeed the argument it expects for the
	// tStar_pure(t2, target) call in the function's post-condition.
	// @ assert t2 < target && jump_idx == 0 ==> let _ := utils.Log2FloorMonotonic(x_in, t2) in x_in == utils.PowOf2_pure(utils.Log2Floor_pure(t2))

	return res /*@, search_idx @*/
}

// Construct the binary ladder for a target value `target`. `t2` is a ghost
// variable which a different value that the server might try prove to be the
// greatest. The returned array `r` is the binary ladder, and `r[idx]` stores
// the first element of the binary ladder for which clients verifying a ladder
// for target or t2 would expect different results.
// @ requires 0 <= target && 0 <= t2 && target != t2
// @ ensures acc(r) && 0 < len(r)
// @ ensures 0 <= idx && idx < len(r)
// @ ensures forall i int :: 0 <= i && i < len(r) ==> 0 <= r[i]
// @ ensures target < t2 ==> r[idx] == TStar_pure(target, t2)
// @ ensures t2 < target ==> r[idx] == TStar_pure(t2, target)
func FullBinaryLadderSteps(target uint64 /*@, ghost t2 uint64 @*/) (r []uint64 /*@, ghost idx int @*/) {
	steps /*@, r_idx @*/ := fullBinaryLadderSteps(target + 1 /*@, t2 + 1 @*/)
	// @ ghost tStarPlusOne := steps[r_idx]
	// @ assert target < t2 ==> steps[r_idx] == tStar_pure(target + 1, t2 + 1)
	// @ assert t2 < target ==> steps[r_idx] == tStar_pure(t2 + 1, target + 1)

	return utils.Decrement(steps) /*@, r_idx @*/
}

// @ requires 0 < len(r) && acc(r)
// @ requires forall i int :: 0 <= i && i < len(r) ==> 0 < r[i]
// @ requires 0 < target && 0 < t2 && target != t2
// @ requires 0 < x_in && x_in <= target && target < x_out
// @ requires 0 < acc_idx && acc_idx < len(r)
// @ ensures acc(res) && 0 < idx && idx < len(res)
// @ ensures forall i int :: 0 <= i && i < len(res) ==> 0 < res[i]
//
// Invariants on acc_x_in/out. Both arguments will have the same value as when
// calling tStarRec_pure such that it returns immediately. These arguments allow
// us to continue recursively constructing the binary ladder while memorizing
// that the value stored at acc_idx is tStar.
// @ requires !found ==> x_in == acc_x_in && x_out == acc_x_out
// @ requires !found && target < t2 ==> t2 < x_out
// @ requires !found && t2 < target ==> x_in <= t2
//
// Case 1: target < t2
// @ requires target < t2 ==> acc_x_in <= target && target < acc_x_out
// @ requires found && target < t2 ==> r[acc_idx] == tStarRec_pure(target, t2, acc_x_in, acc_x_out)
// @ ensures  target < t2 ==> res[idx] == tStarRec_pure(target, t2, acc_x_in, acc_x_out)
//
// Case 2: t2 < target
// @ requires t2 < target ==> acc_x_in <= t2 && t2 < acc_x_out
// @ requires found && t2 < target ==> r[acc_idx] == tStarRec_pure(t2, target, acc_x_in, acc_x_out)
// @ ensures  t2 < target ==> res[idx] == tStarRec_pure(t2, target, acc_x_in, acc_x_out)
//
// @ decreases x_out - x_in
func BinarySearchStep(target uint64, r []uint64, x_in uint64, x_out uint64 /*@, ghost t2 uint64, ghost acc_idx int, ghost acc_x_in uint64, ghost acc_x_out uint64, ghost found bool @*/) (res []uint64 /*@, ghost idx int @*/) {
	if x_in+1 >= x_out {
		return r /*@, acc_idx @*/
	}

	next := x_in + (x_out-x_in)/2
	r = append( /*@ perm(1/2), @*/ r, next)
	rec_x_in := x_in
	rec_x_out := x_out
	if next <= target {
		rec_x_in = next
		/*@
		ghost if t2 < rec_x_in && !found {
			acc_idx = len(r) - 1
			found = true
			// The recursive call in this case will mirror the binary ladder
			// construction for t2, therefore, "recurse" on rec_x_in as the next
			// x_out.
			assert r[acc_idx] == tStarRec_pure(t2, target, x_in, rec_x_in)
			acc_x_out = rec_x_in
		}
		@*/
	} else {
		rec_x_out = next
		/*@
		ghost if rec_x_out <= t2 && !found {
			acc_idx = len(r) - 1
			found = true
			assert r[acc_idx] == tStarRec_pure(target, t2, acc_x_in, rec_x_out)
			assert r[acc_idx] == tStarRec_pure(target, t2, acc_x_in, acc_x_out)
			acc_x_out = rec_x_out
		}
		@*/
	}

	// @ rec_acc_x_in :=  found ? acc_x_in  : rec_x_in
	// @ rec_acc_x_out := found ? acc_x_out : rec_x_out
	return BinarySearchStep(target, r, rec_x_in, rec_x_out /*@, t2, acc_idx, rec_acc_x_in, rec_acc_x_out, found @*/)
}

// FullBinaryLadderSteps_wrapper is the public entry point for computing the full
// binary ladder. It wraps FullBinaryLadderSteps and lifts the single-t2 guarantee
// to a universal quantifier: for ALL possible t2 values, the returned ladder
// contains TStar_pure(target, t2) (or TStar_pure(t2, target)). This is the
// key interface used by CheckGreatest to obtain the ladder steps.
//
// Preconditions: target >= 0.
// Postconditions: for every t2, TStar appears in r. TStar_wrapper holds for
// all t2 in both orderings. All elements >= 0, r[0] == 0.
//
// Returns: r — the full binary ladder steps for target.
//
// @ requires 0 <= target && 0 <= t2
// @ ensures acc(r)
// @ ensures forall j int :: 0 <= j && j < len(r) ==> r[j] >= 0
// @ ensures 0 <= i && i < len(r)
// @ ensures target < t2 ==> target < r[i] && r[i] <= t2
// @ ensures t2 < target ==> t2 < r[i] && r[i] <= target
func FullBinaryLadderSteps_wrapper(target uint64 /*@, ghost t2 uint64 @*/) (r []uint64 /*@, ghost i int@*/) {
	// Ensure that we pass a t2 not equal to target to satisfy FullBinaryLadderSteps preconditions. When they're equal, idx is irrelevant.
	res /*@, idx @*/ := FullBinaryLadderSteps(target /*@, target == t2 ? t2 + 1 : t2 @*/)
	//@ assert target < t2 ==> TStar_pure(target, t2) == res[idx] && target < res[idx] && res[idx] <= t2
	//@ assert t2 < target ==> TStar_pure(t2, target) == res[idx]

	return res /*@, target == t2 ? 0 : idx @*/
}
