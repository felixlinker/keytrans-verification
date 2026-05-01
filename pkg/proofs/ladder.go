package proofs

import "github.com/felixlinker/keytrans-verification/pkg/utils"

/*@
ghost
requires 0 <= t1 && 0 <= t2
ensures t1 != t2 ==> utils.min(t1, t2) < r && r <= utils.max(t1, t2)
decreases
pure func TStar_pure(t1 uint64, t2 uint64) (r uint64) {
	return tStar_pure(t1 + 1, t2 + 1) - 1
}
@*/

// =============================Core Lemma======================================
/*@
ghost
requires 0 < t1 && 0 < t2
ensures 1 <= r
ensures t1 != t2 ==> utils.min(t1, t2) < r && r <= utils.max(t1, t2)
decreases
pure func tStar_pure(t1 uint64, t2 uint64) (r uint64) {
	return t1 == t2 ? 1 :
		t1 < t2 ? let i_low := utils.Log2Floor_pure(t1) in tStarRec_pure(t1, t2, utils.PowOf2_pure(i_low), utils.PowOf2_pure(i_low + 1)) :
			let i_low := utils.Log2Floor_pure(t2) in tStarRec_pure(t2, t1, utils.PowOf2_pure(i_low), utils.PowOf2_pure(i_low + 1))
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

ghost
requires 0 < utils.min(t1, t2)
requires x_in <= utils.min(t1, t2) && utils.min(t1, t2) < x_out
ensures t1 != t2 ==> utils.min(t1, t2) < r && r <= utils.max(t1, t2)
decreases x_out - x_in
pure func tStarRec_pure_general(t1 uint64, t2 uint64, x_in uint64, x_out uint64) (r uint64) {
	return t1 == t2 ? 1 : t1 < t2 ? tStarRec_pure(t1, t2, x_in, x_out) : tStarRec_pure(t2, t1, x_in, x_out)
}
@*/

// TStar returns a value r such that t1 < r <= t2
// @ requires 0 <= t1 && 0 <= t2
// @ ensures t1 != t2 ==> 1 <= t_star
// @ ensures t_star == TStar_pure(t1, t2)
func TStar(t1 uint64, t2 uint64) (t_star uint64) {
	return tStar(t1+1, t2+1) - 1
}

// @ requires 0 < t1 && 0 < t2
// @ ensures t_star == tStar_pure(t1, t2)
func tStar(t1 uint64, t2 uint64) (t_star uint64) {
	if t1 == t2 {
		return 1
	} else if t1 < t2 {
		i_low := utils.Log2Floor(t1)
		return tStarRec(t1, t2, utils.PowOf2(i_low), utils.PowOf2(i_low+1))
	} else {
		i_low := utils.Log2Floor(t2)
		return tStarRec(t2, t1, utils.PowOf2(i_low), utils.PowOf2(i_low+1))
	}
}

// @ requires 0 < t1 && t1 < t2
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

/*@
pred BinaryLadderInv(r []uint64) {
	acc(r) &&
	0 < len(r) && r[0] == 0 &&
	(forall i int :: { r[i] } 0 <= i && i < len(r) ==> 0 <= r[i])
}

ghost
requires acc(BinaryLadderInv(r), _)
requires 0 <= t1 && 0 <= t2
decreases
pure func IstStar(r []uint64, t1, t2 uint64, idx int) bool {
	return unfolding acc(BinaryLadderInv(r), _) in
		0 <= idx && idx < len(r) &&
		r[idx] == TStar_pure(t1, t2)
}
@*/

// Construct a binary ladder, but on the interval [1, ...] so that reasoning
// about logarithms and powers of two becomes simpler.
// @ requires 0 < target && 0 < t2
// @ ensures acc(r)
// @ ensures 0 <= idx && idx < len(r) && 0 < len(r) && r[0] == 1
// @ ensures forall i int :: { r[i] } 0 <= i && i < len(r) ==> 0 < r[i]
// @ ensures r[idx] == tStar_pure(target, t2)
// @ decreases
func fullBinaryLadderSteps(target uint64 /*@, ghost t2 uint64@*/) (r []uint64 /*@, ghost idx int @*/) {
	r = make([]uint64, 0)
	var i uint64 = 1

	/*@
	ghost if t2 < target {
		assert let _ := utils.Log2FloorMonotonic(t2, target) in utils.Log2Floor_pure(t2) <= utils.Log2Floor_pure(target)
	}
	@*/

	// @ ghost var k uint64 = 0
	// @ ghost var jump_idx int = 0

	// @ invariant acc(r)
	// @ invariant len(r) == int(k)
	// @ invariant 0 <= k && k <= target
	// @ invariant i == utils.PowOf2_pure(k) && k == utils.Log2Floor_pure(i)
	// @ invariant 1 < k ==> k - 1 <= utils.Log2Floor_pure(target)
	// @ invariant forall j int :: 0 <= j && j < len(r) ==> 0 < r[j]
	// @ invariant len(r) > 0 ==> r[k-1] == i / 2
	// @ invariant 0 <= jump_idx
	// @ invariant jump_idx == 0 ==> i / 2 <= t2
	// @ invariant jump_idx != 0 ==> t2 < target && jump_idx < len(r) && r[jump_idx] == tStar_pure(t2, target)
	// @ invariant 0 < len(r) ==> r[0] == 1
	// @ decreases target - i
	for i-1 < target {
		// i = 2^k
		r = append( /*@ perm(1/2), @*/ r, i)

		/*@
		ghost if jump_idx == 0 && t2 < i {
			assert let _ := utils.Log2FloorMonotonic(i / 2, t2) in utils.Log2Floor_pure(i / 2) <= utils.Log2Floor_pure(t2)
			assert let _ := utils.Log2FloorMonotonic(t2, i) in utils.Log2Floor_pure(t2) <= utils.Log2Floor_pure(i)
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
	// @ assert let _ := utils.Log2FloorMonotonic(k + 1, x_out) in k <= utils.Log2Floor_pure(x_out)

	// Initialize the variables so that the recursive invariant on
	// BinarySearchStep is established right-away when we already found t*.

	// @ ghost target_idx := jump_idx != 0 ? jump_idx        : len(r) - 1
	// @ ghost acc_x_in   := jump_idx != 0 ? r[jump_idx] / 2 : x_in
	// @ ghost acc_x_out  := jump_idx != 0 ? r[jump_idx]     : x_out
	// @ found            := jump_idx != 0 || x_out <= t2

	/*@
	// special case for handling target == t2:
	ghost if target == t2 {
		target_idx = 0
		found = true
	}
	@*/

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
// FullBinaryLadderSteps is the public entry point for computing the full
// binary ladder. This is the key interface used by CheckGreatest to obtain the
// ladder steps.
// @ requires 0 <= target && 0 <= t2
// @ ensures BinaryLadderInv(r)
// @ ensures IstStar(r, target, t2, idx)
// @ decreases
func FullBinaryLadderSteps(target uint64 /*@, ghost t2 uint64 @*/) (r []uint64 /*@, ghost idx int @*/) {
	steps /*@, idx @*/ := fullBinaryLadderSteps(target + 1 /*@, t2 + 1 @*/)
	r = utils.Decrement(steps)
	//@ fold BinaryLadderInv(r)
	return
}

// @ requires acc(r)
// @ requires 0 < len(r) && r[0] == 1
// @ requires forall i int :: { r[i] } 0 <= i && i < len(r) ==> 0 < r[i]
// @ requires 0 < x_in && x_in <= target
// @ requires 0 < t2
// @ requires 0 <= acc_idx && acc_idx < len(r)
// Invariants on acc_x_in/out. Both arguments will have the same value as when
// calling tStarRec_pure such that it returns immediately. These arguments allow
// us to continue recursively constructing the binary ladder while memorizing
// that the value stored at acc_idx is tStar.
// @ requires !found ==> x_in == acc_x_in && x_out == acc_x_out
// @ requires !found ==> x_in <= utils.min(target, t2) && utils.max(target, t2) < x_out
// @ requires acc_x_in <= utils.min(target, t2) && utils.min(target, t2) < acc_x_out
// @ requires found ==> r[acc_idx] == tStarRec_pure_general(target, t2, acc_x_in, acc_x_out)
// @ requires target == t2 ==> found
// @ ensures  acc(res)
// @ ensures  0 <= idx && idx < len(res) && 0 < len(res) && res[0] == 1
// @ ensures  forall i int :: { res[i] } 0 <= i && i < len(res) ==> 0 < res[i]
// @ ensures  res[idx] == tStarRec_pure_general(target, t2, acc_x_in, acc_x_out)
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
			acc_x_out = rec_x_in
		}
		@*/
	} else {
		rec_x_out = next
		/*@
		ghost if rec_x_out <= t2 && !found {
			acc_idx = len(r) - 1
			found = true
			acc_x_out = rec_x_out
		}
		@*/
	}

	// @ rec_acc_x_in :=  found ? acc_x_in  : rec_x_in
	// @ rec_acc_x_out := found ? acc_x_out : rec_x_out
	return BinarySearchStep(target, r, rec_x_in, rec_x_out /*@, t2, acc_idx, rec_acc_x_in, rec_acc_x_out, found @*/)
}
