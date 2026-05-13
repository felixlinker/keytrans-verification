package utils

/*@
ghost
decreases
pure func min(a, b uint64) uint64 {
  return a < b ? a : b
}

ghost
decreases
pure func max(a, b uint64) uint64 {
  return a > b ? a : b
}

ghost
ensures 0 <= r
ensures 1 <= n ==> PowOf2_pure(r) <= n && n < PowOf2_pure(r+1) && r < n
ensures n <= 1 ==> r == 0
decreases n
pure func Log2Floor_pure(n uint64) (r uint64) {
    return n < 2 ? 0 : 1 + Log2Floor_pure(n / 2)
}

ghost
requires  0 < a && 0 < b
requires  a <= b
ensures   Log2Floor_pure(a) <= Log2Floor_pure(b)
ensures   a <= b/2 ==> Log2Floor_pure(a) < Log2Floor_pure(b)
decreases b
pure func Log2FloorMonotonic(a uint64, b uint64) uint64 {
	return a == b ? 0 :
		(b == 1 ? 0 :
			(a == 1 ? Log2FloorMonotonic(1, b/2) :
				Log2FloorMonotonic(a/2,b/2)))
}
@*/

// @ ensures   0 <= r
// @ ensures   1 <= base ==> PowOf2_pure(r) <= base
// @ ensures   base < PowOf2_pure(r+1)
// @ ensures   r == Log2Floor_pure(base)
// @ decreases base
func Log2Floor(base uint64) (r uint64) {
	if base <= 1 {
		//@ assert Log2Floor_pure(base) == 0
		return 0
	} else {
		//@ assert 1 < base
		//@ assert Log2Floor_pure(base) == 1 + Log2Floor_pure(base / 2)
		return 1 + Log2Floor(base/2)
	}
}

/*@
ghost
ensures   0 < r
decreases exp
pure func PowOf2_pure(exp uint64) (r uint64) {
  return exp <= 0 ? 1 : 2 * PowOf2_pure(exp - 1)
}

// Lemma: Weaker version of PowOf2_pureIncLemma
ghost
requires  0 <= a
requires  0 <= b
requires  a <= b
ensures   PowOf2_pure(a) <= PowOf2_pure(b)
ensures   a < b ==> PowOf2_pure(a) < PowOf2_pure(b)
decreases b - a
pure func PowOf2Monotonic(a uint64, b uint64) uint64 {
	return a == b ? 0 : PowOf2Monotonic(a, b - 1)
}
@*/

// @ ensures  r == PowOf2_pure(exp)
// @ ensures  1 <= r
// @ decreases
func PowOf2(exp uint64) (r uint64) {
	r = 1
	if exp <= 0 {
		return
	}

	//@ invariant 0 <= i && i <= exp
	//@ invariant r == PowOf2_pure(i)
	//@ decreases exp - i
	for i := uint64(0); i < exp; i++ {
		r = r * 2
	}
	return r
}

// @ requires 1 <= n
// @ ensures 1 <= r && r <= n
// @ ensures r == PowOf2_pure(Log2Floor_pure(n))
// @ decreases
func LargestSmallerPower(n uint64) (r uint64) {
	return PowOf2(Log2Floor(n))
}

// @ requires 1 <= n
// @ ensures 0 <= r && r <= n
// @ ensures 1 <= r ==> PowOf2_pure(Log2Floor_pure(n)-1) <= r
// @ ensures 2 <= n ==> 1 <= r
// @ ensures r <= PowOf2_pure(Log2Floor_pure(n))
// @ ensures r < n
// @ decreases
func TrueLargestSmallerPower(n uint64) (r uint64) {
	if n == 1 {
		return 0
	} else if r = PowOf2(Log2Floor(n)); r == n {
		return PowOf2(Log2Floor(n) - 1)
	} else {
		return r
	}
}
