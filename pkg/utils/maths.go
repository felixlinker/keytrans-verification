package utils

/*@
ghost
ensures r >= 0
ensures n >= 1 ==> PowOf2_pure(r) <= n && PowOf2_pure(r+1) > n && r < n
ensures n == 1 ==> r == 0
decreases n
pure
func Log2Floor_pure(n uint64) (r uint64) {
    return n < 2 ? 0 : 1 + Log2Floor_pure(n / 2)
}

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
		(b == 1 ? 0 :
			(a == 1 ? Log2FloorMonotonic(1, b/2) :
				Log2FloorMonotonic(a/2,b/2)))
}
@*/

// @ requires base > 0
// @ ensures r >= 0
// @ ensures PowOf2_pure(r) <= base
// @ ensures base < PowOf2_pure(r+1)
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

/*@
ghost
requires exp >= 0
ensures r > 0
decreases exp
pure
func PowOf2_pure(exp uint64) (r uint64) {
  return exp == 0 ? 1 : 2 * PowOf2_pure(exp - 1)
}

// Lemma: Weaker version of PowOf2_pureIncLemma
ghost
requires a >= 0
requires b >= 0
requires a <= b
ensures PowOf2_pure(a) <= PowOf2_pure(b)
ensures a < b ==> PowOf2_pure(a) < PowOf2_pure(b)
decreases b - a
pure
func PowOf2Monotonic(a uint64, b uint64) uint64 {
	return a == b ? 0 : PowOf2Monotonic(a, b - 1)
}
@*/

// @ requires exp >= 0
// @ ensures r == PowOf2_pure(exp)
// @ ensures 1 <= r
// @ decreases
func PowOf2(exp uint64) (r uint64) {
	var i uint64
	r = 1
	//@ invariant i >= 0 && i<= exp
	//@ invariant r == PowOf2_pure(i)
	//@ decreases exp - i
	for i = 0; i < exp; i += 1 {
		r = r * 2
	}
	return r
}
