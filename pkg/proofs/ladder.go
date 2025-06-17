package proofs

func FullBinaryLadderSteps(target uint32) (r []uint32) {
	//@ assume 0 <= target // see https://github.com/viperproject/gobra/issues/192
	r = make([]uint32, 0)
	var i uint32 = 1

	//@ invariant acc(r)
	//@ invariant 0 <= i - 1
	//@ invariant i-1 <= target || 1 <= len(r)
	for i-1 <= target {
		r = append( /*@ perm(1/2), @*/ r, i-1)
		//@ old_i := i
		i = i << 1
		//@ assume i == old_i * 2 // Gobra currently does not axiomatize left and right shifts
	}
	// i is now the smallest power of two s.t. i-1 is larger than target
	//@ assert target < i - 1

	x_in := r[len(r)-1]
	x_out := i - 1
	r = append( /*@ perm(1/2), @*/ r, x_out) // this will be the first proof of non-inclusion

	//@ invariant acc(r)
	for ((x_out - x_in) / 2) > 0 {
		next := x_in + ((x_out - x_in) / 2) - 1
		r = append( /*@ perm(1/2), @*/ r, next)
		if i <= target {
			x_in = next
		} else {
			x_out = next
		}
	}
	return r
}
