package proofs

func FullBinaryLadderSteps(target uint32) (r []uint32) {
	r = make([]uint32, 0)
	var i uint32 = 1
	for i - 1 < target {
		r = append(r, i - 1)
		i = i << 1
	}
	// i is now the smallest power of two minus one larger than or equal to target
	x_in := r[len(r) - 1]
	x_out := i
	r = append(r, i - 1) // this will be the first proof of non-inclusion
	for i > 1 {
		i := x_in + ((x_out - x_in) / 2)
		r = append(r, i - 1)
		if i <= target {
			x_in = i
		} else {
			x_out = i
		}
	}
	return r
}
