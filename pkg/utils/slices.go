package utils

// @ preserves acc(r_in, 1/2)
// @ ensures acc(r_out)
// @ ensures len(r_in) == len(r_out)
// @ ensures forall i int :: 0 <= i && i < len(r_in) ==> r_in[i] - 1 == r_out[i]
func Decrement(r_in []uint64) (r_out []uint64) {
	r_out = make([]uint64, len(r_in))
	// @ invariant acc(r_in, 1/2)
	// @ invariant acc(r_out)
	// @ invariant 0 <= i && i <= len(r_in) && i <= len(r_out)
	// @ invariant forall j int :: 0 <= j && j < i ==> r_in[j] - 1 == r_out[j]
	for i := 0; i < len(r_in); i++ {
		r_out[i] = r_in[i] - 1
	}
	return r_out
}

// @ preserves acc(r_in, 1/2)
// @ ensures acc(r_out)
// @ ensures len(r_in) == len(r_out)
// @ ensures forall i int :: 0 <= i && i < len(r_in) ==> r_in[i] + add == r_out[i]
func Increment(r_in []uint64, add uint64) (r_out []uint64) {
	r_out = make([]uint64, len(r_in))
	// @ invariant acc(r_in, 1/2)
	// @ invariant acc(r_out)
	// @ invariant 0 <= i && i <= len(r_in) && i <= len(r_out)
	// @ invariant forall j int :: 0 <= j && j < i ==> r_in[j] + add == r_out[j]
	for i := 0; i < len(r_in); i++ {
		r_out[i] = r_in[i] + add
	}
	return r_out
}

// @ preserves acc(r_in, 1/2)
// @ ensures acc(r_out)
// @ ensures len(r_in) == len(r_out)
// @ ensures forall i int :: 0 <= i && i < len(r_in) ==> r_in[len(r_in)-1-i] == r_out[i]
func Reverse(r_in []uint64) (r_out []uint64) {
	r_out = make([]uint64, len(r_in))
	// @ invariant acc(r_in, 1/2)
	// @ invariant acc(r_out)
	// @ invariant 0 <= i && i <= len(r_in) && i <= len(r_out)
	// @ invariant forall j int :: 0 <= j && j < i ==> r_in[len(r_in)-1-j] == r_out[j]
	for i := 0; i < len(r_out); i++ {
		r_out[i] = r_in[len(r_in)-1-i]
	}
	return r_out
}
