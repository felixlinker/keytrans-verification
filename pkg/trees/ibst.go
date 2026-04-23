package trees

import (
	"github.com/felixlinker/keytrans-verification/pkg/proofs"
)

// @ requires 0 < size
// @ requires acc(accum)
// @ requires forall i int :: 0 <= i && i < len(accum) ==> 0 < accum[i]
// @ ensures acc(r)
// @ ensures len(accum) < len(r)
// @ ensures forall i int :: 0 <= i && i < len(r) ==> 0 < r[i]
// @ ensures 0 < len(r) && r[len(r) - 1] == size
func frontier(size uint64, accum []uint64) (r []uint64) {
	i_root := proofs.PowOf2(proofs.Log2Floor(size))
	// @ assert 0 < i_root
	accum = append( /*@ perm(1/2), @*/ accum, i_root)

	if i_root == size {
		return accum
	}

	i := len(accum)
	accum = frontier(size-i_root, accum)
	// @ invariant acc(accum)
	// @ invariant 0 <= i && i <= len(accum)
	// @ invariant i < len(accum)  ==> accum[len(accum) - 1] == size - i_root
	// @ invariant i == len(accum) ==> accum[len(accum) - 1] == size
	// @ invariant forall j int :: 0 <= j && j < len(accum) ==> 0 < accum[j]
	for ; i < len(accum); i++ {
		accum[i] = accum[i] + i_root
	}

	return accum
}

// @ requires 0 < size
// @ ensures acc(r)
// @ ensures 0 < len(r)
// @ ensures forall i int :: 0 <= i && i < len(r) ==> 0 <= r[i]
// @ ensures r[len(r) - 1] == size - 1
func Frontier(size uint64) (r []uint64) {
	res := frontier(size, []uint64{})
	// @ invariant acc(res)
	// @ invariant 0 <= i && i <= len(res)
	// @ invariant forall j int :: i <= j && j < len(res) ==> 0 <  res[j]
	// @ invariant forall j int :: 0 <= j && j < i        ==> 0 <= res[j]
	// @ invariant i < len(res)  ==> res[len(res) - 1] == size
	// @ invariant i == len(res) ==> res[len(res) - 1] == size - 1
	for i := 0; i < len(res); i++ {
		res[i] = res[i] - 1
	}
	return res
}
