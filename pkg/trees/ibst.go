package trees

import (
	"github.com/felixlinker/keytrans-verification/pkg/utils"
)

// ##(--hyperMode extended)

// @ requires  0 < size
// @ ensures   acc(r)
// @ ensures   0 < len(r) && uint64(len(r)) <= size
// @ ensures   forall i int :: { r[i] } 0 <= i && i < len(r) ==> 0 < r[i] && r[i] <= size
// @ ensures   r[len(r) - 1] == size
// @ ensures   low(size) ==> low(len(r)) && forall i int :: { r[i] } 0 <= i && i < len(r) ==> low(r[i])
// @ decreases size
func frontier(size uint64) (r []uint64) {
	i_root := utils.PowOf2(utils.Log2Floor(size))
	// @ assert 0 < i_root && i_root <= size
	r = []uint64{i_root}

	if i_root != size {
		rec := frontier(size - i_root)
		r = append( /*@ perm(1/2), @*/ r, utils.Increment(rec, i_root)...)
	}

	return
}

// @ requires 0 < size
// @ ensures  acc(r)
// @ ensures  0 < len(r) && uint64(len(r)) <= size
// @ ensures  forall i int :: { r[i] } 0 <= i && i < len(r) ==> 0 <= r[i] && r[i] < size
// @ ensures  r[len(r) - 1] == size - 1
// @ ensures  low(size) ==> low(len(r)) && forall i int :: { r[i] } 0 <= i && i < len(r) ==> low(r[i])
// @ decreases
func Frontier(size uint64) (r []uint64) {
	return utils.Decrement(frontier(size))
}

// @ requires  min <= n && n <= max
// @ ensures   acc(r) && 0 < len(r)
// @ ensures   forall i int :: { r[i] } 0 <= i && i < len(r) ==> min <= r[i] && r[i] <= max
// @ decreases max - min
// note that this function operates on tree nodes starting at 0
// size = 3: nodes 0, 1, 2 with min=0 and max=2
func pathToRoot(n uint64, min, max uint64) (r []uint64) {
	i_root := utils.PowOf2(utils.Log2Floor(max+1-min)) + min - 1
	// @ assert min <= i_root && i_root <= max
	var p []uint64
	if i_root == n {
		p = []uint64{}
	} else if i_root < n {
		p = pathToRoot(n, i_root+1, max)
	} else {
		// @ assert n < i_root
		p = pathToRoot(n, min, i_root-1)
	}

	return append( /*@ perm(1/2), @*/ p, i_root)
}

// @ requires 0 <= n && n < size
// @ ensures  acc(r) && 0 < len(r)
// @ ensures  forall i int :: { r[i] } 0 <= i && i < len(r) ==> 0 <= r[i] && r[i] < size
// @ decreases
func PathToRoot(n uint64, size uint64) (r []uint64) {
	return pathToRoot(n, 0, size-1)
}
