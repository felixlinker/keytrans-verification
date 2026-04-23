package trees

import (
	"github.com/felixlinker/keytrans-verification/pkg/utils"
)

// @ requires 0 < size
// @ ensures acc(r)
// @ ensures forall i int :: 0 <= i && i < len(r) ==> 0 < r[i]
// @ ensures 0 < len(r) && r[len(r) - 1] == size
// @ ensures forall i int :: 0 <= i && i < len(r) ==> r[i] <= size
func frontier(size uint64) (r []uint64) {
	i_root := utils.PowOf2(utils.Log2Floor(size))
	// @ assert 0 < i_root && i_root <= size
	res := []uint64{i_root}

	if i_root == size {
		return res
	}

	rec := frontier(size - i_root)
	return append( /*@ perm(1/2), @*/ res, utils.Increment(rec, i_root)...)
}

// @ requires 0 < size
// @ ensures acc(r)
// @ ensures 0 < len(r)
// @ ensures forall i int :: 0 <= i && i < len(r) ==> 0 <= r[i]
// @ ensures r[len(r) - 1] == size - 1
// @ ensures forall i int :: 0 <= i && i < len(r) ==> r[i] < size
func Frontier(size uint64) (r []uint64) {
	return utils.Decrement(frontier(size))
}

// @ requires 0 < n && n <= size
// @ ensures acc(r)
// @ ensures 0 < len(r)
func pathToRoot(n uint64, size uint64) (r []uint64) {
	i_root := utils.PowOf2(utils.Log2Floor(size))
	// @ assert i_root <= size
	var p []uint64
	if i_root == n {
		p = []uint64{}
	} else if i_root < n {
		p = pathToRoot(n-i_root, i_root-1)
		p = utils.Increment(p, i_root)
	} else { // i_root > n
		// @ assert n <= i_root
		p = pathToRoot(n, i_root-1)
	}

	return append( /*@ perm(1/2), @*/ p, i_root)
}

// @ requires 0 <= n && n < size
// @ ensures acc(r)
func PathToRoot(n uint64, size uint64) (r []uint64) {
	path := pathToRoot(n+1, size)
	return utils.Decrement(path)
}
