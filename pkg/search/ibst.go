package search

import (
	"github.com/felixlinker/keytrans-verification/pkg/utils"
)

// ##(--hyperMode extended)

// @ requires  0 < size
// @ ensures   acc(r)
// @ ensures   0 < len(r) && uint64(len(r)) <= size
// @ ensures   forall i int :: { r[i] } 0 <= i && i < len(r) ==> 0 < r[i] && r[i] <= size
// @ ensures   r[0] == utils.PowOf2_pure(utils.Log2Floor_pure(size))
// @ ensures   r[len(r) - 1] == size
// @ ensures   low(size) ==> low(len(r)) && forall i int :: { r[i] } 0 <= i && i < len(r) ==> low(r[i])
// @ decreases size
func frontier(size uint64) (r []uint64) {
	i_root := utils.LargestSmallerPower(size)
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
// @ ensures  r[0] == utils.PowOf2_pure(utils.Log2Floor_pure(size)) - 1
// @ ensures  r[len(r) - 1] == size - 1
// @ ensures  low(size) ==> low(len(r)) && forall i int :: { r[i] } 0 <= i && i < len(r) ==> low(r[i])
// @ decreases
func Frontier(size uint64) (r []uint64) {
	return utils.Decrement(frontier(size))
}

// @ requires  min <= n && n <= max
// @ ensures   acc(r) && 0 < len(r)
// @ ensures  r[0] == n
// @ ensures  r[len(r) - 1] == utils.PowOf2_pure(utils.Log2Floor_pure(max+1-min)) + min - 1
// @ ensures   forall i int :: { r[i] } 0 <= i && i < len(r) ==> min <= r[i] && r[i] <= max
// @ decreases max - min
// note that this function operates on tree nodes starting at 0
// size = 3: nodes 0, 1, 2 with min=0 and max=2
func pathToRoot(n uint64, min, max uint64) (r []uint64) {
	i_root := utils.LargestSmallerPower(max+1-min) + min - 1
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
// @ ensures  r[0] == utils.PowOf2_pure(utils.Log2Floor_pure(size)) - 1
// @ ensures  r[len(r)-1] == n
// @ ensures  forall i int :: { r[i] } 0 <= i && i < len(r) ==> 0 <= r[i] && r[i] < size
// @ decreases
func PathToNode(n uint64, size uint64) (r []uint64) {
	return utils.Reverse(pathToRoot(n, 0, size-1))
}

// @ requires 0 <= n && n < size
// @ ensures  acc(r) && 0 < len(r)
// @ ensures  forall i int :: { r[i] } 0 <= i && i < len(r) ==> 0 <= r[i] && r[i] < size
// @ ensures  r[0] == n
// @ ensures  r[len(r)-1] == size - 1
func NodesToMostRecent(n uint64, size uint64) (r []uint64) {
	front := Frontier(size)
	fromRoot := PathToNode(n, size)
	// @ assert front[0] == fromRoot[0]
	// @ assert front[len(front)-1] == size - 1
	// @ assert fromRoot[len(fromRoot)-1] == n

	i := 0
	diffFound := false
	// @ ghost p := perm(1/2)
	// @ invariant 0 <= i && i <= len(front) && i <= len(fromRoot)
	// @ invariant acc(front, p) && acc(fromRoot, p)
	// @ invariant !diffFound ==> (forall j int :: 0 <= j && j < i ==> front[j] == fromRoot[j])
	// @ invariant diffFound ==> (forall j int :: 0 <= j && j < i - 1 ==> front[j] == fromRoot[j])
	// @ invariant diffFound ==> 0 < i && front[i-1] != fromRoot[i-1]
	for ; !diffFound && i < len(front) && i < len(fromRoot); i++ {
		if front[i] != fromRoot[i] {
			diffFound = true
		}
	}

	if !diffFound {
		if len(fromRoot) <= len(front) {
			r = front[i-1:]
			// @ assert forall j int :: 0 <= j && j < len(r) ==> &r[j] == &front[j+i-1]
		} else {
			r = fromRoot[i-1:]
			// @ assert forall j int :: 0 <= j && j < len(r) ==> &r[j] == &fromRoot[j+i-1]
			// @ assert r[len(r)-1] == n
			// @ assert r[0] == size - 1
			r = utils.Reverse(r)
		}
		// @ assert acc(r)
		// @ assert r[0] == n
		// @ assert r[len(r)-1] == size - 1
	} else {
		// @ assert 2 <= i

		// TODO: I tried using a combination of slicing, utils.Reverse, and append,
		// but gobra kept running forever and raising errors. I think append is the
		// main culprit here.

		r = make([]uint64, len(fromRoot)-i+1+len(front)-i+2)
		// @ assert 3 <= len(r)

		// Copy fromRoot[i:] into r in reverse
		// @ invariant 0 <= j && j <= len(fromRoot) && j < len(r)
		// @ invariant acc(r) && acc(fromRoot, p) && acc(front, p)
		// @ invariant fromRoot[len(fromRoot)-1] == n
		// @ invariant forall k int :: 0 <= k && k < len(fromRoot) ==> 0 <= fromRoot[k] && fromRoot[k] < size
		// @ invariant 0 < j ==> r[0] == n
		// @ invariant forall k int :: 0 <= k && k < len(r) ==> 0 <= r[k] && r[k] < size
		for j := 0; j < len(fromRoot)-i+1; j++ {
			r[j] = fromRoot[len(fromRoot)-j-1]
		}

		// @ invariant 0 <= j && i-2+j <= len(front) && len(fromRoot)-i+1+j <= len(r)
		// @ invariant acc(r) && acc(front, p)
		// @ invariant front[len(front)-1] == size - 1
		// @ invariant forall k int :: 0 <= k && k < len(front) ==> 0 <= front[k] && front[k] < size
		// @ invariant r[0] == n
		// @ invariant forall k int :: 0 <= k && k < len(r) ==> 0 <= r[k] && r[k] < size
		// @ invariant j == len(front)-i+2 ==> r[len(r)-1] == size - 1
		for j := 0; j < len(front)-i+2; j++ {
			// // @ assert i-1+1 == len(front)-1 ==> front[i-1+j] == size - 1
			r[len(fromRoot)-i+1+j] = front[i-2+j]
			// // @ assert i-1+1 == len(front)-1 ==> len(fromRoot)-i+j == len(r) -1 && r[len(r)-1] == size - 1
		}
		// @ assert acc(r) && r[0] == n && r[len(r)-1] == size - 1
	}

	return r
}

// @ requires 0 < rmw
// @ requires noPerm < p && p < writePerm
// @ requires 0 < len(timestamps)
// @ requires acc(timestamps, p) &&
// @   forall i int :: 0 <= i && i < len(timestamps) ==> 0 <= timestamps[i] &&
// @   forall i, j int :: 0 <= i && i < j && j < len(timestamps) ==> timestamps[i] < timestamps[j]
// @ ensures acc(timestamps, p)
// @ ensures 0 <= i && i < len(timestamps)
// @ ensures low(utils.getUint64sContent(timestamps)) && low(rmw) ==> low(i)
func MostRecentDistinguished(timestamps []uint64, rmw uint64 /*@, ghost p perm @*/) (i int) {
	var t uint64 = 0 // left timestamp in recursive algorithm from spec
	// @ ghost pureTimestamps := utils.getUint64sContent(timestamps)
	rightMost := timestamps[len(timestamps)-1] // right timestamp in recursive algorithm from spec
	i = 0
	done := false
	// @ invariant 0 <= t && t <= rightMost
	// @ invariant 0 <= i && i <= len(timestamps)
	// @ invariant acc(timestamps, p) && p < writePerm
	// @ invariant forall j int :: 0 <= j && j < len(timestamps) ==> 0 <= timestamps[j] && timestamps[j] <= rightMost && timestamps[j] == pureTimestamps[j]
	// @ invariant done ==> 0 < i
	// @ invariant low(pureTimestamps) && low(rmw) ==> low(rightMost) && low(done) && low(t) && low(i)
	for ; !done && i < len(timestamps); i++ {
		if rightMost-t < rmw {
			done = true
		} else {
			t = timestamps[i]
			// @ assert t == pureTimestamps[i]
		}
	}

	return i - 1
}
