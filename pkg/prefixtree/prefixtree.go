package prefixtree

import (
	"encoding/binary"
	"errors"
)

type Node struct {
	hasData bool
	key     uint64
	value   int // e.g. some public key
	left    *Node
	right   *Node
}

const InexistentSubtreeHash = -1

/*@
ghost type BitConversion domain {
    func GetBits(uint64) seq[bool]
    func GetInt(seq[bool]) uint64

    axiom { // bijection between int and bits
        forall i uint64 :: { GetBits(i) } GetInt(GetBits(i)) == i
    }
}
@*/

//@ trusted
//@ decreases
//@ ensures acc(res)
//@ ensures len(res) == len(GetBits(key))
//@ ensures forall i int :: { res[i] } 0 <= i && i < len(res) ==> res[i] == GetBits(key)[i]
func ComputeBits(key uint64) (res []bool) {
	bs := make([]byte, 8)
	binary.LittleEndian.PutUint64(bs, key)
	res = make([]bool, 64)
	for i := 0; i < len(bs); i++ {
		b := bs[i]
		for j := 0; j < 8; j++ {
			res[len(res)-(i*8+j)-1] = (b & 1) == 1
			b >>= 1
		}
	}
	return
}

/*@
pred (n *Node) PrefixTree() {
    n.PrefixSubtree(seq[bool]{})
}

pred (n *Node) PrefixSubtree(prefix seq[bool]) {
    acc(n) &&
    (n.hasData ==> GetBits(n.key) == prefix && n.left == nil && n.right == nil) &&
    (n.left != nil ==> n.left.PrefixSubtree(prefix ++ seq[bool]{false})) &&
    (n.right != nil ==> n.right.PrefixSubtree(prefix ++ seq[bool]{true}))
}
@*/

func test() {
	n000 := &Node{true, 0, 42, nil, nil}
	//@ assume GetBits(0) == seq[bool]{false, false, false}
	//@ fold n000.PrefixSubtree(seq[bool]{false, false, false})

	n001 := &Node{true, 1, 0, nil, nil}
	//@ assume GetBits(1) == seq[bool]{false, false, true}
	//@ fold n001.PrefixSubtree(seq[bool]{false, false, true})

	n00 := &Node{false, 2, -1, n000, n001}
	//@ fold n00.PrefixSubtree(seq[bool]{false, false})

	n0 := &Node{false, 3, -1, n00, nil}
	//@ fold n0.PrefixSubtree(seq[bool]{false})

	n := &Node{false, 4, -1, n0, nil}
	//@ fold n.PrefixSubtree(seq[bool]{})
	//@ fold n.PrefixTree()

	_ = n // make Go compiler happy
}

/*@
ghost type Hashing domain {
    // type 0
    func hashKeyValue(uint64, int) int
    func invKeyValue1(int) uint64
    func invKeyValue2(int) int

    // type 1
    func hashSubtrees(int, int) int
    func invSubtrees1(int) int
    func invSubtrees2(int) int

    func getType(int) int

    axiom { // hashKeyValue is injective and disjoint from hashSubtrees
        forall i1 uint64, i2 int :: { hashKeyValue(i1, i2) } invKeyValue1(hashKeyValue(i1, i2)) == i1 && invKeyValue2(hashKeyValue(i1, i2)) == i2 && getType(hashKeyValue(i1, i2)) == 0
    }

    axiom { // hashKeyValue never produces InexistentSubtreeHash
        forall i1 uint64, i2 int :: { hashKeyValue(i1, i2) } hashKeyValue(i1, i2) != InexistentSubtreeHash
    }

    axiom { // hashSubtrees is injective and disjoint from hashKeyValue
        forall i1, i2 int :: { hashSubtrees(i1, i2) } invSubtrees1(hashSubtrees(i1, i2)) == i1 && invSubtrees2(hashSubtrees(i1, i2)) == i2 && getType(hashSubtrees(i1, i2)) == 1
    }

    axiom { // hashSubtrees never produces InexistentSubtreeHash
        forall i1, i2 int :: { hashSubtrees(i1, i2) } hashSubtrees(i1, i2) != InexistentSubtreeHash
    }
}
@*/

//@ trusted
//@ decreases
//@ ensures   res == hashKeyValue(key, value)
func HashData(key uint64, value int) (res int) {
	return int(key) + value // just a stupid example
}

//@ preserves acc(n.PrefixSubtree(prefix), 1/2)
//@ ensures   res == unfolding acc(n.PrefixSubtree(prefix), 1/2) in hashKeyValue(n.key, n.value)
func HashNodeData(n *Node /*@, ghost prefix seq[bool] @*/) (res int) {
	//@ unfold acc(n.PrefixSubtree(prefix), 1/4)
	res = HashData(n.key, n.value)
	//@ fold acc(n.PrefixSubtree(prefix), 1/4)
	return
}

//@ trusted
//@ decreases
//@ ensures   res == hashSubtrees(left, right)
func CombineSubtreeHashes(left, right int) (res int) {
	return left + right // just a stupid example
}

/*@
ghost
decreases
requires acc(n.PrefixTree(), _)
pure func (n *Node) prefixTreeHash() int {
    return unfolding acc(n.PrefixTree(), _) in n.prefixSubtreeHash(seq[bool]{})
}

ghost
decreases n.PrefixSubtree(prefix)
requires acc(n.PrefixSubtree(prefix), _)
pure func (n *Node) prefixSubtreeHash(prefix seq[bool]) int {
    return unfolding acc(n.PrefixSubtree(prefix), _) in (
        n.hasData ?
            hashKeyValue(n.key, n.value) :
            hashSubtrees(
                n.left == nil ? InexistentSubtreeHash : n.left.prefixSubtreeHash(prefix ++ seq[bool]{false}),
                n.right == nil ? InexistentSubtreeHash : n.right.prefixSubtreeHash(prefix ++ seq[bool]{true})))
}

ghost
decreases
requires acc(n.PrefixTree(), _)
pure func (n *Node) prefixTreeContains(key uint64, value int) bool {
    return unfolding acc(n.PrefixTree(), _) in n.prefixSubtreeContains(seq[bool]{}, key, value)
}

ghost
decreases n.PrefixSubtree(prefix)
requires acc(n.PrefixSubtree(prefix), _)
pure func (n *Node) prefixSubtreeContains(prefix seq[bool], key uint64, value int) bool {
    return unfolding acc(n.PrefixSubtree(prefix), _) in (
        len(GetBits(key)) < len(prefix) ?
            false :
            len(GetBits(key)) == len(prefix) ?
                n.hasData && n.key == key && n.value == value :
                GetBits(key)[len(prefix)] ?
                    (n.right == nil ? false : n.right.prefixSubtreeContains(prefix ++ seq[bool]{true}, key, value)) :
                    (n.left == nil ? false : n.left.prefixSubtreeContains(prefix ++ seq[bool]{false}, key, value)))
}
@*/

// copath is sorted such that hashes for subtrees deeper in the prefix tree appear later in the slice
//@ requires  noPerm < p
//@ requires low(key)
//@ requires low(rootHash)
//@ preserves acc(copath, p)
//@ preserves acc(n.PrefixTree(), p) && rootHash == n.prefixTreeHash()
//@ ensures   res ==> n.prefixTreeContains(key, value)
//@ ensures   res ==> low(value)
func CheckInclusionWithoutTree(key uint64, value int, rootHash int, copath []int /*@, ghost n *Node, ghost p perm @*/) (res bool) {
	if len(copath) != len(ComputeBits(key)) {
		return false
	}
	computedHash := ComputePath(key, value, copath /*@, n, p/2 @*/)
	res = computedHash == rootHash
	if res {
		//@ IsValidCoPathInjective(computedHash, hashKeyValue(key, value), copath, GetBits(key), p/2)
		//@ UniqueCopathLemma(key, value, copath, n, p/2)
	}
	return
}

/*@
ghost
decreases
requires acc(copath, _)
pure func IsValidCoPath(rootHash, leafHash int, copath []int, keyBits seq[bool]) bool {
    return len(copath) == len(keyBits) &&
        leafHash != InexistentSubtreeHash &&
        PureComputePath(0, leafHash, copath, keyBits) == rootHash
}

ghost
decreases len(keyBits) - i
requires acc(copath, _)
requires  0 <= i && i <= len(keyBits)
requires len(copath) == len(keyBits)
requires leafHash != InexistentSubtreeHash
ensures  res != InexistentSubtreeHash
pure func PureComputePath(i int, leafHash int, copath []int, keyBits seq[bool]) (res int) {
    return i == len(keyBits) ? leafHash :
        let pathPostfix := PureComputePath(i + 1, leafHash, copath, keyBits) in
        let lhsHash := keyBits[i] ? copath[i] : pathPostfix in
        let rhsHash := keyBits[i] ? pathPostfix : copath[i] in
        hashSubtrees(lhsHash, rhsHash)
}

ghost
decreases
requires noPerm < p && acc(copath, p)
requires low(rootHash) && low(keyBits)
requires IsValidCoPath(rootHash, leafHash, copath, keyBits)
ensures  acc(copath, p)
ensures  low(leafHash)
ensures  forall j int :: { copath[j] } 0 <= j && j < len(copath) ==> low(copath[j])
func IsValidCoPathInjective(rootHash, leafHash int, copath []int, keyBits seq[bool], p perm) {
    PureComputePathInjective(0, leafHash, copath, keyBits, p/2)
}

ghost
decreases len(keyBits) - i
requires noPerm < p && acc(copath, p)
requires  0 <= i && i <= len(keyBits)
requires leafHash != InexistentSubtreeHash
requires len(copath) == len(keyBits)
requires low(keyBits) && low(i)
requires low(PureComputePath(i, leafHash, copath, keyBits))
ensures  acc(copath, p)
ensures  low(leafHash)
// we learn more about the lowness of copath with each recursive invocation:
ensures  forall j int :: { copath[j] } i <= j && j < len(copath) ==> low(copath[j])
func PureComputePathInjective(i int, leafHash int, copath []int, keyBits seq[bool], p perm) {
    if i != len(keyBits) {
        pathPostfix := PureComputePath(i + 1, leafHash, copath, keyBits)
        lhsHash := keyBits[i] ? copath[i] : pathPostfix
        rhsHash := keyBits[i] ? pathPostfix : copath[i]
        // the following assert stmts are not necessary but would hold
        // assert low(hashSubtrees(lhsHash, rhsHash))
        // assert low(lhsHash)
        // assert low(rhsHash)
        PureComputePathInjective(i + 1, leafHash, copath, keyBits, p/2)
    }
}
@*/

// recursive implementation of computing the root hash using the copath.
//@ decreases
//@ requires  len(copath) == len(GetBits(key))
//@ requires  noPerm < p
//@ preserves acc(n.PrefixTree(), p)
//@ preserves acc(copath, p)
//@ ensures   IsValidCoPath(hash, hashKeyValue(key, value), copath, GetBits(key))
func ComputePath(key uint64, value int, copath []int /*@, ghost n *Node, ghost p perm @*/) (hash int) {
	//@ unfold acc(n.PrefixTree(), p)
	hash = ComputePathSubtree(key, value, 0, copath /*@, n, seq[bool]{ }, p @*/)
	//@ fold acc(n.PrefixTree(), p)
	return
}

// recursive implementation of computing the root hash using the copath.
//@ decreases len(GetBits(key)) - i
//@ requires  0 <= i && i <= len(GetBits(key))
//@ requires  len(copath) == len(GetBits(key))
//@ requires  i == len(prefix)
//@ requires  noPerm < p
//@ preserves n != nil ==> acc(n.PrefixSubtree(prefix), p)
//@ preserves acc(copath, p)
//@ ensures   hash == PureComputePath(i, hashKeyValue(key, value), copath, GetBits(key))
func ComputePathSubtree(key uint64, value int, i int, copath []int /*@, ghost n *Node, ghost prefix seq[bool], ghost p perm @*/) (hash int) {
	bits := ComputeBits(key)
	if len(bits) == i {
		hash = HashData(key, value)
	} else if bits[i] {
		/*@
		  ghost var subtree *Node
		  ghost if n == nil {
		      subtree = nil
		  } else {
		      unfold acc(n.PrefixSubtree(prefix), p)
		      subtree = n.right
		  }
		  @*/
		prevHash := ComputePathSubtree(key, value, i+1, copath /*@, subtree, prefix ++ seq[bool]{ true }, p @*/)
		hash = CombineSubtreeHashes(copath[i], prevHash)
		/*@
		  ghost if n != nil {
		      fold acc(n.PrefixSubtree(prefix), p)
		  }
		  @*/
	} else {
		/*@
		  ghost var subtree *Node
		  ghost if n == nil {
		      subtree = nil
		  } else {
		      unfold acc(n.PrefixSubtree(prefix), p)
		      subtree = n.left
		  }
		  @*/
		prevHash := ComputePathSubtree(key, value, i+1, copath /*@, subtree, prefix ++ seq[bool]{ false }, p @*/)
		hash = CombineSubtreeHashes(prevHash, copath[i])
		/*@
		  ghost if n != nil {
		      fold acc(n.PrefixSubtree(prefix), p)
		  }
		  @*/
	}
	return
}

/*@
ghost
decreases
requires  noPerm < p
requires  acc(n.PrefixTree(), p) && acc(copath, p)
requires  IsValidCoPath(n.prefixTreeHash(), hashKeyValue(key, value), copath, GetBits(key))
ensures   acc(n.PrefixTree(), p) && acc(copath, p)
ensures   n.prefixTreeContains(key, value)
// proves that the postcondition of `ComputePath` implies tree containment if root hash matches
func UniqueCopathLemma(key uint64, value int, copath []int, n *Node, p perm) {
    unfold acc(n.PrefixTree(), p)
    UniqueCopathSubtreeLemma(key, value, 0, copath, n, seq[bool]{ }, p)
    fold acc(n.PrefixTree(), p)
}

ghost
decreases len(GetBits(key)) - i
requires  noPerm < p
requires  0 <= i && i <= len(GetBits(key))
requires  i == len(prefix)
requires  len(copath) == len(GetBits(key))
requires  acc(n.PrefixSubtree(prefix), p) && acc(copath, p)
requires  n.prefixSubtreeHash(prefix) == PureComputePath(i, hashKeyValue(key, value), copath, GetBits(key))
ensures   acc(n.PrefixSubtree(prefix), p) && acc(copath, p)
ensures   n.prefixSubtreeContains(prefix, key, value)
// proves that the postcondition of `ComputePathSubtree` implies tree containment if root hash matches
func UniqueCopathSubtreeLemma(key uint64, value, i int, copath []int, n *Node, prefix seq[bool], p perm) {
    if i == len(GetBits(key)) {
        assert unfolding acc(n.PrefixSubtree(prefix), p) in n.hasData
    } else if GetBits(key)[i] {
        // this and the next branch rely on the fact that our hash functions
        // never produce the value `InexistentSubtreeHash`.
        // this branch is more verbose, see next branch for a more concise version of the proof.
        assert n.prefixSubtreeHash(prefix) == PureComputePath(i, hashKeyValue(key, value), copath, GetBits(key))
        hash := n.prefixSubtreeHash(prefix)

        unfold acc(n.PrefixSubtree(prefix), p)
        if n.right == nil {
            if !n.hasData {
                // unfold definition of n.prefixSubtreeHash(prefix):
                lhsHash := n.left == nil ? InexistentSubtreeHash : n.left.prefixSubtreeHash(prefix ++ seq[bool]{false})
                assert hash == hashSubtrees(lhsHash, InexistentSubtreeHash)

                // unfold definition of PureComputePath:
                var pathPostfix int
                if i + 1 == len(GetBits(key)) {
                    pathPostfix = hashKeyValue(key, value)
                } else {
                    pathPostfix = PureComputePath(i + 1, hashKeyValue(key, value), copath, GetBits(key))
                }
                assert hash == hashSubtrees(copath[i], pathPostfix)
                assert copath[i] == lhsHash
                assert pathPostfix == InexistentSubtreeHash // contradiction
            }
            assert false
        } else {
            UniqueCopathSubtreeLemma(key, value, i + 1, copath, n.right, prefix ++ seq[bool]{true}, p)
        }
        fold acc(n.PrefixSubtree(prefix), p)
    } else {
        unfold acc(n.PrefixSubtree(prefix), p)
        if n.left != nil {
            UniqueCopathSubtreeLemma(key, value, i + 1, copath, n.left, prefix ++ seq[bool]{false}, p)
        }
        fold acc(n.PrefixSubtree(prefix), p)
    }
}
@*/

//@ trusted
//@ ensures err != nil
func NewError(msg string) (err error) {
	return errors.New(msg)
}
