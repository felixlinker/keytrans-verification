package trees

import (
	"crypto/sha256"
	"fmt"
	"testing"

	"github.com/felixlinker/keytrans-verification/pkg/proofs"
	"github.com/felixlinker/keytrans-verification/pkg/search"
	"github.com/felixlinker/keytrans-verification/pkg/utils"
)

var testLeafs = []*[sha256.Size]byte{
	{0: 0x01, 31: 0x01},
	{0: 0x02, 31: 0x02},
	{0: 0x03, 31: 0x03},
	{0: 0x04, 31: 0x04},
	{0: 0x05, 31: 0x05},
	{0: 0x06, 31: 0x06},
	{0: 0x07, 31: 0x07},
	{0: 0x08, 31: 0x08},
	{0: 0x09, 31: 0x09},
	{0: 0x0a, 31: 0x0a},
	{0: 0x0b, 31: 0x0b},
	{0: 0x0c, 31: 0x0c},
	{0: 0x0d, 31: 0x0d},
	{0: 0x0e, 31: 0x0e},
	{0: 0x0f, 31: 0x0f},
	{0: 0x10, 31: 0x10},
}

// @ trusted
func assertTreeSize(t *testing.T, tree *logTree, expected uint64) {
	t.Helper()

	if tree == nil {
		return
	} else {
		t.Logf("Checking for size %d", expected)
		if tree.size != expected {
			t.Fatalf("tree.size = %d, expected %d", tree.size, expected)
		} else if tree.left != nil {
			if tree.right == nil {
				t.Fatalf("tree.right == nil, but t.left != nil")
			}
			// First assert checks size of all right trees in left subtree
			t.Log("Recurse left")
			assertTreeSize(t, tree.left, tree.left.size)
			t.Log("Recurse right")
			assertTreeSize(t, tree.right, tree.size-tree.left.size)
			t.Log("Return")
		} else {
			t.Log("Return")
		}
	}
}

// @ trusted
func TestFit(t *testing.T) {
	for i := range uint64(8) {
		t.Run(fmt.Sprintf("fitting to size %d", i+1), func(t *testing.T) {
			tree := Singleton()
			tree.fit(i)
			assertTreeSize(t, tree, i+1)
		})
	}
}

// @ trusted
func TestLogFullTreeLeafHashes(t *testing.T) {
	for i := range len(testLeafs) {
		size := uint64(i + 1)
		t.Run(logTreeSizeName(size), func(t *testing.T) {
			logTreeCheckFullTreeLeafHashes(t, size)
		})
	}
}

// @ trusted
func TestLogGrowNilTreeFrontier(t *testing.T) {
	for i := range len(testLeafs) {
		size := uint64(i + 1)
		t.Run(logTreeSizeName(size), func(t *testing.T) {
			logTreeCheckGrowNilTreeFrontier(t, size)
		})
	}
}

// @ trusted
func TestLogGrowExistingTreeFrontier(t *testing.T) {
	for oldIndex := range len(testLeafs) {
		oldSize := uint64(oldIndex + 1)
		for newIndex := oldIndex + 1; newIndex < len(testLeafs); newIndex++ {
			newSize := uint64(newIndex + 1)
			t.Run(fmt.Sprintf("%s_to_%s", logTreeSizeName(oldSize), logTreeSizeName(newSize)), func(t *testing.T) {
				logTreeCheckGrowExistingTreeFrontier(t, oldSize, newSize)
			})
		}
	}
}

// @ trusted
func logTreeCheckFullTreeLeafHashes(t *testing.T, size uint64) {
	t.Helper()

	tree := logTreeFullTree(t, testLeafs, size)
	logTreeAssertLeafHashes(t, tree, testLeafs[:size])
}

// @ trusted
func logTreeCheckGrowNilTreeFrontier(t *testing.T, size uint64) {
	t.Helper()

	prf := logTreePrunedProof(t, testLeafs, size, 0)
	wantFrontier := logTreeExpectedFrontierEntries(testLeafs, size)
	logTreeAssertProofElements(t, prf, wantFrontier)

	tree := logTreeGrow(t, nil, size, prf)

	logTreeAssertFrontierEntries(t, tree, size, wantFrontier)
}

// @ trusted
func logTreeCheckGrowExistingTreeFrontier(t *testing.T, oldSize uint64, newSize uint64) {
	t.Helper()

	oldPrf := logTreePrunedProof(t, testLeafs, oldSize, 0)
	oldFrontier := logTreeExpectedFrontierEntries(testLeafs, oldSize)
	logTreeAssertProofElements(t, oldPrf, oldFrontier)

	tree := logTreeGrow(t, nil, oldSize, oldPrf)
	logTreeAssertFrontierEntries(t, tree, oldSize, oldFrontier)

	newPrf := logTreePrunedProof(t, testLeafs, newSize, oldSize+1)
	tree = logTreeGrow(t, tree, newSize, newPrf)

	wantFrontier := logTreeExpectedFrontierEntries(testLeafs, newSize)
	logTreeAssertFrontierEntries(t, tree, newSize, wantFrontier)
}

// @ trusted
func logTreeFullTree(t *testing.T, hashes []*[sha256.Size]byte, size uint64) *logTree {
	t.Helper()
	if size == 0 || uint64(len(hashes)) < size {
		t.Fatalf("invalid tree size %d for %d hashes", size, len(hashes))
	}

	tree := FullTree(hashes[:size])
	if tree == nil {
		t.Fatal("FullTree returned nil")
	}
	if got := tree.GetSize(); got != size {
		t.Fatalf("tree size = %d, want %d", got, size)
	}
	return tree
}

// @ trusted
func logTreePrunedProof(t *testing.T, hashes []*[sha256.Size]byte, size uint64, cacheSize uint64) *proofs.InclusionProof {
	t.Helper()

	tree := logTreeFullTree(t, hashes, size)
	tree.Prune()
	prf, err := tree.ProofFromPruned(cacheSize)
	if err != nil {
		t.Fatalf("ProofFromPruned(cacheSize=%d): %v", cacheSize, err)
	}
	if prf == nil {
		t.Fatal("ProofFromPruned returned nil")
	}
	return prf
}

// @ trusted
func logTreeGrow(t *testing.T, tree *logTree, size uint64, prf *proofs.InclusionProof) *logTree {
	t.Helper()

	grown := tree.Grow(size, prf)
	if grown == nil {
		t.Fatal("Grow returned nil")
	}
	if got := grown.GetSize(); got != size {
		t.Fatalf("grown tree size = %d, want %d", got, size)
	}
	return grown
}

// @ trusted
func logTreeAssertLeafHashes(t *testing.T, tree *logTree, want []*[sha256.Size]byte) {
	t.Helper()

	for i, wantHash := range want {
		got, err := tree.GetLeafHash(uint64(i))
		if err != nil {
			t.Fatalf("GetLeafHash(%d): %v", i, err)
		}
		if got == nil {
			t.Fatalf("GetLeafHash(%d) = nil, want %x", i, *wantHash)
		}
		if *got != *wantHash {
			t.Fatalf("GetLeafHash(%d) = %x, want %x", i, *got, *wantHash)
		}
	}
}

// @ trusted
func logTreeAssertFrontierEntries(t *testing.T, tree *logTree, size uint64, want []*proofs.NodeValue) {
	t.Helper()

	frontier := search.Frontier(size)
	if len(frontier) != len(want) {
		t.Fatalf("frontier for size %d has %d entries, want %d proof elements", size, len(frontier), len(want))
	}
	for i, index := range frontier {
		got, err := tree.GetLeafHash(index)
		if err != nil {
			t.Fatalf("GetLeafHash(frontier[%d]=%d): %v", i, index, err)
		}
		if got == nil {
			t.Fatalf("GetLeafHash(frontier[%d]=%d) = nil, want %x", i, index, *want[i])
		}
		if *got != *want[i] {
			t.Fatalf("GetLeafHash(frontier[%d]=%d) = %x, want %x", i, index, *got, *want[i])
		}
	}
}

// @ trusted
func logTreeAssertProofElements(t *testing.T, prf *proofs.InclusionProof, want []*proofs.NodeValue) {
	t.Helper()

	if len(prf.Elements) != len(want) {
		t.Fatalf("proof has %d elements, want %d", len(prf.Elements), len(want))
	}
	for i := range want {
		if *prf.Elements[i] != *want[i] {
			t.Fatalf("proof element %d = %x, want %x", i, *prf.Elements[i], *want[i])
		}
	}
}

// @ trusted
func logTreeExpectedFrontierEntries(hashes []*[sha256.Size]byte, size uint64) []*proofs.NodeValue {
	entries := make([]*proofs.NodeValue, 0)
	offset := uint64(0)
	for offset < size {
		subtreeSize := utils.LargestSmallerPower(size - offset)
		root := logTreeExpectedRoot(hashes[offset : offset+subtreeSize])
		entries = append(entries, &root)
		offset += subtreeSize
	}
	return entries
}

// @ trusted
func logTreeExpectedRoot(hashes []*[sha256.Size]byte) proofs.NodeValue {
	if len(hashes) == 1 {
		return *hashes[0]
	}

	leftSize := utils.TrueLargestSmallerPower(uint64(len(hashes)))
	leftRoot := logTreeExpectedRoot(hashes[:leftSize])
	rightRoot := logTreeExpectedRoot(hashes[leftSize:])

	content := logTreeExpectedHashContent(leftSize, leftRoot)
	content = append(content, logTreeExpectedHashContent(uint64(len(hashes))-leftSize, rightRoot)...)
	return sha256.Sum256(content)
}

// @ trusted
func logTreeExpectedHashContent(size uint64, hash proofs.NodeValue) []byte {
	prefix := byte(0x00)
	if size != 1 {
		prefix = 0x11
	}

	content := []byte{prefix}
	return append(content, hash[:]...)
}

// @ trusted
func logTreeSizeName(size uint64) string {
	return fmt.Sprintf("size_%02d", size)
}
