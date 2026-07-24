package prefix

import (
	"bytes"
	"crypto/sha256"
	"fmt"
	"math/rand"
	"testing"

	"github.com/felixlinker/keytrans-verification/pkg/proofs"
)

// ##(--hyperMode extended --enableExperimentalHyperFeatures)

const prefixTestSeed int64 = 0x5eed

// @ trusted
func TestPrefixInsertionOrderAndPruning(t *testing.T) {
	rng := rand.New(rand.NewSource(prefixTestSeed))
	t.Logf("random seed: %d", prefixTestSeed)

	for testCase := 0; testCase < 4; testCase++ {
		t.Run(fmt.Sprintf("random set %d", testCase), func(t *testing.T) {
			commitments := randomLeafs(t, rng, 15)
			trees := make([]*Tree, 0, 50)

			t.Run("all insertion orders have the same root", func(t *testing.T) {
				var wantRoot []byte
				for range cap(trees) {
					tree := buildPrefixTree(t, rng, commitments)
					if root, err := tree.Value(); err != nil {
						t.Fatalf("Value(): %v", err)
					} else if len(trees) == 0 {
						wantRoot = root
					} else if !bytes.Equal(root, wantRoot) {
						t.Fatalf("root = %x, want %x", root, wantRoot)
					}

					trees = append(trees, tree)
				}
			})

			t.Run("pruning and proof construction works correctly", func(t *testing.T) {
				for _, tree := range trees {
					rootBefore, err := tree.Value()
					if err != nil {
						t.Fatalf("Value() before pruning error: %v", err)
					}

					selection := rng.Perm(len(commitments))
					prunedCount := 1 + rng.Intn(len(commitments)-1)
					prunedKeys := make([][]byte, 0, prunedCount)
					for _, index := range selection[:prunedCount] {
						prunedKeys = append(prunedKeys, commitments[index][:])
					}

					tree.Prune(prunedKeys)
					rootAfter, err := tree.Value()
					if err != nil {
						t.Fatalf("Value() after pruning error: %v", err)
					} else if !bytes.Equal(rootAfter, rootBefore) {
						t.Fatalf("pruning changed root: got %x, want %x", rootAfter, rootBefore)
					}

					for i, index := range selection {
						_, ok := tree.Search(commitments[index][:])
						expectInclusion := prunedCount <= i
						if ok != expectInclusion {
							t.Fatalf("Search(%x) did not match pruning status", index)
						}
					}

					prf := tree.ProofFromTree()
					reconstructed, err := MkPrefix(prf)
					if err != nil {
						t.Fatalf("MkPrefix(ProofFromTree()): %v", err)
					}

					reconstructedRoot, err := reconstructed.Value()
					if err != nil {
						t.Fatalf("reconstructed Value(): %v", err)
					} else if !bytes.Equal(reconstructedRoot, rootAfter) {
						t.Fatalf("reconstructed root = %x, want %x", reconstructedRoot, rootAfter)
					}

					for _, commitment := range commitments {
						expectCommitment, expectOk := tree.Search(commitment[:])
						gotCommitment, gotOk := reconstructed.Search(commitment[:])
						if (expectCommitment == nil) != (gotCommitment == nil) {
							t.Fatalf("got commitment = %x, want %x", gotCommitment, expectCommitment)
						} else if expectCommitment != nil && !bytes.Equal(expectCommitment, gotCommitment) {
							t.Fatalf("got commitment = %x, want %x", gotCommitment, expectCommitment)
						}
						if expectOk != gotOk {
							t.Fatalf("got inclusion status = %v, want %v", gotOk, expectOk)
						}
					}
				}
			})
		})
	}
}

// @ trusted
func randomLeafs(t *testing.T, rng *rand.Rand, count int) [][]byte {
	t.Helper()

	keys := make([][]byte, 0, count)
	seen := make(map[string]bool, count)
	for len(keys) < count {
		searchKey := make([]byte, sha256.Size)
		if _, err := rng.Read(searchKey); err != nil {
			t.Fatalf("generating random search key: %v", err)
		}

		key := string(searchKey)
		if !seen[key] {
			seen[key] = true
			keys = append(keys, searchKey)
		}
	}
	return keys
}

// @ trusted
func buildPrefixTree(t *testing.T, rng *rand.Rand, commitments [][]byte) *Tree {
	t.Helper()

	tree := mkTree()
	tmp := make([][]byte, len(commitments))
	copy(tmp, commitments)
	for 0 < len(tmp) {
		i := rng.Intn(len(tmp))
		commitment := tmp[i]
		leaf := commitmentLeaf(&proofs.PrefixLeaf{
			Vrf_output: commitment,
			Commitment: commitment,
		})
		if err := tree.Insert(leaf); err != nil {
			t.Fatalf("Insert(%x): %v", commitment, err)
		}
		tmp = remove(tmp, i)
	}

	return tree
}

// @ trusted
func remove(s [][]byte, i int) (r [][]byte) {
	if i < len(s) {
		if 2 <= len(s) && i < len(s)-1 {
			s[i] = s[len(s)-1]
		}
		return s[:len(s)-1]
	} else {
		return s
	}
}
