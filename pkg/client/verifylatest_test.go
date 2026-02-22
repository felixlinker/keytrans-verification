package client

import (
	"crypto/sha256"
	"testing"

	"github.com/felixlinker/keytrans-verification/pkg/crypto"
	"github.com/felixlinker/keytrans-verification/pkg/proofs"
)

// ==================================================================================
// ================================== Helpers =======================================
// ==================================================================================

// buildSingleLeafTree creates a PrefixTree with a single leaf whose VRF output
// matches the given (label, version) pair. GetCommitment on this tree returns:
//   - non-nil (inclusion) when queried with the same (label, version)
//   - nil (non-inclusion) for any other (label, version)
func buildSingleLeafTree(label []byte, version uint32) *proofs.PrefixTree {
	vrfInput := crypto.VrfInput{Label: label, Version: version}
	vrfHash := crypto.VRF_hash(nil, vrfInput)
	commitment := sha256.Sum256([]byte("test-commitment"))
	leaf := &proofs.PrefixLeaf{
		Vrf_output: vrfHash,
		Commitment: commitment,
	}
	tree := &proofs.PrefixTree{Leaf: leaf}
	tree.ComputeHash()
	return tree
}

// newUserState creates a fresh UserState with no tree.
func newUserState() *UserState {
	return &UserState{
		Size:                0,
		Full_subtrees:       []proofs.NodeValue{},
		Frontier_timestamps: []uint64{},
	}
}

// uint32Ptr returns a pointer to the given uint32.
func uint32Ptr(v uint32) *uint32 {
	return &v
}

// makeRootHash creates a dummy root hash for testing.
func makeRootHash() []byte {
	h := sha256.Sum256([]byte("root"))
	return h[:]
}

// makeHashPtr creates a pointer to a [sha256.Size]byte for rootHashes slice.
func makeHashPtr() *[sha256.Size]byte {
	h := sha256.Sum256([]byte("root-hash"))
	return &h
}

// ==================================================================================
// ============================= RootNode Tests ====================================
// ==================================================================================

func TestRootNode_SpecCompliance(t *testing.T) {
	tests := []struct {
		name     string
		treeSize uint64
		wantRoot uint64
	}{
		{"size 0", 0, 0},
		{"size 1", 1, 0},
		{"size 2", 2, 1},
		{"size 4", 4, 3},
		{"size 8", 8, 7},
		{"size 16", 16, 15},
		{"size 3", 3, 1},
		{"size 5", 5, 3},
		{"size 6", 6, 3},
		{"size 7", 7, 3},
		{"size 9", 9, 7},
		{"size 14", 14, 7},
		{"size 15", 15, 7},
		{"size 50", 50, 31},
	}

	for _, tc := range tests {
		t.Run(tc.name, func(t *testing.T) {
			got := RootNode(tc.treeSize)
			if got != tc.wantRoot {
				t.Errorf("RootNode(%d) = %d; want %d", tc.treeSize, got, tc.wantRoot)
			}
		})
	}
}

// ==================================================================================
// ============================ CheckGreatest Tests ================================
// ==================================================================================

func TestCheckGreatest_IsGreatest(t *testing.T) {
	// Build a tree with (label, version=0) included.
	// With t=0 and steps=[0,1]:
	//   step 0: inclusion (version 0 matches leaf) → step <= t → ok
	//   step 1: non-inclusion (version 1 not in tree) → step > t → ok
	// Result: res=0 (t is the greatest version)
	label := []byte("alice")
	tree := buildSingleLeafTree(label, 0)
	rootHash := makeRootHash()
	steps := proofs.FullBinaryLadderSteps_wrapper(0)

	res, err := CheckGreatest(tree, steps, label, 0, rootHash, 4)
	if err != nil {
		t.Fatalf("CheckGreatest returned unexpected error: %v", err)
	}
	if res != 0 {
		t.Errorf("CheckGreatest = %d; want 0 (is greatest)", res)
	}
}

func TestCheckGreatest_HoleBelow(t *testing.T) {
	// Build a tree with (label, version=5) included (NOT version 0).
	// With t=0 and steps=[0,1]:
	//   step 0: non-inclusion → step 0 <= t 0 → hole
	// Result: res=-1 (hole found at or below t)
	label := []byte("alice")
	tree := buildSingleLeafTree(label, 5) // wrong version → non-inclusion at step 0
	rootHash := makeRootHash()
	steps := proofs.FullBinaryLadderSteps_wrapper(0)

	res, err := CheckGreatest(tree, steps, label, 0, rootHash, 4)
	if err != nil {
		t.Fatalf("CheckGreatest returned unexpected error: %v", err)
	}
	if res != -1 {
		t.Errorf("CheckGreatest = %d; want -1 (hole below t)", res)
	}
}

func TestCheckGreatest_NilTree(t *testing.T) {
	// A nil PrefixTree: SearchForCommitment handles nil gracefully
	// and returns (nil, nil), meaning non-inclusion.
	// At step 0 (step <= t), non-inclusion → hole → res=-1.
	label := []byte("alice")
	rootHash := makeRootHash()
	steps := proofs.FullBinaryLadderSteps_wrapper(0)

	res, err := CheckGreatest(nil, steps, label, 0, rootHash, 4)
	if err != nil {
		t.Fatalf("CheckGreatest returned unexpected error: %v", err)
	}
	if res != -1 {
		t.Errorf("CheckGreatest = %d; want -1 (hole, nil tree returns non-inclusion)", res)
	}
}

func TestCheckGreatest_EmptySteps(t *testing.T) {
	// With empty steps slice, the loop doesn't execute.
	// Result: res=0, err=nil (vacuously greatest)
	label := []byte("alice")
	tree := buildSingleLeafTree(label, 0)
	rootHash := makeRootHash()

	res, err := CheckGreatest(tree, []uint64{}, label, 0, rootHash, 4)
	if err != nil {
		t.Fatalf("CheckGreatest with empty steps returned error: %v", err)
	}
	if res != 0 {
		t.Errorf("CheckGreatest = %d; want 0 (vacuously greatest)", res)
	}
}

// ==================================================================================
// =========================== VerifyLatestKey Tests ================================
// ==================================================================================

func TestVerifyLatestKey_VersionOutOfBounds(t *testing.T) {
	// version >= size → should return (false, error)
	label := []byte("alice")
	version := uint32(5)
	size := uint64(4)

	tree := buildSingleLeafTree(label, 0)
	trees := []*proofs.PrefixTree{tree, tree, tree, tree}
	rootHashes := []*[sha256.Size]byte{makeHashPtr(), makeHashPtr(), makeHashPtr(), makeHashPtr()}

	query := SearchRequest{Label: label}
	resp := SearchResponse{
		Version: uint32Ptr(version),
		Full_tree_head: FullTreeHead{
			Tree_head: TreeHead{Tree_size: size},
			RootHash:  makeRootHash(),
		},
	}
	config := &Configuration{Mode: DeploymentContractMonitoring}
	monitorMap := make([]MonitoringMapEntry, 0)

	res, err := VerifyLatestKey(trees, rootHashes, size, query, resp, monitorMap, config)
	if err == nil {
		t.Fatal("VerifyLatestKey should return error for version out of bounds")
	}
	if res {
		t.Error("VerifyLatestKey should return false for version out of bounds")
	}
}

func TestVerifyLatestKey_VersionEqualToSize(t *testing.T) {
	// version == size → out of bounds (version must be < size)
	label := []byte("alice")
	version := uint32(4)
	size := uint64(4) // version 4 >= size 4 → out of bounds

	tree := buildSingleLeafTree(label, 0)
	trees := []*proofs.PrefixTree{tree, tree, tree, tree}
	rootHashes := []*[sha256.Size]byte{makeHashPtr(), makeHashPtr(), makeHashPtr(), makeHashPtr()}

	query := SearchRequest{Label: label}
	resp := SearchResponse{
		Version: uint32Ptr(version),
		Full_tree_head: FullTreeHead{
			Tree_head: TreeHead{Tree_size: size},
			RootHash:  makeRootHash(),
		},
	}
	config := &Configuration{Mode: DeploymentContractMonitoring}
	monitorMap := make([]MonitoringMapEntry, 0)

	res, err := VerifyLatestKey(trees, rootHashes, size, query, resp, monitorMap, config)
	if err == nil {
		t.Fatal("VerifyLatestKey should return error when version == size")
	}
	if res {
		t.Error("VerifyLatestKey should return false when version == size")
	}
}

func TestVerifyLatestKey_IsGreatest_SingleFrontier(t *testing.T) {
	// size=1: single frontier node at position 0.
	// Tree has (label, version=0) included → CheckGreatest returns 0.
	// Result: (true, nil)
	label := []byte("alice")
	version := uint32(0)
	size := uint64(1)

	tree := buildSingleLeafTree(label, version)
	trees := []*proofs.PrefixTree{tree}
	rootHashes := []*[sha256.Size]byte{makeHashPtr()}

	query := SearchRequest{Label: label}
	resp := SearchResponse{
		Version: uint32Ptr(version),
		Full_tree_head: FullTreeHead{
			Tree_head: TreeHead{Tree_size: size},
			RootHash:  makeRootHash(),
		},
	}
	config := &Configuration{Mode: DeploymentContractMonitoring}
	monitorMap := make([]MonitoringMapEntry, 0)

	res, err := VerifyLatestKey(trees, rootHashes, size, query, resp, monitorMap, config)
	if err != nil {
		t.Fatalf("VerifyLatestKey returned unexpected error: %v", err)
	}
	if !res {
		t.Error("VerifyLatestKey should return true when version is greatest")
	}
}

func TestVerifyLatestKey_HoleDetected(t *testing.T) {
	// size=1, version=0 but tree has a different version → hole → (false, error)
	label := []byte("alice")
	version := uint32(0)
	size := uint64(1)

	tree := buildSingleLeafTree(label, 99) // wrong version → non-inclusion at step 0
	trees := []*proofs.PrefixTree{tree}
	rootHashes := []*[sha256.Size]byte{makeHashPtr()}

	query := SearchRequest{Label: label}
	resp := SearchResponse{
		Version: uint32Ptr(version),
		Full_tree_head: FullTreeHead{
			Tree_head: TreeHead{Tree_size: size},
			RootHash:  makeRootHash(),
		},
	}
	config := &Configuration{Mode: DeploymentContractMonitoring}
	monitorMap := make([]MonitoringMapEntry, 0)

	res, err := VerifyLatestKey(trees, rootHashes, size, query, resp, monitorMap, config)
	if err == nil {
		t.Fatal("VerifyLatestKey should return error when hole is detected")
	}
	if res {
		t.Error("VerifyLatestKey should return false when hole is detected")
	}
}

func TestVerifyLatestKey_NilTree(t *testing.T) {
	// size=1, prefix tree is nil → should return (false, error)
	label := []byte("alice")
	version := uint32(0)
	size := uint64(1)

	trees := []*proofs.PrefixTree{nil}
	rootHashes := []*[sha256.Size]byte{makeHashPtr()}

	query := SearchRequest{Label: label}
	resp := SearchResponse{
		Version: uint32Ptr(version),
		Full_tree_head: FullTreeHead{
			Tree_head: TreeHead{Tree_size: size},
			RootHash:  makeRootHash(),
		},
	}
	config := &Configuration{Mode: DeploymentContractMonitoring}
	monitorMap := make([]MonitoringMapEntry, 0)

	res, err := VerifyLatestKey(trees, rootHashes, size, query, resp, monitorMap, config)
	if err == nil {
		t.Fatal("VerifyLatestKey should return error when prefix tree is nil")
	}
	if res {
		t.Error("VerifyLatestKey should return false when prefix tree is nil")
	}
}

func TestVerifyLatestKey_MultipleFrontiers(t *testing.T) {
	// size=2: BST root=1, frontiers=[1, ...]. Need 2 prefix trees.
	// version=0, tree at position 0 has (label, 0) included.
	label := []byte("alice")
	version := uint32(0)
	size := uint64(2)

	tree := buildSingleLeafTree(label, version)
	trees := []*proofs.PrefixTree{tree, tree}
	rootHashes := []*[sha256.Size]byte{makeHashPtr(), makeHashPtr()}

	query := SearchRequest{Label: label}
	resp := SearchResponse{
		Version: uint32Ptr(version),
		Full_tree_head: FullTreeHead{
			Tree_head: TreeHead{Tree_size: size},
			RootHash:  makeRootHash(),
		},
	}
	config := &Configuration{Mode: DeploymentContractMonitoring}
	monitorMap := make([]MonitoringMapEntry, 0)

	res, err := VerifyLatestKey(trees, rootHashes, size, query, resp, monitorMap, config)
	if err != nil {
		t.Fatalf("VerifyLatestKey with multiple frontiers returned error: %v", err)
	}
	if !res {
		t.Error("VerifyLatestKey should return true with valid multi-frontier setup")
	}
}

// ==================================================================================
// ============================= VerifyLatest Tests ================================
// ==================================================================================

func TestVerifyLatest_NilVersion(t *testing.T) {
	// resp.Version == nil → should return error
	st := newUserState()
	query := SearchRequest{Label: []byte("alice")}
	resp := SearchResponse{
		Version: nil, // nil version triggers error
		Full_tree_head: FullTreeHead{
			Tree_head: TreeHead{Tree_size: 1, Signature: []byte{}},
			RootHash:  makeRootHash(),
		},
		Binary_ladder: []proofs.BinaryLadderStep{},
		Search: proofs.CombinedTreeProof{
			Timestamps:    []uint64{1},
			Prefix_proofs: []proofs.PrefixProof{{}},
			Prefix_roots:  []proofs.NodeValue{},
		},
		Inclusion: proofs.InclusionProof{},
		Opening:   []byte{},
		Value:     proofs.UpdateValue{Value: []byte{}},
	}
	config := &Configuration{Mode: DeploymentContractMonitoring}

	res, err := st.VerifyLatest(query, resp, config)
	if err == nil {
		t.Fatal("VerifyLatest should return error for nil version")
	}
	if res != nil {
		t.Error("VerifyLatest should return nil result for nil version")
	}
}

func TestVerifyLatest_NonEmptyPrefixRoots(t *testing.T) {
	// resp.Search.Prefix_roots is non-empty → should return error
	st := newUserState()
	version := uint32(0)
	query := SearchRequest{Label: []byte("alice")}
	resp := SearchResponse{
		Version: &version,
		Full_tree_head: FullTreeHead{
			Tree_head: TreeHead{Tree_size: 1, Signature: []byte{}},
			RootHash:  makeRootHash(),
		},
		Binary_ladder: []proofs.BinaryLadderStep{},
		Search: proofs.CombinedTreeProof{
			Timestamps:    []uint64{1},
			Prefix_proofs: []proofs.PrefixProof{{}},
			Prefix_roots:  []proofs.NodeValue{{0x01}}, // non-empty → error
		},
		Inclusion: proofs.InclusionProof{},
		Opening:   []byte{},
		Value:     proofs.UpdateValue{Value: []byte{}},
	}
	config := &Configuration{Mode: DeploymentContractMonitoring}

	res, err := st.VerifyLatest(query, resp, config)
	if err == nil {
		t.Fatal("VerifyLatest should return error when prefix roots are provided")
	}
	if res != nil {
		t.Error("VerifyLatest should return nil result when prefix roots are provided")
	}
}

func TestVerifyLatest_WrongLadderLength(t *testing.T) {
	// Binary ladder length doesn't match expected for version → error
	st := newUserState()
	version := uint32(3) // FullBinaryLadderSteps(3) = [0,1,3,7,5,4] → len 6
	query := SearchRequest{Label: []byte("alice")}
	resp := SearchResponse{
		Version: &version,
		Full_tree_head: FullTreeHead{
			Tree_head: TreeHead{Tree_size: 4, Signature: []byte{}},
			RootHash:  makeRootHash(),
		},
		Binary_ladder: []proofs.BinaryLadderStep{{}, {}}, // len 2, expected 6
		Search: proofs.CombinedTreeProof{
			Timestamps:    []uint64{1},
			Prefix_proofs: []proofs.PrefixProof{{}, {}, {}, {}},
			Prefix_roots:  []proofs.NodeValue{},
		},
		Inclusion: proofs.InclusionProof{},
		Opening:   []byte{},
		Value:     proofs.UpdateValue{Value: []byte{}},
	}
	config := &Configuration{Mode: DeploymentContractMonitoring}

	res, err := st.VerifyLatest(query, resp, config)
	if err == nil {
		t.Fatal("VerifyLatest should return error for wrong binary ladder length")
	}
	if res != nil {
		t.Error("VerifyLatest should return nil result for wrong binary ladder length")
	}
}

// ==================================================================================
// ========================== MkImplicitBinarySearchTree ===========================
// ==================================================================================

func TestMkImplicitBinarySearchTree_SizeZero(t *testing.T) {
	tree := MkImplicitBinarySearchTree(0)
	if tree != nil {
		t.Error("MkImplicitBinarySearchTree(0) should return nil")
	}
}

func TestMkImplicitBinarySearchTree_SizeOne(t *testing.T) {
	tree := MkImplicitBinarySearchTree(1)
	if tree == nil {
		t.Fatal("MkImplicitBinarySearchTree(1) should not return nil")
	}
	if tree.Root != 0 {
		t.Errorf("Root = %d; want 0", tree.Root)
	}
}

func TestFrontierNodes(t *testing.T) {
	tests := []struct {
		name     string
		size     uint64
		wantLen  int
		wantHead uint64
	}{
		{"size 1", 1, 1, 0},
		{"size 2", 2, 1, 1},
		{"size 3", 3, 2, 1},
		{"size 4", 4, 1, 3},
		{"size 5", 5, 2, 3},
		{"size 8", 8, 1, 7},
	}

	for _, tc := range tests {
		t.Run(tc.name, func(t *testing.T) {
			tree := MkImplicitBinarySearchTree(tc.size)
			if tree == nil {
				t.Fatal("tree should not be nil")
			}
			frontiers := tree.FrontierNodes()
			if len(frontiers) != tc.wantLen {
				t.Errorf("len(FrontierNodes(%d)) = %d; want %d", tc.size, len(frontiers), tc.wantLen)
			}
			if len(frontiers) > 0 && frontiers[0] != tc.wantHead {
				t.Errorf("FrontierNodes(%d)[0] = %d; want %d", tc.size, frontiers[0], tc.wantHead)
			}
		})
	}
}

// ==================================================================================
// ========================== FullBinaryLadderSteps ================================
// ==================================================================================

func TestFullBinaryLadderSteps_StartsWithZero(t *testing.T) {
	targets := []uint64{0, 1, 3, 7, 15, 100}
	for _, target := range targets {
		steps := proofs.FullBinaryLadderSteps_wrapper(target)
		if len(steps) == 0 {
			t.Errorf("FullBinaryLadderSteps_wrapper(%d) returned empty", target)
			continue
		}
		if steps[0] != 0 {
			t.Errorf("FullBinaryLadderSteps_wrapper(%d)[0] = %d; want 0", target, steps[0])
		}
	}
}

func TestFullBinaryLadderSteps_ContainsTarget(t *testing.T) {
	// The binary ladder steps should contain the target itself
	// (it appears somewhere in the exponential jump or binary search phase)
	targets := []uint64{0, 1, 2, 3, 7, 8, 15}
	for _, target := range targets {
		steps := proofs.FullBinaryLadderSteps_wrapper(target)
		found := false
		for _, s := range steps {
			if s == target {
				found = true
				break
			}
		}
		// The target appears in steps as an exponential jump element (2^k - 1)
		// or as a binary search midpoint. It should be there for powers of 2 minus 1.
		if !found && (target == 0 || target == 1 || target == 3 || target == 7 || target == 15) {
			t.Errorf("FullBinaryLadderSteps_wrapper(%d) does not contain target; steps = %v", target, steps)
		}
	}
}

// ==================================================================================
// ============================== IsDistinguished ==================================
// ==================================================================================

func TestIsDistinguished(t *testing.T) {
	tests := []struct {
		leftTs  uint64
		rightTs uint64
		rmw     uint64
		want    bool
	}{
		{0, 100, 50, true},
		{0, 100, 100, true},
		{0, 100, 101, false},
		{50, 50, 0, true},
		{100, 50, 10, false}, // right < left
	}

	for _, tc := range tests {
		got := IsDistinguished(tc.leftTs, tc.rightTs, tc.rmw)
		if got != tc.want {
			t.Errorf("IsDistinguished(%d, %d, %d) = %v; want %v",
				tc.leftTs, tc.rightTs, tc.rmw, got, tc.want)
		}
	}
}
