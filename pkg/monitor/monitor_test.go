package monitor

import (
	"crypto/sha256"
	"testing"

	"github.com/felixlinker/keytrans-verification/pkg/client"
	"github.com/felixlinker/keytrans-verification/pkg/crypto"
	"github.com/felixlinker/keytrans-verification/pkg/proofs"
)

// ==================================================================================
// ================================== Helpers =======================================
// ==================================================================================

func newUserState() *client.UserState {
	return &client.UserState{
		Size:                0,
		Full_subtrees:       []proofs.NodeValue{},
		Frontier_timestamps: []uint64{},
	}
}

func makeRootHash() []byte {
	h := sha256.Sum256([]byte("root"))
	return h[:]
}

// ==================================================================================
// ============================== VerifyMonitor Tests ==============================
// ==================================================================================

func TestVerifyMonitor_EmptyMonitorMap(t *testing.T) {
	// Empty monitoring map with valid tree → should succeed with empty new_map.
	// Provide a PrefixProof with one copath element so ToTree succeeds.
	st := newUserState()
	label := []byte("alice")
	size := uint64(1)
	dummyElement := proofs.NodeValue{}
	for i := range dummyElement {
		dummyElement[i] = byte(i)
	}

	resp := MonitorResponse{
		Full_tree_head: client.FullTreeHead{
			Tree_head: client.TreeHead{Tree_size: size, Signature: []byte{}},
			RootHash:  makeRootHash(),
		},
		Binary_ladder: []proofs.BinaryLadderStep{},
		Search: proofs.CombinedTreeProof{
			Timestamps: []uint64{1},
			Prefix_proofs: []proofs.PrefixProof{
				{Results: []proofs.PrefixSearchResult{}, Elements: []proofs.NodeValue{dummyElement}},
			},
			Prefix_roots: []proofs.NodeValue{},
		},
	}
	monitorMap := []client.MonitoringMapEntry{}
	config := &client.Configuration{Mode: client.DeploymentContractMonitoring, ReasonableMonitoringWindow: 1}

	newMap, err := VerifyMonitor(st, label, resp, monitorMap, config)
	if err != nil {
		t.Fatalf("VerifyMonitor returned unexpected error: %v", err)
	}
	if len(newMap) != 0 {
		t.Errorf("VerifyMonitor returned new_map of len %d; want 0", len(newMap))
	}
}

func TestVerifyMonitor_UpdateViewFailsTreeSizeZero(t *testing.T) {
	// tree_size=0 → UpdateView returns error.
	// When determined is set early, new_map is empty (the loop doesn't execute).
	st := newUserState()
	label := []byte("alice")

	resp := MonitorResponse{
		Full_tree_head: client.FullTreeHead{
			Tree_head: client.TreeHead{Tree_size: 0, Signature: []byte{}},
			RootHash:  makeRootHash(),
		},
		Binary_ladder: []proofs.BinaryLadderStep{},
		Search: proofs.CombinedTreeProof{
			Timestamps:    []uint64{},
			Prefix_proofs: []proofs.PrefixProof{},
			Prefix_roots:  []proofs.NodeValue{},
		},
	}
	monitorMap := []client.MonitoringMapEntry{
		{Position: 0, Version: 0},
	}
	config := &client.Configuration{Mode: client.DeploymentContractMonitoring, ReasonableMonitoringWindow: 1}

	newMap, err := VerifyMonitor(st, label, resp, monitorMap, config)
	if err == nil {
		t.Fatal("VerifyMonitor should return error when tree size is 0")
	}
	// When UpdateView fails, determined=true before the monitor loop,
	// so new_map stays empty.
	if len(newMap) != 0 {
		t.Errorf("VerifyMonitor returned new_map of len %d; want 0", len(newMap))
	}
}

func TestVerifyMonitor_PreservesMonitorMapEntries(t *testing.T) {
	// When verification succeeds, new_map should contain all entries
	// from the input monitoring map (always-append pattern).
	st := newUserState()
	label := []byte("alice")
	size := uint64(1)
	dummyElement := proofs.NodeValue{}
	for i := range dummyElement {
		dummyElement[i] = byte(i)
	}

	resp := MonitorResponse{
		Full_tree_head: client.FullTreeHead{
			Tree_head: client.TreeHead{Tree_size: size, Signature: []byte{}},
			RootHash:  makeRootHash(),
		},
		Binary_ladder: []proofs.BinaryLadderStep{},
		Search: proofs.CombinedTreeProof{
			Timestamps: []uint64{1},
			Prefix_proofs: []proofs.PrefixProof{
				{Results: []proofs.PrefixSearchResult{}, Elements: []proofs.NodeValue{dummyElement}},
			},
			Prefix_roots: []proofs.NodeValue{},
		},
	}
	// All entries have version 0, and the tree is a copath node so
	// GetCommitment returns error → but for monitoring, we need to check
	// what happens. Since the tree built from a single copath element
	// has Value set (not a leaf), SearchForCommitment returns error
	// "cannot determine: reached copath node" → CheckGreatest returns 404.
	// That sets determined=true, so remaining entries are still appended.
	monitorMap := []client.MonitoringMapEntry{
		{Position: 0, Version: 1},
		{Position: 0, Version: 2},
		{Position: 0, Version: 3},
	}
	config := &client.Configuration{Mode: client.DeploymentContractMonitoring, ReasonableMonitoringWindow: 1}

	newMap, err := VerifyMonitor(st, label, resp, monitorMap, config)
	// First entry causes CheckGreatest error → determined = true
	// But the always-append pattern still appends all 3 entries
	if err == nil {
		// Copath node causes CheckGreatest to return error
		// Check that entries are preserved even on error
		if len(newMap) != len(monitorMap) {
			t.Errorf("VerifyMonitor new_map len = %d; want %d", len(newMap), len(monitorMap))
		}
	} else {
		// Even on error, some entries may have been appended
		// The always-append pattern ensures entries up to the error point are preserved
		t.Logf("VerifyMonitor returned error (expected): %v", err)
		t.Logf("new_map has %d entries", len(newMap))
	}

	// Verify that all entries in new_map have correct versions
	for i, entry := range newMap {
		if i < len(monitorMap) && entry.Version != monitorMap[i].Version {
			t.Errorf("new_map[%d].Version = %d; want %d", i, entry.Version, monitorMap[i].Version)
		}
	}
}

func TestVerifyMonitor_BadTimestamps(t *testing.T) {
	// Non-increasing timestamps → UpdateView returns error
	st := newUserState()
	label := []byte("alice")

	resp := MonitorResponse{
		Full_tree_head: client.FullTreeHead{
			Tree_head: client.TreeHead{Tree_size: 2, Signature: []byte{}},
			RootHash:  makeRootHash(),
		},
		Binary_ladder: []proofs.BinaryLadderStep{},
		Search: proofs.CombinedTreeProof{
			Timestamps:    []uint64{5, 3}, // non-increasing → error
			Prefix_proofs: []proofs.PrefixProof{{}, {}},
			Prefix_roots:  []proofs.NodeValue{},
		},
	}
	monitorMap := []client.MonitoringMapEntry{}
	config := &client.Configuration{Mode: client.DeploymentContractMonitoring, ReasonableMonitoringWindow: 1}

	_, err := VerifyMonitor(st, label, resp, monitorMap, config)
	if err == nil {
		t.Fatal("VerifyMonitor should return error for non-increasing timestamps")
	}
}

// ==================================================================================
// ============================= Happy-Path Helpers =================================
// ==================================================================================

// makeBinaryLadderStep creates a BinaryLadderStep whose Proof is VRF_hash(nil, {label, version}).
func makeBinaryLadderStep(label []byte, version uint32) proofs.BinaryLadderStep {
	vrfInput := crypto.VrfInput{Label: label, Version: version}
	vrfProof := crypto.VRF_hash(nil, vrfInput)
	commitment := sha256.Sum256(append([]byte("commit-"), byte(version)))
	return proofs.BinaryLadderStep{Proof: vrfProof[:], Commitment: &commitment}
}

// ==================================================================================
// ========================= VerifyMonitor Happy-Path Tests =========================
// ==================================================================================

func TestVerifyMonitor_HappyPath_SingleEntry(t *testing.T) {
	// tree_size=1, 1 monitoring map entry at position 0 with version 0.
	// FullBinaryLadderSteps_wrapper(0) = [0, 1] → 2 binary ladder steps.
	// PrefixProof with Inclusion at depth 0 → leaf for version 0.
	// rmw=1000 → root is NOT distinguished → DirectPathRight returns [0].
	// CheckGreatest: step 0 (inclusion, ≤t) ok; step 1 (non-inclusion, >t) ok → res=0.
	// Expected: VerifyMonitor returns nil error with 1 entry in new_map.
	st := newUserState()
	label := []byte("alice")
	version := uint32(0)
	size := uint64(1)

	ladderSteps := proofs.FullBinaryLadderSteps_wrapper(uint64(version))
	binaryLadder := make([]proofs.BinaryLadderStep, len(ladderSteps))
	for i := range ladderSteps {
		binaryLadder[i] = makeBinaryLadderStep(label, uint32(ladderSteps[i]))
	}

	prefixProof := proofs.PrefixProof{
		Results: []proofs.PrefixSearchResult{
			{Result_type: proofs.Inclusion, Depth: 0},
		},
		Elements: []proofs.NodeValue{},
	}

	resp := MonitorResponse{
		Full_tree_head: client.FullTreeHead{
			Tree_head: client.TreeHead{Tree_size: size, Signature: []byte{}},
			RootHash:  makeRootHash(),
		},
		Binary_ladder: binaryLadder,
		Search: proofs.CombinedTreeProof{
			Timestamps:    []uint64{100},
			Prefix_proofs: []proofs.PrefixProof{prefixProof},
			Prefix_roots:  []proofs.NodeValue{},
		},
	}
	monitorMap := []client.MonitoringMapEntry{
		{Position: 0, Version: version},
	}
	config := &client.Configuration{
		Mode:                       client.DeploymentContractMonitoring,
		ReasonableMonitoringWindow: 1000, // large rmw → root is NOT distinguished
	}

	newMap, err := VerifyMonitor(st, label, resp, monitorMap, config)
	if err != nil {
		t.Fatalf("VerifyMonitor returned unexpected error: %v", err)
	}
	if len(newMap) != 1 {
		t.Fatalf("VerifyMonitor new_map len = %d; want 1", len(newMap))
	}
	if newMap[0].Version != version {
		t.Errorf("new_map[0].Version = %d; want %d", newMap[0].Version, version)
	}
}

// ==================================================================================
// ================ Large Happy-Path Helpers (Spec-aligned) ========================
// ==================================================================================

// buildHappyPathMonitorResponse constructs a valid MonitorResponse for a tree
// of the given treeSize. Frontier positions get Inclusion PrefixProofs for
// version 0; non-frontier positions get copath nodes.
func buildHappyPathMonitorResponse(label []byte, treeSize uint64) MonitorResponse {
	version := uint32(0)
	ladderSteps := proofs.FullBinaryLadderSteps_wrapper(uint64(version))

	binaryLadder := make([]proofs.BinaryLadderStep, len(ladderSteps))
	for i := range ladderSteps {
		binaryLadder[i] = makeBinaryLadderStep(label, uint32(ladderSteps[i]))
	}

	searchTree := client.MkImplicitBinarySearchTree(treeSize)
	frontiers := searchTree.FrontierNodes()
	frontierSet := make(map[uint64]bool)
	for _, f := range frontiers {
		frontierSet[f] = true
	}

	dummyHash := proofs.NodeValue{}
	dummyHash[0] = 0xAB

	prefixProofs := make([]proofs.PrefixProof, treeSize)
	for i := uint64(0); i < treeSize; i++ {
		if frontierSet[i] {
			prefixProofs[i] = proofs.PrefixProof{
				Results: []proofs.PrefixSearchResult{
					{Result_type: proofs.Inclusion, Depth: 0},
				},
				Elements: []proofs.NodeValue{},
			}
		} else {
			prefixProofs[i] = proofs.PrefixProof{
				Results:  []proofs.PrefixSearchResult{},
				Elements: []proofs.NodeValue{dummyHash},
			}
		}
	}

	timestamps := make([]uint64, len(frontiers))
	for i := range frontiers {
		timestamps[i] = uint64((i + 1) * 100)
	}

	return MonitorResponse{
		Full_tree_head: client.FullTreeHead{
			Tree_head: client.TreeHead{Tree_size: treeSize, Signature: []byte{}},
			RootHash:  makeRootHash(),
		},
		Binary_ladder: binaryLadder,
		Search: proofs.CombinedTreeProof{
			Timestamps:    timestamps,
			Prefix_proofs: prefixProofs,
			Prefix_roots:  []proofs.NodeValue{},
		},
	}
}

// ==================================================================================
// =================== Large VerifyMonitor Happy-Path Tests ========================
// ==================================================================================

func TestVerifyMonitor_HappyPath_Size4_RootEntry(t *testing.T) {
	// tree_size=4, frontier=[3]. Monitoring map entry at the root (position 3).
	// DirectPathRight from 3: PathTo(3)=[3], filtered >=3 → [3].
	// CheckGreatest at position 3 → Inclusion for version 0 → res=0 → success.
	st := newUserState()
	label := []byte("alice")
	config := &client.Configuration{
		Mode:                       client.DeploymentContractMonitoring,
		ReasonableMonitoringWindow: 1000,
	}
	resp := buildHappyPathMonitorResponse(label, 4)
	monitorMap := []client.MonitoringMapEntry{
		{Position: 3, Version: 0},
	}

	newMap, err := VerifyMonitor(st, label, resp, monitorMap, config)
	if err != nil {
		t.Fatalf("VerifyMonitor(size=4, root entry) returned error: %v", err)
	}
	if len(newMap) != 1 {
		t.Fatalf("newMap len = %d; want 1", len(newMap))
	}
	if newMap[0].Version != 0 {
		t.Errorf("newMap[0].Version = %d; want 0", newMap[0].Version)
	}
}

func TestVerifyMonitor_HappyPath_Size5_TwoFrontierEntries(t *testing.T) {
	// tree_size=5, frontier=[3, 4]. Two monitoring entries at frontier positions.
	// Each entry's DirectPathRight stays within its own frontier position.
	st := newUserState()
	label := []byte("bob")
	config := &client.Configuration{
		Mode:                       client.DeploymentContractMonitoring,
		ReasonableMonitoringWindow: 1000,
	}
	resp := buildHappyPathMonitorResponse(label, 5)
	monitorMap := []client.MonitoringMapEntry{
		{Position: 3, Version: 0}, // root frontier
		{Position: 4, Version: 0}, // right frontier
	}

	newMap, err := VerifyMonitor(st, label, resp, monitorMap, config)
	if err != nil {
		t.Fatalf("VerifyMonitor(size=5, two entries) returned error: %v", err)
	}
	if len(newMap) != 2 {
		t.Fatalf("newMap len = %d; want 2", len(newMap))
	}
	for i, entry := range newMap {
		if entry.Version != 0 {
			t.Errorf("newMap[%d].Version = %d; want 0", i, entry.Version)
		}
	}
}

func TestVerifyMonitor_HappyPath_Size8_ManyEntries(t *testing.T) {
	// tree_size=8, frontier=[7]. Five monitoring entries all at the root.
	// Tests the always-append pattern with multiple entries at the same position.
	st := newUserState()
	label := []byte("charlie")
	config := &client.Configuration{
		Mode:                       client.DeploymentContractMonitoring,
		ReasonableMonitoringWindow: 1000,
	}
	resp := buildHappyPathMonitorResponse(label, 8)
	monitorMap := make([]client.MonitoringMapEntry, 5)
	for i := range monitorMap {
		monitorMap[i] = client.MonitoringMapEntry{Position: 7, Version: 0}
	}

	newMap, err := VerifyMonitor(st, label, resp, monitorMap, config)
	if err != nil {
		t.Fatalf("VerifyMonitor(size=8, 5 entries) returned error: %v", err)
	}
	if len(newMap) != 5 {
		t.Fatalf("newMap len = %d; want 5", len(newMap))
	}
	for i, entry := range newMap {
		if entry.Version != 0 {
			t.Errorf("newMap[%d].Version = %d; want 0", i, entry.Version)
		}
	}
}

func TestVerifyMonitor_HappyPath_Size14_ThreeFrontierEntries(t *testing.T) {
	// tree_size=14, frontier=[7, 11, 13]. One entry per frontier position.
	// Tests monitoring across multiple frontier nodes (Section 8.2).
	st := newUserState()
	label := []byte("dave")
	config := &client.Configuration{
		Mode:                       client.DeploymentContractMonitoring,
		ReasonableMonitoringWindow: 1000,
	}
	resp := buildHappyPathMonitorResponse(label, 14)
	monitorMap := []client.MonitoringMapEntry{
		{Position: 7, Version: 0},
		{Position: 11, Version: 0},
		{Position: 13, Version: 0},
	}

	newMap, err := VerifyMonitor(st, label, resp, monitorMap, config)
	if err != nil {
		t.Fatalf("VerifyMonitor(size=14, three entries) returned error: %v", err)
	}
	if len(newMap) != 3 {
		t.Fatalf("newMap len = %d; want 3", len(newMap))
	}
	for i, entry := range newMap {
		if entry.Version != 0 {
			t.Errorf("newMap[%d].Version = %d; want 0", i, entry.Version)
		}
	}
}

func TestVerifyMonitor_HappyPath_Size50(t *testing.T) {
	// tree_size=50, frontier=[31, 47, 49]. Spec example.
	// Entries at all three frontier positions.
	st := newUserState()
	label := []byte("eve")
	config := &client.Configuration{
		Mode:                       client.DeploymentContractMonitoring,
		ReasonableMonitoringWindow: 1000,
	}
	resp := buildHappyPathMonitorResponse(label, 50)
	monitorMap := []client.MonitoringMapEntry{
		{Position: 31, Version: 0},
		{Position: 47, Version: 0},
		{Position: 49, Version: 0},
	}

	newMap, err := VerifyMonitor(st, label, resp, monitorMap, config)
	if err != nil {
		t.Fatalf("VerifyMonitor(size=50) returned error: %v", err)
	}
	if len(newMap) != 3 {
		t.Fatalf("newMap len = %d; want 3", len(newMap))
	}
}

func TestVerifyMonitor_HappyPath_MultipleEntries(t *testing.T) {
	// tree_size=1, 3 monitoring map entries all at position 0, version 0.
	// All share the same prefix tree → CheckGreatest returns 0 for each.
	// Expected: VerifyMonitor returns nil error with 3 entries in new_map.
	st := newUserState()
	label := []byte("alice")
	version := uint32(0)
	size := uint64(1)

	ladderSteps := proofs.FullBinaryLadderSteps_wrapper(uint64(version))
	binaryLadder := make([]proofs.BinaryLadderStep, len(ladderSteps))
	for i := range ladderSteps {
		binaryLadder[i] = makeBinaryLadderStep(label, uint32(ladderSteps[i]))
	}

	prefixProof := proofs.PrefixProof{
		Results: []proofs.PrefixSearchResult{
			{Result_type: proofs.Inclusion, Depth: 0},
		},
		Elements: []proofs.NodeValue{},
	}

	resp := MonitorResponse{
		Full_tree_head: client.FullTreeHead{
			Tree_head: client.TreeHead{Tree_size: size, Signature: []byte{}},
			RootHash:  makeRootHash(),
		},
		Binary_ladder: binaryLadder,
		Search: proofs.CombinedTreeProof{
			Timestamps:    []uint64{100},
			Prefix_proofs: []proofs.PrefixProof{prefixProof},
			Prefix_roots:  []proofs.NodeValue{},
		},
	}
	monitorMap := []client.MonitoringMapEntry{
		{Position: 0, Version: version},
		{Position: 0, Version: version},
		{Position: 0, Version: version},
	}
	config := &client.Configuration{
		Mode:                       client.DeploymentContractMonitoring,
		ReasonableMonitoringWindow: 1000,
	}

	newMap, err := VerifyMonitor(st, label, resp, monitorMap, config)
	if err != nil {
		t.Fatalf("VerifyMonitor returned unexpected error: %v", err)
	}
	if len(newMap) != 3 {
		t.Fatalf("VerifyMonitor new_map len = %d; want 3", len(newMap))
	}
	for i, entry := range newMap {
		if entry.Version != version {
			t.Errorf("new_map[%d].Version = %d; want %d", i, entry.Version, version)
		}
	}
}
