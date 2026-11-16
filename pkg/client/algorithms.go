package client

import (
	"github.com/felixlinker/keytrans-verification/pkg/search"
	"github.com/felixlinker/keytrans-verification/pkg/trees/prefix"
)

// ##(--hyperMode extended --enableExperimentalHyperFeatures)

// The algorithms below request timestamps and prefix proofs from a
// ProofReader in exactly the order defined by draft-ietf-keytrans-protocol.
// Errors are recorded in the reader; callers check r.Err().

// updateView requests the timestamps needed to update the user's view of the
// tree from size `m` (0 if the user has no previous view) to size r.n
// (Section "Updating Views of the Tree"): the log entries on the direct path of
// entry m-1 with index >= m, followed by the remainder of the new frontier. If
// the user has no previous view, this is the frontier of the new tree.
// @ trusted
func updateView(r *ProofReader, m uint64) {
	var entries []uint64
	if m == 0 {
		entries = search.Frontier(r.n)
	} else {
		entries = search.YoungerToMostRecent(m-1, r.n)
	}
	for i := 0; i < len(entries) && r.Err() == nil; i++ {
		r.GetTimestamp(entries[i])
	}
}

// greatestVersionSearch requests the prefix proofs for a greatest-version
// search (Section "Greatest-Version Search"): a search binary ladder from each
// log entry along the frontier, starting at the rightmost distinguished log
// entry. It returns the reconstructed prefix trees, in frontier order.
//
// The frontier timestamps are always known after updateView, so identifying
// the starting log entry consumes no timestamps.
// @ trusted
func greatestVersionSearch(r *ProofReader, rmw uint64) (pts []*prefix.Tree) {
	frontier := search.Frontier(r.n)
	timestamps := make([]uint64, len(frontier))
	for i := 0; i < len(frontier); i++ {
		timestamps[i] = r.GetTimestamp(frontier[i])
	}
	if r.Err() != nil {
		return nil
	}

	start := search.MostRecentDistinguished(timestamps, rmw /*@, perm(1/2) @*/)
	for i := start; i < len(frontier) && r.Err() == nil; i++ {
		if t := r.GetPrefixProof(frontier[i]); t != nil {
			pts = auxAppend(pts, t)
		}
	}
	return
}
