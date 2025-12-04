package client

//The following function is for property we want to prove

// To show: forall l p1 p2. p1.root == p2.root ==> st1.VerifyLatestKey(query1, resp1) == st2.VerifyLatestKey(query2, resp2)

// ghost
// requires acc(st1, _) && acc(st2, _)
// requires acc(resp1,_) && acc(resp2,_)
// requires acc(query, _)
// requires st1.Full_tree_head == st2.Full_tree_head //Maybe we need to do something here, pure comparison may not work
// requires st1.Size > 0 && st2.Size > 0 			   //Edge case: First time inspection?
// requires query1.Label == query2.Label 			   //We need this because we don't know if the the last in the SearchRequest is the same
// ensures err == nil ==> resp1.Version == resp2.Version //TODO: Maybe requires? Because we want to prove the function itself given the same version..
// ensures err == nil ==> CheckEquality(st1.VerifyLatestKey(query1, resp1), st2.VerifyLatestKey(query2, resp2))
// pure
func LemmaConsistencyGreatestVersionSearch(st1 *UserState, st2 *UserState, query1 SearchRequest, query2 SearchRequest,
	resp1 SearchResponse, resp2 SearchResponse) (err error) {
	//TODO: Implement
	return nil
}
