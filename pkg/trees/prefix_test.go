package trees

import (
	"crypto/sha256"
	"encoding/hex"
	"testing"

	"github.com/felixlinker/keytrans-verification/pkg/proofs"
)

type prefixDictVector struct {
	name              string
	label             string
	version           uint64
	publicKey         string
	ladderVersions    []uint64
	ladderProofs      []string
	ladderCommitments []string
	prefixResults     []prefixDictResultVector
	prefixElements    []string
	expectedRoot      string
}

type prefixDictResultVector struct {
	resultType     int
	depth          uint8
	leafVrfOutput  string
	leafCommitment string
}

var prefixDictVectors = []prefixDictVector{
	{
		name:      "user000@example.com-v0",
		label:     "user000@example.com",
		version:   0,
		publicKey: "23bc54912c1e6e92c4a86825c867e27ffdc555bffbd4244f17a26abfffee965d",
		ladderVersions: []uint64{
			0, 1,
		},
		ladderProofs: []string{
			"dde7bc4500529c2c837cb6d316c9af45c59c5a750ad24c39b0bff33bd88055f435115b1c364feb452c6ca9692500c339d44c95fa3c543cae87de3ecb97b314315c831c0eb54b86eeafd3a0c83c9a250c",
			"3081be8b1a45fecb0c280d12f08a4db47aeba960123475f559ec55a31e252cfab8db2425979966d0a58075c541d469a312069a9a3847a2f4d30014e35ac664ac7e3e469e5e67e36ae7a4e4fe0fab2009",
		},
		ladderCommitments: []string{
			"2626ec08fb1709477093732fc9d18df486f419838e10ebe8618f9275f7babda5",
			"0000000000000000000000000000000000000000000000000000000000000000",
		},
		prefixResults: []prefixDictResultVector{
			{resultType: proofs.Inclusion, depth: 12},
			{
				resultType:     proofs.NonInclusionLeaf,
				depth:          8,
				leafVrfOutput:  "b9e10134e1c253851d8f01a61b0b9f10d38a204dc14c7b2b582529a1f95952cf",
				leafCommitment: "1d3cad4abf6fbbcd85e5904b6c00c7e579b6c96fd79be88063e05b9eb34d08b0",
			},
		},
		prefixElements: []string{
			"9340872f852a923a38efc3aed4e090c4c94d6a092fd18ce99eb342d0c38183e7",
			"60bd571e451c4b33c5d56efbd231aa39563ac4a447b29d2e2e582c106afd2088",
			"d2d9362a9cc243e22155faecc0888b7d75b926ff67d1bc9f032c171bea01ea05",
			"5616792a13bcbb4a2429d598a7b79dff6cea663aff323f8a8c626499d5c1c58c",
			"4b236805d7d8a06586ab43b37644c348f4446af88b4a2b6a85635f9115f0535a",
			"62a5bfbc58ade5f01c89deeabcedeab7a7049d71aa35e5583781c8e3c6fd8f5e",
			"384e27e384f654e9c78b480445a37decb11feef3bba0832b15a57c12a01c42c8",
			"2238f46254cb9c14ed558f154bff45bc6a2a81ad5b27b0dd7db5095ddd6f1c2f",
			"719d353bcc8492aaa9019ff07b6173cccd0df0be297add7b782e1833789db6a0",
			"26c94994089f07fb8fbd6c2eba1e6ca0e861b4a7d32328f674dff9a9e6885a62",
			"0000000000000000000000000000000000000000000000000000000000000000",
			"89daa9e4f030998a2945faf4278de4c674d6e65be9ea4fff778de05baebc2d3e",
			"0000000000000000000000000000000000000000000000000000000000000000",
			"0000000000000000000000000000000000000000000000000000000000000000",
			"0000000000000000000000000000000000000000000000000000000000000000",
			"3b6cc593bb758282f36da7a469df18a65e6033fc9ab358edeb66728cd4916f38",
			"99530dac13596e14195071de4208e9f9bf1b629958a2dd83667303d6b5f52702",
		},
		expectedRoot: "0694105a4da81329242c79d9a88ebefcc1a28c647d139ade81b4d2e0e8b36585",
	},
	{
		name:      "user002@example.com-v3",
		label:     "user002@example.com",
		version:   3,
		publicKey: "23bc54912c1e6e92c4a86825c867e27ffdc555bffbd4244f17a26abfffee965d",
		ladderVersions: []uint64{
			0, 1, 3, 7, 5, 4,
		},
		ladderProofs: []string{
			"f28a098fd2f88dcd67d34434aa4c54539d94efa71bb4e62952e5de12892c5a63cf1ef52e0ee22e5343450371884c9afe29c20c538fbdd76f6f5cb94892a8f54e1f7eb406237102c87d27aaefe7ad8f02",
			"17a25f78520dc766b8f7a3e7082513125a5151dd68284516518a45013d7556fe7905fe4d8a6691229cd97eb2b6ddb2220f2913c0f7612181f19ce72429d51ca65ece25dac9974509abc96f9b7c88430e",
			"3d838db0b118c0b12c64653728043ed57ae914e4476ce7772408a6ef4bbe2a42aa5f913cdde0864475340b2ae7c0f29ebda3320ffdceae08339cb497b86e983ee6e9cbd40e1eb9df447e314b37035500",
			"4cfb90b56d533cd5ce44e1e75f6f8aab762ee7e7854e6c31dbf3a05c192a8bf724e0a0416b8cc692d8afb752c3e8179bd1d54655ec49952a427244960ee49e294bab645b987e292659bfbdf3c27e7605",
			"05db54f9c4a74bf2447ab48104972352ab8840c977f32ae092cd41c7fec35071802802b0970a4cd17fbd2e02d15b387f927f41fe9dccc73491abd2c9fe5c68f8f5af86680b25883cdeb3d1ff17b6bc05",
			"3aa1b5d8aead56856ac6746f94f4c042b1c1e4f5238dc0e38f53c688214469db477ffcf56381b981b60f0bb898c08c3ce7432406b2c726ee0014d2f5c077414a33a1906c02a1a03f2f2451432ab7a60a",
		},
		ladderCommitments: []string{
			"0dd2e916909a8fd05bccb6c77e0eb9c3a6f8568596bd60ec16c7aea7b7857d55",
			"6f9304aaf95361d455a357fba378e26a7630620590321ba4c4f62dd6430fb6e2",
			"62388d47f2aa98481c187b85958d4c0c3aad4023619d5ca344d7219d37bd95e1",
			"0000000000000000000000000000000000000000000000000000000000000000",
			"0000000000000000000000000000000000000000000000000000000000000000",
			"0000000000000000000000000000000000000000000000000000000000000000",
		},
		prefixResults: []prefixDictResultVector{
			{resultType: proofs.Inclusion, depth: 10},
			{resultType: proofs.Inclusion, depth: 10},
			{resultType: proofs.Inclusion, depth: 8},
			{
				resultType:     proofs.NonInclusionLeaf,
				depth:          8,
				leafVrfOutput:  "0d27ee61e1071c19a29d4878768468a543972fe23bc403e1185e4951405ea449",
				leafCommitment: "5c48d2bbc2d5f5f4b177642c0f33158cfcbad17dd4fbcf19dcf474276c6f7c96",
			},
			{
				resultType:     proofs.NonInclusionLeaf,
				depth:          10,
				leafVrfOutput:  "4750d039b49adc9b9845d7753737377b1c8f46191b13d45ade7e04da575e4962",
				leafCommitment: "31617fe06c9b3cd08d8df863cf8d7f10676f746b134ef656badde3343b6ee7b3",
			},
			{
				resultType:     proofs.NonInclusionLeaf,
				depth:          8,
				leafVrfOutput:  "33dad0f922a7a64389019e5a78ac010bd37d35caa980488f2168ba49ed8c0783",
				leafCommitment: "7ed59722dc0112eee27856ff4de8e0c9f73f6120955fbbb22aead928bf76759e",
			},
		},
		prefixElements: []string{
			"97b145ca2313772d3fa3d01885c5aee88af799a3fd0fac01b98f58a86b03c06f",
			"ab538c0d504929b60824c1cbf4c090f4e5856829c7f0adc3b6a6dd9563d9fcac",
			"e1be9af89fb6df3904a82c2064bf1260cb60cbe12ac7dea9de529a0a83656486",
			"2d0de7d95a096329799e27f418f3387bd70fde6a017acdb10cebce51584c885a",
			"91f1fcb4a9d45f97693a6143b3d6f807bf0f7c4c5a23e9424e41ae2002051c87",
			"0bd5c4b9d0885cbd545410abe5b6d36a033200ad9a74b81ebd579e81f9ce9c14",
			"ec490a6eb6e041c6046d70dbd4976491706350b87ba0c4b82d92fbb89820993f",
			"a10dd637c2a363e3b1a78aa3655791c18f1aa0cbcb43a2c60d6953e3cf6c1fd8",
			"2455c9a685ac6be127622f5265480ff59f7b490990ec21e7befd5248980a7689",
			"1f8688fe025c2841b5ef01011b01c7fc07f102d033dad26b213e764daa314704",
			"0e45c9bfed2a95553c322a847e240cb52a0aa1a8afda38bdfadd669a17fa8ee3",
			"526ade223065c950d3634e14017c252f88b5f619756439678b6a8cc3c16a1088",
			"06157b8dcc47736154ce89e71ed0abeccd2e80063540a958a300c470a059fa96",
			"1a3ca945508bad1ee3883835123f96246ccf6658c942a022411f46494a7fc36f",
			"00c2435b078b5c4f104b4b79fbe3abf57c4d813ff64be6da4f25ab28e751c12b",
			"60b54ad43dca08b4e5d310a702c55e1a462523ffcd537972712a476ae00f7fb1",
			"526c88fd2237174de83e8c012ff139b3f2d16fdb95b241c3430c2861cb21cb52",
			"625b93ad654efc0e10b86c642da3822e6cfe3caa9c75af1e411e9eb1fe11cc3e",
			"0000000000000000000000000000000000000000000000000000000000000000",
			"e5260492013961c57a587335e5eb5bdd292663432d8f11b392f0c9605d886137",
			"38f585f26bf9ea057d03622860d2aa3d567769dc18e49139be8fafcf4fd065c5",
			"576e6e89319e605c0c902fcd21b38aa1068db1d4171f12d643a67db4b6bf66ec",
			"66b78a6e918c52c015020e57b8071e694fd346f27c586da38028e168aebb06ef",
			"3c57590a63e2297bad9b2a6e72589854606f73335876e7ddf27e42322daaee96",
			"6a8eb07ff4fad2c8d11d37d3ba4cbbea10f4bb45714b423fc21257467519a78f",
			"9064d325dff3dc4542063746182ed381dcee6d7bb191daf7d9f2d2a2ca89fd85",
			"a98314e8e19560d0b4d8a3d9199b9ce6c136431d7078b813c9c2d7d980236f60",
			"1a22b1e439bd645ab7cb90c584183df44b2897cc2fc8c284d0bf40e0e5fb21a9",
			"15d0a9f31b53160c32d375951c5095d4ac76ea916df38bf5b7793a29a3c06d8b",
			"9223942fb06511a01996dce7bc4f4ef5d355a7dd19686203487d5abaa1722e80",
			"45650a5911862426497a2d45916710c2b86ce1ef4cda895932189277aa96a552",
			"aac773b7a863b01e53dccb6f51379f21087e7532969b1ef7e4d4f564cf9d1070",
			"88e31c9b7dcc666fe7819abd08935da1d4863a79081e47fd7dd2c5cb1ce7415c",
			"f7997c9a9072d68f53a2c7aa87ad7996ebeccd59ee0cc61335abb97dcc20dbde",
		},
		expectedRoot: "4552e0f0c070f706122047bcac9465a2d42a38608e59d8a99778f4481e556d95",
	},
}

func TestPrefixDictVectors(t *testing.T) {
	for _, vector := range prefixDictVectors {
		t.Run(vector.name, func(t *testing.T) {
			dict, err := Dict(
				[]byte(vector.label),
				vector.version,
				mustDecode(t, vector.publicKey),
				vectorPrefixProof(t, vector),
				vectorLadder(t, vector),
			)
			if err != nil {
				t.Fatal(err)
			} else if got, want := dict.GetRoot(), mustHexDigest(t, vector.expectedRoot); got != want {
				t.Fatalf("root = %x, want %x", got, want)
			}

			for i, version := range vector.ladderVersions {
				got, err := dict.GetCommitment([]byte(vector.label), version)
				if err != nil {
					t.Fatalf("GetCommitment(%d): %v", version, err)
				}
				want := mustHexDigest(t, vector.ladderCommitments[i])
				if want == ([sha256.Size]byte{}) {
					if got != nil {
						t.Fatalf("GetCommitment(%d) = %x, want nil", version, *got)
					}
				} else if got == nil || *got != want {
					t.Fatalf("GetCommitment(%d) = %x, want %x", version, got, want)
				}
			}
		})
	}
}

func vectorPrefixProof(t *testing.T, vector prefixDictVector) proofs.PrefixProof {
	t.Helper()

	results := make([]proofs.PrefixSearchResult, len(vector.prefixResults))
	for i, result := range vector.prefixResults {
		results[i] = proofs.PrefixSearchResult{
			Result_type: result.resultType,
			Depth:       result.depth,
		}
		if result.leafVrfOutput != "" {
			results[i].Leaf = &proofs.PrefixLeaf{
				Vrf_output: mustDecode(t, result.leafVrfOutput),
				Commitment: mustHexDigest(t, result.leafCommitment),
			}
		}
	}

	elements := make([]proofs.NodeValue, len(vector.prefixElements))
	for i, element := range vector.prefixElements {
		elements[i] = mustHexDigest(t, element)
	}

	return proofs.PrefixProof{
		Results:  results,
		Elements: elements,
	}
}

func vectorLadder(t *testing.T, vector prefixDictVector) []proofs.BinaryLadderStep {
	t.Helper()

	if len(vector.ladderProofs) != len(vector.ladderCommitments) {
		t.Fatalf("ladder proof and commitment counts differ")
	}
	ladder := make([]proofs.BinaryLadderStep, len(vector.ladderProofs))
	for i := range ladder {
		ladder[i] = proofs.BinaryLadderStep{
			Proof:      mustDecode(t, vector.ladderProofs[i]),
			Commitment: mustHexDigest(t, vector.ladderCommitments[i]),
		}
	}
	return ladder
}

func mustDecode(t *testing.T, s string) []byte {
	t.Helper()
	if out, err := hex.DecodeString(s); err != nil {
		t.Fatal(err)
		return nil
	} else {
		return out
	}
}

func mustHexDigest(t *testing.T, s string) [sha256.Size]byte {
	t.Helper()
	raw := mustDecode(t, s)
	if len(raw) != sha256.Size {
		t.Fatalf("digest has length %d, want %d", len(raw), sha256.Size)
	}
	var out [sha256.Size]byte
	copy(out[:], raw)
	return out
}
