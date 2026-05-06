package crypto

import (
	"bytes"
	"encoding/hex"
	"testing"
)

type vrfVector struct {
	name      string
	label     string
	version   uint64
	publicKey string
	proof     string
	output    string
}

var vrfVectors = []vrfVector{
	{
		name:      "user000@example.com-v0",
		label:     "user000@example.com",
		version:   0,
		publicKey: "23bc54912c1e6e92c4a86825c867e27ffdc555bffbd4244f17a26abfffee965d",
		proof:     "dde7bc4500529c2c837cb6d316c9af45c59c5a750ad24c39b0bff33bd88055f435115b1c364feb452c6ca9692500c339d44c95fa3c543cae87de3ecb97b314315c831c0eb54b86eeafd3a0c83c9a250c",
		output:    "cf05ca1cb9dce6902239b47883e091fe95b84b78190d03de2b3fee36ca546843",
	},
	{
		name:      "user000@example.com-v1",
		label:     "user000@example.com",
		version:   1,
		publicKey: "23bc54912c1e6e92c4a86825c867e27ffdc555bffbd4244f17a26abfffee965d",
		proof:     "3081be8b1a45fecb0c280d12f08a4db47aeba960123475f559ec55a31e252cfab8db2425979966d0a58075c541d469a312069a9a3847a2f4d30014e35ac664ac7e3e469e5e67e36ae7a4e4fe0fab2009",
		output:    "b96f8d3c6bb1f366103232cd5f2b17390d5d7edddcdbdb75900126feef9f9069",
	},
	{
		name:      "user002@example.com-v0",
		label:     "user002@example.com",
		version:   0,
		publicKey: "23bc54912c1e6e92c4a86825c867e27ffdc555bffbd4244f17a26abfffee965d",
		proof:     "f28a098fd2f88dcd67d34434aa4c54539d94efa71bb4e62952e5de12892c5a63cf1ef52e0ee22e5343450371884c9afe29c20c538fbdd76f6f5cb94892a8f54e1f7eb406237102c87d27aaefe7ad8f02",
		output:    "68b9f40c390f31efbe7c3f159df5b4122b3321fb8970488ca5630258c21b3e79",
	},
	{
		name:      "user002@example.com-v1",
		label:     "user002@example.com",
		version:   1,
		publicKey: "23bc54912c1e6e92c4a86825c867e27ffdc555bffbd4244f17a26abfffee965d",
		proof:     "17a25f78520dc766b8f7a3e7082513125a5151dd68284516518a45013d7556fe7905fe4d8a6691229cd97eb2b6ddb2220f2913c0f7612181f19ce72429d51ca65ece25dac9974509abc96f9b7c88430e",
		output:    "ca847375bd423bf07014a83690f667a4dc417a878f5e0c44eb35f8f50717edf0",
	},
	{
		name:      "user002@example.com-v3",
		label:     "user002@example.com",
		version:   3,
		publicKey: "23bc54912c1e6e92c4a86825c867e27ffdc555bffbd4244f17a26abfffee965d",
		proof:     "3d838db0b118c0b12c64653728043ed57ae914e4476ce7772408a6ef4bbe2a42aa5f913cdde0864475340b2ae7c0f29ebda3320ffdceae08339cb497b86e983ee6e9cbd40e1eb9df447e314b37035500",
		output:    "6d75df10ca1f8e33f3a4d6a06d7bd6de63252635521e7e2f97d0076187c28cd0",
	},
	{
		name:      "user002@example.com-v7",
		label:     "user002@example.com",
		version:   7,
		publicKey: "23bc54912c1e6e92c4a86825c867e27ffdc555bffbd4244f17a26abfffee965d",
		proof:     "4cfb90b56d533cd5ce44e1e75f6f8aab762ee7e7854e6c31dbf3a05c192a8bf724e0a0416b8cc692d8afb752c3e8179bd1d54655ec49952a427244960ee49e294bab645b987e292659bfbdf3c27e7605",
		output:    "0d6cb4651d958c4723a433b1e04458e61c91e1ba19d5c5edf2e2ea59cb0b555f",
	},
	{
		name:      "user002@example.com-v5",
		label:     "user002@example.com",
		version:   5,
		publicKey: "23bc54912c1e6e92c4a86825c867e27ffdc555bffbd4244f17a26abfffee965d",
		proof:     "05db54f9c4a74bf2447ab48104972352ab8840c977f32ae092cd41c7fec35071802802b0970a4cd17fbd2e02d15b387f927f41fe9dccc73491abd2c9fe5c68f8f5af86680b25883cdeb3d1ff17b6bc05",
		output:    "4767eeb2c3929a030876c6959f9a0becd7e0d2b767e9b13a38e8b09353e566a9",
	},
	{
		name:      "user002@example.com-v4",
		label:     "user002@example.com",
		version:   4,
		publicKey: "23bc54912c1e6e92c4a86825c867e27ffdc555bffbd4244f17a26abfffee965d",
		proof:     "3aa1b5d8aead56856ac6746f94f4c042b1c1e4f5238dc0e38f53c688214469db477ffcf56381b981b60f0bb898c08c3ce7432406b2c726ee0014d2f5c077414a33a1906c02a1a03f2f2451432ab7a60a",
		output:    "3357fff0bb27908ca3fe1ec645385ce518ab8e0a64e4b218678057a13d8d4547",
	},
}

func TestVRFVerifyVectors(t *testing.T) {
	for _, vector := range vrfVectors {
		t.Run(vector.name, func(t *testing.T) {
			if got, ok := VRF_verify(
				mustDecode(t, vector.publicKey),
				[]byte(vector.label),
				vector.version,
				mustDecode(t, vector.proof),
			); !ok {
				t.Fatal("VRF_verify failed")
			} else if want := mustDecode(t, vector.output); !bytes.Equal(got, want) {
				t.Fatalf("VRF_verify output = %x, want %x", got, want)
			}
		})
	}
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
