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
		proof:     "dde7bc4500529c2c837cb6d316c9af45c59c5a750ad24c39b0bff33bd88055f43e872d58e270f40738502e9b5e69b3f64257c2900d193e16c8598416e57872e05988aea086dd75112e56275417a72502",
		output:    "cf05ca1cb9dce6902239b47883e091fe95b84b78190d03de2b3fee36ca5468436de8472d20e464d9303150a2013b2570f08929fabc40f9c7c8f0e821e87fe717",
	},
	{
		name:      "user000@example.com-v1",
		label:     "user000@example.com",
		version:   1,
		publicKey: "23bc54912c1e6e92c4a86825c867e27ffdc555bffbd4244f17a26abfffee965d",
		proof:     "3081be8b1a45fecb0c280d12f08a4db47aeba960123475f559ec55a31e252cfae1788005f7cf25770c5ed18baab9529159f735e23c57ef994335796a3d14fafadaa1b189248495f908391406c982820e",
		output:    "b96f8d3c6bb1f366103232cd5f2b17390d5d7edddcdbdb75900126feef9f9069b9626a2bd9afe30447c0210b73b5c16131bbf72954b96c23251730cdafba8faa",
	},
	{
		name:      "user002@example.com-v0",
		label:     "user002@example.com",
		version:   0,
		publicKey: "23bc54912c1e6e92c4a86825c867e27ffdc555bffbd4244f17a26abfffee965d",
		proof:     "f28a098fd2f88dcd67d34434aa4c54539d94efa71bb4e62952e5de12892c5a63191d27459c3489c88d95c8923f7f00acbfcff1be98a6290a0473ca86a179464bc97a35b17979d3e63fc04775d88c8c0d",
		output:    "68b9f40c390f31efbe7c3f159df5b4122b3321fb8970488ca5630258c21b3e79722772aa976315b75b8c8758d4b8541f40054fda5339c182221730730123a957",
	},
	{
		name:      "user002@example.com-v1",
		label:     "user002@example.com",
		version:   1,
		publicKey: "23bc54912c1e6e92c4a86825c867e27ffdc555bffbd4244f17a26abfffee965d",
		proof:     "17a25f78520dc766b8f7a3e7082513125a5151dd68284516518a45013d7556fe69ba1408cb887930143d7e33697d88bbf2c462bf9b73d9232d3a702721ece859347b3fa7874a198f5daa7e173de0db0a",
		output:    "ca847375bd423bf07014a83690f667a4dc417a878f5e0c44eb35f8f50717edf07268a504af38ce7485b7a7553ccdc33d714b14491a6efaf3a4918d5ca7805cd1",
	},
	{
		name:      "user002@example.com-v3",
		label:     "user002@example.com",
		version:   3,
		publicKey: "23bc54912c1e6e92c4a86825c867e27ffdc555bffbd4244f17a26abfffee965d",
		proof:     "3d838db0b118c0b12c64653728043ed57ae914e4476ce7772408a6ef4bbe2a428273dbe088ce874d207a4dfdaab84891c34118b3fbd6bfa4246c674736b52f3891025cc45ad33cf2bbd95b0ff602c602",
		output:    "6d75df10ca1f8e33f3a4d6a06d7bd6de63252635521e7e2f97d0076187c28cd032e3f787f2faae535b1d1af12b61dc9b59a2d9e6ba81c93c734367d6e8f40d82",
	},
	{
		name:      "user002@example.com-v7",
		label:     "user002@example.com",
		version:   7,
		publicKey: "23bc54912c1e6e92c4a86825c867e27ffdc555bffbd4244f17a26abfffee965d",
		proof:     "4cfb90b56d533cd5ce44e1e75f6f8aab762ee7e7854e6c31dbf3a05c192a8bf732e86c80e894f88161db9f37bbb12ca3e06cd6f03e9ac0ebbb16c5f8f05d86b1182ad8638ecb872d45c91b1ea5fd2f02",
		output:    "0d6cb4651d958c4723a433b1e04458e61c91e1ba19d5c5edf2e2ea59cb0b555f9b826b4c9df5f972ef3ea202fd73f44f1804ee2a9dd8e69187c7e2ce8f97ccab",
	},
	{
		name:      "user002@example.com-v5",
		label:     "user002@example.com",
		version:   5,
		publicKey: "23bc54912c1e6e92c4a86825c867e27ffdc555bffbd4244f17a26abfffee965d",
		proof:     "05db54f9c4a74bf2447ab48104972352ab8840c977f32ae092cd41c7fec35071a8bd2251062425bb202bc0ed3bd5cca334329b295aedd16589a15563f37d4342f67339b96a132adf003d119ee7897d07",
		output:    "4767eeb2c3929a030876c6959f9a0becd7e0d2b767e9b13a38e8b09353e566a9a4b526d5e9e961cd3a5dc038f48408f05d3c6f943ba115b6ab22a7c6878a72a3",
	},
	{
		name:      "user002@example.com-v4",
		label:     "user002@example.com",
		version:   4,
		publicKey: "23bc54912c1e6e92c4a86825c867e27ffdc555bffbd4244f17a26abfffee965d",
		proof:     "3aa1b5d8aead56856ac6746f94f4c042b1c1e4f5238dc0e38f53c688214469db14c7d1abffd8e3fe726bbb014556ea7c2631e722b48f74e704d79db010df29b82b159e2ce04e3eefb07fcdc1985b5203",
		output:    "3357fff0bb27908ca3fe1ec645385ce518ab8e0a64e4b218678057a13d8d454727b6110f6b47cad07b3b1405c4daeb6ad2ce0ae6d0d005062b41e8e4e7070dfb",
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
