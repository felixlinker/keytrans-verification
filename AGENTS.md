- We develop a security proof for a key transparency client in this repository.
- The proof is carried out using the Gobra verifier.
- The description of the key transparency design that we verify is available here: https://www.ietf.org/archive/id/draft-ietf-keytrans-protocol-04.html
- To run Gobra, execute the command: `java -Xss128m -Dfile.encoding=UTF-8 -jar agent/gobra.jar`.
You can append Gobra specific arguments as usual, e.g., `--input path/to/file.go` to verify a concerete file or `--help` to see documentation.
