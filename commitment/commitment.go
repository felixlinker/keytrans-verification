package commitment

// ##(--hyperMode extended)

// @ requires low(hash)
// @ ensures  res ==> low(value)
func verify(hash int, value int) (res bool) {
	res = (hash == computeHash(value))
	return
}

// @ requires low(hash)
// @ ensures  res ==> low(value)
func verifyWithBranching(hash int, value int) (res bool) {
	// thanks to hyperMode `extended`, we can branch on a non-low expression.
	// however, we cannot early return in a non-low context, such that we use
	// assignements here.
	if hash != computeHash(value) {
		res = false
	} else {
		res = true
	}
	return
}

// the following postcondition specifies that the Go function `computeHash` behaves like the
// pure (mathematical) function `hashFn` for which we assume injectivity (see domain below)
// @ ensures res == hashFn(input)
// @ trusted
func computeHash(input int) (res int) {
	return res // dummy implementation
}

/* @
ghost type HashFunction domain {
    func hashFn(int) int
    func invFn(int) int

    axiom { // hashFn is injective
        forall v int :: { hashFn(v) } invFn(hashFn(v)) == v
    }
}
@ */
