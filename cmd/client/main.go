package main

import (
	"fmt"
)

// @ trusted
func printMsg(msg string) {
	fmt.Printf("%s", msg)
}

func main() {
	printMsg("Hello world")
}
