package main

import (
	"honnef.co/go/tools/simple"
	"honnef.co/go/tools/staticcheck"
	"honnef.co/go/tools/stylecheck"

	"golang.org/x/tools/go/analysis"
	"golang.org/x/tools/go/analysis/unitchecker"
)

func main() {
	var as []*analysis.Analyzer
	for _, a := range staticcheck.Analyzers {
		as = append(as, a)
	}
	for _, a := range simple.Analyzers {
		as = append(as, a)
	}
	for _, a := range stylecheck.Analyzers {
		as = append(as, a)
	}

	// XXX write our own unitchecker that supports other output
	// formats. specifically, support JSON, so we can implement our
	// own frontend (unitchecker actually has json output already, but
	// doesn't contain most of the things we care about)

	unitchecker.Main(as...)
}
