package lintutil

import (
	"sort"
	"strings"
)

// XXX move flag related code from other files to this file

type StringSet map[string]bool

func (ss *StringSet) Get() interface{} {
	return *ss
}

func (ss *StringSet) String() string {
	var items []string
	for item := range *ss {
		items = append(items, item)
	}
	sort.Strings(items)
	return strings.Join(items, ",")
}

func (ss *StringSet) Set(s string) error {
	m := make(map[string]bool) // clobber previous value
	if s != "" {
		for _, name := range strings.Split(s, ",") {
			if name == "" {
				continue
			}
			m[name] = true
		}
	}
	*ss = m
	return nil
}
