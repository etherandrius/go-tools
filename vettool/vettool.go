package vettool

import (
	"strings"
	"unicode"
)

func FilterChecks(allChecks []string, checks []string) map[string]bool {
	known := map[string]bool{}
	for _, c := range allChecks {
		known[c] = true
	}
	allowedChecks := map[string]bool{}

	for _, check := range checks {
		b := true
		if len(check) > 1 && check[0] == '-' {
			b = false
			check = check[1:]
		}
		if check == "*" || check == "all" {
			// Match all
			for _, c := range allChecks {
				allowedChecks[c] = b
			}
		} else if strings.HasSuffix(check, "*") {
			// Glob
			prefix := check[:len(check)-1]
			isCat := strings.IndexFunc(prefix, func(r rune) bool { return unicode.IsNumber(r) }) == -1

			for _, c := range allChecks {
				idx := strings.IndexFunc(c, func(r rune) bool { return unicode.IsNumber(r) })
				if isCat {
					// Glob is S*, which should match S1000 but not SA1000
					cat := c[:idx]
					if prefix == cat {
						allowedChecks[c] = b
					}
				} else {
					// Glob is S1*
					if strings.HasPrefix(c, prefix) {
						allowedChecks[c] = b
					}
				}
			}
		} else if known[check] {
			// Literal check name
			allowedChecks[check] = b
		}
	}
	return allowedChecks
}
