package lint

import (
	"strings"

	"honnef.co/go/tools/runner"
)

func parseDirectives(dirs []runner.Directive) ([]Ignore, []Problem) {
	var ignores []Ignore
	var problems []Problem

	for _, dir := range dirs {
		cmd := dir.Command
		args := dir.Arguments
		switch cmd {
		case "ignore", "file-ignore":
			if len(args) < 2 {
				p := Problem{
					Pos:      dir.NodePosition,
					Message:  "malformed linter directive; missing the required reason field?",
					Severity: Error,
					Check:    "compile",
				}
				problems = append(problems, p)
				continue
			}
		default:
			// unknown directive, ignore
			continue
		}
		checks := strings.Split(args[0], ",")
		pos := dir.NodePosition
		var ig Ignore
		switch cmd {
		case "ignore":
			ig = &LineIgnore{
				File:   pos.Filename,
				Line:   pos.Line,
				Checks: checks,
				Pos:    dir.DirectivePosition,
			}
		case "file-ignore":
			ig = &FileIgnore{
				File:   pos.Filename,
				Checks: checks,
			}
		}
		ignores = append(ignores, ig)
	}

	return ignores, problems
}
