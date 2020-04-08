// Package lint provides the foundation for tools like staticcheck
package lint // import "honnef.co/go/tools/lint"

import (
	"fmt"
	"go/token"
	"path/filepath"
	"regexp"
	"sort"
	"strconv"
	"strings"
	"unicode"

	"honnef.co/go/tools/config"
	"honnef.co/go/tools/runner"

	"golang.org/x/tools/go/analysis"
	"golang.org/x/tools/go/packages"
)

type Documentation struct {
	Title      string
	Text       string
	Since      string
	NonDefault bool
	Options    []string
}

func (doc *Documentation) String() string {
	b := &strings.Builder{}
	fmt.Fprintf(b, "%s\n\n", doc.Title)
	if doc.Text != "" {
		fmt.Fprintf(b, "%s\n\n", doc.Text)
	}
	fmt.Fprint(b, "Available since\n    ")
	if doc.Since == "" {
		fmt.Fprint(b, "unreleased")
	} else {
		fmt.Fprintf(b, "%s", doc.Since)
	}
	if doc.NonDefault {
		fmt.Fprint(b, ", non-default")
	}
	fmt.Fprint(b, "\n")
	if len(doc.Options) > 0 {
		fmt.Fprintf(b, "\nOptions\n")
		for _, opt := range doc.Options {
			fmt.Fprintf(b, "    %s", opt)
		}
		fmt.Fprint(b, "\n")
	}
	return b.String()
}

type Ignore interface {
	Match(p Problem) bool
}

type LineIgnore struct {
	File    string
	Line    int
	Checks  []string
	Matched bool
	Pos     token.Position
}

func (li *LineIgnore) Match(p Problem) bool {
	pos := p.Pos
	if pos.Filename != li.File || pos.Line != li.Line {
		return false
	}
	for _, c := range li.Checks {
		if m, _ := filepath.Match(c, p.Check); m {
			li.Matched = true
			return true
		}
	}
	return false
}

func (li *LineIgnore) String() string {
	matched := "not matched"
	if li.Matched {
		matched = "matched"
	}
	return fmt.Sprintf("%s:%d %s (%s)", li.File, li.Line, strings.Join(li.Checks, ", "), matched)
}

type FileIgnore struct {
	File   string
	Checks []string
}

func (fi *FileIgnore) Match(p Problem) bool {
	if p.Pos.Filename != fi.File {
		return false
	}
	for _, c := range fi.Checks {
		if m, _ := filepath.Match(c, p.Check); m {
			return true
		}
	}
	return false
}

type Severity uint8

const (
	Error Severity = iota
	Warning
	Ignored
)

// Problem represents a problem in some source code.
type Problem struct {
	Pos      token.Position
	End      token.Position
	Message  string
	Check    string
	Severity Severity
	Related  []Related
}

type Related struct {
	Pos     token.Position
	End     token.Position
	Message string
}

func (p Problem) Equal(o Problem) bool {
	return p.Pos == o.Pos &&
		p.End == o.End &&
		p.Message == o.Message &&
		p.Check == o.Check &&
		p.Severity == o.Severity
}

func (p *Problem) String() string {
	return fmt.Sprintf("%s (%s)", p.Message, p.Check)
}

// A Linter lints Go source code.
type Linter struct {
	Checkers        []*analysis.Analyzer
	GoVersion       int
	Config          config.Config
	Stats           Stats
	RepeatAnalyzers uint
}

func parsePosition(pos string) token.Position {
	if pos == "" {
		return token.Position{}
	}
	var posn token.Position
	off2 := strings.LastIndexByte(pos, ':')
	if off2 == -1 {
		panic(fmt.Sprintf("no colon in %q", pos))
		// XXX
	}
	off1 := strings.LastIndexByte(pos[:off2], ':')
	if off2 == -1 {
		panic(fmt.Sprintf("no colon in %q", pos))
		// XXX
	}
	posn.Filename = pos[:off1]
	posn.Line, _ = strconv.Atoi(pos[off1+1 : off2])
	posn.Column, _ = strconv.Atoi(pos[off2+1:])
	return posn
}

func (l *Linter) Lint(cfg *packages.Config, patterns []string) ([]Problem, error) {
	r, err := runner.New(l.Config)
	if err != nil {
		return nil, err
	}
	// r.goVersion = l.GoVersion

	results, err := r.Run(cfg, l.Checkers, patterns)
	if err != nil {
		return nil, err
	}

	var problems []Problem
	for _, res := range results {
		if len(res.Errors) > 0 && !res.Failed {
			panic("package has errors but isn't marked as failed")
		}
		if res.Failed {
			for _, e := range res.Errors {
				switch e := e.(type) {
				case packages.Error:
					msg := e.Msg
					if len(msg) != 0 && msg[0] == '\n' {
						// TODO(dh): See https://github.com/golang/go/issues/32363
						msg = msg[1:]
					}

					var pos token.Position
					if e.Pos == "" {
						// Under certain conditions (malformed package
						// declarations, multiple packages in the same
						// directory), go list emits an error on stderr
						// instead of JSON. Those errors do not have
						// associated position information in
						// go/packages.Error, even though the output on
						// stderr may contain it.
						if p, n, err := parsePos(msg); err == nil {
							if abs, err := filepath.Abs(p.Filename); err == nil {
								p.Filename = abs
							}
							pos = p
							msg = msg[n+2:]
						}
					} else {
						var err error
						pos, _, err = parsePos(e.Pos)
						if err != nil {
							panic(fmt.Sprintf("internal error: %s", e))
						}
					}
					p := Problem{
						Pos:      pos,
						Message:  msg,
						Severity: Error,
						Check:    "compile",
					}
					problems = append(problems, p)
				case error:
					p := Problem{
						Pos:      token.Position{},
						Message:  e.Error(),
						Severity: Error,
						Check:    "compile",
					}
					problems = append(problems, p)
				}
			}
		} else {
			// XXX we probably don't need this variable
			var pkgProblems []Problem

			diags, err := res.Diagnostics()
			if err != nil {
				// XXX
				panic(err)
			}

			for _, diag := range diags {
				p := Problem{
					Pos:     diag.Pos,
					End:     diag.End,
					Message: diag.Message,
					Check:   diag.Category,
				}
				for _, rel := range diag.Related {
					p.Related = append(p.Related, Related{
						Pos:     rel.Pos,
						End:     rel.End,
						Message: rel.Message,
					})
				}
				pkgProblems = append(pkgProblems, p)
			}

			// XXX we don't need pkg.Problems just to feed it into filtering
			dirs, err := res.Directives()
			if err != nil {
				// XXX
				panic(err)
			}
			ignores, moreProblems := parseDirectives(dirs)
			problems = append(problems, moreProblems...)
			for _, ig := range ignores {
				for i := range pkgProblems {
					p := &pkgProblems[i]
					if ig.Match(*p) {
						p.Severity = Ignored
					}
				}
			}

			// XXX
			// for _, p := range pkg.Problems {
			// 	if p.Check == "compile" || pkg.rpkg.Package.Config.Checks[p.Check] {
			// 		problems = append(problems, p)
			// 	}
			// }
			problems = append(problems, pkgProblems...)

			for _, ig := range ignores {
				ig, ok := ig.(*LineIgnore)
				if !ok {
					continue
				}
				if ig.Matched {
					continue
				}

				couldveMatched := false
				// XXX
				// for _, c := range ig.Checks {
				// 	if !pkg.rpkg.Checks[c] {
				// 		continue
				// 	}
				// 	couldveMatched = true
				// 	break
				// }

				if !couldveMatched {
					// The ignored checks were disabled for the containing package.
					// Don't flag the ignore for not having matched.
					continue
				}
				p := Problem{
					Pos:     ig.Pos,
					Message: "this linter directive didn't match anything; should it be removed?",
					Check:   "",
				}
				problems = append(problems, p)
			}
		}
	}

	if len(problems) == 0 {
		return nil, nil
	}

	sort.Slice(problems, func(i, j int) bool {
		pi := problems[i].Pos
		pj := problems[j].Pos

		if pi.Filename != pj.Filename {
			return pi.Filename < pj.Filename
		}
		if pi.Line != pj.Line {
			return pi.Line < pj.Line
		}
		if pi.Column != pj.Column {
			return pi.Column < pj.Column
		}

		return problems[i].Message < problems[j].Message
	})

	var out []Problem
	out = append(out, problems[0])
	for i, p := range problems[1:] {
		// We may encounter duplicate problems because one file
		// can be part of many packages.
		if !problems[i].Equal(p) {
			out = append(out, p)
		}
	}
	return out, nil
}

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

var posRe = regexp.MustCompile(`^(.+?):(\d+)(?::(\d+)?)?`)

func parsePos(pos string) (token.Position, int, error) {
	if pos == "-" || pos == "" {
		return token.Position{}, 0, nil
	}
	parts := posRe.FindStringSubmatch(pos)
	if parts == nil {
		return token.Position{}, 0, fmt.Errorf("malformed position %q", pos)
	}
	file := parts[1]
	line, _ := strconv.Atoi(parts[2])
	col, _ := strconv.Atoi(parts[3])
	return token.Position{
		Filename: file,
		Line:     line,
		Column:   col,
	}, len(parts[0]), nil
}
