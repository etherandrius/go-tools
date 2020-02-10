package lint

import (
	"fmt"
	"go/token"
	"path/filepath"
	"strings"
)

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
