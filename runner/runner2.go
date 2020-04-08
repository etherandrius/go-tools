package runner

// After we've analyzed a package, we write its facts to disk and
// clear them from memory. When a dependent needs the facts, it will
// load them from disk. This uses up additional CPU resources, but has
// the benefit of keeping peak memory usage lower. Especially when a
// lot of time passes between analyzing a dependency and its
// dependent, we're better off freeing memory. Most of our users
// complain about memory usage, not CPU usage.
//
// If we're willing to add extra complexity, then this model can be
// further optimized. We could keep data in memory for a fixed period
// of time before releasing it. And when two packages A and B both
// depend on C and execute at the same time, then data only needs to
// be loaded once.

import (
	"bytes"
	"encoding/gob"
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"io"
	"os"
	"path/filepath"
	"reflect"
	"runtime"
	"sort"
	"strings"
	"sync/atomic"

	"honnef.co/go/tools/config"
	"honnef.co/go/tools/go/types/objectpath"
	"honnef.co/go/tools/internal/cache"
	tsync "honnef.co/go/tools/internal/sync"
	"honnef.co/go/tools/loader"

	"golang.org/x/tools/go/analysis"
	"golang.org/x/tools/go/packages"
)

type Diagnostic struct {
	Pos      token.Position
	End      token.Position
	Category string
	Message  string

	SuggestedFixed []SuggestedFix
	Related        []RelatedInformation
}

type RelatedInformation struct {
	Pos     token.Position
	End     token.Position
	Message string
}

type SuggestedFix struct {
	Message   string
	TextEdits []TextEdit
}

type TextEdit struct {
	Pos     token.Position
	End     token.Position
	NewText []byte
}

// A Result describes the result of analyzing a single package.
//
// It holds references to cached diagnostics and directives. They can
// be loaded on demand with Diagnostics and Directives respectively.
type Result struct {
	Package *loader.PackageSpec

	Failed bool
	Errors []error
	// Action results, paths to files
	diagnostics string
	directives  string
}

// Diagnostics loads and returns the diagnostics found while analyzing
// the package.
func (r Result) Diagnostics() ([]Diagnostic, error) {
	if r.Failed {
		panic("Diagnostics called on failed Result")
	}
	if r.diagnostics == "" {
		// this package was only a dependency
		return nil, nil
	}
	var diags []Diagnostic
	f, err := os.Open(r.diagnostics)
	if err != nil {
		return nil, fmt.Errorf("failed loading diagnostics: %w", err)
	}
	defer f.Close()
	dec := gob.NewDecoder(f)
	for {
		var diag Diagnostic
		err := dec.Decode(&diag)
		if err != nil {
			if err == io.EOF {
				break
			}
			return nil, fmt.Errorf("failed loading diagnostics: %w", err)
		}
		diags = append(diags, diag)
	}
	return diags, nil
}

// Directives loads and returns the directives found while analyzing
// the package.
func (r Result) Directives() ([]Directive, error) {
	if r.Failed {
		panic("Directives called on failed Result")
	}
	if r.directives == "" {
		// this package was only a dependency
		return nil, nil
	}
	var dirs []Directive
	f, err := os.Open(r.directives)
	if err != nil {
		return nil, fmt.Errorf("failed loading directives: %w", err)
	}
	defer f.Close()
	if err := gob.NewDecoder(f).Decode(&dirs); err != nil {
		return nil, fmt.Errorf("failed loading directives: %w", err)
	}
	return dirs, nil
}

type action interface {
	Deps() []action
	Triggers() []action
	DecrementPending() bool
	MarkFailed()
	IsFailed() bool
	AddError(error)
}

type baseAction struct {
	// Action description

	deps     []action
	triggers []action
	pending  uint32

	// Action results

	// failed is set to true if the action couldn't be processed. This
	// may either be due to an error specific to this action, in
	// which case the errors field will be populated, or due to a
	// dependency being marked as failed, in which case errors will be
	// empty.
	failed bool
	errors []error
}

func (act *baseAction) Deps() []action     { return act.deps }
func (act *baseAction) Triggers() []action { return act.triggers }
func (act *baseAction) DecrementPending() bool {
	return atomic.AddUint32(&act.pending, ^uint32(0)) == 0
}
func (act *baseAction) MarkFailed()        { act.failed = true }
func (act *baseAction) IsFailed() bool     { return act.failed }
func (act *baseAction) AddError(err error) { act.errors = append(act.errors, err) }

// packageAction describes the act of loading a package, fully
// analyzing it, and storing the results.
type packageAction struct {
	baseAction

	// Action description

	Package   *loader.PackageSpec
	factsOnly bool
	hash      cache.ActionID

	// Action results

	vetx        string
	directives  string
	diagnostics string
}

func (act *packageAction) String() string {
	return fmt.Sprintf("packageAction(%s)", act.Package)
}

type objectFactKey struct {
	Obj  types.Object
	Type reflect.Type
}

type packageFactKey struct {
	Pkg  *types.Package
	Type reflect.Type
}

type gobFact struct {
	PkgPath string
	ObjPath string
	Fact    analysis.Fact
}

// analyzerAction describes the act of analyzing a package with a
// single analyzer.
type analyzerAction struct {
	baseAction

	// Action description

	Analyzer *analysis.Analyzer

	// Action results

	// We can store actual results here without worrying about memory
	// consumption because analyzer actions get garbage collected once
	// a package has been fully analyzed.
	Result       interface{}
	Diagnostics  []analysis.Diagnostic
	ObjectFacts  map[objectFactKey]analysis.Fact
	PackageFacts map[packageFactKey]analysis.Fact
}

func (act *analyzerAction) String() string {
	return fmt.Sprintf("analyzerAction(%s)", act.Analyzer)
}

type Directive struct {
	Command           string
	Arguments         []string
	DirectivePosition token.Position
	NodePosition      token.Position
}

type Runner struct {
	// Config that gets merged with per-package configs
	cfg   config.Config
	cache *cache.Cache
	// all analyzers, including recursive dependencies
	analyzers []*analysis.Analyzer
	semaphore tsync.Semaphore
}

func New(cfg config.Config) (*Runner, error) {
	cache, err := cache.Default()
	if err != nil {
		return nil, err
	}

	return &Runner{
		cfg:       cfg,
		cache:     cache,
		semaphore: tsync.NewSemaphore(runtime.NumCPU()),
	}, nil
}

// Planning phase.
//
// We materialize the full dependency graph in its own step, instead
// of simply executing analyses as we run the DFS. This allows us to
// process the graph from the bottom up, triggering actions as
// dependencies are completed. This simplifies parallelism, because
// dependents won't need to explicitly wait for the completion of
// their dependencies.
func newPackageActionRoot(pkg *loader.PackageSpec, cache map[*loader.PackageSpec]*packageAction) *packageAction {
	a := newPackageAction(pkg, cache)
	a.factsOnly = false
	return a
}

func newPackageAction(pkg *loader.PackageSpec, cache map[*loader.PackageSpec]*packageAction) *packageAction {
	if a, ok := cache[pkg]; ok {
		return a
	}

	a := &packageAction{
		Package:   pkg,
		factsOnly: true, // will be overwritten by any call to Action
	}
	cache[pkg] = a

	if len(pkg.Errors) > 0 {
		for _, err := range pkg.Errors {
			a.errors = append(a.errors, err)
		}
		a.failed = true
	}

	for _, dep := range pkg.Imports {
		if dep.PkgPath == "unsafe" {
			continue
		}
		depa := newPackageAction(dep, cache)
		depa.triggers = append(depa.triggers, a)
		a.deps = append(a.deps, depa)
		if depa.failed {
			a.failed = true
		}
	}
	// sort dependencies because the list of dependencies is part of
	// the cache key
	sort.Slice(a.deps, func(i, j int) bool {
		return a.deps[i].(*packageAction).Package.ID < a.deps[j].(*packageAction).Package.ID
	})

	a.pending = uint32(len(a.deps))

	return a
}

func newAnalyzerAction(an *analysis.Analyzer, cache map[*analysis.Analyzer]*analyzerAction) *analyzerAction {
	if a, ok := cache[an]; ok {
		return a
	}

	a := &analyzerAction{
		Analyzer:     an,
		ObjectFacts:  map[objectFactKey]analysis.Fact{},
		PackageFacts: map[packageFactKey]analysis.Fact{},
	}
	cache[an] = a
	for _, dep := range an.Requires {
		depa := newAnalyzerAction(dep, cache)
		depa.triggers = append(depa.triggers, a)
		a.deps = append(a.deps, depa)
	}
	a.pending = uint32(len(a.deps))
	return a
}

// execution phase

func (r *Runner) do(act action) error {
	a := act.(*packageAction)

	// compute hash of action
	cfg := a.Package.Config.Merge(r.cfg)
	h := cache.NewHash("staticcheck " + a.Package.PkgPath)
	// XXX staticcheck version
	// XXX list of analyzers
	fmt.Fprintf(h, "cfg %#v\n", cfg)
	fmt.Fprintf(h, "pkg %x\n", a.Package.Hash)
	for _, dep := range a.deps {
		dep := dep.(*packageAction)
		vetxHash, err := cache.FileHash(dep.vetx)
		if err != nil {
			return fmt.Errorf("failed computing hash: %w", err)
		}
		fmt.Fprintf(h, "vetout %q %x\n", dep.Package.PkgPath, vetxHash)
	}
	a.hash = cache.ActionID(h.Sum())

	// try to fetch hashed data (vetx, directives, diagnostics)
	var err1, err2, err3 error
	var f1, f2, f3 string
	f1, _, err1 = r.cache.GetFile(cache.Subkey(a.hash, "vetx"))
	if !a.factsOnly {
		f2, _, err2 = r.cache.GetFile(cache.Subkey(a.hash, "directives"))
		f3, _, err3 = r.cache.GetFile(cache.Subkey(a.hash, "diagnostics"))
	}
	if err1 != nil || err2 != nil || err3 != nil {
		result, err := r.doUncached(a)
		if err != nil {
			return err
		}
		if a.failed {
			return nil
		}

		// OPT(dh): doUncached returns facts in one format, only for
		// us to immediately convert them to another format.
		gobFacts := &bytes.Buffer{}
		enc := gob.NewEncoder(gobFacts)
		for _, f := range result.objFacts {
			objPath, err := objectpath.For(f.Object)
			if err != nil {
				continue
			}
			gf := gobFact{
				PkgPath: f.Object.Pkg().Path(),
				ObjPath: string(objPath),
				Fact:    f.Fact,
			}
			if err := enc.Encode(gf); err != nil {
				return fmt.Errorf("failed gob encoding data: %w", err)
			}
		}
		for _, f := range result.pkgFacts {
			gf := gobFact{
				PkgPath: f.Package.Path(),
				Fact:    f.Fact,
			}
			if err := enc.Encode(gf); err != nil {
				return fmt.Errorf("failed gob encoding data: %w", err)
			}
		}

		// OPT(dh): We could sort gobFacts for more consistent output,
		// but it doesn't matter. The hash of a package includes all
		// of its files, so whether the vetx hash changes or not, a
		// change to a package requires re-analyzing all dependents,
		// even if the vetx data stayed the same. See also the note at
		// the top of loader/hash.go.

		f1, err = r.writeCache(a, "vetx", gobFacts.Bytes())
		if err != nil {
			return err
		}

		f2, err = r.writeCacheGob(a, "directives", result.dirs)
		if err != nil {
			return err
		}

		gobDiags := &bytes.Buffer{}
		enc = gob.NewEncoder(gobDiags)
		for _, diag := range result.diags {
			d := Diagnostic{
				Pos:      DisplayPosition(result.lpkg.Fset, diag.Pos),
				End:      DisplayPosition(result.lpkg.Fset, diag.End),
				Category: diag.Category,
				Message:  diag.Message,
			}
			for _, sugg := range diag.SuggestedFixes {
				s := SuggestedFix{
					Message: sugg.Message,
				}
				for _, edit := range sugg.TextEdits {
					s.TextEdits = append(s.TextEdits, TextEdit{
						Pos:     DisplayPosition(result.lpkg.Fset, edit.Pos),
						End:     DisplayPosition(result.lpkg.Fset, edit.End),
						NewText: edit.NewText,
					})
				}
				d.SuggestedFixed = append(d.SuggestedFixed, s)
			}
			for _, rel := range diag.Related {
				d.Related = append(d.Related, RelatedInformation{
					Pos:     DisplayPosition(result.lpkg.Fset, rel.Pos),
					End:     DisplayPosition(result.lpkg.Fset, rel.End),
					Message: rel.Message,
				})
			}
			if err := enc.Encode(d); err != nil {
				return fmt.Errorf("failed gob encoding data: %w", err)
			}
		}
		f3, err = r.writeCache(a, "diagnostics", gobDiags.Bytes())
		if err != nil {
			return err
		}
	}
	a.vetx = f1
	a.directives = f2
	a.diagnostics = f3
	return nil
}

func (r *Runner) writeCache(a *packageAction, kind string, data []byte) (string, error) {
	h := cache.Subkey(a.hash, kind)
	if err := r.cache.PutBytes(h, data); err != nil {
		return "", fmt.Errorf("failed caching data: %w", err)
	}
	// OPT(dh): change PutBytes signature so we get the file name right away, not requiring a call to GetFile
	f, _, err := r.cache.GetFile(h)
	if err != nil {
		return "", fmt.Errorf("failed finding cache entry: %w", err)
	}
	return f, nil
}

func (r *Runner) writeCacheGob(a *packageAction, kind string, data interface{}) (string, error) {
	buf := bytes.NewBuffer(nil)
	if err := gob.NewEncoder(buf).Encode(data); err != nil {
		return "", fmt.Errorf("failed gob encoding data: %w", err)
	}
	return r.writeCache(a, kind, buf.Bytes())
}

type packageActionResult struct {
	objFacts []analysis.ObjectFact
	pkgFacts []analysis.PackageFact
	diags    []analysis.Diagnostic
	dirs     []Directive
	lpkg     *loader.Package
}

func (r *Runner) doUncached(a *packageAction) (packageActionResult, error) {
	// OPT(dh): for a -> b; c -> b; if both a and b are being
	// processed concurrently, we shouldn't load b's export data
	// twice.

	pkg, _, err := loader.Load(a.Package)
	if err != nil {
		return packageActionResult{}, err
	}

	if len(pkg.Errors) > 0 {
		// this handles errors that occured during type-checking the
		// package in loader.Load
		for _, err := range pkg.Errors {
			a.errors = append(a.errors, err)
		}
		a.failed = true
		return packageActionResult{}, nil
	}

	dirs := parseDirectives(pkg)
	objFacts, pkgFacts, diagnostics, err := r.runAnalyzers(a, pkg)

	return packageActionResult{
		objFacts: objFacts,
		pkgFacts: pkgFacts,
		diags:    diagnostics,
		dirs:     dirs,
		lpkg:     pkg,
	}, err
}

func pkgPaths(root *types.Package) map[string]*types.Package {
	out := map[string]*types.Package{}
	var dfs func(*types.Package)
	dfs = func(pkg *types.Package) {
		if _, ok := out[pkg.Path()]; ok {
			return
		}
		out[pkg.Path()] = pkg
		for _, imp := range pkg.Imports() {
			dfs(imp)
		}
	}
	dfs(root)
	return out
}

func (r *Runner) loadFacts(root *types.Package, dep *packageAction, objFacts map[objectFactKey]analysis.Fact, pkgFacts map[packageFactKey]analysis.Fact) error {
	// Load facts of all imported packages
	vetx, err := os.Open(dep.vetx)
	if err != nil {
		return fmt.Errorf("failed loading cached facts: %w", err)
	}
	defer vetx.Close()

	pathToPkg := pkgPaths(root)
	dec := gob.NewDecoder(vetx)
	for {
		var gf gobFact
		err := dec.Decode(&gf)
		if err != nil {
			if err == io.EOF {
				break
			}
			return fmt.Errorf("failed loading cached facts: %w", err)
		}

		pkg, ok := pathToPkg[gf.PkgPath]
		if !ok {
			continue
		}
		if gf.ObjPath == "" {
			pkgFacts[packageFactKey{
				Pkg:  pkg,
				Type: reflect.TypeOf(gf.Fact),
			}] = gf.Fact
		} else {
			obj, err := objectpath.Object(pkg, objectpath.Path(gf.ObjPath))
			if err != nil {
				continue
			}
			objFacts[objectFactKey{
				Obj:  obj,
				Type: reflect.TypeOf(gf.Fact),
			}] = gf.Fact
		}
	}
	return nil
}

func genericHandle(a action, root action, queue chan action, sem *tsync.Semaphore, exec func(a action) error) {
	if a == root {
		close(queue)
		if sem != nil {
			sem.Release()
		}
		return
	}
	if !a.IsFailed() {
		// the action may have already been marked as failed during
		// construction of the action graph, for example because of
		// unresolved imports.

		for _, dep := range a.Deps() {
			if dep.IsFailed() {
				// One of our dependencies failed, so mark this package as
				// failed and bail. We don't need to record an error for
				// this package, the relevant error will have been
				// reported by the first package in the chain that failed.
				a.MarkFailed()
				break
			}
		}
	}

	if !a.IsFailed() {
		if err := exec(a); err != nil {
			a.MarkFailed()
			a.AddError(err)
		}
	}
	if sem != nil {
		sem.Release()
	}

	for _, t := range a.Triggers() {
		if t.DecrementPending() {
			queue <- t
		}
	}
}

type analyzerRunner struct {
	pkg *loader.Package
	// object facts of our dependencies; may contain facts of
	// analyzers other than the current one
	depObjFacts map[objectFactKey]analysis.Fact
	// package facts of our dependencies; may contain facts of
	// analyzers other than the current one
	depPkgFacts map[packageFactKey]analysis.Fact
	factsOnly   bool
}

func (ar *analyzerRunner) do(act action) error {
	a := act.(*analyzerAction)
	results := map[*analysis.Analyzer]interface{}{}
	// XXX does this have to be recursive?
	for _, dep := range a.deps {
		dep := dep.(*analyzerAction)
		results[dep.Analyzer] = dep.Result
	}
	factTypes := map[reflect.Type]struct{}{}
	for _, typ := range a.Analyzer.FactTypes {
		factTypes[reflect.TypeOf(typ)] = struct{}{}
	}
	filterFactType := func(typ reflect.Type) bool {
		_, ok := factTypes[typ]
		return ok
	}
	pass := &analysis.Pass{
		Analyzer:   a.Analyzer,
		Fset:       ar.pkg.Fset,
		Files:      ar.pkg.Syntax,
		OtherFiles: ar.pkg.OtherFiles,
		Pkg:        ar.pkg.Types,
		TypesInfo:  ar.pkg.TypesInfo,
		TypesSizes: ar.pkg.TypesSizes,
		Report: func(d analysis.Diagnostic) {
			if !ar.factsOnly {
				if d.Category == "" {
					d.Category = a.Analyzer.Name
				}
				a.Diagnostics = append(a.Diagnostics, d)
			}
		},
		ResultOf: results,
		ImportObjectFact: func(obj types.Object, fact analysis.Fact) bool {
			key := objectFactKey{
				Obj:  obj,
				Type: reflect.TypeOf(fact),
			}
			if f, ok := ar.depObjFacts[key]; ok {
				reflect.ValueOf(fact).Elem().Set(reflect.ValueOf(f).Elem())
				return true
			} else if f, ok := a.ObjectFacts[key]; ok {
				reflect.ValueOf(fact).Elem().Set(reflect.ValueOf(f).Elem())
				return true
			}
			return false
		},
		ImportPackageFact: func(pkg *types.Package, fact analysis.Fact) bool {
			key := packageFactKey{
				Pkg:  pkg,
				Type: reflect.TypeOf(fact),
			}
			if f, ok := ar.depPkgFacts[key]; ok {
				reflect.ValueOf(fact).Elem().Set(reflect.ValueOf(f).Elem())
				return true
			} else if f, ok := a.PackageFacts[key]; ok {
				reflect.ValueOf(fact).Elem().Set(reflect.ValueOf(f).Elem())
				return true
			}
			return false
		},
		ExportObjectFact: func(obj types.Object, fact analysis.Fact) {
			key := objectFactKey{
				Obj:  obj,
				Type: reflect.TypeOf(fact),
			}
			a.ObjectFacts[key] = fact
		},
		ExportPackageFact: func(fact analysis.Fact) {
			key := packageFactKey{
				Pkg:  ar.pkg.Types,
				Type: reflect.TypeOf(fact),
			}
			a.PackageFacts[key] = fact
		},
		AllPackageFacts: func() []analysis.PackageFact {
			out := make([]analysis.PackageFact, 0, len(ar.depPkgFacts)+len(a.PackageFacts))
			for key, fact := range ar.depPkgFacts {
				out = append(out, analysis.PackageFact{
					Package: key.Pkg,
					Fact:    fact,
				})
			}
			for key, fact := range a.PackageFacts {
				out = append(out, analysis.PackageFact{
					Package: key.Pkg,
					Fact:    fact,
				})
			}
			return out
		},
		AllObjectFacts: func() []analysis.ObjectFact {
			out := make([]analysis.ObjectFact, 0, len(ar.depObjFacts)+len(a.ObjectFacts))
			for key, fact := range ar.depObjFacts {
				if filterFactType(key.Type) {
					out = append(out, analysis.ObjectFact{
						Object: key.Obj,
						Fact:   fact,
					})
				}
			}
			for key, fact := range a.ObjectFacts {
				if filterFactType(key.Type) {
					out = append(out, analysis.ObjectFact{
						Object: key.Obj,
						Fact:   fact,
					})
				}
			}
			return out
		},
	}

	res, err := a.Analyzer.Run(pass)
	if err != nil {
		return err
	}
	a.Result = res
	return nil
}

func (r *Runner) runAnalyzers(pkgAct *packageAction, pkg *loader.Package) ([]analysis.ObjectFact, []analysis.PackageFact, []analysis.Diagnostic, error) {
	depObjFacts := map[objectFactKey]analysis.Fact{}
	depPkgFacts := map[packageFactKey]analysis.Fact{}
	for _, dep := range pkgAct.deps {
		if err := r.loadFacts(pkg.Types, dep.(*packageAction), depObjFacts, depPkgFacts); err != nil {
			return nil, nil, nil, err
		}
	}

	// OPT(dh): this computation is the same for all packages
	// (depending on act.factsOnly), we should cache it in the runner.
	analyzerActionCache := map[*analysis.Analyzer]*analyzerAction{}
	root := &analyzerAction{}
	for _, a := range r.analyzers {
		// When analyzing non-initial packages, we only care about
		// analyzers that produce facts.
		if !pkgAct.factsOnly || len(a.FactTypes) > 0 {
			a := newAnalyzerAction(a, analyzerActionCache)
			root.deps = append(root.deps, a)
			a.triggers = append(a.triggers, root)
		}
	}
	root.pending = uint32(len(root.deps))
	all := actionList(root)

	ar := &analyzerRunner{
		pkg:         pkg,
		factsOnly:   pkgAct.factsOnly,
		depObjFacts: depObjFacts,
		depPkgFacts: depPkgFacts,
	}
	queue := make(chan action, len(all))
	for _, a := range all {
		if len(a.Deps()) == 0 {
			queue <- a
		}
	}

	for item := range queue {
		b := r.semaphore.AcquireMaybe()
		if b {
			go genericHandle(item, root, queue, &r.semaphore, ar.do)
		} else {
			// the semaphore is exhausted; run the analysis under the
			// token we've acquired for analyzing the package.
			genericHandle(item, root, queue, nil, ar.do)
		}
	}

	for _, a := range all {
		a := a.(*analyzerAction)
		for key, fact := range a.ObjectFacts {
			depObjFacts[key] = fact
		}
		for key, fact := range a.PackageFacts {
			depPkgFacts[key] = fact
		}
	}

	// OPT(dh): cull objects not reachable via the exported closure
	objFacts := make([]analysis.ObjectFact, 0, len(depObjFacts))
	pkgFacts := make([]analysis.PackageFact, 0, len(depPkgFacts))
	for key, fact := range depObjFacts {
		objFacts = append(objFacts, analysis.ObjectFact{Object: key.Obj, Fact: fact})
	}
	for key, fact := range depPkgFacts {
		pkgFacts = append(pkgFacts, analysis.PackageFact{Package: key.Pkg, Fact: fact})
	}

	var diags []analysis.Diagnostic
	for _, a := range root.deps {
		a := a.(*analyzerAction)
		diags = append(diags, a.Diagnostics...)
	}
	return objFacts, pkgFacts, diags, nil
}

func parseDirectives(pkg *loader.Package) []Directive {
	var dirs []Directive
	for _, f := range pkg.Syntax {
		// XXX in our old code, we skip all the commentmap work if we
		// couldn't find any directives, benchmark if that's actually
		// worth doing
		cm := ast.NewCommentMap(pkg.Fset, f, f.Comments)
		for node, cgs := range cm {
			for _, cg := range cgs {
				for _, c := range cg.List {
					if !strings.HasPrefix(c.Text, "//lint:") {
						continue
					}
					cmd, args := parseDirective(c.Text)
					d := Directive{
						Command:           cmd,
						Arguments:         args,
						DirectivePosition: DisplayPosition(pkg.Fset, c.Pos()),
						NodePosition:      DisplayPosition(pkg.Fset, node.Pos()),
					}
					dirs = append(dirs, d)
				}
			}
		}
	}

	return dirs
}

func parseDirective(s string) (cmd string, args []string) {
	if !strings.HasPrefix(s, "//lint:") {
		return "", nil
	}
	s = strings.TrimPrefix(s, "//lint:")
	fields := strings.Split(s, " ")
	return fields[0], fields[1:]
}

func DisplayPosition(fset *token.FileSet, p token.Pos) token.Position {
	if p == token.NoPos {
		return token.Position{}
	}

	// Only use the adjusted position if it points to another Go file.
	// This means we'll point to the original file for cgo files, but
	// we won't point to a YACC grammar file.
	pos := fset.PositionFor(p, false)
	adjPos := fset.PositionFor(p, true)

	if filepath.Ext(adjPos.Filename) == ".go" {
		return adjPos
	}
	return pos
}

func actionList(root action) []action {
	seen := map[action]bool{}
	all := []action{}
	var walk func(action)
	walk = func(a action) {
		if seen[a] {
			return
		}
		seen[a] = true
		for _, a1 := range a.Deps() {
			walk(a1)
		}
		all = append(all, a)
	}
	walk(root)
	return all
}

func registerGobTypes(analyzers []*analysis.Analyzer) {
	for _, a := range analyzers {
		for _, typ := range a.FactTypes {
			// XXX use RegisterName so we can work around collisions
			// in names. For pointer-types, gob incorrectly qualifies
			// type names with the package name, not the import path.
			gob.Register(typ)
		}
	}
}

func allAnalyzers(analyzers []*analysis.Analyzer) []*analysis.Analyzer {
	seen := map[*analysis.Analyzer]struct{}{}
	out := make([]*analysis.Analyzer, 0, len(analyzers))
	var dfs func(*analysis.Analyzer)
	dfs = func(a *analysis.Analyzer) {
		if _, ok := seen[a]; ok {
			return
		}
		seen[a] = struct{}{}
		out = append(out, a)
		for _, dep := range a.Requires {
			dfs(dep)
		}
	}
	for _, a := range analyzers {
		dfs(a)
	}
	return out
}

func (r *Runner) Run(cfg *packages.Config, analyzers []*analysis.Analyzer, patterns []string) ([]Result, error) {
	r.analyzers = allAnalyzers(analyzers)
	registerGobTypes(r.analyzers)

	lpkgs, err := loader.Graph(cfg, patterns...)
	if err != nil {
		return nil, err
	}

	packageActionCache := map[*loader.PackageSpec]*packageAction{}
	root := &packageAction{}
	for _, lpkg := range lpkgs {
		a := newPackageActionRoot(lpkg, packageActionCache)
		root.deps = append(root.deps, a)
		a.triggers = append(a.triggers, root)
	}
	root.pending = uint32(len(root.deps))

	all := actionList(root)
	queue := make(chan action)

	go func() {
		for _, a := range all {
			if len(a.Deps()) == 0 {
				queue <- a
			}
		}
	}()

	for item := range queue {
		r.semaphore.Acquire()
		go genericHandle(item, root, queue, &r.semaphore, r.do)
	}

	out := make([]Result, len(all))
	for i, item := range all {
		item := item.(*packageAction)
		out[i] = Result{
			Package:     item.Package,
			Failed:      item.failed,
			Errors:      item.errors,
			diagnostics: item.diagnostics,
			directives:  item.directives,
		}
	}
	return out, nil
}
