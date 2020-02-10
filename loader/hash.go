package loader

import (
	"fmt"
	"runtime"
	"sort"

	"honnef.co/go/tools/internal/cache"
)

// OPT(dh): our current hashing algorithm means that _any_ change to a
// dependency will change a dependent's hash, even if the change
// didn't affect the exported API. Should we include dependencies via
// their export data hash instead?

// computeHash computes a package's hash. The hash is based on all Go
// files that make up the package, as well as the hashes of imported
// packages.
func computeHash(pkg *PackageSpec) (cache.ActionID, error) {
	key := cache.NewHash("package " + pkg.PkgPath)
	fmt.Fprintf(key, "goos %s goarch %s", runtime.GOOS, runtime.GOARCH)
	fmt.Fprintf(key, "import %q\n", pkg.PkgPath)
	for _, f := range pkg.CompiledGoFiles {
		h, err := cache.FileHash(f)
		if err != nil {
			return cache.ActionID{}, err
		}
		fmt.Fprintf(key, "file %s %x\n", f, h)
	}

	imps := make([]*PackageSpec, 0, len(pkg.Imports))
	for _, v := range pkg.Imports {
		imps = append(imps, v)
	}
	sort.Slice(imps, func(i, j int) bool {
		return imps[i].PkgPath < imps[j].PkgPath
	})

	for _, dep := range imps {
		if dep.ExportFile == "" {
			fmt.Fprintf(key, "import %s \n", dep.PkgPath)
		} else {
			id, err := getBuildid(dep.ExportFile)
			if err == nil {
				fmt.Fprintf(key, "import %s %s\n", dep.PkgPath, id)
			} else {
				fh, err := cache.FileHash(dep.ExportFile)
				if err != nil {
					return cache.ActionID{}, err
				}
				fmt.Fprintf(key, "import %s %x\n", dep.PkgPath, fh)
			}
		}
	}
	return key.Sum(), nil
}

var buildidCache = map[string]string{}

func getBuildid(f string) (string, error) {
	if h, ok := buildidCache[f]; ok {
		return h, nil
	}
	h, err := ReadFile(f)
	if err != nil {
		return "", err
	}
	buildidCache[f] = h
	return h, nil
}
