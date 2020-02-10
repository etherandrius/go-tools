package stylecheck

import (
	"golang.org/x/tools/go/analysis"
	"golang.org/x/tools/go/analysis/passes/inspect"
	"honnef.co/go/tools/facts"
	"honnef.co/go/tools/internal/passes/buildir"
	"honnef.co/go/tools/lint/lintutil"
)

var Analyzers = lintutil.InitializeAnalyzers(Docs, map[string]*analysis.Analyzer{
	"ST1000": {
		Run: CheckPackageComment,
	},
	"ST1001": {
		Run:      CheckDotImports,
		Requires: []*analysis.Analyzer{facts.Generated},
	},
	"ST1003": {
		Run:      CheckNames,
		Requires: []*analysis.Analyzer{inspect.Analyzer, facts.Generated},
	},
	"ST1005": {
		Run:      CheckErrorStrings,
		Requires: []*analysis.Analyzer{buildir.Analyzer},
	},
	"ST1006": {
		Run:      CheckReceiverNames,
		Requires: []*analysis.Analyzer{buildir.Analyzer, facts.Generated},
	},
	"ST1008": {
		Run:      CheckErrorReturn,
		Requires: []*analysis.Analyzer{buildir.Analyzer},
	},
	"ST1011": {
		Run:      CheckTimeNames,
		Requires: []*analysis.Analyzer{inspect.Analyzer},
	},
	"ST1012": {
		Run:      CheckErrorVarNames,
		Requires: []*analysis.Analyzer{},
	},
	"ST1013": {
		Run: CheckHTTPStatusCodes,
		// TODO(dh): why does this depend on facts.TokenFile?
		Requires: []*analysis.Analyzer{facts.Generated, facts.TokenFile, inspect.Analyzer},
	},
	"ST1015": {
		Run:      CheckDefaultCaseOrder,
		Requires: []*analysis.Analyzer{inspect.Analyzer, facts.Generated, facts.TokenFile},
	},
	"ST1016": {
		Run:      CheckReceiverNamesIdentical,
		Requires: []*analysis.Analyzer{buildir.Analyzer, facts.Generated},
	},
	"ST1017": {
		Run:      CheckYodaConditions,
		Requires: []*analysis.Analyzer{inspect.Analyzer, facts.Generated, facts.TokenFile},
	},
	"ST1018": {
		Run:      CheckInvisibleCharacters,
		Requires: []*analysis.Analyzer{inspect.Analyzer},
	},
	"ST1019": {
		Run:      CheckDuplicatedImports,
		Requires: []*analysis.Analyzer{facts.Generated},
	},
	"ST1020": {
		Run:      CheckExportedFunctionDocs,
		Requires: []*analysis.Analyzer{facts.Generated, inspect.Analyzer},
	},
	"ST1021": {
		Run:      CheckExportedTypeDocs,
		Requires: []*analysis.Analyzer{facts.Generated, inspect.Analyzer},
	},
	"ST1022": {
		Run:      CheckExportedVarDocs,
		Requires: []*analysis.Analyzer{facts.Generated, inspect.Analyzer},
	},
})

func init() {
	dotImportWhitelist := lintutil.StringSet{}
	initialisms := lintutil.StringSet{
		"ACL": true, "API": true, "ASCII": true, "CPU": true, "CSS": true, "DNS": true,
		"EOF": true, "GUID": true, "HTML": true, "HTTP": true, "HTTPS": true, "ID": true,
		"SMTP": true, "SQL": true, "SSH": true, "TCP": true, "TLS": true, "TTL": true,
		"UDP": true, "UI": true, "GID": true, "UID": true, "UUID": true, "URI": true,
		"URL": true, "UTF8": true, "VM": true, "XML": true, "XMPP": true, "XSRF": true,
		"XSS": true, "SIP": true, "RTP": true, "AMQP": true, "DB": true, "TS": true,
	}
	httpStatusCodeWhitelist := lintutil.StringSet{
		"200": true, "400": true, "404": true, "500": true,
	}

	Analyzers["ST1001"].Flags.Var(&dotImportWhitelist, "whitelist", "comma-separated list of permitted dot-imports")
	Analyzers["ST1003"].Flags.Var(&initialisms, "initialisms", "comma-separated list of initialisms")
	Analyzers["ST1013"].Flags.Var(&httpStatusCodeWhitelist, "whitelist", "comma-separated list of permitted numerical status codes")
}
