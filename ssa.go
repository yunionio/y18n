package main

import (
	"flag"
	"fmt"
	"go/constant"
	"go/token"
	"go/types"
	"io/ioutil"
	"os"
	"path/filepath"
	"sort"
	"strings"

	"golang.org/x/mod/modfile"
	"golang.org/x/text/language"
	"golang.org/x/text/message/pipeline"
	"golang.org/x/tools/go/callgraph"
	"golang.org/x/tools/go/callgraph/cha"
	"golang.org/x/tools/go/loader"
	"golang.org/x/tools/go/ssa"
	"golang.org/x/tools/go/ssa/ssautil"

	"github.com/golang/glog"
)

type empty struct{}

type todo struct {
	position *token.Position
	inst     ssa.CallInstruction
	argi     int
}

func (t *todo) String() string {
	argi := t.argi
	arg := t.inst.Common().Args[argi]
	return fmt.Sprintf("%s: %s(%d:%T)",
		t.position, t.inst, argi, arg)
}

type callBox struct {
	visited map[*ssa.Function]empty
	*messageBox
}

func newCallBox() *callBox {
	cb := &callBox{
		visited:    map[*ssa.Function]empty{},
		messageBox: newMessageBox(),
	}
	return cb
}

func (cbox *callBox) mark(f *ssa.Function) bool {
	if _, ok := cbox.visited[f]; ok {
		return true
	}
	cbox.visited[f] = empty{}
	return false
}

type messageBox struct {
	messages     map[token.Pos][]string
	positionFunc func(token.Pos) token.Position
}

func newMessageBox() *messageBox {
	box := &messageBox{
		messages: map[token.Pos][]string{},
	}
	return box
}

func (box *messageBox) addMessages(p token.Pos, ids []string) {
	for _, id := range ids {
		box.addMessage(p, id)
	}
}

func (box *messageBox) addMessage(p token.Pos, id string) {
	if id == "" || id == "%s" || id == "%v" {
		return
	}
	box.messages[p] = append(box.messages[p], id)
}

func (box *messageBox) multiply(box1 *messageBox) *messageBox {
	box2 := newMessageBox()
	for p, ids0 := range box.messages {
		ids1, ok := box1.messages[p]
		if !ok {
			continue
		}
		for _, id0 := range ids0 {
			for _, id1 := range ids1 {
				box2.addMessage(p, id0+": "+id1)
			}
		}
	}
	return box2
}

func (box *messageBox) add(box1 *messageBox) {
	for p, ids := range box1.messages {
		ids0, ok := box.messages[p]
		if ok {
			glog.Errorf("dup: %s", p)
		}
		box.messages[p] = append(ids0, ids...)
	}
}

func (box *messageBox) PositionFunc(f func(token.Pos) token.Position) {
	box.positionFunc = f
}

func (box *messageBox) Messages() []pipeline.Message {
	ms := make([]pipeline.Message, 0, len(box.messages))
	ps := make([]token.Pos, 0, len(box.messages))
	for p := range box.messages {
		ps = append(ps, p)
	}
	sort.Slice(ps, func(i, j int) bool {
		pi := box.positionFunc(ps[i])
		pj := box.positionFunc(ps[j])
		if pi.Filename != pj.Filename {
			return pi.Filename < pj.Filename
		}
		if pi.Line != pj.Line {
			return pi.Line < pj.Line
		}
		return pi.Column < pj.Column
	})
	for _, p := range ps {
		ids := box.messages[p]
		for _, id := range ids {
			var position string
			if pos := box.positionFunc(p); pos.IsValid() {
				position = pos.String()
			}
			ms = append(ms, pipeline.Message{
				ID:       pipeline.IDList{id},
				Key:      id,
				Message:  pipeline.Text{Msg: id},
				Position: position,
			})
		}
	}
	return ms
}

type basicBlockWalkerCb func(*basicBlockWalker, ssa.Instruction)
type basicBlockWalker struct {
	visited  map[*ssa.Function]empty
	visitedB map[*ssa.BasicBlock]empty
	cb       basicBlockWalkerCb
}

func newBasicBlockWalker(cb basicBlockWalkerCb) *basicBlockWalker {
	bbw := &basicBlockWalker{
		visited:  map[*ssa.Function]empty{},
		visitedB: map[*ssa.BasicBlock]empty{},
		cb:       cb,
	}
	return bbw
}

func (bbw *basicBlockWalker) walkFunc(f *ssa.Function) {
	if _, ok := bbw.visited[f]; ok {
		return
	}
	bbw.visited[f] = empty{}
	for _, bb := range f.Blocks {
		bbw.walkOne(bb)
	}
}

func (bbw *basicBlockWalker) walkOne(bb *ssa.BasicBlock) {
	if _, ok := bbw.visitedB[bb]; ok {
		return
	}
	bbw.visitedB[bb] = empty{}
	for _, instr := range bb.Instrs {
		bbw.cb(bbw, instr)
	}
	for _, bb1 := range bb.Succs {
		bbw.walkOne(bb1)
	}
}

type extractor struct {
	pkgnames []string
	pkginfos []*loader.PackageInfo

	lprog *loader.Program
	sprog *ssa.Program
	callg *callgraph.Graph

	errorType     types.Type
	newJerrorFunc *ssa.Function
	newVerrorFunc *ssa.Function
	vErrType      types.Type
	vErrTypeMap   map[int64]string

	todos map[string][]*todo
	box   *messageBox
}

func loadPackage(pkgnames []string) (*loader.Program, error) {
	conf := &loader.Config{}
	for _, pkgname := range pkgnames {
		conf.Import(pkgname)
	}
	lprog, err := conf.Load()
	if err != nil {
		return nil, err
	}
	return lprog, nil
}

func newExtractor(pkgnames []string) (*extractor, error) {
	lprog, err := loadPackage(pkgnames)
	if err != nil {
		return nil, err
	}
	pkginfos := make([]*loader.PackageInfo, len(pkgnames))
	for i, pkgname := range pkgnames {
		pkginfo := lprog.Imported[pkgname]
		if pkginfo == nil {
			return nil, fmt.Errorf("%s not imported", pkgname)
		}
		pkginfos[i] = pkginfo
	}

	sprog := ssautil.CreateProgram(lprog, ssa.BuilderMode(0))
	sprog.Build()
	callg := cha.CallGraph(sprog)
	x := &extractor{
		pkgnames: pkgnames,
		pkginfos: pkginfos,

		lprog: lprog,
		sprog: sprog,
		callg: callg,

		todos: map[string][]*todo{},
		box:   newMessageBox(),
	}
	if info := x.findPkg("yunion.io/x/pkg/errors"); info != nil {
		tpkg := info.Pkg
		tscope := tpkg.Scope()
		tobj := tscope.Lookup("Error")
		if tobj != nil {
			x.errorType = tobj.Type()
		}
	}
	if info := x.findPkg("yunion.io/x/onecloud/pkg/util/httputils"); info != nil {
		spkg := x.sprog.Package(info.Pkg)
		f := spkg.Func("NewJsonClientError")
		x.newJerrorFunc = f
	}
	if info := x.findPkg("yunion.io/x/onecloud/pkg/cloudcommon/validators"); info != nil {
		tpkg := info.Pkg
		tscope := tpkg.Scope()
		tobj := tscope.Lookup("ErrType")
		if tobj != nil {
			x.vErrType = tobj.Type()
			x.vErrTypeMap = map[int64]string{}
			spkg := x.sprog.Package(info.Pkg)
			initf := spkg.Func("init")
			for {
				ins := callg.Nodes[initf].In
				if len(ins) == 0 {
					break
				}
				initf = ins[0].Caller.Func
			}
			bbw := newBasicBlockWalker(x.populateVErrTypeMap)
			bbw.walkFunc(initf)
			f := spkg.Func("newError")
			x.newVerrorFunc = f
		}
	}

	if x.newJerrorFunc != nil || x.newVerrorFunc != nil {
	}
	return x, nil
}

func (x *extractor) populateVErrTypeMap(bbw *basicBlockWalker, inst ssa.Instruction) {
	switch inst1 := inst.(type) {
	case *ssa.MapUpdate:
		k, ok := inst1.Key.(*ssa.Const)
		if ok && k.Type() != x.vErrType {
			return
		}
		v, ok := inst1.Value.(*ssa.Const)
		if !ok {
			return
		}
		if t, ok := v.Type().(*types.Basic); !ok || t.Kind() != types.String {
			return
		}
		x.vErrTypeMap[k.Int64()] = constant.StringVal(v.Value)
	case *ssa.Call:
		f := inst1.Common().StaticCallee()
		if f != nil {
			bbw.walkFunc(f)
		}
	}
}

func (x *extractor) posStr(p token.Pos) string {
	return x.lprog.Fset.Position(p).String()
}

func (x *extractor) findPkg(pkgsearch string) *loader.PackageInfo {
	var (
		lprog = x.lprog
	)
	if info := lprog.Package(pkgsearch); info != nil {
		return info
	}
	var (
		pkgnames = x.pkgnames
	)
	for _, pkgname := range pkgnames {
		for p := pkgname; p != "."; p = filepath.Dir(p) {
			path := filepath.Join(p, "vendor", pkgsearch)
			if info := lprog.Package(path); info != nil {
				return info
			}
		}
	}
	return nil
}

func (x *extractor) x() {
	x.xErrors()
	x.xJerrors()
	x.xVerrors()
}

func findModPath(pkgpath string) string {
	for p := pkgpath; p != "."; p = filepath.Dir(p) {
		f := filepath.Join(p, "go.mod")
		if _, err := os.Stat(f); err == nil {
			fdata, err := ioutil.ReadFile(f)
			if err != nil {
				return ""
			}
			mf, err := modfile.Parse(f, fdata, nil)
			if err != nil {
				return ""
			}
			return mf.Module.Mod.Path
		}
	}
	return ""
}

func findYunionRepoName(pkgpath string) string {
	const y = "yunion.io/x/"
	i := strings.Index(pkgpath, y)
	if i < 0 {
		return ""
	}
	if i > 0 && pkgpath[i-1] != '/' {
		return ""
	}
	i += len(y)
	j := i
	for ; j < len(pkgpath); j++ {
		switch pkgpath[j] {
		case '@':
			// -mod mod
			return pkgpath[i:j]
		case '/':
			return pkgpath[i:j]
		}
	}
	return pkgpath[i:j]
}

func (x *extractor) ignorePkg(pkg *ssa.Package) bool {
	pkgPath := pkg.Pkg.Path()
	if strings.Contains(pkgPath, "/vendor/") {
		return true
	}
	if strings.Contains(pkgPath, "/pkg/mod/") {
		return true
	}

	yourMod := findModPath(pkgPath)
	yourName := findYunionRepoName(pkgPath)
	for _, pkginfo := range x.pkginfos {
		myPath := pkginfo.Pkg.Path()
		myMod := findModPath(myPath)
		if myMod != yourMod {
			return true
		}
		myName := findYunionRepoName(myPath)
		if myName != yourName {
			return true
		}
	}
	return false
}

func (x *extractor) xErrors() {
	if x.errorType == nil {
		return
	}
	// find all errors.Error const
	for _, pkg := range x.sprog.AllPackages() {
		if x.ignorePkg(pkg) {
			// glog.Infof("pkg ignore %s", pkg.Pkg.Path())
			continue
		}
		// glog.Infof("pkg noignore %s", pkg.Pkg.Path())
		for _, member := range pkg.Members {
			namedConst, ok := member.(*ssa.NamedConst)
			if !ok {
				continue
			}
			val := namedConst.Value
			valType := val.Type()
			if valType == x.errorType {
				x.box.addMessage(namedConst.Pos(), constant.StringVal(val.Value))
			}
		}
	}
}

func (x *extractor) xJerrors() {
	if x.newJerrorFunc == nil {
		return
	}
	cbox := newCallBox()
	x.handleCallFmt(cbox, x.newJerrorFunc, 2)
	x.importMessageBox(cbox.messageBox)
}

func (x *extractor) xVerrors() {
	if x.newVerrorFunc == nil {
		return
	}
	callBox0 := newCallBox()
	x.handleCallVReason(callBox0, x.newVerrorFunc, 0)
	callBox1 := newCallBox()
	x.handleCallFmt(callBox1, x.newVerrorFunc, 1)

	box := callBox0.messageBox.multiply(callBox1.messageBox)
	x.importMessageBox(box)
}

func (x *extractor) handleCallFmt(cbox *callBox, f *ssa.Function, fmtArgI int) {
	cbox.mark(f)
	for _, edge := range x.callg.Nodes[f].In {
		callCommon := edge.Site.Common()
		if callCommon == nil {
			continue
		}
		args := callCommon.Args
		if len(args) <= fmtArgI {
			continue
		}
		pos := callCommon.Pos()
		argMsg := args[fmtArgI]
		switch arg := argMsg.(type) {
		case *ssa.Parameter:
			caller := edge.Caller
			callerFunc := caller.Func
			for i, param := range callerFunc.Params {
				if param == arg {
					x.handleCallFmt(cbox, callerFunc, i)
				}
			}
		case *ssa.Const:
			cbox.addMessage(pos, constant.StringVal(arg.Value))
		case *ssa.Phi:
			for _, val := range arg.Edges {
				r := x.handleMsgValue(val)
				cbox.addMessages(pos, r)
			}
		default:
			x.addTodo(edge.Site, fmtArgI)
		}
	}
}

func (x *extractor) handleCallVReason(cbox *callBox, f *ssa.Function, fmtArgI int) {
	cbox.mark(f)
	for _, edge := range x.callg.Nodes[f].In {
		callCommon := edge.Site.Common()
		if callCommon == nil {
			continue
		}
		args := callCommon.Args
		if len(args) <= fmtArgI {
			continue
		}
		pos := callCommon.Pos()
		argMsg := args[fmtArgI]
		switch arg := argMsg.(type) {
		case *ssa.Const:
			if arg.Type() == x.vErrType {
				id, ok := x.vErrTypeMap[arg.Int64()]
				if ok {
					cbox.addMessage(pos, id)
				}
			}
		default:
		}
	}
}

func (x *extractor) handleMsgValue(val ssa.Value) []string {
	switch v := val.(type) {
	case *ssa.Phi:
		var r []string
		for _, vval := range v.Edges {
			r0 := x.handleMsgValue(vval)
			r = append(r, r0...)
		}
		return r
	case *ssa.BinOp:
		if v.Op != token.ADD {
			return nil
		}
		ss := [2][]string{}
		for i, v := range []ssa.Value{v.X, v.Y} {
			ss[i] = x.handleMsgValue(v)
			if len(ss[i]) == 0 {
				return nil
			}
		}
		sx := ss[0]
		sy := ss[1]
		r := make([]string, 0, len(sx)*len(sy))
		for _, sx0 := range sx {
			for _, sy0 := range sy {
				s0 := sx0 + sy0
				if s0 != "" {
					r = append(r, s0)
				}
			}
		}
		return r
	case *ssa.Const:
		return []string{
			constant.StringVal(v.Value),
		}
	case *ssa.Call:
		// pkg/cloudcommon/validators/errors.go, newInvalidStructError
	default:
		glog.Errorf("%s: unhandled ssa value: %T %s %#v", x.posStr(v.Pos()), v, v, v)
	}
	return nil
}

func (x *extractor) importMessageBox(box *messageBox) {
	x.box.add(box)
}

func (x *extractor) addTodo(inst ssa.CallInstruction, argi int) {
	if inst.Parent() == x.newVerrorFunc {
		// We handle it specifically in x.xVerrors()
		return
	}
	pos := inst.Pos()
	position := x.lprog.Fset.Position(pos)
	fname := position.Filename
	x.todos[fname] = append(x.todos[fname], &todo{
		position: &position,
		inst:     inst,
		argi:     argi,
	})
}

func (x *extractor) relPosition(p token.Pos) token.Position {
	pos := x.lprog.Fset.Position(p)
	cwd, err := os.Getwd()
	if err != nil {
		return pos
	}
	rel, err := filepath.Rel(cwd, pos.Filename)
	if err != nil {
		return pos
	}
	pos.Filename = rel
	return pos
}

func (x *extractor) State(c *pipeline.Config) *pipeline.State {
	x.box.PositionFunc(x.relPosition)
	messages := x.box.Messages()
	state := &pipeline.State{
		Config: *c,
		Extracted: pipeline.Messages{
			Language: c.SourceLanguage,
			Messages: messages,
		},
	}
	return state
}

var (
	chdir   = flag.String("chdir", "", "working directory")
	srcLang = flag.String("srclang", "en-US", "the source-code language")
	lang    = flag.String("lang", "en-US", "comma-separated list of languages to process")
	dir     = flag.String("dir", "locales", "default subdirectory to store translation files")
	out     = flag.String("out", "", "output file to write to")
)

func configFromArg() (*pipeline.Config, error) {
	srcLangTag, err := language.Parse(*srcLang)
	if err != nil {
		return nil, fmt.Errorf("invalid srclang: %w", err)
	}
	var supportedTags []language.Tag
	for _, s := range strings.Split(*lang, ",") {
		if s == "" {
			continue
		}
		tag, err := language.Parse(s)
		if err != nil {
			return nil, fmt.Errorf("parse language tag %q: %w", s, err)
		}
		supportedTags = append(supportedTags, tag)
	}
	outf := filepath.Base(*out)
	outp := filepath.Dir(*out)
	if outp != "" && outp[0] != '/' {
		outp = "./" + outp
	}
	return &pipeline.Config{
		Dir: *dir,

		GenFile:    outf,
		GenPackage: outp,
		DeclareVar: "Catalog",
		SetDefault: false,

		SourceLanguage:      srcLangTag,
		Supported:           supportedTags,
		TranslationsPattern: `messages\.(.*)\.json`,
	}, nil
}

func actionPrepWriteFunc(c *pipeline.Config) func() error {
	return func() error {
		var (
			err  error
			name = filepath.Base(c.GenPackage)
			mode = os.FileMode(0644)
		)
		err = os.MkdirAll(c.Dir, os.FileMode(0755))
		if err != nil {
			return err
		}
		err = ioutil.WriteFile(filepath.Join(c.Dir, "doc.go"), []byte("package "+name+"\n"), mode)
		if err != nil {
			return err
		}
		err = ioutil.WriteFile(
			filepath.Join(c.Dir, "locales.go"), []byte(
				fmt.Sprintf(`
package %s
import "golang.org/x/text/message/catalog"
var %s catalog.Catalog
				`, name, c.DeclareVar)),
			mode)
		if err != nil {
			return err
		}
		return nil
	}
}

type stateAction uint32

const (
	actionImport stateAction = iota
	actionMerge
	actionPrepWrite_
	actionExport
	actionGenerate
	actionMAX_
)

var stateActionStrings = [...]string{
	"import",
	"merge",
	"prep_write_",
	"export",
	"generate",
}

func (sa stateAction) String() string {
	return stateActionStrings[sa]
}

func main() {
	flag.Lookup("logtostderr").Value.Set("true")
	flag.Parse()

	if *chdir != "" {
		err := os.Chdir(*chdir)
		if err != nil {
			glog.Fatalf("chdir %v", err)
		}
	}

	pkgnames := flag.Args()
	if len(pkgnames) == 0 {
		return
	}
	x, err := newExtractor(pkgnames)
	if err != nil {
		glog.Fatalf("load package: %v", err)
	}

	x.x()
	c, err := configFromArg()
	if err != nil {
		glog.Fatalf("config from arg: %v", err)
	}
	state := x.State(c)
	actionFuncMap := map[stateAction]func() error{
		actionImport:     state.Import,
		actionMerge:      state.Merge,
		actionPrepWrite_: actionPrepWriteFunc(c),
		actionExport:     state.Export,
		actionGenerate:   state.Generate,
	}
	for action := actionImport; action < actionMAX_; action++ {
		f := actionFuncMap[action]
		if err := f(); err != nil {
			glog.Fatalf("%s: %v", action, err)
		} else {
			glog.Infof("%s: done", action)
		}
	}

	for _, todos := range x.todos {
		for _, todo := range todos {
			glog.Infof("%s", todo.String())
		}
	}
	/*
	 *for p, ids := range x.box.messages {
	 *        for i, id := range ids {
	 *                glog.Infof("%s: %d: %s", x.posStr(p), i, id)
	 *        }
	 *}
	 */
	glog.Infof("messages %d", len(x.box.messages))
}
