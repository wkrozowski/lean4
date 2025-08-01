/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich, Mac Malone, Siddharth Bhat
-/
prelude
import Lake.Util.OrdHashSet
import Lake.Util.List
import Lean.Elab.ParseImportsFast
import Lake.Build.Common
import Lake.Build.Target

/-! # Module Facet Builds
Build function definitions for a module's builtin facets.
-/

open System Lean

namespace Lake

/-- Compute library directories and build external library Jobs of the given packages. -/
@[deprecated "Deprecated without replacement" (since := "2025-03-28")]
def recBuildExternDynlibs (pkgs : Array Package)
: FetchM (Array (Job Dynlib) × Array FilePath) := do
  let mut libDirs := #[]
  let mut jobs : Array (Job Dynlib) := #[]
  for pkg in pkgs do
    libDirs := libDirs.push pkg.sharedLibDir
    jobs := jobs.append <| ← pkg.externLibs.mapM (·.dynlib.fetch)
  return (jobs, libDirs)

/-- Parse the header of a Lean file from its source. -/
def Module.recFetchInput (mod : Module) : FetchM (Job ModuleInput) := Job.async do
  let path := mod.leanFile
  let contents ← IO.FS.readFile path
  setTrace {caption := path.toString, mtime := ← getMTime path, hash := .ofText contents}
  let header ← Lean.parseImports' contents path.toString
  let imports ← header.imports.mapM fun imp => do
    return ⟨imp, (← findModule? imp.module)⟩
  return {path, header, imports}

/-- The `ModuleFacetConfig` for the builtin `inputFacet`. -/
def Module.inputFacetConfig : ModuleFacetConfig inputFacet :=
  mkFacetJobConfig recFetchInput (buildable := false)

/-- The `ModuleFacetConfig` for the builtin `leanFacet`. -/
def Module.leanFacetConfig : ModuleFacetConfig leanFacet :=
  mkFacetJobConfig fun mod =>
    return (← mod.input.fetch).map (sync := true) (·.path)

/-- The `ModuleFacetConfig` for the builtin `headerFacet`. -/
def Module.headerFacetConfig : ModuleFacetConfig headerFacet :=
   mkFacetJobConfig (buildable := false) fun mod =>
    return (← mod.input.fetch).map (sync := true) (·.header)

/-- Compute an `Array` of a module's direct local imports from its header. -/
def Module.recParseImports (mod : Module) : FetchM (Job (Array Module)) := do
  (← mod.input.fetch).mapM (sync := true) fun input => do
    let mods := input.imports.foldl (init := OrdModuleSet.empty) fun set imp =>
      match imp.module? with | some mod => set.insert mod | none => set
    return mods.toArray

/-- The `ModuleFacetConfig` for the builtin `importsFacet`. -/
def Module.importsFacetConfig : ModuleFacetConfig importsFacet :=
  mkFacetJobConfig recParseImports (buildable := false)

private structure ModuleImportData where
  module : Module
  transImports : Job (Array Module)
  includeSelf : Bool

@[inline] private def collectImportsAux
  (fileName : String) (imports : Array Module)
  (f : Module → FetchM (Bool × Job (Array Module)))
: FetchM (Job (Array Module)) := do
  let imps ← imports.mapM fun imp => do
    let (includeSelf, transImports) ← f imp
    return {module := imp, transImports, includeSelf : ModuleImportData}
  let task : JobTask OrdModuleSet := imps.foldl (init := .pure (.ok .empty {})) fun r imp =>
    r.bind (sync := true) fun r =>
    imp.transImports.task.map (sync := true) fun
    | .ok transImps _ =>
      match r with
      | .ok impSet s =>
        let impSet := impSet.appendArray transImps
        let impSet := if imp.includeSelf then impSet.insert imp.module else impSet
        .ok impSet s
      | .error e s => .error e s
    | .error _ _ =>
      let entry := LogEntry.error s!"{fileName}: bad import '{imp.module.name}'"
      match r with
      | .ok _ s => .error 0 (s.logEntry entry)
      | .error e s => .error e (s.logEntry entry)
  return Job.ofTask <| task.map (sync := true) fun
    | .ok impSet s => .ok impSet.toArray s
    | .error e s => .error e s

/-- Recursively compute a module's transitive imports. -/
def Module.recComputeTransImports (mod : Module) : FetchM (Job (Array Module)) := ensureJob do
  collectImportsAux mod.leanFile.toString (← (← mod.imports.fetch).await) fun imp =>
    (true, ·) <$> imp.transImports.fetch

/-- The `ModuleFacetConfig` for the builtin `transImportsFacet`. -/
def Module.transImportsFacetConfig : ModuleFacetConfig transImportsFacet :=
  mkFacetJobConfig recComputeTransImports (buildable := false)

def computePrecompileImportsAux
  (fileName : String) (imports : Array Module)
: FetchM (Job (Array Module)) := do
  collectImportsAux fileName imports fun imp =>
    if imp.shouldPrecompile then
      (true, ·) <$> imp.transImports.fetch
    else
      (false, ·) <$> imp.precompileImports.fetch

/-- Recursively compute a module's precompiled imports. -/
def Module.recComputePrecompileImports (mod : Module) : FetchM (Job (Array Module)) := ensureJob do
  inline <| computePrecompileImportsAux mod.leanFile.toString (← (← mod.imports.fetch).await)

/-- The `ModuleFacetConfig` for the builtin `precompileImportsFacet`. -/
def Module.precompileImportsFacetConfig : ModuleFacetConfig precompileImportsFacet :=
  mkFacetJobConfig recComputePrecompileImports (buildable := false)

/--
Computes the transitive dynamic libraries of a module's imports.
Modules from the same library are loaded individually, while modules
from other libraries are loaded as part of the whole library.
-/
private def Module.fetchImportLibs
  (self : Module) (imps : Array Module) (compileSelf : Bool)
: FetchM (Array (Job Dynlib)) := do
  let (_, jobs) ← imps.foldlM (init := (({} : NameSet), #[])) fun (libs, jobs) imp => do
    if libs.contains imp.lib.name then
      return (libs, jobs)
    else if compileSelf && self.lib.name = imp.lib.name then
      let job ← imp.dynlib.fetch
      return (libs, jobs.push job)
    else if compileSelf || imp.shouldPrecompile then
      let jobs ← jobs.push <$> imp.lib.shared.fetch
      return (libs.insert imp.lib.name, jobs)
    else
      return (libs, jobs)
  return jobs

/--
Fetches the library dynlibs of a list of non-local imports.
Modules are loaded as part of their whole library.
-/
private def fetchImportLibs
  (mods : Array Module) : FetchM (Job (Array Dynlib))
:= do
  let (_, jobs) ← mods.foldlM (init := (({} : NameSet), #[])) fun (libs, jobs) imp => do
    if libs.contains imp.lib.name then
      return (libs, jobs)
    else if imp.shouldPrecompile then
      let jobs ← jobs.push <$> imp.lib.shared.fetch
      return (libs.insert imp.lib.name, jobs)
    else
      return (libs, jobs)
  return Job.collectArray jobs "import dynlibs"

/--
Topologically sorts the library dependency tree by name.
Libraries come *after* their dependencies.
-/
private partial def mkLoadOrder (libs : Array Dynlib) : FetchM (Array Dynlib) := do
  let r := libs.foldlM (m := Except (Cycle String)) (init := ({}, #[])) fun (v, o) lib =>
    go lib [] v o
  match r with
  | .ok (_, order) => pure order
  | .error cycle => error s!"library dependency cycle:\n{formatCycle cycle}"
where
  go lib (ps : List String) (v : Std.TreeSet String compare) (o : Array Dynlib) := do
    if v.contains lib.name then
      return (v, o)
    if ps.contains lib.name then
      throw (lib.name :: ps)
    let ps := lib.name :: ps
    let v := v.insert lib.name
    let (v, o) ← lib.deps.foldlM (init := (v, o)) fun (v, o) lib =>
      go lib ps v o
    let o := o.push lib
    return (v, o)

private structure ModuleDeps where
  dynlibs : Array Dynlib := #[]
  plugins : Array Dynlib := #[]
  deriving Inhabited, Repr

private def computeModuleDeps
  (impLibs : Array Dynlib) (externLibs : Array Dynlib)
  (dynlibs : Array Dynlib) (plugins : Array Dynlib)
: FetchM ModuleDeps := do
  /-
  Requirements:
  * Lean wants the external library symbols before module symbols.
  * Unix requires the file extension of the dynlib.
  * For some reason, building from the Lean server requires full paths.
    Everything else loads fine with just the augmented library path.
  * Linux needs the augmented path to resolve nested dependencies in dynlibs.
  -/
  let impLibs ← mkLoadOrder impLibs
  let mut dynlibs := externLibs ++ dynlibs
  let mut plugins := plugins
  for impLib in impLibs do
    if impLib.plugin then
      plugins := plugins.push impLib
    else
      dynlibs := dynlibs.push impLib
  /-
  On MacOS, Lake must be loaded as a plugin for
  `import Lake` to work with precompiled modules.
  https://github.com/leanprover/lean4/issues/7388
  -/
  if Platform.isOSX && !(plugins.isEmpty && dynlibs.isEmpty) then
    plugins := plugins.push (← getLakeInstall).sharedDynlib
  return {dynlibs, plugins}

private partial def fetchTransImportArts
  (directImports : Array ModuleImport) (directArts : NameMap ImportArtifacts) (nonModule : Bool)
: FetchM (NameMap ImportArtifacts) := do
  let q ← directImports.foldlM (init := #[]) fun q imp => do
    let some mod := imp.module? | return q
    let input ← (← mod.input.fetch).await
    let importAll := strictOr nonModule imp.importAll
    return enqueue importAll input q
  walk directArts q
where
  walk s q := do
    if h : 0 < q.size then
      let (mod, importAll) := q.back
      let q := q.pop
      if let some arts := s.find? mod.name then
        -- may need to promote a module system `import` to an `import all`
        -- size of 1 = non-module, 3 = module system `import`, 4 = `import all`
        unless importAll && arts.size == 3 do
          return ← walk s q
      let info ← (← mod.exportInfo.fetch).await
      let arts := if importAll then info.allArts else info.arts
      let s := s.insert mod.name arts
      let input ← (← mod.input.fetch).await
      let q := enqueue importAll input q
      walk s q
    else
      return s
  enqueue importAll input q :=
    input.imports.foldr (init := q) fun imp q =>
      if let some mod := imp.module? then
        if importAll || imp.isExported then
          q.push (mod, nonModule || (importAll && imp.importAll))
        else q
      else q

private def ModuleImportInfo.nil (modName : Name) : ModuleImportInfo where
  directArts := {}
  trace := .nil s!"imports"
  transTrace := .nil s!"{modName} transitive imports (public)"
  metaTransTrace := .nil s!"{modName} transitive imports (meta)"
  allTransTrace := .nil s!"{modName} transitive imports (all)"
  legacyTransTrace := .nil s!"{modName} transitive imports (legacy)"

private def ModuleImportInfo.addImport
  (info : ModuleImportInfo) (nonModule : Bool)
  (mod : Module) (imp : Import) (expInfo : ModuleExportInfo)
: ModuleImportInfo :=
  let info :=
    if nonModule then
      {info with
        directArts := info.directArts.insert mod.name expInfo.allArts
        trace := info.trace.mix expInfo.legacyTransTrace |>.mix expInfo.allArtsTrace.withoutInputs
      }
    else if imp.importAll then
      {info with
        directArts := info.directArts.insert mod.name expInfo.allArts
        trace := info.trace.mix expInfo.allTransTrace |>.mix expInfo.allArtsTrace.withoutInputs
      }
    else
      let info :=
        if !info.directArts.contains mod.name then -- do not demote `import all`
          {info with directArts := info.directArts.insert mod.name expInfo.arts}
        else
          info
      if imp.isMeta then
        {info with trace := info.trace.mix expInfo.metaTransTrace |>.mix expInfo.metaArtsTrace.withoutInputs}
      else
        {info with trace := info.trace.mix expInfo.transTrace |>.mix expInfo.artsTrace.withoutInputs}
  let info := {info with
    legacyTransTrace := info.legacyTransTrace
      |>.mix expInfo.legacyTransTrace
      |>.mix expInfo.allArtsTrace.withoutInputs
      |>.withoutInputs
  }
  let info :=
    if imp.importAll then
      {info with
        allTransTrace := info.allTransTrace
          |>.mix expInfo.allTransTrace
          |>.mix expInfo.allArtsTrace.withoutInputs
          |>.withoutInputs
      }
    else if imp.isMeta then
      {info with
        allTransTrace := info.allTransTrace
          |>.mix expInfo.metaTransTrace
          |>.mix expInfo.metaArtsTrace.withoutInputs
          |>.withoutInputs
      }
    else
      {info with
        allTransTrace := info.allTransTrace
          |>.mix expInfo.transTrace
          |>.mix expInfo.artsTrace.withoutInputs
          |>.withoutInputs
      }
  if imp.isExported then
    let info := {info with
      metaTransTrace := info.metaTransTrace
        |>.mix expInfo.metaTransTrace
        |>.mix expInfo.metaArtsTrace.withoutInputs
        |>.withoutInputs
    }
    if imp.isMeta then
      {info with
        transTrace := info.transTrace
          |>.mix expInfo.metaTransTrace
          |>.mix expInfo.metaArtsTrace.withoutInputs
          |>.withoutInputs
      }
    else
      {info with
        transTrace := info.transTrace
          |>.mix expInfo.transTrace
          |>.mix expInfo.artsTrace.withoutInputs
          |>.withoutInputs
      }
  else
    info

private def fetchImportInfo
  (fileName : String) (modName : Name) (header : ModuleHeader)
: FetchM (Job ModuleImportInfo) := do
  let nonModule := !header.isModule
  let info := ModuleImportInfo.nil modName
  let impArtsJob : Job ModuleImportInfo := .pure info
  header.imports.foldlM (init := impArtsJob) fun s imp => do
    if modName = imp.module then
      logError s!"{fileName}: module imports itself"
      return .error
    let some mod ← findModule? imp.module
      | return s
    let importJob ← mod.exportInfo.fetch
    return s.zipWith (·.addImport nonModule mod imp ·) importJob

/-- The `ModuleFacetConfig` for the builtin `importInfoFacet`. -/
def Module.importInfoFacetConfig : ModuleFacetConfig importInfoFacet :=
  mkFacetJobConfig fun mod => do
    let header ← (← mod.header.fetch).await
    fetchImportInfo mod.relLeanFile.toString mod.name header

private def noServerOLeanError :=
  "No server olean generated. Ensure the module system is enabled."

private def noPrivateOLeanError :=
  "No private olean generated. Ensure the module system is enabled."

private def noIRError :=
  "No `.ir` generated. Ensure the module system is enabled."

/-- Computes the import artifacts and transitive import trace of a module's imports. -/
def Module.computeExportInfo (mod : Module) : FetchM (Job ModuleExportInfo) := do
  (← mod.leanArts.fetch).mapM (sync := true) fun arts => do
    let header ← (← mod.header.fetch).await
    let importInfo ← (← mod.importInfo.fetch).await
    let artsTrace := BuildTrace.nil s!"{mod.name}:importArts"
    let metaArtsTrace := BuildTrace.nil s!"{mod.name}:importArts (meta)"
    let allArtsTrace := BuildTrace.nil s!"{mod.name}:importAllArts"
    let olean := arts.olean
    if header.isModule then
      let some oleanServer := arts.oleanServer?
        | error noServerOLeanError
      let some ir := arts.ir?
        | error noIRError
      let some oleanPrivate := arts.oleanPrivate?
        | error noPrivateOLeanError
      return {
        arts := .ofArray #[olean.path, ir.path, oleanServer.path]
        artsTrace := artsTrace.mix olean.trace
        metaArtsTrace := metaArtsTrace.mix olean.trace |>.mix ir.trace
        allArts := .ofArray #[olean.path, ir.path, oleanServer.path, oleanPrivate.path]
        allArtsTrace := allArtsTrace.mix
          olean.trace |>.mix ir.trace |>.mix oleanServer.trace |>.mix oleanPrivate.trace
        transTrace := importInfo.transTrace
        metaTransTrace := importInfo.metaTransTrace
        allTransTrace := importInfo.allTransTrace
        legacyTransTrace := importInfo.legacyTransTrace
      }
    else
      return {
        arts := ⟨#[olean.path]⟩
        artsTrace := artsTrace.mix olean.trace
        metaArtsTrace := metaArtsTrace.mix olean.trace
        allArts := ⟨#[olean.path]⟩
        allArtsTrace:= allArtsTrace.mix olean.trace
        transTrace := importInfo.transTrace
        metaTransTrace := importInfo.metaTransTrace
        allTransTrace := importInfo.allTransTrace
        legacyTransTrace := importInfo.legacyTransTrace
      }

/-- The `ModuleFacetConfig` for the builtin `exportInfoFacet`. -/
def Module.exportInfoFacetConfig : ModuleFacetConfig exportInfoFacet :=
  mkFacetJobConfig computeExportInfo (buildable := false)

/-- The `ModuleFacetConfig` for the builtin `importArtsFacet`. -/
def Module.importArtsFacetConfig : ModuleFacetConfig importArtsFacet :=
  mkFacetJobConfig fun mod =>
    return (← mod.exportInfo.fetch).mapOk (sync := true) fun i s =>
      .ok i.arts {s with trace := i.artsTrace}

/-- The `ModuleFacetConfig` for the builtin `importAllArtsFacet`. -/
def Module.importAllArtsFacetConfig : ModuleFacetConfig importAllArtsFacet :=
  mkFacetJobConfig fun mod =>
    return (← mod.exportInfo.fetch).mapOk (sync := true) fun i s =>
      .ok i.arts {s with trace := i.allArtsTrace}

/--
Recursively build a module's dependencies, including:
* Transitive local imports
* Shared libraries (e.g., `extern_lib` targets or precompiled modules)
* `extraDepTargets` of its library
-/
def Module.recFetchSetup (mod : Module) : FetchM (Job ModuleSetup) := ensureJob do
  let extraDepJob ← mod.lib.extraDep.fetch
  let headerJob ← mod.header.fetch

  /-
  Remark: We must build direct imports before we fetch the transitive
  precompiled imports so that errors in the import block of transitive imports
  will not kill this job before the direct imports are built.
  -/
  let impInfoJob ← mod.importInfo.fetch

  /-
  Remark: It should be possible to avoid transitive imports here when the module
  itself is precompiled, but they are currently kept to preserve the "bad import" errors.
  -/
  let precompileImports ← if mod.shouldPrecompile then
    mod.transImports.fetch else mod.precompileImports.fetch
  let precompileImports ← precompileImports.await
  let impLibsJob ← Job.collectArray (traceCaption := "import dynlibs") <$>
    mod.fetchImportLibs precompileImports mod.shouldPrecompile

  let externLibsJob ← Job.collectArray (traceCaption := "package external libraries") <$>
    if mod.shouldPrecompile then mod.pkg.externLibs.mapM (·.dynlib.fetch) else pure #[]
  let dynlibsJob ← mod.dynlibs.fetchIn mod.pkg "module dynlibs"
  let pluginsJob ← mod.plugins.fetchIn mod.pkg "module plugins"

  headerJob.bindM (sync := true) fun header => do
  extraDepJob.bindM (sync := true) fun _ => do
  impInfoJob.bindM (sync := true) fun info => do
  newTrace
  impLibsJob.bindM (sync := true) fun impLibs => do
  externLibsJob.bindM (sync := true) fun externLibs => do
  dynlibsJob.bindM (sync := true) fun dynlibs => do
  pluginsJob.mapM fun plugins => do
    let libTrace ← takeTrace
    let trace := BuildTrace.nil "deps"
    let depTrace := trace.mix extraDepJob.getTrace |>.mix info.trace
    setTraceCaption s!"{mod.name.toString}:deps"
    let libTrace := libTrace.withCaption "libs"
    match mod.platformIndependent with
    | none => addTrace depTrace; addTrace libTrace
    | some false => addTrace depTrace; addTrace libTrace; addPlatformTrace
    | some true => addTrace depTrace
    let {dynlibs, plugins} ← computeModuleDeps impLibs externLibs dynlibs plugins
    return {
      name := mod.name
      isModule := header.isModule
      imports? := none
      importArts := info.directArts
      dynlibs := dynlibs.map (·.path)
      plugins := plugins.map (·.path)
      options := mod.leanOptions
    }

/-- The `ModuleFacetConfig` for the builtin `setupFacet`. -/
def Module.setupFacetConfig : ModuleFacetConfig setupFacet :=
  mkFacetJobConfig recFetchSetup

/-- The `ModuleFacetConfig` for the builtin `depsFacet`. -/
def Module.depsFacetConfig : ModuleFacetConfig depsFacet :=
  mkFacetJobConfig fun mod => (·.toOpaque) <$> mod.setup.fetch

/-- Remove any cached file hashes of the module build outputs (in `.hash` files). -/
def Module.clearOutputHashes (mod : Module) : IO PUnit := do
  clearFileHash mod.oleanFile
  clearFileHash mod.oleanServerFile
  clearFileHash mod.oleanPrivateFile
  clearFileHash mod.ileanFile
  clearFileHash mod.irFile
  clearFileHash mod.cFile
  clearFileHash mod.bcFile

/-- Cache the file hashes of the module build outputs in `.hash` files. -/
def Module.cacheOutputHashes (mod : Module) : IO PUnit := do
  cacheFileHash mod.oleanFile
  if (← mod.oleanServerFile.pathExists) then
    cacheFileHash mod.oleanServerFile
  if (← mod.oleanPrivateFile.pathExists)  then
    cacheFileHash mod.oleanPrivateFile
  cacheFileHash mod.ileanFile
  if (← mod.irFile.pathExists)  then
    cacheFileHash mod.irFile
  cacheFileHash mod.cFile
  if Lean.Internal.hasLLVMBackend () then
    cacheFileHash mod.bcFile

private def ModuleOutputHashes.getArtifactsFrom?
  (cache : Cache) (hashes : ModuleOutputHashes)
: BaseIO (Option ModuleOutputArtifacts) := OptionT.run do
  let mut arts : ModuleOutputArtifacts := {
    olean := ← cache.getArtifact? hashes.olean "olean"
    ilean := ← cache.getArtifact? hashes.ilean "ilean"
    c :=← cache.getArtifact? hashes.c "c"
  }
  if let some hash := hashes.oleanServer? then
    arts := {arts with oleanServer? := some (← cache.getArtifact? hash "olean.server")}
  if let some hash := hashes.oleanPrivate? then
    arts := {arts with oleanPrivate? := some (← cache.getArtifact? hash "olean.private")}
  if let some hash := hashes.ir? then
    arts := {arts with ir? := some (← cache.getArtifact? hash "ir")}
  if Lean.Internal.hasLLVMBackend () then
    arts := {arts with bc? := some (← cache.getArtifact? (← hashes.bc?) "bc")}
  return arts

@[inline] def ModuleOutputHashes.getArtifacts?
  [MonadLakeEnv m] [MonadLiftT BaseIO m] [Monad m] (hashes : ModuleOutputHashes)
: m (Option ModuleOutputArtifacts) := do hashes.getArtifactsFrom? (← getLakeCache)

instance
  [MonadLakeEnv m] [MonadLiftT BaseIO m] [Monad m]
: ResolveArtifacts m ModuleOutputHashes ModuleOutputArtifacts := ⟨ ModuleOutputHashes.getArtifacts?⟩

/-- Save module build artifacts to the local Lake cache. Requires the artifact cache to be enabled. -/
private def Module.cacheOutputArtifacts (mod : Module) : JobM ModuleOutputArtifacts := do
  return {
    olean := ← cacheArtifact mod.oleanFile "olean"
    oleanServer? := ← cacheIfExists? mod.oleanServerFile "olean.server"
    oleanPrivate? := ← cacheIfExists? mod.oleanPrivateFile "olean.private"
    ir? := ← cacheIfExists? mod.irFile "ir"
    ilean := ← cacheArtifact mod.ileanFile "ilean"
    c := ← cacheArtifact mod.cFile "c"
    bc? := ← cacheIf? (Lean.Internal.hasLLVMBackend ()) mod.bcFile "bc"
  }
where
  @[inline] cacheIf? c art ext := do
    if c then return some (← cacheArtifact art ext) else return none
  @[inline] cacheIfExists? art ext := do
    cacheIf? (← art.pathExists) art ext

/--
Some module build artifacts must be located in the build directory (e.g., ILeans).
This copies the required artifacts from the local Lake cache to the build directory and
updates the data structure with the new paths.
-/
private def Module.restoreArtifacts (mod : Module) (cached : ModuleOutputArtifacts) : JobM ModuleOutputArtifacts := do
  return {cached with
    ilean := ← restore mod.ileanFile cached.ilean
  }
where
  restore file art := do
    unless (← file.pathExists) do
      logVerbose s!"restored artifact from cache to: {file}"
      copyFile art.path file
      writeFileHash file art.hash
    return art.useLocalFile file

private def Module.mkArtifacts (mod : Module) (srcFile : FilePath) (isModule : Bool) : ModuleArtifacts where
  lean? := srcFile
  olean? := mod.oleanFile
  oleanServer? := if isModule then some mod.oleanServerFile else none
  oleanPrivate? := if isModule then some mod.oleanPrivateFile else none
  ilean? := mod.ileanFile
  ir? := if isModule then some mod.irFile else none
  c? := mod.cFile
  bc? := if Lean.Internal.hasLLVMBackend () then some mod.bcFile else none

private def Module.computeOutputHashes (mod : Module) (isModule : Bool) : FetchM ModuleOutputHashes :=
  return {
    olean := ← computeFileHash mod.oleanFile
    oleanServer? := ← if isModule then some <$> computeFileHash mod.oleanServerFile else pure none
    oleanPrivate? := ← if isModule then some <$> computeFileHash mod.oleanPrivateFile else pure none
    ilean := ← computeFileHash mod.ileanFile
    ir? := ← if isModule then some <$> computeFileHash mod.irFile else pure none
    c := ← computeFileHash mod.cFile
    bc? := ← if Lean.Internal.hasLLVMBackend () then some <$> computeFileHash mod.bcFile else pure none
  }

private def Module.fetchLocalArtifacts (mod : Module) (isModule : Bool) : FetchM ModuleOutputArtifacts :=
  return {
    olean := ← fetchLocalArtifact mod.oleanFile
    oleanServer? := ← if isModule then some <$> fetchLocalArtifact mod.oleanServerFile else pure none
    oleanPrivate? := ← if isModule then some <$> fetchLocalArtifact mod.oleanPrivateFile else pure none
    ilean := ← fetchLocalArtifact mod.ileanFile
    ir? := ← if isModule then some <$> fetchLocalArtifact mod.irFile else pure none
    c := ← fetchLocalArtifact mod.cFile
    bc? := ← if Lean.Internal.hasLLVMBackend () then some <$> fetchLocalArtifact mod.bcFile else pure none
  }

private def Module.buildLean
  (mod : Module) (depTrace : BuildTrace) (srcFile : FilePath) (setup : ModuleSetup)
: JobM ModuleOutputHashes := buildAction depTrace mod.traceFile do
  let args := mod.weakLeanArgs ++ mod.leanArgs
  let relSrcFile := relPathFrom mod.pkg.dir srcFile
  let directImports := (← (← mod.input.fetch).await).imports
  let transImpArts ← fetchTransImportArts directImports setup.importArts !setup.isModule
  let setup := {setup with importArts := transImpArts}
  let arts := mod.mkArtifacts srcFile setup.isModule
  compileLeanModule srcFile relSrcFile setup mod.setupFile arts args
    (← getLeanPath) (← getLean)
  mod.clearOutputHashes
  mod.computeOutputHashes setup.isModule

private def traceOptions (opts : LeanOptions) (caption := "opts") : BuildTrace :=
  opts.values.foldl (init := .nil caption) fun t n v =>
    let opt := s!"-D{n}={v.asCliFlagValue}"
    t.mix <| .ofHash (pureHash opt) opt

/--
Recursively build a Lean module.
Fetch its dependencies and then elaborate the Lean source file, producing
all possible artifacts (e.g., `.olean`, `.ilean`, `.c`, `.bc`).
-/
def Module.recBuildLean (mod : Module) : FetchM (Job ModuleOutputArtifacts) := do
  /-
  Remark: `withRegisterJob` must register `setupJob` to display module builds
  in the job monitor. However, it must also include the fetching of both jobs to
  ensure all logs end up under its caption in the job monitor.
  -/
  withRegisterJob mod.name.toString do
  let setupJob ← mod.setup.fetch
  let leanJob ← mod.lean.fetch
  setupJob.mapM fun setup => do
    addLeanTrace
    let srcFile ← leanJob.await
    let srcTrace := leanJob.getTrace
    addTrace srcTrace
    addTrace <| traceOptions setup.options "options"
    addPureTrace mod.leanArgs "Module.leanArgs"
    setTraceCaption s!"{mod.name.toString}:leanArts"
    let depTrace ← getTrace
    let inputHash := depTrace.hash
    let savedTrace ← readTraceFile mod.traceFile
    if let some ref := mod.pkg.cacheRef? then
      if let some arts ← resolveArtifactsUsing? ModuleOutputHashes inputHash mod.traceFile savedTrace ref then
        return ← mod.restoreArtifacts arts
    let upToDate ← savedTrace.replayIfUpToDate (oldTrace := srcTrace.mtime) mod depTrace
    unless upToDate do
      discard <| mod.buildLean depTrace srcFile setup
    if let some ref := mod.pkg.cacheRef? then
      let arts ← mod.cacheOutputArtifacts
      ref.insert inputHash arts.hashes
      return arts
    else
      mod.fetchLocalArtifacts setup.isModule

/-- The `ModuleFacetConfig` for the builtin `leanArtsFacet`. -/
def Module.leanArtsFacetConfig : ModuleFacetConfig leanArtsFacet :=
  mkFacetJobConfig recBuildLean

@[inline] private def Module.fetchOLeanCore
  (facet : String) (f : ModuleOutputArtifacts → Option Artifact) (errMsg : String) (mod : Module)
: FetchM (Job FilePath) := do
  (← mod.leanArts.fetch).mapM (sync := true) fun arts => do
      let some art := f arts
        | error errMsg
      /-
      Avoid recompiling unchanged OLean files.
      OLean files transitively include their imports.
      THowever, imports are pre-resolved by Lake, so they are not included in their trace.
      -/
      newTrace s!"{mod.name.toString}:{facet}"
      addTrace art.trace
      return art.path

/-- The `ModuleFacetConfig` for the builtin `oleanFacet`. -/
def Module.oleanFacetConfig : ModuleFacetConfig oleanFacet :=
  mkFacetJobConfig <| fetchOLeanCore "olean" (·.olean)
    "No olean generated. This is likely an error in Lean or Lake."

/-- The `ModuleFacetConfig` for the builtin `oleanServerFacet`. -/
def Module.oleanServerFacetConfig : ModuleFacetConfig oleanServerFacet :=
  mkFacetJobConfig <| fetchOLeanCore "olean.server" (·.oleanServer?) noServerOLeanError

/-- The `ModuleFacetConfig` for the builtin `oleanPrivateFacet`. -/
def Module.oleanPrivateFacetConfig : ModuleFacetConfig oleanPrivateFacet :=
  mkFacetJobConfig <| fetchOLeanCore "olean.private" (·.oleanPrivate?) noPrivateOLeanError

/-- The `ModuleFacetConfig` for the builtin `ileanFacet`. -/
def Module.ileanFacetConfig : ModuleFacetConfig ileanFacet :=
  mkFacetJobConfig fun mod => do
    (← mod.leanArts.fetch).mapM (sync := true) fun arts => do
      let art := arts.ilean
      /-
      Avoid recompiling unchanged Ilean files.
      Ilean files are assumed to only incorporate their own content
      and not transitively include their inputs (e.g., imports).
      Lean also produces LF-only Ilean files, so no line ending normalization.
      -/
      newTrace s!"{mod.name.toString}:ilean"
      addTrace art.trace
      return art.path

/-- The `ModuleFacetConfig` for the builtin `irFacet`. -/
def Module.irFacetConfig : ModuleFacetConfig irFacet :=
  mkFacetJobConfig <| fetchOLeanCore "ir" (·.ir?) noIRError

/-- The `ModuleFacetConfig` for the builtin `cFacet`. -/
def Module.cFacetConfig : ModuleFacetConfig cFacet :=
  mkFacetJobConfig fun mod => do
    (← mod.leanArts.fetch).mapM (sync := true) fun arts => do
      let art := arts.c
      /-
      Avoid recompiling unchanged C files.
      C files are assumed to incorporate their own content
      and not transitively include their inputs (e.g., imports).
      They do, however, include `lean/lean.h`.
      Lean also produces LF-only C files, so no line ending normalization.
      -/
      newTrace s!"{mod.name.toString}:c"
      addTrace art.trace
      addLeanTrace
      return art.path

/-- The `ModuleFacetConfig` for the builtin `bcFacet`. -/
def Module.bcFacetConfig : ModuleFacetConfig bcFacet :=
  mkFacetJobConfig fun mod => do
    (← mod.leanArts.fetch).mapM (sync := true) fun arts => do
      let some art := arts.bc?
        | error "No LLVM bitcode generated. Ensure your Lean version supports the LLVM backend."
      /-
      Avoid recompiling unchanged bitcode files.
      Bitcode files are assumed to only depend on their content
      and not transitively on their inputs (e.g., imports).
      -/
      newTrace s!"{mod.name.toString}:bc"
      addTrace art.trace
      return art.path

/--
Recursively build the module's object file from its C file produced by `lean`
with `-DLEAN_EXPORTING` set, which exports Lean symbols defined within the C files.
-/
def Module.recBuildLeanCToOExport (self : Module) : FetchM (Job FilePath) := do
  let suffix := if (← getIsVerbose) then " (with exports)" else ""
  withRegisterJob s!"{self.name}:c.o{suffix}" <| withCurrPackage self.pkg do
  -- TODO: add option to pass a target triplet for cross compilation
  let leancArgs := self.leancArgs ++ #["-DLEAN_EXPORTING"]
  buildLeanO self.coExportFile (← self.c.fetch) self.weakLeancArgs leancArgs self.leanIncludeDir?

/-- The `ModuleFacetConfig` for the builtin `coExportFacet`. -/
def Module.coExportFacetConfig : ModuleFacetConfig coExportFacet :=
  mkFacetJobConfig Module.recBuildLeanCToOExport

/--
Recursively build the module's object file from its C file produced by `lean`.
This version does not export any Lean symbols.
-/
def Module.recBuildLeanCToONoExport (self : Module) : FetchM (Job FilePath) := do
  let suffix := if (← getIsVerbose) then " (without exports)" else ""
  withRegisterJob s!"{self.name}:c.o{suffix}" <| withCurrPackage self.pkg do
  -- TODO: add option to pass a target triplet for cross compilation
  buildLeanO self.coNoExportFile (← self.c.fetch) self.weakLeancArgs self.leancArgs self.leanIncludeDir?

/-- The `ModuleFacetConfig` for the builtin `coNoExportFacet`. -/
def Module.coNoExportFacetConfig : ModuleFacetConfig coNoExportFacet :=
  mkFacetJobConfig recBuildLeanCToONoExport

/-- The `ModuleFacetConfig` for the builtin `coFacet`. -/
def Module.coFacetConfig : ModuleFacetConfig coFacet :=
  mkFacetJobConfig (memoize := false) fun mod =>
    if Platform.isWindows then mod.coNoExport.fetch else mod.coExport.fetch

/-- Recursively build the module's object file from its bitcode file produced by `lean`. -/
def Module.recBuildLeanBcToO (self : Module) : FetchM (Job FilePath) := do
  withRegisterJob s!"{self.name}:bc.o" <| withCurrPackage self.pkg do
  -- TODO: add option to pass a target triplet for cross compilation
  buildLeanO self.bcoFile (← self.bc.fetch) self.weakLeancArgs self.leancArgs

/-- The `ModuleFacetConfig` for the builtin `bcoFacet`. -/
def Module.bcoFacetConfig : ModuleFacetConfig bcoFacet :=
  mkFacetJobConfig recBuildLeanBcToO

/-- The `ModuleFacetConfig` for the builtin `oExportFacet`. -/
def Module.oExportFacetConfig : ModuleFacetConfig oExportFacet :=
  mkFacetJobConfig (memoize := false) fun mod =>
    match mod.backend with
    | .default | .c => mod.coExport.fetch
    | .llvm => mod.bco.fetch

/-- The `ModuleFacetConfig` for the builtin `oNoExportFacet`. -/
def Module.oNoExportFacetConfig : ModuleFacetConfig oNoExportFacet :=
  mkFacetJobConfig (memoize := false) fun mod =>
    match mod.backend with
    | .default | .c => mod.coNoExport.fetch
    | .llvm => error "the LLVM backend only supports exporting Lean symbols"

/-- The `ModuleFacetConfig` for the builtin `oFacet`. -/
def Module.oFacetConfig : ModuleFacetConfig oFacet :=
  mkFacetJobConfig (memoize := false) fun mod =>
    match mod.backend with
    | .default | .c => mod.co.fetch
    | .llvm => mod.bco.fetch

/--
Recursively build the shared library of a module
(e.g., for `--load-dynlib` or `--plugin`).
-/
def Module.recBuildDynlib (mod : Module) : FetchM (Job Dynlib) :=
  withRegisterJob s!"{mod.name}:dynlib" <| withCurrPackage mod.pkg do
  /-
  Fetch the module's object files.

  NOTE: The `moreLinkObjs` of the module's library are not included
  here because they would then be linked to the dynlib of each module of the library.
  On Windows, were module dynlibs must be linked with those of their imports, this would
  result in duplicate symbols when one library module imports another of the same library.
  -/
  let objJobs ← (mod.nativeFacets true).mapM (·.fetch mod)
  -- Fetch dependencies' dynlibs
  let libJobs ← id do
    let imps ← (← mod.imports.fetch).await
    let libJobs ← mod.fetchImportLibs imps true
    let libJobs ← mod.lib.moreLinkLibs.foldlM
      (·.push <$> ·.fetchIn mod.pkg) libJobs
    let libJobs ← mod.pkg.externLibs.foldlM
      (·.push <$> ·.dynlib.fetch) libJobs
    return libJobs
  buildLeanSharedLib mod.dynlibName mod.dynlibFile objJobs libJobs
    mod.weakLinkArgs mod.linkArgs (plugin := true)

/-- The `ModuleFacetConfig` for the builtin `dynlibFacet`. -/
def Module.dynlibFacetConfig : ModuleFacetConfig dynlibFacet :=
  mkFacetJobConfig recBuildDynlib

/--
A name-configuration map for the initial set of
Lake module facets (e.g., `imports`, `c`, `o`, `dynlib`).
-/
def Module.initFacetConfigs : DNameMap ModuleFacetConfig :=
  DNameMap.empty
  |>.insert inputFacet inputFacetConfig
  |>.insert leanFacet leanFacetConfig
  |>.insert headerFacet headerFacetConfig
  |>.insert importsFacet importsFacetConfig
  |>.insert transImportsFacet transImportsFacetConfig
  |>.insert precompileImportsFacet precompileImportsFacetConfig
  |>.insert importInfoFacet importInfoFacetConfig
  |>.insert setupFacet setupFacetConfig
  |>.insert depsFacet depsFacetConfig
  |>.insert leanArtsFacet leanArtsFacetConfig
  |>.insert importArtsFacet importArtsFacetConfig
  |>.insert importAllArtsFacet importAllArtsFacetConfig
  |>.insert exportInfoFacet exportInfoFacetConfig
  |>.insert oleanFacet oleanFacetConfig
  |>.insert oleanServerFacet oleanServerFacetConfig
  |>.insert oleanPrivateFacet oleanPrivateFacetConfig
  |>.insert ileanFacet ileanFacetConfig
  |>.insert irFacet irFacetConfig
  |>.insert cFacet cFacetConfig
  |>.insert bcFacet bcFacetConfig
  |>.insert coFacet coFacetConfig
  |>.insert coExportFacet coExportFacetConfig
  |>.insert coNoExportFacet coNoExportFacetConfig
  |>.insert bcoFacet bcoFacetConfig
  |>.insert oFacet oFacetConfig
  |>.insert oExportFacet oExportFacetConfig
  |>.insert oNoExportFacet oNoExportFacetConfig
  |>.insert dynlibFacet dynlibFacetConfig

@[inherit_doc Module.initFacetConfigs]
abbrev initModuleFacetConfigs := Module.initFacetConfigs

/-!
Definitions to support `lake setup-file` builds.
-/

/--
Computes the module setup of Lean code external to the workspace,
building its imports and other dependencies.

This is used by `lake setup-file` to configure modules for the Lean server and by `lake lean`
to build the dependencies of the file and generate the data for `lean --setup`.

Due to its exclusive use as a top-level build, it does not construct a proper trace state.
-/
def setupExternalModule
  (fileName : String) (header : ModuleHeader) (leanOpts : LeanOptions)
: FetchM (Job ModuleSetup) := do
  withRegisterJob s!"setup ({fileName})" do
  let root ← getRootPackage
  let extraDepJob ← root.extraDep.fetch
  let imports ← header.imports.mapM fun imp => do
    return ⟨imp, ← findModule? imp.module⟩
  let localImports := imports.filterMap (·.module?)
  let impInfoJob ← fetchImportInfo fileName .anonymous header
  let precompileImports ← (← computePrecompileImportsAux fileName localImports).await
  let impLibsJob ← fetchImportLibs precompileImports
  let externLibsJob ← Job.collectArray <$>
    if root.precompileModules then root.externLibs.mapM (·.dynlib.fetch) else pure #[]
  let dynlibsJob ← root.dynlibs.fetchIn root
  let pluginsJob ← root.plugins.fetchIn root
  extraDepJob.bindM (sync := true) fun _ =>
  impInfoJob.bindM (sync := true) fun info =>
  impLibsJob.bindM (sync := true) fun impLibs =>
  dynlibsJob.bindM (sync := true) fun dynlibs =>
  pluginsJob.bindM (sync := true) fun plugins =>
  externLibsJob.mapM fun externLibs => do
    let {dynlibs, plugins} ← computeModuleDeps impLibs externLibs dynlibs plugins
    let transImpArts ← fetchTransImportArts imports info.directArts !header.isModule
    return {
      name := `_unknown
      isModule := header.isModule
      imports? := none
      importArts := transImpArts
      dynlibs := dynlibs.map (·.path)
      plugins := plugins.map (·.path)
      options := leanOpts
    }
