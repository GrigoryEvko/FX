import Lean
import FX1PolyAudit.AuditAll

/-! # FX1PolyAudit/DependencySpine — the layer DAG as a build-failing checked artifact

The dependency spine (frontiers.md §16 rail 9):

    Init  ⟶  ComputerAlgebra/  ⟶  Polygraph/  ⟶  Axis/  ⟶  Core/  ⟶  Typed/

Later layers may import earlier ones, never the reverse.  Until 2026-07-02 this was enforced
socially; the POLYGRAPH-5 carve-out exposed a silent transitive-import reliance and POLYGRAPH-14..17
fixed eleven accumulated back-edges — so the spine is now a CHECKED artifact, like the zero-axiom
policy (`#assert_no_axioms`) and the deletion tripwire (`AuditAll`).

`#assert_dependency_spine` walks the `FX1Poly/` source tree at elaboration time, parses each file's
import block (the strict header prefix — `import` lines, blank lines, `--` comments; anything else
ends the block, so docstring examples cannot false-positive), and FAILS THE BUILD on any back-edge.

This module imports `AuditAll`, so it re-elaborates — and the scan re-runs — whenever any registered
kernel file changes.  Known debt is carried in an explicit allowlist that must only ever SHRINK;
allowlisted files are reported as warnings on every build. -/

namespace FX1PolyAudit.DependencySpine

open Lean Elab Command

/-- One layer rule: files under `layerDirectory` may not import modules whose names start with any
of `forbiddenModulePrefixes`.  `allowlistedDebtSuffixes` names known-violating files (path suffixes)
that are pending relocation — reported as warnings, and the list must only shrink. -/
structure SpineRule where
  layerDirectory : String
  forbiddenModulePrefixes : List String
  allowlistedDebtSuffixes : List String

/-- The layer DAG, one rule per layer (a layer may import everything EARLIER, so each rule forbids
exactly the LATER layers). -/
def spineRules : List SpineRule :=
  [ { layerDirectory := "FX1Poly/ComputerAlgebra"
      forbiddenModulePrefixes :=
        ["FX1Poly.Polygraph.", "FX1Poly.Axis.", "FX1Poly.Core.", "FX1Poly.Typed."]
      allowlistedDebtSuffixes := [] },
    { layerDirectory := "FX1Poly/Polygraph"
      forbiddenModulePrefixes := ["FX1Poly.Axis.", "FX1Poly.Core.", "FX1Poly.Typed."]
      allowlistedDebtSuffixes := [] },
    { layerDirectory := "FX1Poly/Axis"
      forbiddenModulePrefixes := ["FX1Poly.Core.", "FX1Poly.Typed."]
      allowlistedDebtSuffixes :=
        [ -- Context-axis instances entangled with Core.Metatheory sconing/reducibility;
          -- relocation pending the Context-wave move-out (they cascade through Instances/Subst/).
          "Axis/Context/Instances/Subst/FxBaseSubstWitnessScone.lean",
          "Axis/Context/Instances/Subst/FxBaseSubstConcreteScone.lean",
          "Axis/Context/Instances/Subst/FxBaseSubstComprehension.lean" ] },
    { layerDirectory := "FX1Poly/Core"
      forbiddenModulePrefixes := ["FX1Poly.Typed."]
      allowlistedDebtSuffixes := [] } ]

/-- Recursively collect every `.lean` file under a directory. -/
partial def collectLeanFilesUnder (directory : System.FilePath) :
    IO (Array System.FilePath) := do
  let mut collectedFiles : Array System.FilePath := #[]
  for entry in (← directory.readDir) do
    if (← entry.path.isDir) then
      collectedFiles := collectedFiles ++ (← collectLeanFilesUnder entry.path)
    else if entry.path.extension == some "lean" then
      collectedFiles := collectedFiles.push entry.path
  return collectedFiles

/-- Extract the import block of a Lean source: the strict header prefix consisting of `import`
lines, blank lines, and `--` line comments.  The first line of any other shape ends the block
(Lean requires imports before all other commands, including module docstrings), so `import`
occurrences inside docstrings or code can never be picked up. -/
def importedModuleNames (sourceText : String) : List String :=
  let rec scanHeader : List String → List String → List String
    | collected, [] => collected.reverse
    | collected, line :: remainingLines =>
        let trimmedLine := line.trimAscii.toString
        if trimmedLine.startsWith "import " then
          scanHeader ((trimmedLine.drop "import ".length).trimAscii.toString :: collected)
            remainingLines
        else if trimmedLine.isEmpty || trimmedLine.startsWith "--" then
          scanHeader collected remainingLines
        else
          collected.reverse
  scanHeader [] (sourceText.splitOn "\n")

/-- Does this path end with the given allowlist suffix (path-separator aware, textual)? -/
def matchesDebtSuffix (filePath : System.FilePath) (debtSuffixes : List String) : Bool :=
  debtSuffixes.any (fun debtSuffix => filePath.toString.endsWith debtSuffix)

/-- **Build-failing spine gate.**  Scans every layer directory against its rule; throws on any
non-allowlisted back-edge, warns on each allowlisted debt file that still violates. -/
elab "#assert_dependency_spine" : command => do
  let repoHasKernelTree ← System.FilePath.pathExists "FX1Poly"
  if !repoHasKernelTree then
    throwError "dependency-spine audit: FX1Poly/ not found under the working directory \
      {(← IO.currentDir)} — the gate must run from the package root"
  let mut violationReports : Array String := #[]
  let mut debtReports : Array String := #[]
  let mut scannedFileCount : Nat := 0
  for rule in spineRules do
    let layerPath : System.FilePath := rule.layerDirectory
    if (← layerPath.pathExists) then
      for sourceFile in (← collectLeanFilesUnder layerPath) do
        scannedFileCount := scannedFileCount + 1
        let sourceText ← IO.FS.readFile sourceFile
        for importedModule in importedModuleNames sourceText do
          if rule.forbiddenModulePrefixes.any (fun forbidden =>
              importedModule.startsWith forbidden) then
            let report := s!"{sourceFile} imports {importedModule}"
            if matchesDebtSuffix sourceFile rule.allowlistedDebtSuffixes then
              debtReports := debtReports.push report
            else
              violationReports := violationReports.push report
  for debtReport in debtReports do
    logWarning m!"dependency-spine DEBT (allowlisted, must shrink): {debtReport}"
  if violationReports.isEmpty then
    logInfo m!"dependency spine ok: {scannedFileCount} files scanned, \
      {debtReports.size} allowlisted debt edge(s) remaining"
  else
    throwError "dependency-spine audit FAILED — back-edge(s) against the layer DAG \
      (Init ⟶ ComputerAlgebra ⟶ Polygraph ⟶ Axis ⟶ Core ⟶ Typed):\n  \
      {String.intercalate "\n  " violationReports.toList}"

#assert_dependency_spine

end FX1PolyAudit.DependencySpine
