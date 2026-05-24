import LeanFX2.Tools.StrictHarness.Common.ImportSurface.ExactFX1

/-! # Layering — TODO POLYCELL: BODY DISABLED

Body depends on cd_lemma / Conv.canonical_form / parStar.confluence /
RawStep.parStar orchestration deleted in commit c2efaccf (cascade-fake
bulldoze).  Replacement: FXcdLemma / FXConv view defs per polycell.md §5.
Imports are preserved at top so downstream transitive imports still work.
-/

/- TODO POLYCELL: original body preserved as block comment


namespace LeanFX2.Tools

open Lean Elab Command

/-- Subject-reduction modules live under `Term/` for theorem naming, but
semantically depend on the reduction layer. -/
def isSubjectReductionMetatheoryModuleName (moduleName : Name) : Bool :=
  moduleName == `LeanFX2.Term.SubjectReduction ||
    moduleName == `LeanFX2.Term.SubjectReductionGeneral ||
    moduleName == `LeanFX2.Term.SubjectReductionUniverse

/-- Modules whose physical location is `Term/PreservesTerm/` for
namespace clustering but whose semantic dependency graph is purely
Term-layer (Layer 1).  These are NOT preservation-bridge modules —
they ship pure Term-layer helpers and have no `Reduction.*` imports.

* `Term.PreservesTerm.InlineDestructors` — Term-layer inversion
  helpers consumed both by sibling preservation modules and by
  `Term.StrengtheningImage.TargetImageTotality` (which itself is
  Layer 1). -/
def isPreservesTermLayerOneModuleName (moduleName : Name) : Bool :=
  moduleName == `LeanFX2.Term.PreservesTerm.InlineDestructors

/-- Term-preservation bridge modules live under `Term/PreservesTerm/` for
theorem-naming convenience but transitively depend on `Reduction.ParRed`
and `Reduction.RawParInversion` (Layer 2).

The entire `LeanFX2.Term.PreservesTerm.*` subtree is lifted to Layer 2
EXCEPT the modules explicitly listed in
`isPreservesTermLayerOneModuleName` (which ship pure Term-layer
helpers despite their directory placement).

Every other file in PreservesTerm either (a) directly imports a
`Reduction.ParRed.*` / `Reduction.RawParInversion.*` module, or
(b) imports a sibling that does.  Tracking them individually would
require an ever-growing per-file allowlist whose only function is to
mirror the directory listing, so we collapse to a prefix match.

Role: lift parallel-reduction inversions and constructor-shape
exclusions into typed-Term preservation lemmas — semantically a
Reduction-layer concern, not a Term-layer one. -/
def isPreservesTermBridgeModuleName (moduleName : Name) : Bool :=
  (`LeanFX2.Term.PreservesTerm).isPrefixOf moduleName &&
    !isPreservesTermLayerOneModuleName moduleName

/-- Term-vacuity / exclusion bridges live under `Foundation/` for
namespace-locality with raw infrastructure, but transitively depend on
`LeanFX2.Term` (Layer 1).

Their role is to state and prove vacuity / exclusion lemmas about typed
`Term` constructors that downstream raw-layer dispatchers consume to
discharge inadmissible branches.

Files in this allowlist:

* `Foundation.TermPathLamExcludes` — typed-`Term.pathLam` vacuity used
  by the hcomp dispatcher arm.
* `Foundation.TermTranspPathVacuity` — typed-`Term.transp` path-shape
  vacuity used by the transp dispatcher arm.
* `Foundation.TermUaToEquivExcludesOeqRefl` — typed-`Term.uaToEquiv`
  exclusion used by the uaToEquiv dispatcher arm. -/
def isFoundationTermBridgeModuleName (moduleName : Name) : Bool :=
  moduleName == `LeanFX2.Foundation.TermPathLamExcludes ||
    moduleName == `LeanFX2.Foundation.TermTranspPathVacuity ||
    moduleName == `LeanFX2.Foundation.TermUaToEquivExcludesOeqRefl

/-- Reduction modules that are metatheorems about conversion or canonical
forms, not primitive reduction infrastructure.

Each of these lives under the `Reduction/` namespace for theorem-naming
convenience but semantically depends on the Bridge layer (Layer 3 in
`productionImportLayer?`).

* `Reduction.ConvCanonical` / `Reduction.ConvCongIsClosedTy` —
  conversion-canonical / conversion-congruence statements that consume
  bridge content.
* `Reduction.ParRed.PreEtaInversion` — typed binder-headed inversion
  for `Step.par`; uses `Step.par.toRawBridge` from
  `LeanFX2.Bridge` to project to raw inversions. -/
def isReductionMetatheoryModuleName (moduleName : Name) : Bool :=
  moduleName == `LeanFX2.Reduction.ConvCanonical ||
    moduleName == `LeanFX2.Reduction.ConvCongIsClosedTy ||
    moduleName == `LeanFX2.Reduction.ParRed.PreEtaInversion

/-- Reduction modules that are Confluence-layer metatheorems.

These live under `Reduction/` for theorem-naming convenience but
transitively depend on `Confluence.RawDiamond` and therefore semantically
sit at the Confluence layer (Layer 4 in `productionImportLayer?`).

* `Reduction.RawParWeakenInv.ParStar` — `parStar` chain lift of the
  per-ctor rename-image preservation lemmas; the chain induction
  consumes the diamond-property infrastructure from
  `Confluence.RawDiamond`.

The shim umbrella `Reduction.RawParWeakenInv` intentionally does NOT
re-export this module so the Reduction-layer (Layer 2) gate stays
clean. -/
def isConfluenceParStarModuleName (moduleName : Name) : Bool :=
  moduleName == `LeanFX2.Reduction.RawParWeakenInv.ParStar

/-- Cross-theory bridge modules depend on HoTT, Cubical, or Modal layers and
therefore must not be classified with the low-level typed/raw bridge. -/
def isCrossTheoryBridgeModuleName (moduleName : Name) : Bool :=
  moduleName == `LeanFX2.Cubical.Bridge ||
    moduleName == `LeanFX2.Cubical.Ua ||
    moduleName == `LeanFX2.Bridge.PathToId ||
    moduleName == `LeanFX2.Bridge.IdToPath ||
    moduleName == `LeanFX2.Bridge.PathIdInverse ||
    moduleName == `LeanFX2.Bridge.PathIdMeta ||
    moduleName == `LeanFX2.Bridge.IdEqType ||
    moduleName == `LeanFX2.Bridge.PathEqType ||
    moduleName == `LeanFX2.Bridge.BoxObservational ||
    moduleName == `LeanFX2.Bridge.BoxCubical ||
    moduleName == `LeanFX2.Bridge.BoxObservationalInverse

/-- Semantic import layer for production modules.  The numbering matches the
public `LeanFX2.lean` umbrella comments after refining path names that carry
metatheory (`Term.SubjectReduction*`) or cross-theory bridge content.

`none` means the module is outside this production layering contract and is
checked by a different gate (`FX1`, tooling, smoke, sketches, or legacy
LeanKernel). -/
def productionImportLayer? (moduleName : Name) : Option Nat :=
  if moduleName == `LeanFX2.Kernel then
    some 4
  else if moduleName == `LeanFX2.Rich then
    some 13
  else if isFX1BridgeModuleName moduleName then
    some 14
  else if isSubjectReductionMetatheoryModuleName moduleName then
    some 3
  else if isReductionMetatheoryModuleName moduleName then
    some 3
  else if isConfluenceParStarModuleName moduleName then
    some 4
  else if isCrossTheoryBridgeModuleName moduleName then
    some 13
  else if isPreservesTermBridgeModuleName moduleName then
    some 2
  else if isFoundationTermBridgeModuleName moduleName then
    some 1
  else if (`LeanFX2.Foundation).isPrefixOf moduleName then
    some 0
  else if moduleName == `LeanFX2.Term ||
      (`LeanFX2.Term).isPrefixOf moduleName then
    some 1
  else if (`LeanFX2.Reduction).isPrefixOf moduleName then
    some 2
  else if moduleName == `LeanFX2.Bridge then
    some 3
  else if (`LeanFX2.Confluence).isPrefixOf moduleName then
    some 4
  else if (`LeanFX2.HoTT).isPrefixOf moduleName ||
      (`LeanFX2.Cubical).isPrefixOf moduleName then
    some 5
  else if (`LeanFX2.Modal).isPrefixOf moduleName then
    some 6
  else if (`LeanFX2.Effects).isPrefixOf moduleName ||
      (`LeanFX2.Sessions).isPrefixOf moduleName ||
      (`LeanFX2.Codata).isPrefixOf moduleName then
    some 7
  else if (`LeanFX2.Graded).isPrefixOf moduleName then
    some 8
  else if (`LeanFX2.Refine).isPrefixOf moduleName then
    some 9
  else if (`LeanFX2.Algo).isPrefixOf moduleName then
    some 10
  else if (`LeanFX2.Surface).isPrefixOf moduleName then
    some 11
  else if moduleName == `LeanFX2.Pipeline then
    some 12
  else if (`LeanFX2.Conservativity).isPrefixOf moduleName ||
      (`LeanFX2.Translation).isPrefixOf moduleName ||
      (`LeanFX2.InternalLanguage).isPrefixOf moduleName then
    some 13
  else
    none

/-- Does a direct import point from a lower semantic layer to a higher one? -/
def isLayerImportViolation
    (sourceModuleName importedModuleName : Name) : Bool :=
  match productionImportLayer? sourceModuleName,
      productionImportLayer? importedModuleName with
  | some sourceLayer, some importedLayer => sourceLayer < importedLayer
  | _, _ => false

/-- Direct upward imports for one production module. -/
def layerImportViolationsForModule
    (sourceModuleName : Name) (moduleData : ModuleData) :
    Array Name :=
  moduleData.imports.foldl
    (init := (#[] : Array Name))
    (fun violations directImport =>
      if isLayerImportViolation sourceModuleName directImport.module then
        violations.push directImport.module
      else
        violations)

/-- Build-failing gate for semantic production layering.  This complements
the broad import-surface gates: it does not care whether an import is host or
tooling, but whether a production module imports a later production layer. -/
elab "#assert_production_layer_imports_clean" : command => do
  let environment ← getEnv
  let moduleEntries :=
    Array.zip environment.header.modules environment.header.moduleData
  let mut scannedLayeredModules : Nat := 0
  let mut violations : Array (Name × Array Name) := #[]
  for (effectiveImport, moduleData) in moduleEntries do
    let moduleName := effectiveImport.module
    if moduleName != `LeanFX2 &&
        isProductionLeanFX2ModuleName moduleName &&
        (productionImportLayer? moduleName).isSome then
      scannedLayeredModules := scannedLayeredModules + 1
      let upwardImports := layerImportViolationsForModule moduleName moduleData
      if !upwardImports.isEmpty then
        violations := violations.push (moduleName, upwardImports)
  if violations.isEmpty then
    logInfo m!"production layer imports ok: {scannedLayeredModules} modules"
  else
    let perModuleLines := violations.toList.map fun (moduleName, upwardImports) =>
      let renderedImports :=
        String.intercalate ", " (upwardImports.toList.map toString)
      s!"  - {moduleName}: upward imports [{renderedImports}]"
    let header :=
      s!"production layer imports FAILED: " ++
      s!"{violations.size} of {scannedLayeredModules} modules import later layers"
    throwError (header ++ "\n" ++ String.intercalate "\n" perModuleLines)

/-! ## Redundant direct project-import discipline -/

/-- Convert the loaded module header into the compact lookup shape used by
import-reachability checks. -/
def loadedModuleImportEntries (environment : Environment) :
    Array (Name × ModuleData) :=
  (Array.zip environment.header.modules environment.header.moduleData).map
    (fun (effectiveImport, moduleData) => (effectiveImport.module, moduleData))

/-- Direct imports recorded for one source module in the currently loaded
module graph. -/
def directImportNamesForModuleName
    (moduleEntries : Array (Name × ModuleData))
    (sourceModuleName : Name) :
    List Name :=
  match moduleEntries.find? (fun (entryName, _) => entryName == sourceModuleName) with
  | some (_, moduleData) =>
      moduleData.imports.toList.map (fun directImport => directImport.module)
  | none => []

/-- Fuel-bounded reachability over direct module imports.

The fuel is normally the number of loaded modules plus one.  A visited list
prevents cycles from expanding forever; the fuel keeps the definition plainly
structural and acceptable to the kernel. -/
def isModuleReachableFromFrontierWithFuel
    (moduleEntries : Array (Name × ModuleData))
    (targetModuleName : Name)
    (fuel : Nat)
    (visitedModuleNames : List Name)
    (frontierModuleNames : List Name) :
    Bool :=
  match fuel with
  | 0 => false
  | Nat.succ remainingFuel =>
      match frontierModuleNames with
      | [] => false
      | candidateModuleName :: remainingFrontier =>
          if candidateModuleName == targetModuleName then
            true
          else if visitedModuleNames.contains candidateModuleName then
            isModuleReachableFromFrontierWithFuel
              moduleEntries targetModuleName remainingFuel visitedModuleNames
              remainingFrontier
          else
            let candidateImports :=
              directImportNamesForModuleName moduleEntries candidateModuleName
            isModuleReachableFromFrontierWithFuel
              moduleEntries targetModuleName remainingFuel
              (candidateModuleName :: visitedModuleNames)
              (candidateImports ++ remainingFrontier)

/-- Project-local direct imports from one module.  Host imports are handled by
the host-heavy gates and by FX1's stricter prelude rule. -/
def directProjectImportNamesForModuleData
    (moduleData : ModuleData) :
    Array Name :=
  moduleData.imports.foldl
    (init := (#[] : Array Name))
    (fun projectImports directImport =>
      if (`LeanFX2).isPrefixOf directImport.module then
        projectImports.push directImport.module
      else
        projectImports)

/-- Public entrypoints are intentionally broad and are checked by umbrella
isolation/reachability gates rather than by redundant-edge minimization. -/
def shouldScanRedundantProjectImportsForModule
    (sourceModuleName : Name) :
    Bool :=
  isProductionLeanFX2ModuleName sourceModuleName &&
    !isPublicUmbrellaImportModuleName sourceModuleName

/-- Documented direct imports that are intentionally kept even though the
target is reachable through another loaded project import.

These four edges name semantic dependencies that are core to the source
module's interface, not incidental transitive conveniences.  Keeping the
allowlist small makes future redundancy drift fail fast. -/
def isDocumentedRedundantProjectImport
    (sourceModuleName importedModuleName : Name) :
    Bool :=
  (sourceModuleName == `LeanFX2.Term &&
      importedModuleName == `LeanFX2.Foundation.RawTerm) ||
    (sourceModuleName == `LeanFX2.Term &&
      importedModuleName == `LeanFX2.Foundation.Ty) ||
    (sourceModuleName == `LeanFX2.Graded.Rules &&
      importedModuleName == `LeanFX2.Graded.GradeVector) ||
    (sourceModuleName == `LeanFX2.Graded.Dimensions21 &&
      importedModuleName == `LeanFX2.Graded.Instances.Complexity)

/-- Redundant direct imports for one production module.  A direct import is
redundant when the same project module is reachable through the source's other
direct imports. -/
def redundantProjectImportsForModule
    (moduleEntries : Array (Name × ModuleData))
    (sourceModuleName : Name)
    (moduleData : ModuleData) :
    Array DirectImportRecord :=
  let directProjectImports := directProjectImportNamesForModuleData moduleData
  directProjectImports.foldl
    (init := (#[] : Array DirectImportRecord))
    (fun redundantImports importedModuleName =>
      if isDocumentedRedundantProjectImport sourceModuleName importedModuleName then
        redundantImports
      else
        let otherDirectImports :=
          directProjectImports.toList.filter
            (fun candidateModuleName => candidateModuleName != importedModuleName)
        let isReachableWithoutDirectEdge :=
          isModuleReachableFromFrontierWithFuel moduleEntries importedModuleName
            (moduleEntries.size + 1) [] otherDirectImports
        if isReachableWithoutDirectEdge then
          redundantImports.push {
            sourceModuleName := sourceModuleName
            importedModuleName := importedModuleName
          }
        else
          redundantImports)

/-- Build-failing gate for redundant direct project imports in production
modules.

This turns the repository import-pruning script into a durable invariant:
regular production modules should import the narrow modules they actually use,
but not keep extra direct project edges that are already supplied by another
direct import. -/
elab "#assert_no_redundant_production_project_imports" : command => do
  let environment ← getEnv
  let moduleEntries := loadedModuleImportEntries environment
  let mut scannedProductionModules : Nat := 0
  let mut violations : Array DirectImportRecord := #[]
  for (sourceModuleName, moduleData) in moduleEntries do
    if shouldScanRedundantProjectImportsForModule sourceModuleName then
      scannedProductionModules := scannedProductionModules + 1
      violations :=
        violations ++
          redundantProjectImportsForModule
            moduleEntries sourceModuleName moduleData
  if violations.isEmpty then
    logInfo
      m!"redundant production project imports ok: {scannedProductionModules} modules"
  else
    let renderedImports := formatDirectImportRecords violations
    let header :=
      s!"redundant production project imports FAILED: " ++
      s!"{violations.size} redundant direct project imports"
    throwError (header ++ "\n  " ++ renderedImports)

/-! ## Import-surface summary

The fail-fast gates above catch invalid dependency edges.  This
summary is intentionally informational: it keeps the current import
cone visible in every import-surface smoke run, including the few
allowed host/tooling edges that should remain explicit rather than
hidden in prose.
-/

/-- Does this direct import point from a project module to a host-heavy
module that should stay rare and visible? -/
def isHostHeavyDirectImportModuleName (moduleName : Name) : Bool :=
  (`Lean).isPrefixOf moduleName ||
    (`Lake).isPrefixOf moduleName ||
    (`Std).isPrefixOf moduleName ||
    (`Mathlib).isPrefixOf moduleName ||
    (`Classical).isPrefixOf moduleName ||
    (`Quot).isPrefixOf moduleName

/-- Explicit allowlist for direct host-heavy imports anywhere inside
`LeanFX2.*`.

Only the audit implementation itself may import Lean elaborator APIs.  FX1's
temporary `Init.Prelude` imports are intentionally not host-heavy here: the
FX1-specific source and declaration gates police them separately. -/
def isAllowedHostHeavyDirectImport
    (directImportRecord : DirectImportRecord) :
    Bool :=
  directImportRecord.sourceModuleName == `LeanFX2.Tools.DependencyAudit &&
    directImportRecord.importedModuleName == `Lean

/-! ## Public umbrella reachability -/

/-- Whether a module is one of the public roots that should reach all
production modules.  `LeanFX2` intentionally imports neither FX1 nor the
FX1Bridge layer directly, so the reachability root set has three entries. -/
def isPublicProductionRootModuleName (moduleName : Name) : Bool :=
  moduleName == `LeanFX2 ||
    moduleName == `LeanFX2.FX1 ||
    moduleName == `LeanFX2.FX1Bridge

/-- Is a project module already present in a small name set? -/
def containsModuleName (moduleNames : Array Name) (moduleName : Name) :
    Bool :=
  moduleNames.contains moduleName

/-- Build-failing gate that checks every loaded production module is reachable
from the public production roots `LeanFX2` or `LeanFX2.FX1`.

This is intentionally run from `Smoke.ImportEverywhere`, where Lake has loaded
the whole library glob.  Running it only from `Smoke.ImportSurface` would see
only the already-public cone and could not detect a production module that is
loaded only by a smoke audit. -/
elab "#assert_public_production_umbrella_reaches_all" : command => do
  let environment ← getEnv
  let moduleEntries :=
    Array.zip environment.header.modules environment.header.moduleData
  let mut reachableModuleNames : Array Name :=
    #[`LeanFX2, `LeanFX2.FX1, `LeanFX2.FX1Bridge]
  for _iteration in List.range moduleEntries.size do
    for (effectiveImport, moduleData) in moduleEntries do
      let sourceModuleName := effectiveImport.module
      if containsModuleName reachableModuleNames sourceModuleName then
        for directImport in moduleData.imports do
          let importedModuleName := directImport.module
          if (`LeanFX2).isPrefixOf importedModuleName &&
              !containsModuleName reachableModuleNames importedModuleName then
            reachableModuleNames := reachableModuleNames.push importedModuleName
  let mut missingProductionModules : Array Name := #[]
  let mut scannedProductionModules : Nat := 0
  for (effectiveImport, _moduleData) in moduleEntries do
    let moduleName := effectiveImport.module
    if isProductionLeanFX2ModuleName moduleName then
      scannedProductionModules := scannedProductionModules + 1
      if !containsModuleName reachableModuleNames moduleName then
        missingProductionModules := missingProductionModules.push moduleName
  if missingProductionModules.isEmpty then
    logInfo
      m!"public production umbrella reachability ok: {scannedProductionModules} modules"
  else
    let renderedModules :=
      String.intercalate ", " (missingProductionModules.toList.map toString)
    let header :=
      s!"public production umbrella reachability FAILED: " ++
      s!"{missingProductionModules.size} of {scannedProductionModules} " ++
      "production modules are not reachable from LeanFX2 or LeanFX2.FX1"
    throwError (header ++ "\n  " ++ renderedModules)

end LeanFX2.Tools

-/
