import LeanFX2.Tools.StrictHarness.Common.ImportSurface.Predicates

namespace LeanFX2.Tools

open Lean Elab Command

/-- Exact direct imports allowed for the current FX1/Core root DAG.

The broader `#assert_fx1_import_surface_clean` gate proves FX1 stays inside
the FX1 cone, apart from the single host-prelude edge.  This gate is stricter:
it pins the current minimal lambda-Pi root to the intended dependency DAG so a
leaf module cannot silently import the `Core` umbrella or a later metatheory
module.  When `Check` and `Soundness` land, this table must grow in the same
commit that adds those files. -/
def isAllowedFX1CoreExactDirectImport
    (sourceModuleName importedModuleName : Name) :
    Bool :=
  if sourceModuleName == `LeanFX2.FX1 then
    importedModuleName == `LeanFX2.FX1.Core ||
      importedModuleName == `LeanFX2.FX1.LeanKernel
  else if sourceModuleName == `LeanFX2.FX1.Core then
    importedModuleName == `LeanFX2.FX1.Core.Primitive ||
      importedModuleName == `LeanFX2.FX1.Core.Name ||
      importedModuleName == `LeanFX2.FX1.Core.Level ||
      importedModuleName == `LeanFX2.FX1.Core.Expr ||
      importedModuleName == `LeanFX2.FX1.Core.Declaration ||
      importedModuleName == `LeanFX2.FX1.Core.Environment ||
      importedModuleName == `LeanFX2.FX1.Core.Context ||
      importedModuleName == `LeanFX2.FX1.Core.Substitution ||
      importedModuleName == `LeanFX2.FX1.Core.Reduction ||
      importedModuleName == `LeanFX2.FX1.Core.HasType ||
      importedModuleName == `LeanFX2.FX1.Core.WellFormed ||
      importedModuleName == `LeanFX2.FX1.Core.Check ||
      importedModuleName == `LeanFX2.FX1.Core.Soundness
  else if sourceModuleName == `LeanFX2.FX1.Core.Primitive then
    importedModuleName == `Init.Prelude
  else if sourceModuleName == `LeanFX2.FX1.Core.Name then
    importedModuleName == `LeanFX2.FX1.Core.Primitive
  else if sourceModuleName == `LeanFX2.FX1.Core.Level then
    importedModuleName == `LeanFX2.FX1.Core.Name
  else if sourceModuleName == `LeanFX2.FX1.Core.Expr then
    importedModuleName == `LeanFX2.FX1.Core.Level
  else if sourceModuleName == `LeanFX2.FX1.Core.Declaration then
    importedModuleName == `LeanFX2.FX1.Core.Expr
  else if sourceModuleName == `LeanFX2.FX1.Core.Environment then
    importedModuleName == `LeanFX2.FX1.Core.Declaration
  else if sourceModuleName == `LeanFX2.FX1.Core.Context then
    importedModuleName == `LeanFX2.FX1.Core.Expr
  else if sourceModuleName == `LeanFX2.FX1.Core.Substitution then
    importedModuleName == `LeanFX2.FX1.Core.Expr
  else if sourceModuleName == `LeanFX2.FX1.Core.Reduction then
    importedModuleName == `LeanFX2.FX1.Core.Environment ||
      importedModuleName == `LeanFX2.FX1.Core.Substitution
  else if sourceModuleName == `LeanFX2.FX1.Core.HasType then
    importedModuleName == `LeanFX2.FX1.Core.Context ||
      importedModuleName == `LeanFX2.FX1.Core.Reduction
  else if sourceModuleName == `LeanFX2.FX1.Core.WellFormed then
    importedModuleName == `LeanFX2.FX1.Core.HasType
  else if sourceModuleName == `LeanFX2.FX1.Core.Check then
    importedModuleName == `LeanFX2.FX1.Core.Check.CheckEntry
  else if sourceModuleName == `LeanFX2.FX1.Core.Check.CheckBeq then
    importedModuleName == `LeanFX2.FX1.Core.HasType
  else if sourceModuleName == `LeanFX2.FX1.Core.Check.CheckLookup then
    importedModuleName == `LeanFX2.FX1.Core.Check.CheckBeq
  else if sourceModuleName == `LeanFX2.FX1.Core.Check.CheckReduction then
    importedModuleName == `LeanFX2.FX1.Core.Check.CheckLookup
  else if sourceModuleName == `LeanFX2.FX1.Core.Check.CheckInferCore then
    importedModuleName == `LeanFX2.FX1.Core.Check.CheckReduction
  else if sourceModuleName == `LeanFX2.FX1.Core.Check.CheckInferApp then
    importedModuleName == `LeanFX2.FX1.Core.Check.CheckInferCore
  else if sourceModuleName == `LeanFX2.FX1.Core.Check.CheckEntry then
    importedModuleName == `LeanFX2.FX1.Core.Check.CheckInferApp
  else if sourceModuleName == `LeanFX2.FX1.Core.Soundness then
    importedModuleName == `LeanFX2.FX1.Core.Check
  else
    false

/-- Direct imports that violate the exact FX1/Core root DAG. -/
def fx1CoreExactImportViolationsForModule
    (sourceModuleName : Name) (moduleData : ModuleData) :
    Array Name :=
  moduleData.imports.foldl
    (init := (#[] : Array Name))
    (fun violations directImport =>
      if isAllowedFX1CoreExactDirectImport sourceModuleName directImport.module then
        violations
      else
        violations.push directImport.module)

/-- Build-failing gate for the exact FX1/Core root import DAG.

This checks only the current minimal root umbrella and `FX1/Core` modules.  It
does not police `FX1/LeanKernel` files; those are checked by
`#assert_fx1_lean_kernel_exact_import_shape`. -/
elab "#assert_fx1_core_exact_import_shape" : command => do
  let environment ← getEnv
  let moduleEntries :=
    Array.zip environment.header.modules environment.header.moduleData
  let mut scannedRootModules : Nat := 0
  let mut violations : Array (Name × Array Name) := #[]
  for (effectiveImport, moduleData) in moduleEntries do
    let sourceModuleName := effectiveImport.module
    if sourceModuleName == `LeanFX2.FX1 ||
        sourceModuleName == `LeanFX2.FX1.Core ||
        isFX1CoreModuleName sourceModuleName then
      scannedRootModules := scannedRootModules + 1
      let forbiddenImports :=
        fx1CoreExactImportViolationsForModule sourceModuleName moduleData
      if !forbiddenImports.isEmpty then
        violations := violations.push (sourceModuleName, forbiddenImports)
  if violations.isEmpty then
    logInfo m!"FX1/Core exact import shape ok: {scannedRootModules} modules"
  else
    let perModuleLines := violations.toList.map fun (moduleName, forbiddenImports) =>
      let renderedImports :=
        String.intercalate ", " (forbiddenImports.toList.map toString)
      s!"  - {moduleName}: unexpected direct imports [{renderedImports}]"
    let header :=
      s!"FX1/Core exact import shape FAILED: " ++
      s!"{violations.size} of {scannedRootModules} root modules violate the DAG"
    throwError (header ++ "\n" ++ String.intercalate "\n" perModuleLines)

/-! ## FX1/LeanKernel exact import discipline -/

/-- Exact direct imports allowed for the current FX1/LeanKernel DAG.

The Lean-kernel model is allowed to depend on FX1/Core through the broader FX1
source-import gate, but the current migrated scaffold does not need that edge
yet.  Keeping this table exact makes the first future dependency on FX1/Core
an explicit policy change in the same commit as the checker theorem work. -/
def isAllowedFX1LeanKernelExactDirectImport
    (sourceModuleName importedModuleName : Name) :
    Bool :=
  if sourceModuleName == `LeanFX2.FX1.LeanKernel then
    importedModuleName == `LeanFX2.FX1.LeanKernel.Inductive ||
      importedModuleName == `LeanFX2.FX1.LeanKernel.HasType ||
      importedModuleName == `LeanFX2.FX1.LeanKernel.Check ||
      importedModuleName == `LeanFX2.FX1.LeanKernel.Soundness ||
      importedModuleName == `LeanFX2.FX1.LeanKernel.Audit
  else if sourceModuleName == `LeanFX2.FX1.LeanKernel.Name then
    importedModuleName == `LeanFX2.FX1.Core.Primitive
  else if sourceModuleName == `LeanFX2.FX1.LeanKernel.Level then
    importedModuleName == `LeanFX2.FX1.LeanKernel.Name
  else if sourceModuleName == `LeanFX2.FX1.LeanKernel.Expr then
    importedModuleName == `LeanFX2.FX1.LeanKernel.Level
  else if sourceModuleName == `LeanFX2.FX1.LeanKernel.Substitution then
    importedModuleName == `LeanFX2.FX1.LeanKernel.Expr
  else if sourceModuleName == `LeanFX2.FX1.LeanKernel.Reduction then
    importedModuleName == `LeanFX2.FX1.LeanKernel.Substitution
  else if sourceModuleName == `LeanFX2.FX1.LeanKernel.Inductive then
    importedModuleName == `LeanFX2.FX1.LeanKernel.Reduction
  else if sourceModuleName == `LeanFX2.FX1.LeanKernel.HasType then
    importedModuleName == `LeanFX2.FX1.LeanKernel.Inductive
  else if sourceModuleName == `LeanFX2.FX1.LeanKernel.Check then
    importedModuleName == `LeanFX2.FX1.LeanKernel.HasType
  else if sourceModuleName == `LeanFX2.FX1.LeanKernel.Soundness then
    importedModuleName == `LeanFX2.FX1.LeanKernel.Check
  else if sourceModuleName == `LeanFX2.FX1.LeanKernel.Audit then
    importedModuleName == `LeanFX2.FX1.LeanKernel.Soundness
  else
    false

/-- Direct imports that violate the exact FX1/LeanKernel DAG. -/
def fx1LeanKernelExactImportViolationsForModule
    (sourceModuleName : Name) (moduleData : ModuleData) :
    Array Name :=
  moduleData.imports.foldl
    (init := (#[] : Array Name))
    (fun violations directImport =>
      if isAllowedFX1LeanKernelExactDirectImport
          sourceModuleName directImport.module then
        violations
      else
        violations.push directImport.module)

/-- Build-failing gate for the exact FX1/LeanKernel import DAG. -/
elab "#assert_fx1_lean_kernel_exact_import_shape" : command => do
  let environment ← getEnv
  let moduleEntries :=
    Array.zip environment.header.modules environment.header.moduleData
  let mut scannedLeanKernelModules : Nat := 0
  let mut violations : Array (Name × Array Name) := #[]
  for (effectiveImport, moduleData) in moduleEntries do
    let sourceModuleName := effectiveImport.module
    if sourceModuleName == `LeanFX2.FX1.LeanKernel ||
        isFX1LeanKernelModuleName sourceModuleName then
      scannedLeanKernelModules := scannedLeanKernelModules + 1
      let forbiddenImports :=
        fx1LeanKernelExactImportViolationsForModule sourceModuleName moduleData
      if !forbiddenImports.isEmpty then
        violations := violations.push (sourceModuleName, forbiddenImports)
  if violations.isEmpty then
    logInfo
      m!"FX1/LeanKernel exact import shape ok: {scannedLeanKernelModules} modules"
  else
    let perModuleLines := violations.toList.map fun (moduleName, forbiddenImports) =>
      let renderedImports :=
        String.intercalate ", " (forbiddenImports.toList.map toString)
      s!"  - {moduleName}: unexpected direct imports [{renderedImports}]"
    let header :=
      s!"FX1/LeanKernel exact import shape FAILED: " ++
      s!"{violations.size} of {scannedLeanKernelModules} modules violate the DAG"
    throwError (header ++ "\n" ++ String.intercalate "\n" perModuleLines)

/-! ## Legacy Lean-kernel scaffold isolation -/

/-- Modules allowed to import the legacy Lean-kernel scaffold directly. -/
def mayImportLegacyLeanKernelScaffold (sourceModuleName : Name) : Bool :=
  isLegacyLeanKernelScaffoldModuleName sourceModuleName ||
    (`LeanFX2.Tools).isPrefixOf sourceModuleName ||
    (`LeanFX2.Smoke).isPrefixOf sourceModuleName

/-- Legacy Lean-kernel direct imports that cross out of the allowed
audit/scaffold boundary. -/
def forbiddenLegacyLeanKernelImportsForModule
    (sourceModuleName : Name) (moduleData : ModuleData) :
    Array Name :=
  moduleData.imports.foldl
    (init := (#[] : Array Name))
    (fun forbiddenImports directImport =>
      if isLegacyLeanKernelScaffoldModuleName directImport.module &&
          !mayImportLegacyLeanKernelScaffold sourceModuleName then
        forbiddenImports.push directImport.module
      else
        forbiddenImports)

/-- Build-failing isolation gate for old `LeanFX2.Lean.Kernel.*` modules.

This prevents rich production modules and the public `LeanFX2` umbrella from
depending on the old scaffold while Day 8 is retargeted to
`LeanFX2.FX1.LeanKernel`. -/
elab "#assert_legacy_lean_kernel_scaffold_isolated" : command => do
  let environment ← getEnv
  let moduleEntries :=
    Array.zip environment.header.modules environment.header.moduleData
  let mut scannedModules : Nat := 0
  let mut violations : Array (Name × Array Name) := #[]
  for (effectiveImport, moduleData) in moduleEntries do
    let moduleName := effectiveImport.module
    if (`LeanFX2).isPrefixOf moduleName then
      scannedModules := scannedModules + 1
      let forbiddenImports :=
        forbiddenLegacyLeanKernelImportsForModule moduleName moduleData
      if !forbiddenImports.isEmpty then
        violations := violations.push (moduleName, forbiddenImports)
  if violations.isEmpty then
    logInfo m!"legacy LeanKernel scaffold isolated: {scannedModules} modules"
  else
    let perModuleLines := violations.toList.map fun (moduleName, forbiddenImports) =>
      let renderedImports :=
        String.intercalate ", " (forbiddenImports.toList.map toString)
      s!"  - {moduleName}: forbidden legacy LeanKernel imports [{renderedImports}]"
    let header :=
      s!"legacy LeanKernel scaffold isolation FAILED: " ++
      s!"{violations.size} of {scannedModules} modules import the old scaffold"
    throwError (header ++ "\n" ++ String.intercalate "\n" perModuleLines)

/-- Direct project imports from one legacy Lean-kernel scaffold module that
escape the legacy scaffold namespace.  Non-project imports are ignored here
because Lean records the ambient `Init` prelude in module data; the global
host-heavy gate already catches broad host imports such as `Lean` or `Std`. -/
def legacyLeanKernelOutwardImportsForModule
    (sourceModuleName : Name) (moduleData : ModuleData) :
    Array Name :=
  if isLegacyLeanKernelScaffoldModuleName sourceModuleName then
    moduleData.imports.foldl
      (init := (#[] : Array Name))
      (fun outwardImports directImport =>
        if (`LeanFX2).isPrefixOf directImport.module &&
            !isLegacyLeanKernelScaffoldModuleName directImport.module then
          outwardImports.push directImport.module
        else
          outwardImports)
  else
    #[]

/-- Build-failing isolation gate for outbound dependencies of the old
`LeanFX2.Lean.Kernel.*` scaffold.

The legacy scaffold may depend on itself while it remains audited, but it must
not grow imports into the production kernel, FX1, tools, smoke tests, or the
public umbrella.  This keeps it quarantined while Day 8 moves toward
`LeanFX2.FX1.LeanKernel`. -/
elab "#assert_legacy_lean_kernel_import_surface_clean" : command => do
  let environment ← getEnv
  let moduleEntries :=
    Array.zip environment.header.modules environment.header.moduleData
  let mut scannedLegacyModules : Nat := 0
  let mut violations : Array (Name × Array Name) := #[]
  for (effectiveImport, moduleData) in moduleEntries do
    let moduleName := effectiveImport.module
    if isLegacyLeanKernelScaffoldModuleName moduleName then
      scannedLegacyModules := scannedLegacyModules + 1
      let outwardImports :=
        legacyLeanKernelOutwardImportsForModule moduleName moduleData
      if !outwardImports.isEmpty then
        violations := violations.push (moduleName, outwardImports)
  if violations.isEmpty then
    logInfo m!"legacy LeanKernel import surface ok: {scannedLegacyModules} modules"
  else
    let perModuleLines := violations.toList.map fun (moduleName, outwardImports) =>
      let renderedImports :=
        String.intercalate ", " (outwardImports.toList.map toString)
      s!"  - {moduleName}: outward imports [{renderedImports}]"
    let header :=
      s!"legacy LeanKernel import surface FAILED: " ++
      s!"{violations.size} of {scannedLegacyModules} legacy modules import outside the scaffold"
    throwError (header ++ "\n" ++ String.intercalate "\n" perModuleLines)

end LeanFX2.Tools
