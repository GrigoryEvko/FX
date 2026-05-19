import LeanFX2.Tools.StrictHarness.Common.ImportSurface.Layering

namespace LeanFX2.Tools

open Lean Elab Command

/-- Coarse family label for import-census summaries.  The label is
informational only; policy gates above enforce the actual boundaries. -/
def importFamilyLabel (moduleName : Name) : String :=
  if moduleName == `LeanFX2 then
    "LeanFX2.Root"
  else if moduleName == `LeanFX2.Kernel then
    "LeanFX2.Kernel"
  else if moduleName == `LeanFX2.Rich then
    "LeanFX2.Rich"
  else if isFX1BridgeModuleName moduleName then
    "LeanFX2.FX1Bridge"
  else if (`LeanFX2.FX1).isPrefixOf moduleName then
    "LeanFX2.FX1"
  else if isLegacyLeanKernelScaffoldModuleName moduleName then
    "LeanFX2.LegacyLeanKernel"
  else if isHostBoundaryModuleName moduleName then
    "LeanFX2.HostBoundary"
  else if (`LeanFX2.Tools).isPrefixOf moduleName then
    "LeanFX2.Tools"
  else if (`LeanFX2.Smoke).isPrefixOf moduleName then
    "LeanFX2.Smoke"
  else if (`LeanFX2.Sketch).isPrefixOf moduleName then
    "LeanFX2.Sketch"
  else if (`LeanFX2.Foundation).isPrefixOf moduleName then
    "LeanFX2.Foundation"
  else if moduleName == `LeanFX2.Term ||
      (`LeanFX2.Term).isPrefixOf moduleName then
    "LeanFX2.Term"
  else if (`LeanFX2.Reduction).isPrefixOf moduleName then
    "LeanFX2.Reduction"
  else if moduleName == `LeanFX2.Bridge ||
      (`LeanFX2.Bridge).isPrefixOf moduleName then
    "LeanFX2.Bridge"
  else if (`LeanFX2.Confluence).isPrefixOf moduleName then
    "LeanFX2.Confluence"
  else if (`LeanFX2.HoTT).isPrefixOf moduleName then
    "LeanFX2.HoTT"
  else if (`LeanFX2.Cubical).isPrefixOf moduleName then
    "LeanFX2.Cubical"
  else if (`LeanFX2.Modal).isPrefixOf moduleName then
    "LeanFX2.Modal"
  else if (`LeanFX2.Effects).isPrefixOf moduleName then
    "LeanFX2.Effects"
  else if (`LeanFX2.Sessions).isPrefixOf moduleName then
    "LeanFX2.Sessions"
  else if (`LeanFX2.Codata).isPrefixOf moduleName then
    "LeanFX2.Codata"
  else if (`LeanFX2.Graded).isPrefixOf moduleName then
    "LeanFX2.Graded"
  else if (`LeanFX2.Refine).isPrefixOf moduleName then
    "LeanFX2.Refine"
  else if (`LeanFX2.Algo).isPrefixOf moduleName then
    "LeanFX2.Algo"
  else if (`LeanFX2.Surface).isPrefixOf moduleName then
    "LeanFX2.Surface"
  else if moduleName == `LeanFX2.Pipeline then
    "LeanFX2.Pipeline"
  else if (`LeanFX2.Conservativity).isPrefixOf moduleName then
    "LeanFX2.Conservativity"
  else if (`LeanFX2.Translation).isPrefixOf moduleName then
    "LeanFX2.Translation"
  else if (`LeanFX2.InternalLanguage).isPrefixOf moduleName then
    "LeanFX2.InternalLanguage"
  else if (`Lean).isPrefixOf moduleName then
    "Host.Lean"
  else if (`Lake).isPrefixOf moduleName then
    "Host.Lake"
  else if (`Std).isPrefixOf moduleName then
    "Host.Std"
  else if (`Init).isPrefixOf moduleName then
    "Host.Init"
  else if (`Classical).isPrefixOf moduleName then
    "Host.Classical"
  else if (`Quot).isPrefixOf moduleName then
    "Host.Quot"
  else
    "Other"

/-- Increment an import-family count in a small association list. -/
def incrementImportFamilyCount
    (counts : Array (String × Nat)) (familyLabel : String) :
    Array (String × Nat) :=
  match counts.findIdx? (fun (storedLabel, _) => storedLabel == familyLabel) with
  | some familyIndex =>
      counts.modify familyIndex
        (fun (storedLabel, count) => (storedLabel, count + 1))
  | none => counts.push (familyLabel, 1)

/-- Render import-family counts in stable first-seen order. -/
def formatImportFamilyCounts (counts : Array (String × Nat)) : String :=
  if counts.isEmpty then
    "none"
  else
    String.intercalate "; "
      (counts.toList.map fun (familyLabel, count) =>
        s!"{familyLabel}={count}")

/-- Build-failing global host-heavy import gate.

This scans every loaded `LeanFX2.*` module, including tools and smoke tests.
The broader production gates already forbid host-heavy imports in production
modules; this gate also keeps tools/smoke host imports explicit and prevents a
second accidental `import Lean` from entering unnoticed. -/
elab "#assert_host_heavy_import_surface_allowlisted" : command => do
  let environment ← getEnv
  let moduleEntries :=
    Array.zip environment.header.modules environment.header.moduleData
  let mut scannedLeanFX2Modules : Nat := 0
  let mut violations : Array DirectImportRecord := #[]
  for (effectiveImport, moduleData) in moduleEntries do
    let sourceModuleName := effectiveImport.module
    if (`LeanFX2).isPrefixOf sourceModuleName then
      scannedLeanFX2Modules := scannedLeanFX2Modules + 1
      for directImport in moduleData.imports do
        let directImportRecord : DirectImportRecord := {
          sourceModuleName := sourceModuleName
          importedModuleName := directImport.module
        }
        if isHostHeavyDirectImportModuleName directImport.module &&
            !isAllowedHostHeavyDirectImport directImportRecord then
          violations := violations.push directImportRecord
  if violations.isEmpty then
    logInfo m!"host-heavy import allowlist ok: {scannedLeanFX2Modules} modules"
  else
    let renderedImports := formatDirectImportRecords violations
    let header :=
      s!"host-heavy import allowlist FAILED: " ++
      s!"{violations.size} forbidden direct host-heavy imports"
    throwError (header ++ "\n  " ++ renderedImports)

/-- Informational import-family census over the currently loaded
`LeanFX2.*` modules.  This exposes import mass by source family and target
family without creating a committed report file. -/
elab "#audit_import_family_summary" : command => do
  let environment ← getEnv
  let moduleEntries :=
    Array.zip environment.header.modules environment.header.moduleData
  let mut sourceFamilyCounts : Array (String × Nat) := #[]
  let mut targetFamilyCounts : Array (String × Nat) := #[]
  let mut directImportCount : Nat := 0
  for (effectiveImport, moduleData) in moduleEntries do
    let sourceModuleName := effectiveImport.module
    if (`LeanFX2).isPrefixOf sourceModuleName then
      sourceFamilyCounts :=
        incrementImportFamilyCount sourceFamilyCounts
          (importFamilyLabel sourceModuleName)
      for directImport in moduleData.imports do
        directImportCount := directImportCount + 1
        targetFamilyCounts :=
          incrementImportFamilyCount targetFamilyCounts
            (importFamilyLabel directImport.module)
  logInfo
    (String.intercalate "\n" [
      "──────────── IMPORT FAMILY SUMMARY ────────────",
      s!"  Direct import edges scanned: {directImportCount}",
      s!"  Source families: {formatImportFamilyCounts sourceFamilyCounts}",
      s!"  Target families: {formatImportFamilyCounts targetFamilyCounts}",
      "───────────────────────────────────────────────"
    ])

/-- Informational import summary over the currently loaded `LeanFX2.*`
modules.  This is not a policy gate; the policy gates above remain the
build-failing checks. -/
elab "#audit_import_surface_summary" : command => do
  let environment ← getEnv
  let moduleEntries :=
    Array.zip environment.header.modules environment.header.moduleData
  let mut leanFX2ModuleCount : Nat := 0
  let mut productionModuleCount : Nat := 0
  let mut richProductionModuleCount : Nat := 0
  let mut fx1BridgeModuleCount : Nat := 0
  let mut fx1ModuleCount : Nat := 0
  let mut toolsModuleCount : Nat := 0
  let mut smokeModuleCount : Nat := 0
  let mut sketchModuleCount : Nat := 0
  let mut legacyLeanKernelModuleCount : Nat := 0
  let mut publicUmbrellaHeaderImportCount : Nat := 0
  let mut directImportCount : Nat := 0
  let mut hostHeavyDirectImports : Array DirectImportRecord := #[]
  let mut richProductionFX1Imports : Array DirectImportRecord := #[]
  let mut richProductionHostImports : Array DirectImportRecord := #[]
  let mut legacyLeanKernelImports : Array DirectImportRecord := #[]
  let mut legacyLeanKernelOutwardImports : Array DirectImportRecord := #[]
  let mut hostBoundaryImports : Array DirectImportRecord := #[]
  let mut fx1ForbiddenImports : Array DirectImportRecord := #[]
  let mut fx1PreludeImports : Array DirectImportRecord := #[]
  for (effectiveImport, moduleData) in moduleEntries do
    let sourceModuleName := effectiveImport.module
    if (`LeanFX2).isPrefixOf sourceModuleName then
      leanFX2ModuleCount := leanFX2ModuleCount + 1
      if isProductionLeanFX2ModuleName sourceModuleName then
        productionModuleCount := productionModuleCount + 1
      if isRichProductionLeanFX2ModuleName sourceModuleName then
        richProductionModuleCount := richProductionModuleCount + 1
      if isFX1BridgeModuleName sourceModuleName then
        fx1BridgeModuleCount := fx1BridgeModuleCount + 1
      if isFX1ModuleName sourceModuleName then
        fx1ModuleCount := fx1ModuleCount + 1
      if (`LeanFX2.Tools).isPrefixOf sourceModuleName then
        toolsModuleCount := toolsModuleCount + 1
      if (`LeanFX2.Smoke).isPrefixOf sourceModuleName then
        smokeModuleCount := smokeModuleCount + 1
      if (`LeanFX2.Sketch).isPrefixOf sourceModuleName then
        sketchModuleCount := sketchModuleCount + 1
      if isLegacyLeanKernelScaffoldModuleName sourceModuleName then
        legacyLeanKernelModuleCount := legacyLeanKernelModuleCount + 1
      for directImport in moduleData.imports do
        let importedModuleName := directImport.module
        if sourceModuleName == `LeanFX2 then
          publicUmbrellaHeaderImportCount := publicUmbrellaHeaderImportCount + 1
        directImportCount := directImportCount + 1
        let directImportRecord : DirectImportRecord := {
          sourceModuleName := sourceModuleName
          importedModuleName := importedModuleName
        }
        if isHostHeavyDirectImportModuleName importedModuleName then
          hostHeavyDirectImports :=
            hostHeavyDirectImports.push directImportRecord
        if isRichProductionLeanFX2ModuleName sourceModuleName &&
            isFX1ModuleName importedModuleName then
          richProductionFX1Imports :=
            richProductionFX1Imports.push directImportRecord
        if isRichProductionLeanFX2ModuleName sourceModuleName &&
            isHostHeavyDirectImportModuleName importedModuleName then
          richProductionHostImports :=
            richProductionHostImports.push directImportRecord
        if isLegacyLeanKernelScaffoldModuleName importedModuleName then
          legacyLeanKernelImports :=
            legacyLeanKernelImports.push directImportRecord
        if isLegacyLeanKernelScaffoldModuleName sourceModuleName &&
            (`LeanFX2).isPrefixOf importedModuleName &&
            !isLegacyLeanKernelScaffoldModuleName importedModuleName then
          legacyLeanKernelOutwardImports :=
            legacyLeanKernelOutwardImports.push directImportRecord
        if isHostBoundaryModuleName importedModuleName then
          hostBoundaryImports :=
            hostBoundaryImports.push directImportRecord
        if isFX1ModuleName sourceModuleName &&
            !isAllowedFX1DirectImport sourceModuleName importedModuleName then
          fx1ForbiddenImports :=
            fx1ForbiddenImports.push directImportRecord
        if isFX1ModuleName sourceModuleName &&
            importedModuleName == `Init.Prelude then
          fx1PreludeImports :=
            fx1PreludeImports.push directImportRecord
  logInfo
    (String.intercalate "\n" [
      "──────────── IMPORT SURFACE SUMMARY ────────────",
      s!"  LeanFX2 modules visible:          {leanFX2ModuleCount}",
      s!"  Production modules:               {productionModuleCount}",
      s!"  Rich production modules:          {richProductionModuleCount}",
      s!"  FX1Bridge modules:                {fx1BridgeModuleCount}",
      s!"  FX1 modules:                      {fx1ModuleCount}",
      s!"  Tool modules:                     {toolsModuleCount}",
      s!"  Smoke modules:                    {smokeModuleCount}",
      s!"  Sketch modules:                   {sketchModuleCount}",
      s!"  Legacy LeanKernel modules:        {legacyLeanKernelModuleCount}",
      s!"  Public umbrella header imports:   {publicUmbrellaHeaderImportCount}",
      s!"  Direct import edges scanned:      {directImportCount}",
      s!"  Host-heavy direct imports:        {hostHeavyDirectImports.size}",
      s!"    {formatDirectImportRecords hostHeavyDirectImports}",
      s!"  Rich-production -> FX1 imports:   {richProductionFX1Imports.size}",
      s!"    {formatDirectImportRecords richProductionFX1Imports}",
      s!"  Rich-production host imports:     {richProductionHostImports.size}",
      s!"    {formatDirectImportRecords richProductionHostImports}",
      s!"  Legacy LeanKernel direct imports: {legacyLeanKernelImports.size}",
      s!"    {formatDirectImportRecords legacyLeanKernelImports}",
      s!"  Legacy LeanKernel outward imports: {legacyLeanKernelOutwardImports.size}",
      s!"    {formatDirectImportRecords legacyLeanKernelOutwardImports}",
      s!"  Host-boundary direct imports:   {hostBoundaryImports.size}",
      s!"    {formatDirectImportRecords hostBoundaryImports}",
      s!"  FX1 forbidden direct imports:     {fx1ForbiddenImports.size}",
      s!"    {formatDirectImportRecords fx1ForbiddenImports}",
      s!"  FX1 direct Init.Prelude imports:  {fx1PreludeImports.size}",
      s!"    {formatDirectImportRecords fx1PreludeImports}",
      "────────────────────────────────────────────────"
    ])

/-! ## Raw/typed parity check -/

end LeanFX2.Tools
