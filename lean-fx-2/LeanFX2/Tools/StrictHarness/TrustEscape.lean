import LeanFX2.Tools.StrictHarness.Common
import LeanFX2.Tools.StrictHarness.Census
import LeanFX2.Tools.StrictHarness.DeclShape
import LeanFX2.Tools.StrictHarness.AxiomAdjacent

namespace LeanFX2.Tools

open Lean Elab Command

/-! ## Inductive ctor-count regression gate

Pin the current ctor count for each load-bearing inductive (Term, Ty,
Step, Step.par, RawTerm, RawStep.par, Conv, Mode, Ctx).  The gate
fails on SHRINKAGE only — growth is logged informationally because
codex / the user legitimately add new ctors all the time.

Catches accidental code deletion: if a refactor removes a ctor by
mistake, this gate fires before the broader build can collapse around
the missing case.
-/

/-- Build-failing budget gate for inductive ctor-count regression.
Fails if `actualCtorCount < expectedCtorCount` (regression).  Logs
INFORMATIONALLY if `actualCtorCount > expectedCtorCount` (growth).
Logs OK if equal. -/
elab "#assert_inductive_ctor_count_ratchet " inductiveSyntax:ident
    expectedCtorCountSyntax:num : command => do
  let environment ← getEnv
  let inductiveName := inductiveSyntax.getId
  let expectedCtorCount := expectedCtorCountSyntax.getNat
  let actualCtorCount :=
    (getInductiveConstructorNames environment inductiveName).size
  if actualCtorCount == expectedCtorCount then
    logInfo
      (s!"inductive ctor-count ratchet ok: {inductiveName} " ++
      s!"({actualCtorCount} ctors, matches pinned)")
  else if actualCtorCount > expectedCtorCount then
    logInfo
      (s!"inductive ctor-count GROWTH: {inductiveName} " ++
      s!"({actualCtorCount} ctors, was pinned at {expectedCtorCount}; " ++
      "consider bumping expected count)")
  else
    let header :=
      s!"inductive ctor-count REGRESSION for {inductiveName}: " ++
      s!"{actualCtorCount} ctors, expected at least {expectedCtorCount}"
    throwError header

/-! ## Coe family dependent gate

Coe / CoeSort / CoeFun typeclass instances silently inject elements
between types.  A bad Coe makes the type system structurally porous.
This gate counts kernel-tier decls whose closure references the Coe
typeclass family.
-/

/-- Whether a name is in the Coe coercion family. -/
def isCoeFamilyName (someName : Name) : Bool :=
  someName == `Coe ||
    someName == `Coe.coe ||
    someName == `CoeSort ||
    someName == `CoeSort.coe ||
    someName == `CoeFun ||
    someName == `CoeFun.coe ||
    someName == `CoeHead ||
    someName == `CoeTail ||
    someName == `CoeOut ||
    someName == `CoeOut.coe ||
    someName == `CoeOTC ||
    someName == `CoeTC ||
    someName == `CoeDep

/-- Closure dependents on Coe family. -/
def collectCoeDependencies
    (environment : Environment) (targetName : Name) :
    Array Name :=
  let dependencyNames :=
    collectDependencies environment targetName (includeStdlib := true)
  dependencyNames.toList.foldl
    (init := (#[] : Array Name))
    (fun coeDependencies dependencyName =>
      if isCoeFamilyName dependencyName then
        coeDependencies.push dependencyName
      else
        coeDependencies)

elab "#assert_coe_dependent_budget " namespaceSyntax:ident
    coeBudgetSyntax:num : command => do
  let environment ← getEnv
  let namespaceName := namespaceSyntax.getId
  let coeBudget := coeBudgetSyntax.getNat
  let targetNames := namespaceAuditTargets environment namespaceName
  let mut violations : Array Name := #[]
  for targetName in targetNames do
    if !isKernelTierProductionDecl targetName then
      continue
    if !(collectCoeDependencies environment targetName).isEmpty then
      violations := violations.push targetName
  if violations.size <= coeBudget then
    logInfo
      (s!"Coe dependent budget ok: {namespaceName} " ++
      s!"({violations.size}/{coeBudget} kernel decls reference Coe family)")
  else
    let perDeclLines := violations.toList.take 20 |>.map fun declName =>
      s!"  - {declName}"
    let header :=
      s!"Coe dependent budget FAILED for {namespaceName}: " ++
      s!"{violations.size} dependents exceed budget {coeBudget}"
    throwError (header ++ "\n" ++ String.intercalate "\n" perDeclLines)

/-! ## OfNat literal-injection dependent gate

`OfNat T n` instances let numeric literals inject into T.  A custom
OfNat for inappropriate T types is a literal-injection vector.  This
gate counts kernel-tier decls whose closure references OfNat (any
type).
-/

/-- Whether a name is in the OfNat literal family. -/
def isOfNatFamilyName (someName : Name) : Bool :=
  someName == `OfNat ||
    someName == `OfNat.ofNat ||
    someName == `OfNat.mk ||
    someName == `OfScientific ||
    someName == `OfScientific.ofScientific

def collectOfNatDependencies
    (environment : Environment) (targetName : Name) :
    Array Name :=
  let dependencyNames :=
    collectDependencies environment targetName (includeStdlib := true)
  dependencyNames.toList.foldl
    (init := (#[] : Array Name))
    (fun ofNatDependencies dependencyName =>
      if isOfNatFamilyName dependencyName then
        ofNatDependencies.push dependencyName
      else
        ofNatDependencies)

elab "#assert_ofnat_dependent_budget " namespaceSyntax:ident
    ofNatBudgetSyntax:num : command => do
  let environment ← getEnv
  let namespaceName := namespaceSyntax.getId
  let ofNatBudget := ofNatBudgetSyntax.getNat
  let targetNames := namespaceAuditTargets environment namespaceName
  let mut violations : Array Name := #[]
  for targetName in targetNames do
    if !isKernelTierProductionDecl targetName then
      continue
    if !(collectOfNatDependencies environment targetName).isEmpty then
      violations := violations.push targetName
  if violations.size <= ofNatBudget then
    logInfo
      (s!"OfNat dependent budget ok: {namespaceName} " ++
      s!"({violations.size}/{ofNatBudget} kernel decls reference OfNat family)")
  else
    let perDeclLines := violations.toList.take 20 |>.map fun declName =>
      s!"  - {declName}"
    let header :=
      s!"OfNat dependent budget FAILED for {namespaceName}: " ++
      s!"{violations.size} dependents exceed budget {ofNatBudget}"
    throwError (header ++ "\n" ++ String.intercalate "\n" perDeclLines)

/-! ## Subtype dependent gate

`Subtype` packages a value with a refinement proof.  `Subtype.mk` /
`Subtype.val` mediate between the bare type and the refined view.
Heavy use signals subtype-encoded reasoning that may be hiding
structural complexity.  Pin current count.
-/

def isSubtypeFamilyName (someName : Name) : Bool :=
  someName == `Subtype ||
    someName == `Subtype.mk ||
    someName == `Subtype.val ||
    someName == `Subtype.property ||
    someName == `Subtype.rec

def collectSubtypeDependencies
    (environment : Environment) (targetName : Name) :
    Array Name :=
  let dependencyNames :=
    collectDependencies environment targetName (includeStdlib := true)
  dependencyNames.toList.foldl
    (init := (#[] : Array Name))
    (fun subtypeDependencies dependencyName =>
      if isSubtypeFamilyName dependencyName then
        subtypeDependencies.push dependencyName
      else
        subtypeDependencies)

elab "#assert_subtype_dependent_budget " namespaceSyntax:ident
    subtypeBudgetSyntax:num : command => do
  let environment ← getEnv
  let namespaceName := namespaceSyntax.getId
  let subtypeBudget := subtypeBudgetSyntax.getNat
  let targetNames := namespaceAuditTargets environment namespaceName
  let mut violations : Array Name := #[]
  for targetName in targetNames do
    if !isKernelTierProductionDecl targetName then
      continue
    if !(collectSubtypeDependencies environment targetName).isEmpty then
      violations := violations.push targetName
  if violations.size <= subtypeBudget then
    logInfo
      (s!"Subtype dependent budget ok: {namespaceName} " ++
      s!"({violations.size}/{subtypeBudget} kernel decls reference Subtype family)")
  else
    let perDeclLines := violations.toList.take 20 |>.map fun declName =>
      s!"  - {declName}"
    let header :=
      s!"Subtype dependent budget FAILED for {namespaceName}: " ++
      s!"{violations.size} dependents exceed budget {subtypeBudget}"
    throwError (header ++ "\n" ++ String.intercalate "\n" perDeclLines)

/-! ## Function-property dependent gate

`Function.Injective`, `Function.Bijective`, `Function.Surjective`,
`Function.LeftInverse`, `Function.RightInverse` encode mathematical
properties of functions.  Heavy kernel-tier usage signals
typing-by-cardinality reasoning that may not transport across the
trust spine.  Pin current count.
-/

def isFunctionPropertyName (someName : Name) : Bool :=
  someName == `Function.Injective ||
    someName == `Function.Bijective ||
    someName == `Function.Surjective ||
    someName == `Function.LeftInverse ||
    someName == `Function.RightInverse ||
    someName == `Function.HasLeftInverse ||
    someName == `Function.HasRightInverse ||
    someName == `Function.invFun

def collectFunctionPropertyDependencies
    (environment : Environment) (targetName : Name) :
    Array Name :=
  let dependencyNames :=
    collectDependencies environment targetName (includeStdlib := true)
  dependencyNames.toList.foldl
    (init := (#[] : Array Name))
    (fun functionDependencies dependencyName =>
      if isFunctionPropertyName dependencyName then
        functionDependencies.push dependencyName
      else
        functionDependencies)

elab "#assert_function_property_dependent_budget " namespaceSyntax:ident
    functionBudgetSyntax:num : command => do
  let environment ← getEnv
  let namespaceName := namespaceSyntax.getId
  let functionBudget := functionBudgetSyntax.getNat
  let targetNames := namespaceAuditTargets environment namespaceName
  let mut violations : Array Name := #[]
  for targetName in targetNames do
    if !isKernelTierProductionDecl targetName then
      continue
    if !(collectFunctionPropertyDependencies environment targetName).isEmpty then
      violations := violations.push targetName
  if violations.size <= functionBudget then
    logInfo
      (s!"Function-property dependent budget ok: {namespaceName} " ++
      s!"({violations.size}/{functionBudget} kernel decls reference " ++
      "Function.Injective / Bijective / etc.)")
  else
    let perDeclLines := violations.toList.take 20 |>.map fun declName =>
      s!"  - {declName}"
    let header :=
      s!"Function-property dependent budget FAILED for {namespaceName}: " ++
      s!"{violations.size} dependents exceed budget {functionBudget}"
    throwError (header ++ "\n" ++ String.intercalate "\n" perDeclLines)

/-! ## Reducibility-status decl-shape gate

Decls marked `@[reducible]` or shipped via `abbrev` have reducibility
hint `.abbrev`.  These let the kernel reducer unfold them eagerly,
which can mask structural reasoning and cause unification loops.  This
gate pins the count of reducible / abbrev decls in kernel namespaces.
-/

/-- Whether a constant info has reducibility hint indicating abbrev /
reducible.  Default reducibility is `.regular`, abbrev is `.abbrev`,
opaque is `.opaque`. -/
def hasAbbrevReducibilityHint
    (environment : Environment) (declName : Name) : Bool :=
  match environment.find? declName with
  | some (.defnInfo defnInfo) =>
      match defnInfo.hints with
      | .abbrev => true
      | _ => false
  | _ => false

elab "#assert_reducible_decl_budget " namespaceSyntax:ident
    reducibleBudgetSyntax:num : command => do
  let environment ← getEnv
  let namespaceName := namespaceSyntax.getId
  let reducibleBudget := reducibleBudgetSyntax.getNat
  let targetNames := namespaceAuditTargets environment namespaceName
  let mut reducibleCount : Nat := 0
  let mut violations : Array Name := #[]
  for targetName in targetNames do
    if !isKernelTierProductionDecl targetName then
      continue
    if hasAbbrevReducibilityHint environment targetName then
      reducibleCount := reducibleCount + 1
      violations := violations.push targetName
  if reducibleCount <= reducibleBudget then
    logInfo
      (s!"reducible decl budget ok: {namespaceName} " ++
      s!"({reducibleCount}/{reducibleBudget} kernel decls are reducible/abbrev)")
  else
    let perDeclLines := violations.toList.take 20 |>.map fun declName =>
      s!"  - {declName}"
    let header :=
      s!"reducible decl budget FAILED for {namespaceName}: " ++
      s!"{reducibleCount} reducible decls exceed budget {reducibleBudget}"
    throwError (header ++ "\n" ++ String.intercalate "\n" perDeclLines)

/-! ## Inductive ctor exact-count assertion gate

For inductives whose ctor count is fixed by spec (e.g., Mode = exactly
5 ctors per kernel-sprint §1.4), this gate fails on ANY mismatch
(growth or shrinkage).  Stricter than the regression-only ratchet.
-/

elab "#assert_inductive_ctor_count_exact " inductiveSyntax:ident
    expectedCtorCountSyntax:num : command => do
  let environment ← getEnv
  let inductiveName := inductiveSyntax.getId
  let expectedCtorCount := expectedCtorCountSyntax.getNat
  let actualCtorCount :=
    (getInductiveConstructorNames environment inductiveName).size
  if actualCtorCount == expectedCtorCount then
    logInfo
      (s!"inductive ctor-count exact ok: {inductiveName} " ++
      s!"({actualCtorCount} ctors, matches expected)")
  else
    let header :=
      s!"inductive ctor-count exact MISMATCH for {inductiveName}: " ++
      s!"{actualCtorCount} ctors, expected EXACTLY {expectedCtorCount}"
    throwError header

/-! ## Bridge round-trip parity gate

For every `FX1Bridge.encodeTermSound_<X>` (the bridge soundness theorem
for ctor X), there should be a companion `FX1Bridge.encodeTermSound_<X>_roundTrip`
proving `decode (encode t) = t`.  Without round-trip, the bridge could
be lossy — encoding might collapse distinct typed terms.

This gate scans the FX1Bridge namespace for `encodeTermSound_*` decls
and checks each has a companion round-trip.  Pin current debt.
-/

/-- Whether a name is the soundness theorem for a Term ctor encoding. -/
def isEncodeTermSoundName (someName : Name) : Bool :=
  let lastSegment := Name.lastSegmentString someName
  (`LeanFX2.FX1Bridge).isPrefixOf someName &&
    lastSegment.startsWith "encodeTermSound_" &&
    !lastSegment.endsWith "_roundTrip"

/-- Expected round-trip companion name. -/
def expectedRoundTripCompanionName (soundnessName : Name) : Name :=
  Name.str
    (`LeanFX2.FX1Bridge)
    (Name.lastSegmentString soundnessName ++ "_roundTrip")

elab "#assert_bridge_round_trip_budget " namespaceSyntax:ident
    roundTripBudgetSyntax:num : command => do
  let environment ← getEnv
  let namespaceName := namespaceSyntax.getId
  let roundTripBudget := roundTripBudgetSyntax.getNat
  let targetNames := namespaceAuditTargets environment namespaceName
  let mut soundnessCount : Nat := 0
  let mut missingRoundTrips : Array Name := #[]
  for targetName in targetNames do
    if isEncodeTermSoundName targetName then
      soundnessCount := soundnessCount + 1
      let companionName := expectedRoundTripCompanionName targetName
      if !environment.contains companionName then
        missingRoundTrips := missingRoundTrips.push targetName
  if missingRoundTrips.size <= roundTripBudget then
    logInfo
      (s!"bridge round-trip parity budget ok: {namespaceName} " ++
      s!"({soundnessCount - missingRoundTrips.size}/{soundnessCount} " ++
      s!"soundness theorems have round-trip companions; " ++
      s!"debt {missingRoundTrips.size}/{roundTripBudget})")
  else
    let perDeclLines := missingRoundTrips.toList.take 20 |>.map fun declName =>
      s!"  - {declName}: missing _roundTrip companion"
    let header :=
      s!"bridge round-trip parity budget FAILED for {namespaceName}: " ++
      s!"{missingRoundTrips.size} soundness theorems lack round-trip, " ++
      s!"exceeds budget {roundTripBudget}"
    throwError (header ++ "\n" ++ String.intercalate "\n" perDeclLines)

/-! ## Equality-rewriting dependent gate

`Eq.symm`, `Eq.trans`, `Eq.mp`, `Eq.mpr`, `Eq.rec`, `Eq.recOn` are the
core equality-rewriting primitives.  Heavy use signals chain-rewriting
proofs that obscure structural reasoning.  Note: `Eq.mpr` is already
counted in cast-operator gate; this gate widens to the full eq-rewrite
family.
-/

/-- Whether a name is in the Eq-rewriting family.  Subset that's not
already counted by cast-operator gate. -/
def isEqRewritingName (someName : Name) : Bool :=
  someName == `Eq.symm ||
    someName == `Eq.trans ||
    someName == `Eq.mp ||
    someName == `Eq.recOn ||
    someName == `Eq.casesOn ||
    someName == `Eq.elim ||
    someName == `Eq.subst

def collectEqRewritingDependencies
    (environment : Environment) (targetName : Name) :
    Array Name :=
  let dependencyNames :=
    collectDependencies environment targetName (includeStdlib := true)
  dependencyNames.toList.foldl
    (init := (#[] : Array Name))
    (fun eqDependencies dependencyName =>
      if isEqRewritingName dependencyName then
        eqDependencies.push dependencyName
      else
        eqDependencies)

elab "#assert_eq_rewriting_dependent_budget " namespaceSyntax:ident
    eqBudgetSyntax:num : command => do
  let environment ← getEnv
  let namespaceName := namespaceSyntax.getId
  let eqBudget := eqBudgetSyntax.getNat
  let targetNames := namespaceAuditTargets environment namespaceName
  let mut violations : Array Name := #[]
  for targetName in targetNames do
    if !isKernelTierProductionDecl targetName then
      continue
    if !(collectEqRewritingDependencies environment targetName).isEmpty then
      violations := violations.push targetName
  if violations.size <= eqBudget then
    logInfo
      (s!"Eq-rewriting dependent budget ok: {namespaceName} " ++
      s!"({violations.size}/{eqBudget} kernel decls reference Eq.symm/trans/mp/etc.)")
  else
    let perDeclLines := violations.toList.take 20 |>.map fun declName =>
      s!"  - {declName}"
    let header :=
      s!"Eq-rewriting dependent budget FAILED for {namespaceName}: " ++
      s!"{violations.size} dependents exceed budget {eqBudget}"
    throwError (header ++ "\n" ++ String.intercalate "\n" perDeclLines)

/-! ## True / False / Unit empty-result gates

Theorems whose claimed result type is `True` are vacuous; `False` is
evidence of inconsistency.  Decls with these as result types should be
budgeted carefully.  `Unit`-result decls are non-suspicious but
counted.
-/

def claimsTrueResultType (constantInfo : ConstantInfo) : Bool :=
  match constantInfo.type with
  | .const `True _ => true
  | _ => doesExprMentionConst `True constantInfo.type

def claimsFalseResultType (constantInfo : ConstantInfo) : Bool :=
  match constantInfo.type with
  | .const `False _ => true
  | _ => doesExprMentionConst `False constantInfo.type

elab "#assert_false_in_result_type_budget " namespaceSyntax:ident
    falseBudgetSyntax:num : command => do
  let environment ← getEnv
  let namespaceName := namespaceSyntax.getId
  let falseBudget := falseBudgetSyntax.getNat
  let targetNames := namespaceAuditTargets environment namespaceName
  let mut violations : Array Name := #[]
  for targetName in targetNames do
    if !isKernelTierProductionDecl targetName then
      continue
    match environment.find? targetName with
    | some constantInfo =>
        if claimsFalseResultType constantInfo then
          violations := violations.push targetName
    | none => pure ()
  if violations.size <= falseBudget then
    logInfo
      (s!"False-in-result-type budget ok: {namespaceName} " ++
      s!"({violations.size}/{falseBudget} kernel decls mention False " ++
      "in result type)")
  else
    let perDeclLines := violations.toList.take 20 |>.map fun declName =>
      s!"  - {declName}"
    let header :=
      s!"False-in-result-type budget FAILED for {namespaceName}: " ++
      s!"{violations.size} dependents exceed budget {falseBudget}"
    throwError (header ++ "\n" ++ String.intercalate "\n" perDeclLines)

/-! ## Term ctor → RawTerm projection-shape audit

Term has 75 constructors but RawTerm has 67.  The 8-decl gap means
some Term ctors share raw projections — typing is NOT a function from
RawTerm to Term.  This gate counts the shared-raw-projection delta:
`Term ctors - RawTerm ctors`.  When the delta is positive, manufactured-
witness ctors with shared raw projections exist (architectural choice
for refl-fragment Univalence/funext).
-/

elab "#assert_term_raw_ctor_delta " termInductiveSyntax:ident
    rawTermInductiveSyntax:ident expectedDeltaSyntax:num : command => do
  let environment ← getEnv
  let termInductiveName := termInductiveSyntax.getId
  let rawTermInductiveName := rawTermInductiveSyntax.getId
  let expectedDelta := expectedDeltaSyntax.getNat
  let termCtorCount :=
    (getInductiveConstructorNames environment termInductiveName).size
  let rawTermCtorCount :=
    (getInductiveConstructorNames environment rawTermInductiveName).size
  let actualDelta :=
    if termCtorCount >= rawTermCtorCount then
      termCtorCount - rawTermCtorCount
    else 0
  if actualDelta == expectedDelta then
    logInfo
      (s!"Term/RawTerm ctor delta ok: " ++
      s!"Term={termCtorCount} RawTerm={rawTermCtorCount} delta={actualDelta} " ++
      "(matches expected; manufactured-witness sharing intact)")
  else if actualDelta > expectedDelta then
    let header :=
      s!"Term/RawTerm ctor delta GREW: " ++
      s!"Term={termCtorCount} RawTerm={rawTermCtorCount} actual={actualDelta} " ++
      s!"expected={expectedDelta} — new manufactured-witness Term ctor was " ++
      "added without RawTerm parity (or RawTerm shrank)"
    throwError header
  else
    logInfo
      (s!"Term/RawTerm ctor delta SHRANK: " ++
      s!"Term={termCtorCount} RawTerm={rawTermCtorCount} actual={actualDelta} " ++
      s!"expected={expectedDelta} — bump expected count")

/-! ## Sigma / PSigma / dependent-pair dependent gate

`Sigma`, `PSigma`, `Sum`, `PSum`, `PProd` are dependent / heterogeneous
packaging types.  Heavy use signals existential reasoning that may
hide non-canonical inhabitants.  `PSigma` in particular is propext-
adjacent on Prop-typed second components.
-/

def isDependentPairFamilyName (someName : Name) : Bool :=
  someName == `Sigma ||
    someName == `Sigma.mk ||
    someName == `Sigma.fst ||
    someName == `Sigma.snd ||
    someName == `PSigma ||
    someName == `PSigma.mk ||
    someName == `PSigma.fst ||
    someName == `PSigma.snd ||
    someName == `Sum ||
    someName == `Sum.inl ||
    someName == `Sum.inr ||
    someName == `PSum ||
    someName == `PSum.inl ||
    someName == `PSum.inr ||
    someName == `PProd ||
    someName == `PProd.mk

def collectDependentPairDependencies
    (environment : Environment) (targetName : Name) :
    Array Name :=
  let dependencyNames :=
    collectDependencies environment targetName (includeStdlib := true)
  dependencyNames.toList.foldl
    (init := (#[] : Array Name))
    (fun pairDependencies dependencyName =>
      if isDependentPairFamilyName dependencyName then
        pairDependencies.push dependencyName
      else
        pairDependencies)

elab "#assert_dependent_pair_dependent_budget " namespaceSyntax:ident
    pairBudgetSyntax:num : command => do
  let environment ← getEnv
  let namespaceName := namespaceSyntax.getId
  let pairBudget := pairBudgetSyntax.getNat
  let targetNames := namespaceAuditTargets environment namespaceName
  let mut violations : Array Name := #[]
  for targetName in targetNames do
    if !isKernelTierProductionDecl targetName then
      continue
    if !(collectDependentPairDependencies environment targetName).isEmpty then
      violations := violations.push targetName
  if violations.size <= pairBudget then
    logInfo
      (s!"dependent-pair dependent budget ok: {namespaceName} " ++
      s!"({violations.size}/{pairBudget} kernel decls reference " ++
      "Sigma / PSigma / Sum / PSum / PProd)")
  else
    let perDeclLines := violations.toList.take 20 |>.map fun declName =>
      s!"  - {declName}"
    let header :=
      s!"dependent-pair dependent budget FAILED for {namespaceName}: " ++
      s!"{violations.size} dependents exceed budget {pairBudget}"
    throwError (header ++ "\n" ++ String.intercalate "\n" perDeclLines)

/-! ## Classical.X direct dependent gate

Refines the existing Inhabited gate to specifically count uses of
`Classical.choice`, `Classical.choose`, `Classical.choose_spec`,
`Classical.byContradiction`, `Classical.em`, `Classical.byCases`.
These are the genuine excluded-middle / choice operations that
silently summon Classical reasoning.  The Inhabited gate counts them
collectively; this one names them directly.
-/

def isClassicalReasoningName (someName : Name) : Bool :=
  someName == `Classical.choice ||
    someName == `Classical.choose ||
    someName == `Classical.choose_spec ||
    someName == `Classical.indefiniteDescription ||
    someName == `Classical.byContradiction ||
    someName == `Classical.byCases ||
    someName == `Classical.em ||
    someName == `Classical.not_not ||
    someName == `Classical.dec ||
    someName == `Classical.propDecidable

def collectClassicalReasoningDependencies
    (environment : Environment) (targetName : Name) :
    Array Name :=
  let dependencyNames :=
    collectDependencies environment targetName (includeStdlib := true)
  dependencyNames.toList.foldl
    (init := (#[] : Array Name))
    (fun classicalDependencies dependencyName =>
      if isClassicalReasoningName dependencyName then
        classicalDependencies.push dependencyName
      else
        classicalDependencies)

elab "#assert_classical_reasoning_dependent_budget " namespaceSyntax:ident
    classicalBudgetSyntax:num : command => do
  let environment ← getEnv
  let namespaceName := namespaceSyntax.getId
  let classicalBudget := classicalBudgetSyntax.getNat
  let targetNames := namespaceAuditTargets environment namespaceName
  let mut violations : Array Name := #[]
  for targetName in targetNames do
    if !isKernelTierProductionDecl targetName then
      continue
    if !(collectClassicalReasoningDependencies environment targetName).isEmpty then
      violations := violations.push targetName
  if violations.size <= classicalBudget then
    logInfo
      (s!"Classical-reasoning dependent budget ok: {namespaceName} " ++
      s!"({violations.size}/{classicalBudget} kernel decls reference " ++
      "Classical.choose / em / byContradiction / etc.)")
  else
    let perDeclLines := violations.toList.take 20 |>.map fun declName =>
      s!"  - {declName}"
    let header :=
      s!"Classical-reasoning dependent budget FAILED for {namespaceName}: " ++
      s!"{violations.size} dependents exceed budget {classicalBudget}"
    throwError (header ++ "\n" ++ String.intercalate "\n" perDeclLines)

/-! ## API typeclass dependent gate (Hash / Repr / ToString / BEq)

`Hash`, `Repr`, `ToString`, `BEq` are user-facing API typeclasses for
hashing / printing / comparison.  Kernel theorems should NOT depend
on these — they're for humans, not metatheory.  Pinning the count
catches kernel-tier decls that drift toward API-coupling.
-/

def isApiTypeclassName (someName : Name) : Bool :=
  someName == `Hashable ||
    someName == `Hashable.hash ||
    someName == `Repr ||
    someName == `Repr.reprPrec ||
    someName == `ToString ||
    someName == `ToString.toString ||
    someName == `BEq ||
    someName == `BEq.beq ||
    someName == `LawfulBEq ||
    someName == `Format ||
    someName == `Std.Format ||
    someName == `Std.ToFormat

def collectApiTypeclassDependencies
    (environment : Environment) (targetName : Name) :
    Array Name :=
  let dependencyNames :=
    collectDependencies environment targetName (includeStdlib := true)
  dependencyNames.toList.foldl
    (init := (#[] : Array Name))
    (fun apiDependencies dependencyName =>
      if isApiTypeclassName dependencyName then
        apiDependencies.push dependencyName
      else
        apiDependencies)

elab "#assert_api_typeclass_dependent_budget " namespaceSyntax:ident
    apiBudgetSyntax:num : command => do
  let environment ← getEnv
  let namespaceName := namespaceSyntax.getId
  let apiBudget := apiBudgetSyntax.getNat
  let targetNames := namespaceAuditTargets environment namespaceName
  let mut violations : Array Name := #[]
  for targetName in targetNames do
    if !isKernelTierProductionDecl targetName then
      continue
    if !(collectApiTypeclassDependencies environment targetName).isEmpty then
      violations := violations.push targetName
  if violations.size <= apiBudget then
    logInfo
      (s!"API typeclass dependent budget ok: {namespaceName} " ++
      s!"({violations.size}/{apiBudget} kernel decls reference " ++
      "Hashable / Repr / ToString / BEq)")
  else
    let perDeclLines := violations.toList.take 20 |>.map fun declName =>
      s!"  - {declName}"
    let header :=
      s!"API typeclass dependent budget FAILED for {namespaceName}: " ++
      s!"{violations.size} dependents exceed budget {apiBudget}"
    throwError (header ++ "\n" ++ String.intercalate "\n" perDeclLines)

/-! ## IO / Task / Ref dependent gate

Kernel decls should not depend on IO / Task / IO.Ref / IO.FS / etc.
These are runtime-effect operations belonging to the executable
boundary, not the kernel.  Pin current count.
-/

def isIOEffectName (someName : Name) : Bool :=
  (`IO).isPrefixOf someName ||
    (`Task).isPrefixOf someName ||
    someName == `EIO ||
    someName == `BaseIO ||
    someName == `IO.Ref ||
    someName == `IO.FS.IO ||
    (`System.IO).isPrefixOf someName

def collectIOEffectDependencies
    (environment : Environment) (targetName : Name) :
    Array Name :=
  let dependencyNames :=
    collectDependencies environment targetName (includeStdlib := true)
  dependencyNames.toList.foldl
    (init := (#[] : Array Name))
    (fun ioDependencies dependencyName =>
      if isIOEffectName dependencyName then
        ioDependencies.push dependencyName
      else
        ioDependencies)

elab "#assert_io_effect_dependent_budget " namespaceSyntax:ident
    ioBudgetSyntax:num : command => do
  let environment ← getEnv
  let namespaceName := namespaceSyntax.getId
  let ioBudget := ioBudgetSyntax.getNat
  let targetNames := namespaceAuditTargets environment namespaceName
  let mut violations : Array Name := #[]
  for targetName in targetNames do
    if !isKernelTierProductionDecl targetName then
      continue
    if !(collectIOEffectDependencies environment targetName).isEmpty then
      violations := violations.push targetName
  if violations.size <= ioBudget then
    logInfo
      (s!"IO effect dependent budget ok: {namespaceName} " ++
      s!"({violations.size}/{ioBudget} kernel decls reference " ++
      "IO / Task / EIO / BaseIO)")
  else
    let perDeclLines := violations.toList.take 20 |>.map fun declName =>
      s!"  - {declName}"
    let header :=
      s!"IO effect dependent budget FAILED for {namespaceName}: " ++
      s!"{violations.size} dependents exceed budget {ioBudget}"
    throwError (header ++ "\n" ++ String.intercalate "\n" perDeclLines)

/-! ## Subterm-projection (anonymous .1 / .2 / .fst / .snd) gate

Kernel theorems that use `.fst`/`.snd`/`.1`/`.2` projections on dependent
pairs without naming the field can hide structural reasoning.  These
project from `Sigma`/`Prod`/`PSigma`/`Subtype`/etc.  Heavy use signals
proofs that destructure dependent values without being explicit about
the structure.
-/

def isAnonymousProjectionName (someName : Name) : Bool :=
  someName == `Prod.fst ||
    someName == `Prod.snd ||
    someName == `Prod.mk ||
    someName == `And.intro ||
    someName == `And.left ||
    someName == `And.right ||
    someName == `And.elim ||
    someName == `Or.intro_left ||
    someName == `Or.intro_right ||
    someName == `Or.elim ||
    someName == `Iff.intro ||
    someName == `Iff.mp ||
    someName == `Iff.mpr ||
    someName == `Iff.elim

def collectAnonymousProjectionDependencies
    (environment : Environment) (targetName : Name) :
    Array Name :=
  let dependencyNames :=
    collectDependencies environment targetName (includeStdlib := true)
  dependencyNames.toList.foldl
    (init := (#[] : Array Name))
    (fun projDependencies dependencyName =>
      if isAnonymousProjectionName dependencyName then
        projDependencies.push dependencyName
      else
        projDependencies)

elab "#assert_anonymous_projection_dependent_budget " namespaceSyntax:ident
    projBudgetSyntax:num : command => do
  let environment ← getEnv
  let namespaceName := namespaceSyntax.getId
  let projBudget := projBudgetSyntax.getNat
  let targetNames := namespaceAuditTargets environment namespaceName
  let mut violations : Array Name := #[]
  for targetName in targetNames do
    if !isKernelTierProductionDecl targetName then
      continue
    if !(collectAnonymousProjectionDependencies environment targetName).isEmpty then
      violations := violations.push targetName
  if violations.size <= projBudget then
    logInfo
      (s!"Anonymous-projection dependent budget ok: {namespaceName} " ++
      s!"({violations.size}/{projBudget} kernel decls reference " ++
      "Prod.fst / And.intro / Or.elim / Iff.mp / etc.)")
  else
    let perDeclLines := violations.toList.take 20 |>.map fun declName =>
      s!"  - {declName}"
    let header :=
      s!"Anonymous-projection dependent budget FAILED for {namespaceName}: " ++
      s!"{violations.size} dependents exceed budget {projBudget}"
    throwError (header ++ "\n" ++ String.intercalate "\n" perDeclLines)


end LeanFX2.Tools
