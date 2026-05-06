import LeanFX2.Tools.StrictHarness.Common
import LeanFX2.Tools.StrictHarness.Census

namespace LeanFX2.Tools

open Lean Elab Command

/-! ## Step.par cong-rule coverage gate

Every `Term` constructor with at least one explicit sub-Term position
should be reachable by parallel reduction.  The reaching mechanism is a
`Step.par.<ctorname>Cong` rule that lifts a parallel step in any
sub-term to a parallel step on the wrapping ctor.  Without that rule,
parallel reduction cannot enter the constructor and Church-Rosser is
incomplete on terms that mention it.

This gate counts Term constructors that DO NOT have a same-suffix
`Step.par.<ctorname>Cong` rule.  Value constructors (no sub-Term
parameters) naturally lack a cong rule and contribute to the count;
the budget accommodates that as architectural fact.  Future Term
ctors with sub-terms but no cong rule make the count grow and fail.

Exact name expected: `LeanFX2.Step.par.<ctorname>Cong`.  Ctors are
named via `Term.lastSegmentString`; the gate does a contains-check
against the loaded environment.  No structural analysis of the ctor
shape is performed; that would prematurely allow exemptions for
"this ctor's subterms are all raw".  The budget is the shape
discipline. -/

/-- Exact `Step.par.<ctorname>Cong` name expected for a Term ctor. -/
def expectedStepParCongName (constructorName : Name) : Name :=
  Name.str
    `LeanFX2.Step.par
    (Name.lastSegmentString constructorName ++ "Cong")

/-- One Term constructor whose Step.par cong mirror is not in the
loaded environment. -/
structure StepParCongCoverageDebtRecord where
  /-- Constructor whose mirror is missing. -/
  constructorName : Name
  /-- Exact mirror name expected by the coverage matrix. -/
  expectedCongName : Name
  deriving Inhabited, Repr

/-- Report Step.par cong coverage debt for one Term constructor. -/
def stepParCongCoverageDebtRecord?
    (environment : Environment) (constructorName : Name) :
    Option StepParCongCoverageDebtRecord :=
  let expectedCongName := expectedStepParCongName constructorName
  if environment.contains expectedCongName then
    none
  else
    some {
      constructorName := constructorName
      expectedCongName := expectedCongName
    }

/-- Collect Step.par cong coverage debt records for every constructor
of the given Term inductive. -/
def stepParCongCoverageDebtRecordsForInductive
    (environment : Environment) (inductiveName : Name) :
    Array StepParCongCoverageDebtRecord :=
  let constructorNames := getInductiveConstructorNames environment inductiveName
  constructorNames.foldl
    (init := (#[] : Array StepParCongCoverageDebtRecord))
    (fun records constructorName =>
      match stepParCongCoverageDebtRecord? environment constructorName with
      | some record => records.push record
      | none => records)

/-- Build-failing budget gate for Term constructors whose
`Step.par.<name>Cong` mirror is missing.  Existing debt may be pinned
by the budget; future ctors without cong rules push the count above
the ceiling and fail the build. -/
elab "#assert_step_par_cong_coverage_budget " inductiveSyntax:ident
    coverageDebtBudgetSyntax:num : command => do
  let environment ← getEnv
  let inductiveName := inductiveSyntax.getId
  let coverageDebtBudget := coverageDebtBudgetSyntax.getNat
  let records :=
    stepParCongCoverageDebtRecordsForInductive environment inductiveName
  let constructorCount :=
    (getInductiveConstructorNames environment inductiveName).size
  let coveredCount :=
    if constructorCount >= records.size then
      constructorCount - records.size
    else 0
  if records.size <= coverageDebtBudget then
    logInfo
      (s!"step-par cong coverage budget ok: {inductiveName} " ++
      s!"({coveredCount}/{constructorCount} ctors have Step.par.*Cong " ++
      s!"mirror; debt {records.size}/{coverageDebtBudget})")
  else
    let perCtorLines := records.toList.map fun record =>
      s!"  - {record.constructorName}: expected {record.expectedCongName}"
    let header :=
      s!"step-par cong coverage budget FAILED for {inductiveName}: " ++
      s!"{records.size} ctors lack Step.par.*Cong mirror, exceeds budget " ++
      s!"{coverageDebtBudget}"
    throwError (header ++ "\n" ++ String.intercalate "\n" perCtorLines)

/-! ## Conv cong-rule coverage gate

Symmetric to `#assert_step_par_cong_coverage_budget` but for the
definitional-conversion layer.  A `Term` constructor whose
sub-positions can step under `Step.par` should also have a cong rule
on `Conv` (so `Conv` lifts through the constructor).  The expected
name is `LeanFX2.Conv.<ctorname>Cong` or `LeanFX2.Conv.<ctorname>_cong`.
Either form is accepted because both naming conventions appear in the
codebase.

Exact-name coverage; no structural analysis of subterms.  Value ctors
naturally lack a Conv cong rule and the budget accommodates that.
-/

/-- Both expected Conv cong names for a Term ctor.  Accepts the two
naming conventions present in the codebase. -/
def expectedConvCongNames (constructorName : Name) : Name × Name :=
  let suffix := Name.lastSegmentString constructorName
  ( Name.str `LeanFX2.Conv (suffix ++ "Cong"),
    Name.str `LeanFX2.Conv (suffix ++ "_cong") )

/-- Whether either Conv cong-name shape exists in the environment for
this Term ctor. -/
def hasAnyConvCongMirror
    (environment : Environment) (constructorName : Name) : Bool :=
  let (camelName, snakeName) := expectedConvCongNames constructorName
  environment.contains camelName || environment.contains snakeName

/-- Report Conv cong coverage debt for one Term ctor. -/
def convCongCoverageDebtRecord?
    (environment : Environment) (constructorName : Name) :
    Option SignatureDebtRecord :=
  if hasAnyConvCongMirror environment constructorName then
    none
  else
    let (camelName, snakeName) := expectedConvCongNames constructorName
    some {
      constructorName := constructorName
      detail :=
        s!"missing both {camelName} and {snakeName}"
    }

/-- Collect Conv cong coverage debt across the Term inductive. -/
def convCongCoverageDebtRecordsForInductive
    (environment : Environment) (inductiveName : Name) :
    Array SignatureDebtRecord :=
  let constructorNames := getInductiveConstructorNames environment inductiveName
  constructorNames.foldl
    (init := (#[] : Array SignatureDebtRecord))
    (fun records constructorName =>
      match convCongCoverageDebtRecord? environment constructorName with
      | some record => records.push record
      | none => records)

/-- Build-failing budget gate for Term ctors whose Conv cong mirror is
absent.  Pins current count; future ctors without Conv lifting push
the count above the ceiling and fail. -/
elab "#assert_conv_cong_coverage_budget " inductiveSyntax:ident
    coverageDebtBudgetSyntax:num : command => do
  let environment ← getEnv
  let inductiveName := inductiveSyntax.getId
  let coverageDebtBudget := coverageDebtBudgetSyntax.getNat
  let records :=
    convCongCoverageDebtRecordsForInductive environment inductiveName
  let constructorCount :=
    (getInductiveConstructorNames environment inductiveName).size
  let coveredCount :=
    if constructorCount >= records.size then
      constructorCount - records.size
    else 0
  if records.size <= coverageDebtBudget then
    logInfo
      (s!"conv cong coverage budget ok: {inductiveName} " ++
      s!"({coveredCount}/{constructorCount} ctors have Conv cong mirror; " ++
      s!"debt {records.size}/{coverageDebtBudget})")
  else
    let perCtorLines := records.toList.map fun record =>
      s!"  - {record.constructorName}: {record.detail}"
    let header :=
      s!"conv cong coverage budget FAILED for {inductiveName}: " ++
      s!"{records.size} ctors lack Conv cong mirror, exceeds budget " ++
      s!"{coverageDebtBudget}"
    throwError (header ++ "\n" ++ String.intercalate "\n" perCtorLines)

/-! ## Cast-operator usage counter

Heterogeneous-equality cast operators (`Eq.mpr`, `Eq.ndrec`, `Eq.rec`,
`HEq.rec`, `HEq.subst`, `cast`) are common vectors for hidden propext
or Quot.sound dependencies.  The kernel reducer cannot in general
reduce a cast to the underlying value because the type-equality
witness blocks reduction.  In practice, a proliferation of cast
operations in the kernel correlates with structural typing tricks
that paper over real propositional gaps.

This gate counts decls in production namespaces whose transitive
closure references a cast operator.  Pinning the count makes new
casts visible to review.  The dashboard row surfaces the running
count.
-/

/-- Whether a name is one of the cast operators tracked by the audit. -/
def isCastOperatorName (someName : Name) : Bool :=
  someName == `Eq.mpr ||
    someName == `Eq.ndrec ||
    someName == `Eq.rec ||
    someName == `HEq.rec ||
    someName == `HEq.ndrec ||
    someName == `HEq.subst ||
    someName == `cast ||
    someName == `Eq.subst ||
    someName == `Eq.symm ||
    someName == `HEq.symm

/-- Whether a decl name lives inside a kernel-tier production module
where cast operators get scrutinised by this gate. -/
def isKernelTierProductionDecl (declName : Name) : Bool :=
  (`LeanFX2.Term).isPrefixOf declName ||
    (`LeanFX2.Foundation).isPrefixOf declName ||
    (`LeanFX2.Reduction).isPrefixOf declName ||
    (`LeanFX2.Confluence).isPrefixOf declName ||
    (`LeanFX2.HoTT).isPrefixOf declName ||
    (`LeanFX2.Cubical).isPrefixOf declName ||
    (`LeanFX2.Modal).isPrefixOf declName ||
    (`LeanFX2.Graded).isPrefixOf declName

/-- Collect cast operators referenced by one decl's closure. -/
def collectCastOperatorDependencies
    (environment : Environment) (targetName : Name) :
    Array Name :=
  let dependencyNames :=
    collectDependencies environment targetName (includeStdlib := true)
  dependencyNames.toList.foldl
    (init := (#[] : Array Name))
    (fun castDependencies dependencyName =>
      if isCastOperatorName dependencyName then
        castDependencies.push dependencyName
      else
        castDependencies)

/-- Build-failing budget gate counting kernel-tier decls whose closure
references a cast operator.  Pins current debt; new casts in the
kernel push the count above the ceiling and fail. -/
elab "#assert_cast_operator_dependent_budget " namespaceSyntax:ident
    castDebtBudgetSyntax:num : command => do
  let environment ← getEnv
  let namespaceName := namespaceSyntax.getId
  let castDebtBudget := castDebtBudgetSyntax.getNat
  let targetNames := namespaceAuditTargets environment namespaceName
  let mut violations : Array (Name × Array Name) := #[]
  for targetName in targetNames do
    if !isKernelTierProductionDecl targetName then
      continue
    let castDependencies :=
      collectCastOperatorDependencies environment targetName
    if !castDependencies.isEmpty then
      violations := violations.push (targetName, castDependencies)
  recordAuditCount `cast_operator_dependent violations.size
  if violations.size <= castDebtBudget then
    logInfo
      (s!"cast-operator dependent budget ok: {namespaceName} " ++
      s!"({violations.size}/{castDebtBudget} kernel-tier decls reference " ++
      "cast operators)")
  else
    let perDeclLines := violations.toList.take 20 |>.map fun (declName, _) =>
      s!"  - {declName}"
    let header :=
      s!"cast-operator dependent budget FAILED for {namespaceName}: " ++
      s!"{violations.size} kernel-tier dependents exceed budget " ++
      s!"{castDebtBudget}"
    let suffix :=
      if violations.size > 20 then
        s!"\n  ... and {violations.size - 20} more"
      else ""
    throwError (header ++ "\n" ++ String.intercalate "\n" perDeclLines ++ suffix)

/-! ## Forbidden-shape decl count

CLAUDE.md bans `noncomputable`, `@[extern]`, `@[implemented_by]`, and
strongly discourages `partial def` / `opaque` (without rfl-reducible
body) / `unsafe def` for kernel theorems.  The existing strict audit
catches noncomputable and extern attributes; this gate widens the lens
to `partial`, `opaque`, and `unsafe` constant-info shapes for kernel
namespaces (which should never use these).

A `partial` def is rejected because it bypasses Lean's termination
checker; an `opaque` decl is rejected because callers cannot reduce
through it; an `unsafe` def is rejected because Lean does not check
it.  None should appear in the kernel.
-/

/-- Forbidden constant-info shape detected on a kernel decl. -/
inductive ForbiddenDeclShape : Type
  /-- `partial def` — bypasses termination checker. -/
  | partialDef : ForbiddenDeclShape
  /-- `opaque` — callers cannot reduce through. -/
  | opaqueDef : ForbiddenDeclShape
  /-- `unsafe` — Lean does not type-check. -/
  | unsafeDef : ForbiddenDeclShape
  deriving Inhabited, Repr

namespace ForbiddenDeclShape

/-- Render the shape for diagnostics. -/
def format : ForbiddenDeclShape → String
  | .partialDef => "partial"
  | .opaqueDef => "opaque"
  | .unsafeDef => "unsafe"

end ForbiddenDeclShape

/-- Detect a forbidden constant-info shape on a kernel decl.  Returns
`none` when the decl uses one of the permitted shapes (`def`,
`theorem`, `inductive`, `structure`, `instance`). -/
def forbiddenDeclShape?
    (environment : Environment) (declName : Name) :
    Option ForbiddenDeclShape :=
  match environment.find? declName with
  | some (.opaqueInfo opaqueInfo) =>
      -- `opaque` decls survive only with `isUnsafe := false` and a
      -- definitional value; treat any non-unsafe opaque as forbidden in
      -- the kernel.  Unsafe opaque is a stronger violation handled below.
      if opaqueInfo.isUnsafe then some .unsafeDef
      else some .opaqueDef
  | some (.defnInfo defnInfo) =>
      -- partial defs surface via `definitionVal.safety` field.
      match defnInfo.safety with
      | .partial => some .partialDef
      | .unsafe => some .unsafeDef
      | _ => none
  | _ => none

/-- Build-failing budget gate counting forbidden-shape decls in kernel
tier namespaces.  Pins current count; the kernel target is zero. -/
elab "#assert_forbidden_decl_shape_budget " namespaceSyntax:ident
    shapeDebtBudgetSyntax:num : command => do
  let environment ← getEnv
  let namespaceName := namespaceSyntax.getId
  let shapeDebtBudget := shapeDebtBudgetSyntax.getNat
  let targetNames := namespaceAuditTargets environment namespaceName
  let mut violations : Array (Name × ForbiddenDeclShape) := #[]
  for targetName in targetNames do
    if !isKernelTierProductionDecl targetName then
      continue
    match forbiddenDeclShape? environment targetName with
    | some shape => violations := violations.push (targetName, shape)
    | none => pure ()
  recordAuditCount `forbidden_decl_shape violations.size
  if violations.size <= shapeDebtBudget then
    logInfo
      (s!"forbidden decl shape budget ok: {namespaceName} " ++
      s!"({violations.size}/{shapeDebtBudget} kernel decls use " ++
      "partial/opaque/unsafe)")
  else
    let perDeclLines := violations.toList.map fun (declName, shape) =>
      s!"  - {declName}: {shape.format}"
    let header :=
      s!"forbidden decl shape budget FAILED for {namespaceName}: " ++
      s!"{violations.size} kernel-tier decls exceed budget " ++
      s!"{shapeDebtBudget}"
    throwError (header ++ "\n" ++ String.intercalate "\n" perDeclLines)

/-! ## All-raw-payload Term ctor count

A Term constructor whose every explicit (default-binder) parameter has
type starting with `LeanFX2.RawTerm` or `Nat` is structurally
untyped — its arguments do not carry typing constraints.  Such ctors
are typing wrappers around raw syntax: they exist in the typed Term
inductive but enforce no real typing discipline beyond the result Ty.

Today's known examples include the `*Code` ctors (arrowCode, piTyCode,
sigmaTyCode, productCode, sumCode, listCode, optionCode, eitherCode,
idCode, equivCode) and the manufactured-witness ctors (equivReflId,
funextRefl, equivReflIdAtId, funextReflAtId, uaIntroHet,
funextIntroHet) when they accept only schematic raw payloads.

The gate pins the current count so future ctors with all-raw payloads
must come with explicit budget revision.
-/

/-- Whether a constructor parameter type is one of the all-raw-payload
shapes counted by this gate. -/
def isAllRawPayloadParameterType (parameterType : Expr) : Bool :=
  match parameterType.getAppFn with
  | .const typeName _ =>
      typeName == `LeanFX2.RawTerm ||
        typeName == `Nat ||
        typeName == `LeanFX2.UniverseLevel
  | _ => false

/-- Whether every default (explicit) binder in a constructor type has
an all-raw-payload type.  Implicit binders are skipped — they carry
the family indices `{mode level scope context ...}` which are
naturally raw. -/
partial def hasAllRawPayloadExplicitBinders (constructorType : Expr) :
    Bool :=
  let rec sweep (currentType : Expr) (sawExplicit : Bool) :
      Bool := Id.run do
    match currentType with
    | .forallE _ parameterType bodyType binderInfo =>
        match binderInfo with
        | .default =>
            if isAllRawPayloadParameterType parameterType then
              sweep bodyType true
            else
              false
        | _ => sweep bodyType sawExplicit
    | _ => sawExplicit
  sweep constructorType false

/-- Report all-raw-payload debt for one Term ctor. -/
def allRawPayloadDebtRecord?
    (environment : Environment) (constructorName : Name) :
    Option SignatureDebtRecord :=
  match environment.find? constructorName with
  | some (.ctorInfo constructorInfo) =>
      if hasAllRawPayloadExplicitBinders constructorInfo.type then
        some {
          constructorName := constructorName
          detail := "every explicit binder is RawTerm/Nat/UniverseLevel"
        }
      else
        none
  | _ => none

/-- Collect all-raw-payload debt records across a Term inductive. -/
def allRawPayloadDebtRecordsForInductive
    (environment : Environment) (inductiveName : Name) :
    Array SignatureDebtRecord :=
  let constructorNames := getInductiveConstructorNames environment inductiveName
  constructorNames.foldl
    (init := (#[] : Array SignatureDebtRecord))
    (fun records constructorName =>
      match allRawPayloadDebtRecord? environment constructorName with
      | some record => records.push record
      | none => records)

/-- Build-failing budget gate for Term ctors whose every explicit binder
is a raw-payload type.  Pins current debt; new ctors of this shape must
deliberately revise the budget. -/
elab "#assert_all_raw_payload_budget " inductiveSyntax:ident
    allRawDebtBudgetSyntax:num : command => do
  let environment ← getEnv
  let inductiveName := inductiveSyntax.getId
  let allRawDebtBudget := allRawDebtBudgetSyntax.getNat
  let records :=
    allRawPayloadDebtRecordsForInductive environment inductiveName
  if records.size <= allRawDebtBudget then
    logInfo
      (s!"all-raw-payload budget ok: {inductiveName} " ++
      s!"({records.size}/{allRawDebtBudget} ctors are structurally " ++
      "untyped wrappers)")
  else
    let perCtorLines := records.toList.map fun record =>
      s!"  - {record.constructorName}: {record.detail}"
    let header :=
      s!"all-raw-payload budget FAILED for {inductiveName}: " ++
      s!"{records.size} all-raw-payload ctors exceed budget " ++
      s!"{allRawDebtBudget}"
    throwError (header ++ "\n" ++ String.intercalate "\n" perCtorLines)

/-! ## Single-step Conv claim detector

A theorem named `<X>` whose result type is `Conv ...` and whose body
reduces to `Conv.fromStep <stepRule>` is a single-step Conv claim — it
asserts convertibility but only via one reduction step.  Real
mathematical Conv claims chain through `Conv.trans` / `Conv.sym` /
`Conv.fromStepStar` and are NOT collapsible to a single Step.fromStep
application.

This gate counts theorems in kernel namespaces whose definitional
unfolding is exactly `Conv.fromStep <const>`.  Pinning catches
"Theorem X = Conv.fromStep RuleY" claims that pretend more than they
prove.
-/

/-- Whether a Conv-typed theorem's body unwraps to a single
`Conv.fromStep` application.  We detect by stripping outer lambdas
(implicit binders for `mode level scope context` etc.) and checking
the resulting head is `LeanFX2.Conv.fromStep`. -/
partial def isSingleStepConvBody (bodyExpr : Expr) : Bool :=
  match bodyExpr with
  | .lam _ _ innerBody _ => isSingleStepConvBody innerBody
  | .mdata _ innerBody => isSingleStepConvBody innerBody
  | .letE _ _ _ innerBody _ => isSingleStepConvBody innerBody
  | .app _ _ =>
      match bodyExpr.getAppFn with
      | .const headName _ =>
          headName == `LeanFX2.Conv.fromStep ||
            headName == `LeanFX2.Conv.fromStepStar
      | _ => false
  | _ => false

/-- Whether a theorem's claimed result type mentions `LeanFX2.Conv`. -/
def claimsConvType (constantInfo : ConstantInfo) : Bool :=
  doesExprMentionConst `LeanFX2.Conv constantInfo.type

/-- Build-failing budget gate counting Conv-typed theorems whose body
collapses to a single `Conv.fromStep` / `Conv.fromStepStar`.  Pins
current debt; new single-step Conv claims push the count over and
fail. -/
elab "#assert_single_step_conv_claim_budget " namespaceSyntax:ident
    convClaimBudgetSyntax:num : command => do
  let environment ← getEnv
  let namespaceName := namespaceSyntax.getId
  let convClaimBudget := convClaimBudgetSyntax.getNat
  let targetNames := namespaceAuditTargets environment namespaceName
  let mut violations : Array Name := #[]
  for targetName in targetNames do
    match environment.find? targetName with
    | some constantInfo =>
        if claimsConvType constantInfo then
          match constantInfo.value? with
          | some bodyExpr =>
              if isSingleStepConvBody bodyExpr then
                violations := violations.push targetName
          | none => pure ()
    | none => pure ()
  recordAuditCount `single_step_conv_claim violations.size
  if violations.size <= convClaimBudget then
    logInfo
      (s!"single-step Conv claim budget ok: {namespaceName} " ++
      s!"({violations.size}/{convClaimBudget} Conv-typed theorems " ++
      "collapse to one Step)")
  else
    let perDeclLines := violations.toList.take 20 |>.map fun declName =>
      s!"  - {declName}"
    let header :=
      s!"single-step Conv claim budget FAILED for {namespaceName}: " ++
      s!"{violations.size} single-step Conv claims exceed budget " ++
      s!"{convClaimBudget}"
    let suffix :=
      if violations.size > 20 then
        s!"\n  ... and {violations.size - 20} more"
      else ""
    throwError (header ++ "\n" ++ String.intercalate "\n" perDeclLines ++ suffix)

/-! ## Reduction.Compat per-Step.par-cong coverage

For every parallel-reduction cong rule `Step.par.<name>Cong`, the
Reduction.Compat layer must ship `<name>Cong.rename_compatible` and
`<name>Cong.subst_compatible` lemmas (or equivalents).  These are the
substitution-stability witnesses that make confluence go through.

Without rename_compatible, parallel reduction can step a term but the
renaming `t.rename rho` does not necessarily step in parallel — that
breaks the cd_lemma cascade.  Without subst_compatible, the diamond
property fails for any β/ι rule that uses substitution.

The gate counts Step.par cong rules that lack one or both compat
mirrors in the loaded environment.  Two expected names per cong rule;
either both must exist or the rule contributes one debt unit.
-/

/-- Expected rename-compatibility lemma name for a Step.par cong rule. -/
def expectedRenameCompatibleName (parCongName : Name) : Name :=
  Name.str parCongName "rename_compatible"

/-- Expected subst-compatibility lemma name for a Step.par cong rule. -/
def expectedSubstCompatibleName (parCongName : Name) : Name :=
  Name.str parCongName "subst_compatible"

/-- Whether a Step.par cong rule has BOTH compat lemmas in the
environment.  Names are derived by suffixing
`.rename_compatible` and `.subst_compatible` to the cong rule's full
name. -/
def hasFullCompatCoverage
    (environment : Environment) (parCongName : Name) : Bool :=
  environment.contains (expectedRenameCompatibleName parCongName) &&
    environment.contains (expectedSubstCompatibleName parCongName)

/-- Report Reduction.Compat coverage debt for one Step.par cong rule. -/
def reductionCompatCoverageDebtRecord?
    (environment : Environment) (parCongName : Name) :
    Option SignatureDebtRecord :=
  let lastSegment := Name.lastSegmentString parCongName
  if !lastSegment.endsWith "Cong" then
    none
  else if hasFullCompatCoverage environment parCongName then
    none
  else
    let renameName := expectedRenameCompatibleName parCongName
    let substName := expectedSubstCompatibleName parCongName
    some {
      constructorName := parCongName
      detail :=
        s!"missing one or both of {renameName} / {substName}"
    }

/-- Collect Reduction.Compat coverage debt for every Step.par
constructor in the inductive. -/
def reductionCompatCoverageDebtRecordsForInductive
    (environment : Environment) (parInductiveName : Name) :
    Array SignatureDebtRecord :=
  let constructorNames :=
    getInductiveConstructorNames environment parInductiveName
  constructorNames.foldl
    (init := (#[] : Array SignatureDebtRecord))
    (fun records parCongName =>
      match reductionCompatCoverageDebtRecord? environment parCongName with
      | some record => records.push record
      | none => records)

/-- Build-failing budget gate for Step.par cong rules whose
Reduction.Compat lemmas are absent.  Pins current debt; new cong
rules without compat lemmas push the count and fail. -/
elab "#assert_reduction_compat_coverage_budget " parInductiveSyntax:ident
    compatCoverageBudgetSyntax:num : command => do
  let environment ← getEnv
  let parInductiveName := parInductiveSyntax.getId
  let compatCoverageBudget := compatCoverageBudgetSyntax.getNat
  let records :=
    reductionCompatCoverageDebtRecordsForInductive
      environment parInductiveName
  if records.size <= compatCoverageBudget then
    logInfo
      (s!"reduction-compat coverage budget ok: {parInductiveName} " ++
      s!"({records.size}/{compatCoverageBudget} cong rules lack " ++
      "rename_compatible or subst_compatible)")
  else
    let perRuleLines := records.toList.take 20 |>.map fun record =>
      s!"  - {record.constructorName}: {record.detail}"
    let header :=
      s!"reduction-compat coverage budget FAILED for " ++
      s!"{parInductiveName}: {records.size} cong rules exceed budget " ++
      s!"{compatCoverageBudget}"
    let suffix :=
      if records.size > 20 then
        s!"\n  ... and {records.size - 20} more"
      else ""
    throwError (header ++ "\n" ++ String.intercalate "\n" perRuleLines ++ suffix)


end LeanFX2.Tools
