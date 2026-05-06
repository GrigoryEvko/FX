import LeanFX2.Tools.StrictHarness.Common

namespace LeanFX2.Tools

open Lean Elab Command

/-! ## Schematic-payload budget check -/

/-- Counts of explicit schematic payload types in constructor signatures. -/
structure SchematicPayloadCounts where
  rawTermPayloadCount : Nat := 0
  natPayloadCount : Nat := 0
  deriving Inhabited, Repr

namespace SchematicPayloadCounts

/-- Pointwise addition for schematic-payload counts. -/
def add
    (leftCounts rightCounts : SchematicPayloadCounts) :
    SchematicPayloadCounts :=
  {
    rawTermPayloadCount :=
      leftCounts.rawTermPayloadCount + rightCounts.rawTermPayloadCount
    natPayloadCount :=
      leftCounts.natPayloadCount + rightCounts.natPayloadCount
  }

/-- Whether any schematic payload was counted. -/
def hasAnyPayload (payloadCounts : SchematicPayloadCounts) : Bool :=
  payloadCounts.rawTermPayloadCount != 0 ||
    payloadCounts.natPayloadCount != 0

/-- Render counts for build-log diagnostics. -/
def format (payloadCounts : SchematicPayloadCounts) : String :=
  s!"RawTerm={payloadCounts.rawTermPayloadCount}, Nat={payloadCounts.natPayloadCount}"

end SchematicPayloadCounts

/-- Schematic payload kind recognized by the constructor census. -/
inductive SchematicPayloadKind : Type
  /-- Explicit `RawTerm` payload; this usually means a typed constructor is
  carrying untyped syntax as trusted data. -/
  | rawTerm : SchematicPayloadKind
  /-- Explicit `Nat` payload; this often means an unstructured tag or arity
  escaped a richer schema. -/
  | nat : SchematicPayloadKind
  deriving Inhabited, Repr

/-- Classify a constructor parameter type as a schematic payload type. -/
def schematicPayloadKind? (parameterType : Expr) :
    Option SchematicPayloadKind :=
  match parameterType.getAppFn with
  | .const typeName _ =>
      if typeName == `LeanFX2.RawTerm then
        some SchematicPayloadKind.rawTerm
      else if typeName == `Nat then
        some SchematicPayloadKind.nat
      else
        none
  | _ => none

/-- Turn one recognized schematic payload into a singleton count. -/
def countForSchematicPayloadKind
    (payloadKind : SchematicPayloadKind) :
    SchematicPayloadCounts :=
  match payloadKind with
  | .rawTerm => { rawTermPayloadCount := 1 }
  | .nat => { natPayloadCount := 1 }

/-- Count explicit schematic payloads in a constructor type.

Implicit parameters are skipped so family indices such as `{scope : Nat}` do
not pollute the budget.  The audit is intentionally focused on explicit data
the constructor accepts from callers. -/
partial def countExplicitSchematicPayloads (constructorType : Expr) :
    SchematicPayloadCounts :=
  match constructorType with
  | .forallE _ parameterType bodyType binderInfo =>
      let bodyCounts := countExplicitSchematicPayloads bodyType
      let parameterCounts :=
        match binderInfo with
        | .default =>
            match schematicPayloadKind? parameterType with
            | some payloadKind => countForSchematicPayloadKind payloadKind
            | none => {}
        | _ => {}
      parameterCounts.add bodyCounts
  | _ => {}

/-- One constructor that contributes to the schematic-payload budget. -/
structure SchematicPayloadRecord where
  /-- Constructor name being reported. -/
  constructorName : Name
  /-- Counts contributed by this constructor. -/
  payloadCounts : SchematicPayloadCounts
  deriving Inhabited, Repr

/-- Count schematic payloads for one constructor if it exists. -/
def schematicPayloadRecord?
    (environment : Environment) (constructorName : Name) :
    Option SchematicPayloadRecord :=
  match environment.find? constructorName with
  | some (.ctorInfo constructorInfo) =>
      let payloadCounts :=
        countExplicitSchematicPayloads constructorInfo.type
      if payloadCounts.hasAnyPayload then
        some {
          constructorName := constructorName
          payloadCounts := payloadCounts
        }
      else
        none
  | _ => none

/-- Collect schematic-payload records for every constructor of an inductive. -/
def schematicPayloadRecordsForInductive
    (environment : Environment) (inductiveName : Name) :
    Array SchematicPayloadRecord :=
  let constructorNames := getInductiveConstructorNames environment inductiveName
  constructorNames.foldl
    (init := (#[] : Array SchematicPayloadRecord))
    (fun records constructorName =>
      match schematicPayloadRecord? environment constructorName with
      | some record => records.push record
      | none => records)

/-- Total schematic-payload counts across a record list. -/
def totalSchematicPayloadCounts
    (records : Array SchematicPayloadRecord) :
    SchematicPayloadCounts :=
  records.foldl
    (init := ({} : SchematicPayloadCounts))
    (fun payloadCounts record =>
      payloadCounts.add record.payloadCounts)

/-- Build-failing budget gate for explicit schematic payloads in an inductive's
constructors.  Budgets are ceilings: existing debt may be recorded, but new
explicit `RawTerm` or `Nat` payloads fail the build until the budget is
deliberately revised. -/
elab "#assert_schematic_payload_budget " inductiveSyntax:ident
    rawTermBudgetSyntax:num natBudgetSyntax:num : command => do
  let environment ← getEnv
  let inductiveName := inductiveSyntax.getId
  let rawTermPayloadBudget := rawTermBudgetSyntax.getNat
  let natPayloadBudget := natBudgetSyntax.getNat
  let records := schematicPayloadRecordsForInductive environment inductiveName
  let totalCounts := totalSchematicPayloadCounts records
  let isWithinBudget :=
    totalCounts.rawTermPayloadCount <= rawTermPayloadBudget &&
      totalCounts.natPayloadCount <= natPayloadBudget
  if isWithinBudget then
    let successMessage :=
      s!"schematic payload budget ok: {inductiveName} " ++
      s!"({totalCounts.format}; budget RawTerm={rawTermPayloadBudget}, " ++
      s!"Nat={natPayloadBudget}; payload ctors={records.size})"
    logInfo successMessage
  else
    let perCtorLines := records.toList.map fun record =>
      s!"  - {record.constructorName}: {record.payloadCounts.format}"
    let header :=
      s!"schematic payload budget FAILED for {inductiveName}: " ++
      s!"actual {totalCounts.format}; " ++
      s!"budget RawTerm={rawTermPayloadBudget}, Nat={natPayloadBudget}"
    throwError (header ++ "\n" ++ String.intercalate "\n" perCtorLines)

/-! ## Mode-discipline budget check -/

/-- Required mode for constructors that should not be available in every mode. -/
inductive RequiredMode : Type
  /-- Constructor should be restricted to the strict fragment. -/
  | strict : RequiredMode
  /-- Constructor should be restricted to the univalent/cubical fragment. -/
  | univalent : RequiredMode
  deriving Inhabited, Repr

namespace RequiredMode

/-- The concrete `Mode` constructor that witnesses this requirement. -/
def modeConstructorName : RequiredMode → Name
  | .strict => `LeanFX2.Mode.strict
  | .univalent => `LeanFX2.Mode.univalent

/-- Human-readable name for diagnostics. -/
def format : RequiredMode → String
  | .strict => "Mode.strict"
  | .univalent => "Mode.univalent"

end RequiredMode

/-- Whether an expression mentions a specific constant anywhere inside it. -/
partial def doesExprMentionConst (targetName : Name) : Expr → Bool
  | .const constantName _ => constantName == targetName
  | .app functionExpr argumentExpr =>
      doesExprMentionConst targetName functionExpr ||
        doesExprMentionConst targetName argumentExpr
  | .lam _ parameterType bodyType _ =>
      doesExprMentionConst targetName parameterType ||
        doesExprMentionConst targetName bodyType
  | .forallE _ parameterType bodyType _ =>
      doesExprMentionConst targetName parameterType ||
        doesExprMentionConst targetName bodyType
  | .letE _ typeExpr valueExpr bodyExpr _ =>
      doesExprMentionConst targetName typeExpr ||
        doesExprMentionConst targetName valueExpr ||
        doesExprMentionConst targetName bodyExpr
  | .mdata _ bodyExpr => doesExprMentionConst targetName bodyExpr
  | .proj _ _ bodyExpr => doesExprMentionConst targetName bodyExpr
  | _ => false

/-- Whether a parameter type is an equality premise to the required mode. -/
def isModeRequirementEquality
    (requiredMode : RequiredMode) (parameterType : Expr) :
    Bool :=
  match parameterType.getAppFn with
  | .const equalityName _ =>
      equalityName == `Eq &&
        doesExprMentionConst requiredMode.modeConstructorName parameterType
  | _ => false

/-- Detect whether a constructor type already carries the required mode proof. -/
partial def hasRequiredModePremise
    (requiredMode : RequiredMode) (constructorType : Expr) :
    Bool :=
  match constructorType with
  | .forallE _ parameterType bodyType _ =>
      isModeRequirementEquality requiredMode parameterType ||
        hasRequiredModePremise requiredMode bodyType
  | _ => false

/-- Expected mode restriction for the current known mode-sensitive Term ctors. -/
def requiredModeForConstructor? (constructorName : Name) :
    Option RequiredMode :=
  let suffix := Name.lastSegmentString constructorName
  if suffix == "idStrictRefl" ||
      suffix == "idStrictRec" then
    some RequiredMode.strict
  else if suffix == "pathLam" ||
      suffix == "pathApp" ||
      suffix == "glueIntro" ||
      suffix == "glueElim" ||
      suffix == "transp" ||
      suffix == "hcomp" then
    some RequiredMode.univalent
  else
    none

/-- One constructor whose mode-sensitive typing still accepts arbitrary mode. -/
structure ModeDisciplineDebtRecord where
  /-- Constructor name being reported. -/
  constructorName : Name
  /-- Mode the constructor should require. -/
  requiredMode : RequiredMode
  deriving Inhabited, Repr

/-- Report a mode-sensitive constructor if it lacks the required mode premise. -/
def modeDisciplineDebtRecord?
    (environment : Environment) (constructorName : Name) :
    Option ModeDisciplineDebtRecord :=
  match requiredModeForConstructor? constructorName, environment.find? constructorName with
  | some requiredMode, some (.ctorInfo constructorInfo) =>
      if hasRequiredModePremise requiredMode constructorInfo.type then
        none
      else
        some {
          constructorName := constructorName
          requiredMode := requiredMode
        }
  | _, _ => none

/-- Collect mode-discipline debt records for every constructor of an inductive. -/
def modeDisciplineDebtRecordsForInductive
    (environment : Environment) (inductiveName : Name) :
    Array ModeDisciplineDebtRecord :=
  let constructorNames := getInductiveConstructorNames environment inductiveName
  constructorNames.foldl
    (init := (#[] : Array ModeDisciplineDebtRecord))
    (fun records constructorName =>
      match modeDisciplineDebtRecord? environment constructorName with
      | some record => records.push record
      | none => records)

/-- Build-failing budget gate for constructors that should be mode-restricted
but currently accept arbitrary mode.  The budget is a ceiling over known debt:
as ctors gain real mode premises the count should fall, and new unrestricted
mode-sensitive ctors must deliberately revise this number. -/
elab "#assert_mode_discipline_budget " inductiveSyntax:ident
    modeDebtBudgetSyntax:num : command => do
  let environment ← getEnv
  let inductiveName := inductiveSyntax.getId
  let modeDebtBudget := modeDebtBudgetSyntax.getNat
  let records := modeDisciplineDebtRecordsForInductive environment inductiveName
  if records.size <= modeDebtBudget then
    let successMessage :=
      s!"mode discipline budget ok: {inductiveName} " ++
      s!"({records.size}/{modeDebtBudget} mode-sensitive ctors lack " ++
      "mode equality premises)"
    logInfo successMessage
  else
    let perCtorLines := records.toList.map fun record =>
      s!"  - {record.constructorName}: expected {record.requiredMode.format} equality premise"
    let header :=
      s!"mode discipline budget FAILED for {inductiveName}: " ++
      s!"{records.size} unrestricted mode-sensitive ctors exceed budget " ++
      s!"{modeDebtBudget}"
    throwError (header ++ "\n" ++ String.intercalate "\n" perCtorLines)

/-! ## Semantic-signature debt gates -/

/-- One constructor-level semantic signature debt record. -/
structure SignatureDebtRecord where
  /-- Constructor name being reported. -/
  constructorName : Name
  /-- Human-readable description of the missing signature obligation. -/
  detail : String
  deriving Inhabited, Repr

/-- Whether a constructor is one of the eliminators that currently use a fixed
`motiveType` where the real dependent eliminator needs a motive family. -/
def isDependentEliminatorConstructorName (constructorName : Name) : Bool :=
  let suffix := Name.lastSegmentString constructorName
  suffix == "boolElim" ||
    suffix == "natElim" ||
    suffix == "natRec" ||
    suffix == "listElim" ||
    suffix == "optionMatch" ||
    suffix == "eitherMatch" ||
    suffix == "idJ" ||
    suffix == "oeqJ" ||
    suffix == "idStrictRec"

/-- Whether the second argument applied to `LeanFX2.Ty` extends the surrounding
scope (i.e. the motive family lives in `scope + 1`).  A genuinely dependent
eliminator's motive is parameterised over an extra context entry, so its scope
index is no longer a bare variable: it is `Nat.succ <scope>`, `<scope> + 1`,
`<scope>.succ`, or any other expression that wraps the scope variable in
additional structure.

Returns `true` when the motive parameter type is `Ty <level> (<scope> + 1)`
or any equivalent shape; `false` when it is the bare-variable form
`Ty <level> <scope>` that still characterises a fixed-motive eliminator. -/
def hasExtendedScopeMotiveArg (parameterType : Expr) : Bool :=
  match parameterType with
  | .app (.app (.const tyName _) _levelArg) scopeArg =>
      if tyName != `LeanFX2.Ty then false
      else
        match scopeArg with
        | .bvar _ => false
        | .fvar _ => false
        | .mvar _ => false
        | _ => true
  | _ => false

/-- Whether a constructor type still binds a fixed `motiveType : Ty level scope`
parameter, indicating non-dependent eliminator debt.  Refactored eliminators
whose motive parameter has type `Ty level (scope + 1)` -- a genuine dependent
motive family -- are NOT flagged: the extended-scope index is the marker that
the eliminator already accepts a motive family parameterised over the
scrutinee's value, which is the desired shape.

Heuristic: traverse the constructor's pi-telescope.  For each binder named
`motiveType` whose parameter type mentions `LeanFX2.Ty`, classify the parameter
type via `hasExtendedScopeMotiveArg`.  Bare-scope-index motives are debt;
extended-scope motives are correctly dependent and produce `false` here. -/
partial def hasFixedMotiveTypeBinder (constructorType : Expr) : Bool :=
  match constructorType with
  | .forallE binderName parameterType bodyType _ =>
      let isFixedMotiveBinder :=
        Name.lastSegmentString binderName == "motiveType" &&
          doesExprMentionConst `LeanFX2.Ty parameterType &&
          !hasExtendedScopeMotiveArg parameterType
      isFixedMotiveBinder || hasFixedMotiveTypeBinder bodyType
  | _ => false

/-- Report dependent-eliminator motive debt for one constructor. -/
def dependentEliminatorDebtRecord?
    (environment : Environment) (constructorName : Name) :
    Option SignatureDebtRecord :=
  if !isDependentEliminatorConstructorName constructorName then
    none
  else
    match environment.find? constructorName with
    | some (.ctorInfo constructorInfo) =>
        if hasFixedMotiveTypeBinder constructorInfo.type then
          some {
            constructorName := constructorName
            detail := "fixed motiveType binder; expected dependent motive family"
          }
        else
          none
    | _ => none

/-- Collect dependent-eliminator motive debt records for an inductive. -/
def dependentEliminatorDebtRecordsForInductive
    (environment : Environment) (inductiveName : Name) :
    Array SignatureDebtRecord :=
  let constructorNames := getInductiveConstructorNames environment inductiveName
  constructorNames.foldl
    (init := (#[] : Array SignatureDebtRecord))
    (fun records constructorName =>
      match dependentEliminatorDebtRecord? environment constructorName with
      | some record => records.push record
      | none => records)

/-- Build-failing budget gate for fixed-motive eliminator debt. -/
elab "#assert_dependent_eliminator_motive_budget " inductiveSyntax:ident
    motiveDebtBudgetSyntax:num : command => do
  let environment ← getEnv
  let inductiveName := inductiveSyntax.getId
  let motiveDebtBudget := motiveDebtBudgetSyntax.getNat
  let records := dependentEliminatorDebtRecordsForInductive environment inductiveName
  if records.size <= motiveDebtBudget then
    logInfo
      (s!"dependent eliminator motive budget ok: {inductiveName} " ++
      s!"({records.size}/{motiveDebtBudget} fixed-motive eliminators)")
  else
    let perCtorLines := records.toList.map fun record =>
      s!"  - {record.constructorName}: {record.detail}"
    let header :=
      s!"dependent eliminator motive budget FAILED for {inductiveName}: " ++
      s!"{records.size} fixed-motive eliminators exceed budget " ++
      s!"{motiveDebtBudget}"
    throwError (header ++ "\n" ++ String.intercalate "\n" perCtorLines)

/-- Explicit parameter names that are currently used as proof/tag placeholders
while carrying only `Term context Ty.unit ...`. -/
def isKnownUnitPlaceholderBinderName (binderName : Name) : Bool :=
  let suffix := Name.lastSegmentString binderName
  suffix == "predicateProof" ||
    suffix == "operationTag" ||
    suffix == "pointwiseProof"

/-- Whether a parameter type is a typed term whose asserted type is `Ty.unit`. -/
def isTermAtUnitType (parameterType : Expr) : Bool :=
  doesExprMentionConst `LeanFX2.Term parameterType &&
    doesExprMentionConst `LeanFX2.Ty.unit parameterType

/-- Whether a constructor type still contains an explicit unit-typed
placeholder parameter. -/
partial def hasUnitTypedPlaceholderParameter (constructorType : Expr) : Bool :=
  match constructorType with
  | .forallE binderName parameterType bodyType binderInfo =>
      let currentBinderHasDebt :=
        match binderInfo with
        | .default =>
            isKnownUnitPlaceholderBinderName binderName &&
              isTermAtUnitType parameterType
        | _ => false
      currentBinderHasDebt || hasUnitTypedPlaceholderParameter bodyType
  | _ => false

/-- Report unit-typed proof/tag placeholder debt for one constructor. -/
def unitPlaceholderDebtRecord?
    (environment : Environment) (constructorName : Name) :
    Option SignatureDebtRecord :=
  match environment.find? constructorName with
  | some (.ctorInfo constructorInfo) =>
      if hasUnitTypedPlaceholderParameter constructorInfo.type then
        some {
          constructorName := constructorName
          detail := "explicit proof/tag placeholder is typed as Ty.unit"
        }
      else
        none
  | _ => none

/-- Collect unit-placeholder debt records for an inductive. -/
def unitPlaceholderDebtRecordsForInductive
    (environment : Environment) (inductiveName : Name) :
    Array SignatureDebtRecord :=
  let constructorNames := getInductiveConstructorNames environment inductiveName
  constructorNames.foldl
    (init := (#[] : Array SignatureDebtRecord))
    (fun records constructorName =>
      match unitPlaceholderDebtRecord? environment constructorName with
      | some record => records.push record
      | none => records)

/-- Build-failing budget gate for `Ty.unit` proof/tag placeholders. -/
elab "#assert_unit_placeholder_budget " inductiveSyntax:ident
    unitPlaceholderBudgetSyntax:num : command => do
  let environment ← getEnv
  let inductiveName := inductiveSyntax.getId
  let unitPlaceholderBudget := unitPlaceholderBudgetSyntax.getNat
  let records := unitPlaceholderDebtRecordsForInductive environment inductiveName
  if records.size <= unitPlaceholderBudget then
    logInfo
      (s!"unit-placeholder budget ok: {inductiveName} " ++
      s!"({records.size}/{unitPlaceholderBudget} unit-typed placeholders)")
  else
    let perCtorLines := records.toList.map fun record =>
      s!"  - {record.constructorName}: {record.detail}"
    let header :=
      s!"unit-placeholder budget FAILED for {inductiveName}: " ++
      s!"{records.size} unit-typed placeholders exceed budget " ++
      s!"{unitPlaceholderBudget}"
    throwError (header ++ "\n" ++ String.intercalate "\n" perCtorLines)

/-- Modal constructors that should mention `Ty.modal` once they stop being
typing no-ops. -/
def isModalNoopConstructorName (constructorName : Name) : Bool :=
  let suffix := Name.lastSegmentString constructorName
  suffix == "modIntro" ||
    suffix == "modElim" ||
    suffix == "subsume"

/-- Report modal no-op debt for one constructor. -/
def modalNoopDebtRecord?
    (environment : Environment) (constructorName : Name) :
    Option SignatureDebtRecord :=
  if !isModalNoopConstructorName constructorName then
    none
  else
    match environment.find? constructorName with
    | some (.ctorInfo constructorInfo) =>
        if doesExprMentionConst `LeanFX2.Ty.modal constructorInfo.type then
          none
        else
          some {
            constructorName := constructorName
            detail := "modal constructor type does not mention Ty.modal"
          }
    | _ => none

/-- Collect modal no-op debt records for an inductive. -/
def modalNoopDebtRecordsForInductive
    (environment : Environment) (inductiveName : Name) :
    Array SignatureDebtRecord :=
  let constructorNames := getInductiveConstructorNames environment inductiveName
  constructorNames.foldl
    (init := (#[] : Array SignatureDebtRecord))
    (fun records constructorName =>
      match modalNoopDebtRecord? environment constructorName with
      | some record => records.push record
      | none => records)

/-- Build-failing budget gate for modal constructors that preserve the inner
type instead of using `Ty.modal`. -/
elab "#assert_modal_noop_budget " inductiveSyntax:ident
    modalNoopBudgetSyntax:num : command => do
  let environment ← getEnv
  let inductiveName := inductiveSyntax.getId
  let modalNoopBudget := modalNoopBudgetSyntax.getNat
  let records := modalNoopDebtRecordsForInductive environment inductiveName
  if records.size <= modalNoopBudget then
    logInfo
      (s!"modal no-op budget ok: {inductiveName} " ++
      s!"({records.size}/{modalNoopBudget} modal ctors lack Ty.modal)")
  else
    let perCtorLines := records.toList.map fun record =>
      s!"  - {record.constructorName}: {record.detail}"
    let header :=
      s!"modal no-op budget FAILED for {inductiveName}: " ++
      s!"{records.size} modal no-op ctors exceed budget " ++
      s!"{modalNoopBudget}"
    throwError (header ++ "\n" ++ String.intercalate "\n" perCtorLines)

/-- Session constructors that should carry protocol continuation/transition
evidence once the core signature enforces session advance. -/
def isSessionAdvanceConstructorName (constructorName : Name) : Bool :=
  let suffix := Name.lastSegmentString constructorName
  suffix == "sessionSend" || suffix == "sessionRecv"

/-- Whether a binder name looks like protocol-advance evidence. -/
def isProtocolAdvanceBinderName (binderName : Name) : Bool :=
  let suffix := Name.lastSegmentString binderName
  suffix.contains "next" ||
    suffix.contains "Next" ||
    suffix.contains "continuation" ||
    suffix.contains "Continuation" ||
    suffix.contains "transition" ||
    suffix.contains "Transition"

/-- Whether a constructor type contains protocol-advance evidence by name. -/
partial def hasProtocolAdvanceBinder (constructorType : Expr) : Bool :=
  match constructorType with
  | .forallE binderName _ bodyType _ =>
      isProtocolAdvanceBinderName binderName ||
        hasProtocolAdvanceBinder bodyType
  | _ => false

/-- Report session no-advance debt for one constructor. -/
def sessionNoAdvanceDebtRecord?
    (environment : Environment) (constructorName : Name) :
    Option SignatureDebtRecord :=
  if !isSessionAdvanceConstructorName constructorName then
    none
  else
    match environment.find? constructorName with
    | some (.ctorInfo constructorInfo) =>
        if hasProtocolAdvanceBinder constructorInfo.type then
          none
        else
          some {
            constructorName := constructorName
            detail := "session constructor lacks protocol continuation evidence"
          }
    | _ => none

/-- Collect session no-advance debt records for an inductive. -/
def sessionNoAdvanceDebtRecordsForInductive
    (environment : Environment) (inductiveName : Name) :
    Array SignatureDebtRecord :=
  let constructorNames := getInductiveConstructorNames environment inductiveName
  constructorNames.foldl
    (init := (#[] : Array SignatureDebtRecord))
    (fun records constructorName =>
      match sessionNoAdvanceDebtRecord? environment constructorName with
      | some record => records.push record
      | none => records)

/-- Build-failing budget gate for session ctors that do not advance protocol. -/
elab "#assert_session_no_advance_budget " inductiveSyntax:ident
    sessionNoAdvanceBudgetSyntax:num : command => do
  let environment ← getEnv
  let inductiveName := inductiveSyntax.getId
  let sessionNoAdvanceBudget := sessionNoAdvanceBudgetSyntax.getNat
  let records := sessionNoAdvanceDebtRecordsForInductive environment inductiveName
  if records.size <= sessionNoAdvanceBudget then
    logInfo
      (s!"session no-advance budget ok: {inductiveName} " ++
      s!"({records.size}/{sessionNoAdvanceBudget} session ctors lack continuation)")
  else
    let perCtorLines := records.toList.map fun record =>
      s!"  - {record.constructorName}: {record.detail}"
    let header :=
      s!"session no-advance budget FAILED for {inductiveName}: " ++
      s!"{records.size} session no-advance ctors exceed budget " ++
      s!"{sessionNoAdvanceBudget}"
    throwError (header ++ "\n" ++ String.intercalate "\n" perCtorLines)

/-- Whether a constructor type contains a binder with the given final segment. -/
partial def hasBinderWithLastSegment
    (wantedSegment : String) (constructorType : Expr) :
    Bool :=
  match constructorType with
  | .forallE binderName _ bodyType _ =>
      Name.lastSegmentString binderName == wantedSegment ||
        hasBinderWithLastSegment wantedSegment bodyType
  | _ => false

/-- Report equivalence-introduction coherence debt for one constructor. -/
def equivCoherenceDebtRecord?
    (environment : Environment) (constructorName : Name) :
    Option SignatureDebtRecord :=
  if Name.lastSegmentString constructorName != "equivIntroHet" then
    none
  else
    match environment.find? constructorName with
    | some (.ctorInfo constructorInfo) =>
        let hasLeftInverse := hasBinderWithLastSegment "leftInv" constructorInfo.type
        let hasRightInverse := hasBinderWithLastSegment "rightInv" constructorInfo.type
        if hasLeftInverse && hasRightInverse then
          none
        else
          some {
            constructorName := constructorName
            detail := "equivalence intro lacks leftInv/rightInv coherence binders"
          }
    | _ => none

/-- Collect equivalence-coherence debt records for an inductive. -/
def equivCoherenceDebtRecordsForInductive
    (environment : Environment) (inductiveName : Name) :
    Array SignatureDebtRecord :=
  let constructorNames := getInductiveConstructorNames environment inductiveName
  constructorNames.foldl
    (init := (#[] : Array SignatureDebtRecord))
    (fun records constructorName =>
      match equivCoherenceDebtRecord? environment constructorName with
      | some record => records.push record
      | none => records)

/-- Build-failing budget gate for equivalence introduction without coherence. -/
elab "#assert_equiv_coherence_budget " inductiveSyntax:ident
    equivCoherenceBudgetSyntax:num : command => do
  let environment ← getEnv
  let inductiveName := inductiveSyntax.getId
  let equivCoherenceBudget := equivCoherenceBudgetSyntax.getNat
  let records := equivCoherenceDebtRecordsForInductive environment inductiveName
  if records.size <= equivCoherenceBudget then
    logInfo
      (s!"equiv coherence budget ok: {inductiveName} " ++
      s!"({records.size}/{equivCoherenceBudget} equiv intro ctors lack coherence)")
  else
    let perCtorLines := records.toList.map fun record =>
      s!"  - {record.constructorName}: {record.detail}"
    let header :=
      s!"equiv coherence budget FAILED for {inductiveName}: " ++
      s!"{records.size} equiv coherence debts exceed budget " ++
      s!"{equivCoherenceBudget}"
    throwError (header ++ "\n" ++ String.intercalate "\n" perCtorLines)

/-! ## Bridge constructor coverage budget -/

/-- Exact bridge theorem name expected for a `Term` constructor suffix. -/
def exactBridgeSoundnessNameForConstructor (constructorName : Name) : Name :=
  Name.str
    `LeanFX2.FX1Bridge
    ("encodeTermSound_" ++ Name.lastSegmentString constructorName)

/-- Raw constructor names that can witness an exact bridge for a `Term`
constructor.

Most typed constructors pin the same-suffix raw constructor.  Dependent and
non-dependent lambda/application share raw syntax, so `lamPi` and `appPi`
intentionally map to the same raw constructors as `lam` and `app`. -/
def expectedRawConstructorNamesForTermConstructor
    (constructorName : Name) :
    Array Name :=
  let constructorSuffix := Name.lastSegmentString constructorName
  let rawSuffix :=
    if constructorSuffix == "lamPi" then
      "lam"
    else if constructorSuffix == "appPi" then
      "app"
    else
      constructorSuffix
  #[Name.str `LeanFX2.RawTerm rawSuffix]

/-- One `Term` constructor without a certificate-shaped exact
`FX1Bridge.encodeTermSound_*` theorem.  Fragment-specific bridge lemmas are
useful, but this exact-name matrix is the ratchet for whole-constructor bridge
coverage. -/
structure BridgeCoverageDebtRecord where
  /-- Constructor name being reported. -/
  constructorName : Name
  /-- Exact bridge theorem name expected by the coverage matrix. -/
  expectedBridgeName : Name
  /-- Why the exact bridge theorem did not count. -/
  detail : String
  deriving Inhabited, Repr

/-- Whether an exact bridge coverage declaration has the minimum soundness
shape: it must consume/mention a rich `Term`, produce/mention an FX1
`HasType` derivation, and mention the raw constructor pinned by the covered
typed constructor.  This is still a shape check, not a proof of semantic
faithfulness; the separate round-trip gate checks certificate companions. -/
def isExactBridgeSoundnessShapeValid
    (constructorName : Name) (constantInfo : ConstantInfo) :
    Bool :=
  let expectedRawConstructors :=
    expectedRawConstructorNamesForTermConstructor constructorName
  doesExprMentionConst `LeanFX2.Term constantInfo.type &&
    doesExprMentionConst `LeanFX2.FX1.HasType constantInfo.type &&
    expectedRawConstructors.any
      (fun rawConstructorName =>
        doesExprMentionConst rawConstructorName constantInfo.type)

/-- Report bridge coverage debt for one constructor. -/
def bridgeCoverageDebtRecord?
    (environment : Environment) (constructorName : Name) :
    Option BridgeCoverageDebtRecord :=
  let expectedBridgeName := exactBridgeSoundnessNameForConstructor constructorName
  match environment.find? expectedBridgeName with
  | some constantInfo =>
      if isExactBridgeSoundnessShapeValid constructorName constantInfo then
        none
      else
        some {
          constructorName := constructorName
          expectedBridgeName := expectedBridgeName
          detail :=
            "declaration exists but is not Term/raw-ctor -> FX1.HasType shaped"
        }
  | none =>
      some {
        constructorName := constructorName
        expectedBridgeName := expectedBridgeName
        detail := "missing declaration"
      }

/-- Collect exact bridge coverage debt records for an inductive. -/
def bridgeCoverageDebtRecordsForInductive
    (environment : Environment) (inductiveName : Name) :
    Array BridgeCoverageDebtRecord :=
  let constructorNames := getInductiveConstructorNames environment inductiveName
  constructorNames.foldl
    (init := (#[] : Array BridgeCoverageDebtRecord))
    (fun records constructorName =>
      match bridgeCoverageDebtRecord? environment constructorName with
      | some record => records.push record
      | none => records)

/-- Build-failing budget gate for exact `encodeTermSound_*` constructor coverage.
This intentionally does not count narrower demo fragments as full constructor
coverage. -/
elab "#assert_bridge_exact_coverage_budget " inductiveSyntax:ident
    bridgeDebtBudgetSyntax:num : command => do
  let environment ← getEnv
  let inductiveName := inductiveSyntax.getId
  let bridgeDebtBudget := bridgeDebtBudgetSyntax.getNat
  let records := bridgeCoverageDebtRecordsForInductive environment inductiveName
  let constructorCount := getInductiveConstructorNames environment inductiveName |>.size
  let coveredCount := constructorCount - records.size
  if records.size <= bridgeDebtBudget then
    logInfo
      (s!"bridge exact coverage budget ok: {inductiveName} " ++
      s!"({coveredCount}/{constructorCount} exact bridge soundness theorems; " ++
      s!"debt {records.size}/{bridgeDebtBudget})")
  else
    let perCtorLines := records.toList.map fun record =>
      s!"  - {record.constructorName}: expected {record.expectedBridgeName}; " ++
      record.detail
    let header :=
      s!"bridge exact coverage budget FAILED for {inductiveName}: " ++
      s!"{records.size} unbridged ctors exceed budget {bridgeDebtBudget}"
    throwError (header ++ "\n" ++ String.intercalate "\n" perCtorLines)

/-! ## Rich schema and linkage debt gates -/

/-- Whether a binder name contains a specific substring. -/
partial def hasBinderContainingSegment
    (wantedSegment : String) (constructorType : Expr) :
    Bool :=
  match constructorType with
  | .forallE binderName _ bodyType _ =>
      (Name.lastSegmentString binderName).contains wantedSegment ||
        hasBinderContainingSegment wantedSegment bodyType
  | _ => false

/-- `Ty` ctors whose identity/path endpoints are still raw terms instead of
typed endpoint evidence. -/
def isTyRawEndpointConstructorName (constructorName : Name) : Bool :=
  let suffix := Name.lastSegmentString constructorName
  suffix == "id" ||
    suffix == "path" ||
    suffix == "oeq" ||
    suffix == "idStrict"

/-- Whether the constructor already appears to carry typed endpoint evidence. -/
def hasTypedEndpointEvidence (constructorType : Expr) : Bool :=
  hasBinderContainingSegment "EndpointTerm" constructorType ||
    hasBinderContainingSegment "endpointTerm" constructorType ||
    hasBinderContainingSegment "EndpointWitness" constructorType ||
    hasBinderContainingSegment "endpointWitness" constructorType

/-- Report raw endpoint debt for one `Ty` constructor. -/
def tyRawEndpointDebtRecord?
    (environment : Environment) (constructorName : Name) :
    Option SignatureDebtRecord :=
  if !isTyRawEndpointConstructorName constructorName then
    none
  else
    match environment.find? constructorName with
    | some (.ctorInfo constructorInfo) =>
        let hasRawEndpoints :=
          hasBinderWithLastSegment "leftEndpoint" constructorInfo.type &&
            hasBinderWithLastSegment "rightEndpoint" constructorInfo.type &&
            doesExprMentionConst `LeanFX2.RawTerm constructorInfo.type
        if hasRawEndpoints && !hasTypedEndpointEvidence constructorInfo.type then
          some {
            constructorName := constructorName
            detail := "type constructor has raw endpoints without typed endpoint evidence"
          }
        else
          none
    | _ => none

/-- Collect raw endpoint debt records for a type inductive. -/
def tyRawEndpointDebtRecordsForInductive
    (environment : Environment) (inductiveName : Name) :
    Array SignatureDebtRecord :=
  let constructorNames := getInductiveConstructorNames environment inductiveName
  constructorNames.foldl
    (init := (#[] : Array SignatureDebtRecord))
    (fun records constructorName =>
      match tyRawEndpointDebtRecord? environment constructorName with
      | some record => records.push record
      | none => records)

/-- Build-failing budget gate for raw endpoint type constructors. -/
elab "#assert_ty_raw_endpoint_budget " inductiveSyntax:ident
    rawEndpointBudgetSyntax:num : command => do
  let environment ← getEnv
  let inductiveName := inductiveSyntax.getId
  let rawEndpointBudget := rawEndpointBudgetSyntax.getNat
  let records := tyRawEndpointDebtRecordsForInductive environment inductiveName
  if records.size <= rawEndpointBudget then
    logInfo
      (s!"Ty raw endpoint budget ok: {inductiveName} " ++
      s!"({records.size}/{rawEndpointBudget} raw endpoint ctors)")
  else
    let perCtorLines := records.toList.map fun record =>
      s!"  - {record.constructorName}: {record.detail}"
    let header :=
      s!"Ty raw endpoint budget FAILED for {inductiveName}: " ++
      s!"{records.size} raw endpoint ctors exceed budget {rawEndpointBudget}"
    throwError (header ++ "\n" ++ String.intercalate "\n" perCtorLines)

/-- Whether a Ty constructor has the richer schema object expected by its
surface meaning. -/
def hasExpectedTySchemaPayload
    (constructorName : Name) (constructorType : Expr) :
    Bool :=
  let suffix := Name.lastSegmentString constructorName
  if suffix == "modal" then
    doesExprMentionConst `LeanFX2.Modality constructorType
  else if suffix == "glue" then
    doesExprMentionConst `LeanFX2.BoundaryCofib constructorType &&
      doesExprMentionConst `LeanFX2.Ty.equiv constructorType
  else if suffix == "refine" then
    hasBinderContainingSegment "predicateTerm" constructorType ||
      hasBinderContainingSegment "predicateWitness" constructorType
  else if suffix == "session" then
    doesExprMentionConst `LeanFX2.SessionProtocol constructorType
  else if suffix == "effect" then
    doesExprMentionConst `LeanFX2.Effects.EffectRow constructorType
  else
    true

/-- Ty constructors whose semantics currently travel through raw/Nat tags. -/
def isTyUnstructuredSchemaConstructorName (constructorName : Name) : Bool :=
  let suffix := Name.lastSegmentString constructorName
  suffix == "modal" ||
    suffix == "glue" ||
    suffix == "refine" ||
    suffix == "session" ||
    suffix == "effect"

/-- Report unstructured schema payload debt for one `Ty` constructor. -/
def tyUnstructuredSchemaDebtRecord?
    (environment : Environment) (constructorName : Name) :
    Option SignatureDebtRecord :=
  if !isTyUnstructuredSchemaConstructorName constructorName then
    none
  else
    match environment.find? constructorName with
    | some (.ctorInfo constructorInfo) =>
        if hasExpectedTySchemaPayload constructorName constructorInfo.type then
          none
        else
          some {
            constructorName := constructorName
            detail := "type constructor uses raw/Nat schema payload instead of rich schema object"
          }
    | _ => none

/-- Collect unstructured schema payload debt records for a type inductive. -/
def tyUnstructuredSchemaDebtRecordsForInductive
    (environment : Environment) (inductiveName : Name) :
    Array SignatureDebtRecord :=
  let constructorNames := getInductiveConstructorNames environment inductiveName
  constructorNames.foldl
    (init := (#[] : Array SignatureDebtRecord))
    (fun records constructorName =>
      match tyUnstructuredSchemaDebtRecord? environment constructorName with
      | some record => records.push record
      | none => records)

/-- Build-failing budget gate for unstructured Ty schema payloads. -/
elab "#assert_ty_unstructured_schema_budget " inductiveSyntax:ident
    schemaBudgetSyntax:num : command => do
  let environment ← getEnv
  let inductiveName := inductiveSyntax.getId
  let schemaBudget := schemaBudgetSyntax.getNat
  let records := tyUnstructuredSchemaDebtRecordsForInductive environment inductiveName
  if records.size <= schemaBudget then
    logInfo
      (s!"Ty unstructured schema budget ok: {inductiveName} " ++
      s!"({records.size}/{schemaBudget} raw/Nat schema ctors)")
  else
    let perCtorLines := records.toList.map fun record =>
      s!"  - {record.constructorName}: {record.detail}"
    let header :=
      s!"Ty unstructured schema budget FAILED for {inductiveName}: " ++
      s!"{records.size} schema debts exceed budget {schemaBudget}"
    throwError (header ++ "\n" ++ String.intercalate "\n" perCtorLines)

/-- Report cubical transport endpoint-linkage debt for `Term.transp`. -/
def transportLinkageDebtRecord?
    (environment : Environment) (constructorName : Name) :
    Option SignatureDebtRecord :=
  if Name.lastSegmentString constructorName != "transp" then
    none
  else
    match environment.find? constructorName with
    | some (.ctorInfo constructorInfo) =>
        let hasSeparateRawCodes :=
          hasBinderWithLastSegment "sourceTypeRaw" constructorInfo.type &&
            hasBinderWithLastSegment "targetTypeRaw" constructorInfo.type
        let hasLinkageEvidence :=
          hasBinderContainingSegment "sourceTypeLink" constructorInfo.type ||
            hasBinderContainingSegment "targetTypeLink" constructorInfo.type ||
            hasBinderContainingSegment "decodedSource" constructorInfo.type ||
            hasBinderContainingSegment "decodedTarget" constructorInfo.type
        if hasSeparateRawCodes && !hasLinkageEvidence then
          some {
            constructorName := constructorName
            detail := "transport has raw universe endpoints without source/target linkage evidence"
          }
        else
          none
    | _ => none

/-- Collect transport endpoint-linkage debt records for an inductive. -/
def transportLinkageDebtRecordsForInductive
    (environment : Environment) (inductiveName : Name) :
    Array SignatureDebtRecord :=
  let constructorNames := getInductiveConstructorNames environment inductiveName
  constructorNames.foldl
    (init := (#[] : Array SignatureDebtRecord))
    (fun records constructorName =>
      match transportLinkageDebtRecord? environment constructorName with
      | some record => records.push record
      | none => records)

/-- Build-failing budget gate for cubical transport endpoint linkage debt. -/
elab "#assert_transport_linkage_budget " inductiveSyntax:ident
    transportLinkageBudgetSyntax:num : command => do
  let environment ← getEnv
  let inductiveName := inductiveSyntax.getId
  let transportLinkageBudget := transportLinkageBudgetSyntax.getNat
  let records := transportLinkageDebtRecordsForInductive environment inductiveName
  if records.size <= transportLinkageBudget then
    logInfo
      (s!"transport linkage budget ok: {inductiveName} " ++
      s!"({records.size}/{transportLinkageBudget} unlinked transport ctors)")
  else
    let perCtorLines := records.toList.map fun record =>
      s!"  - {record.constructorName}: {record.detail}"
    let header :=
      s!"transport linkage budget FAILED for {inductiveName}: " ++
      s!"{records.size} transport linkage debts exceed budget " ++
      s!"{transportLinkageBudget}"
    throwError (header ++ "\n" ++ String.intercalate "\n" perCtorLines)

/-- Glue-related Term constructors that should mention boundary cofibrations and
equivalence data when they stop being schematic. -/
def isGlueSchemaConstructorName (constructorName : Name) : Bool :=
  let suffix := Name.lastSegmentString constructorName
  suffix == "glueIntro" || suffix == "glueElim"

/-- Report Glue boundary/equivalence schema debt for one Term constructor. -/
def glueSchemaDebtRecord?
    (environment : Environment) (constructorName : Name) :
    Option SignatureDebtRecord :=
  if !isGlueSchemaConstructorName constructorName then
    none
  else
    match environment.find? constructorName with
    | some (.ctorInfo constructorInfo) =>
        let hasBoundarySchema :=
          doesExprMentionConst `LeanFX2.BoundaryCofib constructorInfo.type
        let hasEquivSchema :=
          doesExprMentionConst `LeanFX2.Ty.equiv constructorInfo.type ||
            doesExprMentionConst `LeanFX2.IsEquiv constructorInfo.type
        if hasBoundarySchema && hasEquivSchema then
          none
        else
          some {
            constructorName := constructorName
            detail := "Glue constructor lacks BoundaryCofib/equivalence schema evidence"
          }
    | _ => none

/-- Collect Glue boundary/equivalence schema debt records for an inductive. -/
def glueSchemaDebtRecordsForInductive
    (environment : Environment) (inductiveName : Name) :
    Array SignatureDebtRecord :=
  let constructorNames := getInductiveConstructorNames environment inductiveName
  constructorNames.foldl
    (init := (#[] : Array SignatureDebtRecord))
    (fun records constructorName =>
      match glueSchemaDebtRecord? environment constructorName with
      | some record => records.push record
      | none => records)

/-- Build-failing budget gate for schematic Glue constructors. -/
elab "#assert_glue_schema_budget " inductiveSyntax:ident
    glueSchemaBudgetSyntax:num : command => do
  let environment ← getEnv
  let inductiveName := inductiveSyntax.getId
  let glueSchemaBudget := glueSchemaBudgetSyntax.getNat
  let records := glueSchemaDebtRecordsForInductive environment inductiveName
  if records.size <= glueSchemaBudget then
    logInfo
      (s!"Glue schema budget ok: {inductiveName} " ++
      s!"({records.size}/{glueSchemaBudget} schematic Glue ctors)")
  else
    let perCtorLines := records.toList.map fun record =>
      s!"  - {record.constructorName}: {record.detail}"
    let header :=
      s!"Glue schema budget FAILED for {inductiveName}: " ++
      s!"{records.size} Glue schema debts exceed budget {glueSchemaBudget}"
    throwError (header ++ "\n" ++ String.intercalate "\n" perCtorLines)

/-- Term constructors that should mention `EffectRow` instead of raw/unit tags. -/
def isEffectSchemaConstructorName (constructorName : Name) : Bool :=
  Name.lastSegmentString constructorName == "effectPerform"

/-- Report effect-row schema debt for one Term constructor. -/
def effectSchemaDebtRecord?
    (environment : Environment) (constructorName : Name) :
    Option SignatureDebtRecord :=
  if !isEffectSchemaConstructorName constructorName then
    none
  else
    match environment.find? constructorName with
    | some (.ctorInfo constructorInfo) =>
        if doesExprMentionConst `LeanFX2.Effects.EffectRow constructorInfo.type then
          none
        else
          some {
            constructorName := constructorName
            detail := "effect constructor lacks EffectRow membership evidence"
          }
    | _ => none

/-- Collect effect-row schema debt records for an inductive. -/
def effectSchemaDebtRecordsForInductive
    (environment : Environment) (inductiveName : Name) :
    Array SignatureDebtRecord :=
  let constructorNames := getInductiveConstructorNames environment inductiveName
  constructorNames.foldl
    (init := (#[] : Array SignatureDebtRecord))
    (fun records constructorName =>
      match effectSchemaDebtRecord? environment constructorName with
      | some record => records.push record
      | none => records)

/-- Build-failing budget gate for effect-row schema debt. -/
elab "#assert_effect_schema_budget " inductiveSyntax:ident
    effectSchemaBudgetSyntax:num : command => do
  let environment ← getEnv
  let inductiveName := inductiveSyntax.getId
  let effectSchemaBudget := effectSchemaBudgetSyntax.getNat
  let records := effectSchemaDebtRecordsForInductive environment inductiveName
  if records.size <= effectSchemaBudget then
    logInfo
      (s!"effect schema budget ok: {inductiveName} " ++
      s!"({records.size}/{effectSchemaBudget} effect ctors lack row evidence)")
  else
    let perCtorLines := records.toList.map fun record =>
      s!"  - {record.constructorName}: {record.detail}"
    let header :=
      s!"effect schema budget FAILED for {inductiveName}: " ++
      s!"{records.size} effect schema debts exceed budget {effectSchemaBudget}"
    throwError (header ++ "\n" ++ String.intercalate "\n" perCtorLines)

/-- Term constructors that should mention `SessionProtocol` at the core
signature once sessions stop being raw protocol tags. -/
def isSessionSchemaConstructorName (constructorName : Name) : Bool :=
  let suffix := Name.lastSegmentString constructorName
  suffix == "sessionSend" || suffix == "sessionRecv"

/-- Report session schema debt for one Term constructor. -/
def sessionSchemaDebtRecord?
    (environment : Environment) (constructorName : Name) :
    Option SignatureDebtRecord :=
  if !isSessionSchemaConstructorName constructorName then
    none
  else
    match environment.find? constructorName with
    | some (.ctorInfo constructorInfo) =>
        if doesExprMentionConst `LeanFX2.SessionProtocol constructorInfo.type then
          none
        else
          some {
            constructorName := constructorName
            detail := "session constructor lacks SessionProtocol schema evidence"
          }
    | _ => none

/-- Collect session schema debt records for an inductive. -/
def sessionSchemaDebtRecordsForInductive
    (environment : Environment) (inductiveName : Name) :
    Array SignatureDebtRecord :=
  let constructorNames := getInductiveConstructorNames environment inductiveName
  constructorNames.foldl
    (init := (#[] : Array SignatureDebtRecord))
    (fun records constructorName =>
      match sessionSchemaDebtRecord? environment constructorName with
      | some record => records.push record
      | none => records)

/-- Build-failing budget gate for session protocol schema debt. -/
elab "#assert_session_schema_budget " inductiveSyntax:ident
    sessionSchemaBudgetSyntax:num : command => do
  let environment ← getEnv
  let inductiveName := inductiveSyntax.getId
  let sessionSchemaBudget := sessionSchemaBudgetSyntax.getNat
  let records := sessionSchemaDebtRecordsForInductive environment inductiveName
  if records.size <= sessionSchemaBudget then
    logInfo
      (s!"session schema budget ok: {inductiveName} " ++
      s!"({records.size}/{sessionSchemaBudget} session ctors lack protocol schema)")
  else
    let perCtorLines := records.toList.map fun record =>
      s!"  - {record.constructorName}: {record.detail}"
    let header :=
      s!"session schema budget FAILED for {inductiveName}: " ++
      s!"{records.size} session schema debts exceed budget {sessionSchemaBudget}"
    throwError (header ++ "\n" ++ String.intercalate "\n" perCtorLines)

/-- Report homogeneous-composition Kan-boundary debt for `Term.hcomp`. -/
def hcompKanDebtRecord?
    (environment : Environment) (constructorName : Name) :
    Option SignatureDebtRecord :=
  if Name.lastSegmentString constructorName != "hcomp" then
    none
  else
    match environment.find? constructorName with
    | some (.ctorInfo constructorInfo) =>
        let hasKanBoundaryEvidence :=
          doesExprMentionConst `LeanFX2.BoundaryCofib constructorInfo.type ||
            hasBinderContainingSegment "boundary" constructorInfo.type ||
            hasBinderContainingSegment "kan" constructorInfo.type ||
            hasBinderContainingSegment "Kan" constructorInfo.type
        if hasKanBoundaryEvidence then
          none
        else
          some {
            constructorName := constructorName
            detail := "hcomp lacks Kan boundary/filler evidence"
          }
    | _ => none

/-- Collect hcomp Kan-boundary debt records for an inductive. -/
def hcompKanDebtRecordsForInductive
    (environment : Environment) (inductiveName : Name) :
    Array SignatureDebtRecord :=
  let constructorNames := getInductiveConstructorNames environment inductiveName
  constructorNames.foldl
    (init := (#[] : Array SignatureDebtRecord))
    (fun records constructorName =>
      match hcompKanDebtRecord? environment constructorName with
      | some record => records.push record
      | none => records)

/-- Build-failing budget gate for `hcomp` without Kan boundary evidence. -/
elab "#assert_hcomp_kan_budget " inductiveSyntax:ident
    hcompKanBudgetSyntax:num : command => do
  let environment ← getEnv
  let inductiveName := inductiveSyntax.getId
  let hcompKanBudget := hcompKanBudgetSyntax.getNat
  let records := hcompKanDebtRecordsForInductive environment inductiveName
  if records.size <= hcompKanBudget then
    logInfo
      (s!"hcomp Kan budget ok: {inductiveName} " ++
      s!"({records.size}/{hcompKanBudget} hcomp ctors lack Kan evidence)")
  else
    let perCtorLines := records.toList.map fun record =>
      s!"  - {record.constructorName}: {record.detail}"
    let header :=
      s!"hcomp Kan budget FAILED for {inductiveName}: " ++
      s!"{records.size} hcomp Kan debts exceed budget {hcompKanBudget}"
    throwError (header ++ "\n" ++ String.intercalate "\n" perCtorLines)

/-! ## Exact semantic-debt snapshots

The budget gates above prevent debt counts from growing.  Count-only
budgets still miss a dangerous substitution pattern: one known bad
constructor can be repaired while a new bad constructor appears in the
same class, keeping the total count unchanged.  These snapshot gates pin
the exact constructor names for the small, high-risk semantic debt
classes so any replacement debt requires an explicit harness update.
-/

/-- Extract constructor names from signature-debt records. -/
def signatureDebtConstructorNames
    (records : Array SignatureDebtRecord) :
    Array Name :=
  records.map (fun record => record.constructorName)

/-- Render a constructor-name array compactly for error messages. -/
def formatNameArray (names : Array Name) : String :=
  "[" ++ String.intercalate ", " (names.toList.map toString) ++ "]"

/-- Order-sensitive equality for constructor-name arrays.  Constructor
collectors walk the inductive in declaration order, so an ordering change is
also useful signal during review. -/
def nameArraysEqual (leftNames rightNames : Array Name) : Bool :=
  leftNames.size == rightNames.size &&
    (leftNames.toList.zip rightNames.toList).all
      (fun (namePair : Name × Name) => namePair.1 == namePair.2)

/-- Build-failing exact snapshot for a small semantic-debt class. -/
def assertExactDebtSnapshot
    (snapshotName : String) (auditCountName : Name)
    (actualNames expectedNames : Array Name) :
    CommandElabM Unit := do
  recordAuditCount auditCountName actualNames.size
  if nameArraysEqual actualNames expectedNames then
    logInfo
      (s!"{snapshotName} exact snapshot ok " ++
      s!"({actualNames.size} constructors)")
  else
    throwError
      (s!"{snapshotName} exact snapshot FAILED\n" ++
      s!"  actual:   {formatNameArray actualNames}\n" ++
      s!"  expected: {formatNameArray expectedNames}")

/-- Expected current Term constructors with missing mode premises. -/
def expectedTermModeDebtNames : Array Name := #[]

/-- Expected current fixed-motive eliminator constructors.  `Term.boolElim`
was refactored to a dependent motive family `Ty level (scope + 1)` in commit
db1b88d ("Restore LeanFX2 build and strict audit"); the heuristic in
`hasFixedMotiveTypeBinder` recognises the extended-scope motive shape and
excludes it from this debt list. -/
def expectedTermDependentMotiveDebtNames : Array Name := #[
  `LeanFX2.Term.natElim,
  `LeanFX2.Term.natRec,
  `LeanFX2.Term.listElim,
  `LeanFX2.Term.optionMatch,
  `LeanFX2.Term.eitherMatch,
  `LeanFX2.Term.idJ,
  `LeanFX2.Term.oeqJ,
  `LeanFX2.Term.idStrictRec
]

/-- Expected current constructors with unit-typed proof/tag placeholders. -/
def expectedTermUnitPlaceholderDebtNames : Array Name := #[
  `LeanFX2.Term.refineIntro
]

/-- Expected current modal constructors whose type signatures are no-ops. -/
def expectedTermModalNoopDebtNames : Array Name := #[
  `LeanFX2.Term.modIntro,
  `LeanFX2.Term.modElim,
  `LeanFX2.Term.subsume
]

/-- Expected current session constructors without protocol advancement. -/
def expectedTermSessionNoAdvanceDebtNames : Array Name := #[
  `LeanFX2.Term.sessionSend,
  `LeanFX2.Term.sessionRecv
]

/-- Expected current equivalence constructors without coherence witnesses. -/
def expectedTermEquivCoherenceDebtNames : Array Name := #[]

/-- Expected current transport constructor with unlinked universe endpoints. -/
def expectedTermTransportLinkageDebtNames : Array Name := #[
  `LeanFX2.Term.transp
]

/-- Expected current Glue constructors without rich boundary/equiv schema. -/
def expectedTermGlueSchemaDebtNames : Array Name := #[
  `LeanFX2.Term.glueIntro,
  `LeanFX2.Term.glueElim
]

/-- Expected current effect constructor without row-membership schema. -/
def expectedTermEffectSchemaDebtNames : Array Name := #[
]

/-- Expected current session constructors without protocol schema. -/
def expectedTermSessionSchemaDebtNames : Array Name := #[
  `LeanFX2.Term.sessionSend,
  `LeanFX2.Term.sessionRecv
]

/-- Expected current hcomp constructor without Kan-boundary evidence. -/
def expectedTermHcompKanDebtNames : Array Name := #[
  `LeanFX2.Term.hcomp
]

/-- Exact snapshots for the small high-risk Term semantic-debt classes. -/
elab "#assert_term_semantic_debt_snapshots " inductiveSyntax:ident :
    command => do
  let environment ← getEnv
  let inductiveName := inductiveSyntax.getId
  assertExactDebtSnapshot "Term mode-discipline debt"
    `term_mode_discipline_snapshot
    (modeDisciplineDebtRecordsForInductive environment inductiveName |>.map
      (fun record => record.constructorName))
    expectedTermModeDebtNames
  assertExactDebtSnapshot "Term dependent-motive debt"
    `term_dependent_motive_snapshot
    (dependentEliminatorDebtRecordsForInductive environment inductiveName |>
      signatureDebtConstructorNames)
    expectedTermDependentMotiveDebtNames
  assertExactDebtSnapshot "Term unit-placeholder debt"
    `term_unit_placeholder_snapshot
    (unitPlaceholderDebtRecordsForInductive environment inductiveName |>
      signatureDebtConstructorNames)
    expectedTermUnitPlaceholderDebtNames
  assertExactDebtSnapshot "Term modal-noop debt"
    `term_modal_noop_snapshot
    (modalNoopDebtRecordsForInductive environment inductiveName |>
      signatureDebtConstructorNames)
    expectedTermModalNoopDebtNames
  assertExactDebtSnapshot "Term session no-advance debt"
    `term_session_no_advance_snapshot
    (sessionNoAdvanceDebtRecordsForInductive environment inductiveName |>
      signatureDebtConstructorNames)
    expectedTermSessionNoAdvanceDebtNames
  assertExactDebtSnapshot "Term equiv-coherence debt"
    `term_equiv_coherence_snapshot
    (equivCoherenceDebtRecordsForInductive environment inductiveName |>
      signatureDebtConstructorNames)
    expectedTermEquivCoherenceDebtNames
  assertExactDebtSnapshot "Term transport-linkage debt"
    `term_transport_linkage_snapshot
    (transportLinkageDebtRecordsForInductive environment inductiveName |>
      signatureDebtConstructorNames)
    expectedTermTransportLinkageDebtNames
  assertExactDebtSnapshot "Term Glue-schema debt"
    `term_glue_schema_snapshot
    (glueSchemaDebtRecordsForInductive environment inductiveName |>
      signatureDebtConstructorNames)
    expectedTermGlueSchemaDebtNames
  assertExactDebtSnapshot "Term effect-schema debt"
    `term_effect_schema_snapshot
    (effectSchemaDebtRecordsForInductive environment inductiveName |>
      signatureDebtConstructorNames)
    expectedTermEffectSchemaDebtNames
  assertExactDebtSnapshot "Term session-schema debt"
    `term_session_schema_snapshot
    (sessionSchemaDebtRecordsForInductive environment inductiveName |>
      signatureDebtConstructorNames)
    expectedTermSessionSchemaDebtNames
  assertExactDebtSnapshot "Term hcomp-Kan debt"
    `term_hcomp_kan_snapshot
    (hcompKanDebtRecordsForInductive environment inductiveName |>
      signatureDebtConstructorNames)
    expectedTermHcompKanDebtNames

/-- Expected current Ty constructors whose endpoints remain raw. -/
def expectedTyRawEndpointDebtNames : Array Name := #[
  `LeanFX2.Ty.id,
  `LeanFX2.Ty.path,
  `LeanFX2.Ty.oeq,
  `LeanFX2.Ty.idStrict
]

/-- Expected current Ty constructors with unstructured schema payloads. -/
def expectedTyUnstructuredSchemaDebtNames : Array Name := #[
  `LeanFX2.Ty.glue,
  `LeanFX2.Ty.refine,
  `LeanFX2.Ty.session,
  `LeanFX2.Ty.effect,
  `LeanFX2.Ty.modal
]

/-- Exact snapshots for the small high-risk Ty schema-debt classes. -/
elab "#assert_ty_schema_debt_snapshots " inductiveSyntax:ident :
    command => do
  let environment ← getEnv
  let inductiveName := inductiveSyntax.getId
  assertExactDebtSnapshot "Ty raw-endpoint debt"
    `ty_raw_endpoint_snapshot
    (tyRawEndpointDebtRecordsForInductive environment inductiveName |>
      signatureDebtConstructorNames)
    expectedTyRawEndpointDebtNames
  assertExactDebtSnapshot "Ty unstructured-schema debt"
    `ty_unstructured_schema_snapshot
    (tyUnstructuredSchemaDebtRecordsForInductive environment inductiveName |>
      signatureDebtConstructorNames)
    expectedTyUnstructuredSchemaDebtNames

/-! ## Value-shaped type-code constructor gate

The all-raw-payload gate deliberately ignores proof binders, which made it
miss the `*Code` constructors: they carry proof premises such as
`levelLe : outerLevel.toNat + 1 <= level`, but their computational payload is
still schematic rather than recursively typed.  This gate tracks type-code
constructors whose explicit parameters contain no recursive `Term` child.
-/

/-- Whether a constructor name is one of the `Term.*Code` type-code ctors. -/
def isTypeCodeConstructorName (constructorName : Name) : Bool :=
  (Name.lastSegmentString constructorName).endsWith "Code"

/-- Whether a constructor signature has any explicit recursive `Term` child. -/
partial def hasExplicitTermChildBinder (constructorType : Expr) : Bool :=
  match constructorType with
  | .forallE _ parameterType bodyType binderInfo =>
      let currentBinderIsTermChild :=
        match binderInfo with
        | .default => doesExprMentionConst `LeanFX2.Term parameterType
        | _ => false
      currentBinderIsTermChild || hasExplicitTermChildBinder bodyType
  | _ => false

/-- Report a value-shaped type-code constructor if it has no recursive Term
child tying the code payload back to typed syntax. -/
def valueTypeCodeDebtRecord?
    (environment : Environment) (constructorName : Name) :
    Option SignatureDebtRecord :=
  if !isTypeCodeConstructorName constructorName then
    none
  else
    match environment.find? constructorName with
    | some (.ctorInfo constructorInfo) =>
        if hasExplicitTermChildBinder constructorInfo.type then
          none
        else
          some {
            constructorName := constructorName
            detail := "type-code constructor has no recursive Term child"
          }
    | _ => none

/-- Collect value-shaped type-code debt records across a Term inductive. -/
def valueTypeCodeDebtRecordsForInductive
    (environment : Environment) (inductiveName : Name) :
    Array SignatureDebtRecord :=
  let constructorNames := getInductiveConstructorNames environment inductiveName
  constructorNames.foldl
    (init := (#[] : Array SignatureDebtRecord))
    (fun records constructorName =>
      match valueTypeCodeDebtRecord? environment constructorName with
      | some record => records.push record
      | none => records)

/-- Expected current value-shaped type-code constructors. -/
def expectedTermValueTypeCodeDebtNames : Array Name := #[
  `LeanFX2.Term.universeCode,
  `LeanFX2.Term.arrowCode,
  `LeanFX2.Term.piTyCode,
  `LeanFX2.Term.sigmaTyCode,
  `LeanFX2.Term.productCode,
  `LeanFX2.Term.sumCode,
  `LeanFX2.Term.listCode,
  `LeanFX2.Term.optionCode,
  `LeanFX2.Term.eitherCode,
  `LeanFX2.Term.idCode,
  `LeanFX2.Term.equivCode
]

/-- Build-failing budget gate for `Term.*Code` ctors whose code payloads are
value-shaped instead of recursive typed subterms. -/
elab "#assert_value_type_code_budget " inductiveSyntax:ident
    typeCodeBudgetSyntax:num : command => do
  let environment ← getEnv
  let inductiveName := inductiveSyntax.getId
  let typeCodeBudget := typeCodeBudgetSyntax.getNat
  let records := valueTypeCodeDebtRecordsForInductive environment inductiveName
  recordAuditCount `value_type_code_ctor records.size
  if records.size <= typeCodeBudget then
    logInfo
      (s!"value-shaped type-code budget ok: {inductiveName} " ++
      s!"({records.size}/{typeCodeBudget} *Code ctors have no Term child)")
  else
    let perCtorLines := records.toList.map fun record =>
      s!"  - {record.constructorName}: {record.detail}"
    let header :=
      s!"value-shaped type-code budget FAILED for {inductiveName}: " ++
      s!"{records.size} *Code ctors exceed budget {typeCodeBudget}"
    throwError (header ++ "\n" ++ String.intercalate "\n" perCtorLines)

/-- Exact snapshot for the current value-shaped type-code constructor debt. -/
elab "#assert_value_type_code_snapshot " inductiveSyntax:ident :
    command => do
  let environment ← getEnv
  let inductiveName := inductiveSyntax.getId
  assertExactDebtSnapshot "Term value-shaped type-code debt"
    `value_type_code_ctor_snapshot
    (valueTypeCodeDebtRecordsForInductive environment inductiveName |>
      signatureDebtConstructorNames)
    expectedTermValueTypeCodeDebtNames


end LeanFX2.Tools
