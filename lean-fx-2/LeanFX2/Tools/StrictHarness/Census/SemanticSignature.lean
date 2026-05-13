import LeanFX2.Tools.StrictHarness.Common
import LeanFX2.Tools.StrictHarness.Census.ModeDiscipline

/-! # LeanFX2.Tools.StrictHarness.Census.SemanticSignature

Five semantic-signature debt gates for the typed Term inductive:

* dependent-eliminator motive debt
* unit-typed proof/tag placeholder debt
* modal-noop constructor debt
* session-no-advance constructor debt
* equivalence-introduction coherence debt

Shares the `SignatureDebtRecord` shape used by Rich-schema and Snapshot
sub-modules.

## Root status

Layer T strict-harness audit gate. -/

namespace LeanFX2.Tools

open Lean Elab Command

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

end LeanFX2.Tools
