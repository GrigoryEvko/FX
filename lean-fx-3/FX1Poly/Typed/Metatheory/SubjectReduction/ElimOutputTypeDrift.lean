import FX1Poly.Typed.Metatheory.SubjectReduction.ElimOutputTypeCongruence
import FX1Poly.Typed.Metatheory.SubjectReduction.ElimObligationsDrift

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/ElimOutputTypeDrift
    — SR-DSL-5: per-row OUTPUT-type drift under one arg `StepChildren`

The eliminator-congruence gate (`elimGateRowReassemble`) rebuilds a stepped eliminator cell at
`rule.outputType scope argsAfter params` and post-composes the `outputDrift : Conv (rule.outputType scope argsAfter
params) (rule.outputType scope args params)`.  This file ships that `outputDrift` for the rows whose output reads a
STEPPING child (so the drift is not `Conv.refl`):

  * **`app`** — output `subst0 codomainCode argument`: a function step leaves the output fixed (`Conv.refl`); an
    argument step drifts it (`subst0` argument-congruence, via `appElimRuleOutputType_isConvStableUnderArgumentStep`).
  * **the six `subst0 motive scrutinee` rows** — `boolElim` / `listElim` (scrutinee at position 1) and `natElim` /
    `natRec` / `optionMatch` / `eitherMatch` (scrutinee at position 3): a motive step or a scrutinee step drifts the
    output (the two `subst0`-congruence halves `dependentEliminatorOutputType_isConvStableUnder{Motive,Scrutinee}Step`);
    every branch child is absent from the output, so a branch step is `Conv.refl`.
  * **`idJ`** — output `idJMotiveAt motive rightEndpoint witness`: a motive step or a witness step drifts it (the two
    `Conv.substPair` legs `idJOutputType_isConvStableUnder{Motive,Witness}Step`); the base-case child is absent.

Each lemma `cases` the single-arg `StepChildren` across the row's arg positions and dispatches to the matching shipped
stability half, taking `.sym` (the gate wants the `argsAfter → args` direction; the stability lemmas give
`args → argsAfter`).  The pure-param rows (`fst` / `snd` / `pathApp`) need no lemma here — their output ignores the
args, so their gate `outputDrift` is `Conv.refl` directly.

## Zero-axiom

`cases` on the `StepChildren` mutual inductive + the shipped `ElimOutputTypeCongruence` stability lemmas + `Conv.sym`
/ `Conv.refl`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration
audit-gated. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **`app`'s output drift under one arg step.**  Function step → output (`subst0 codomainCode argument`) fixed;
argument step → `subst0` argument-congruence. -/
theorem appOutputTypeDriftUnderArgStep {scope : Nat}
    (function domainCode : RawTerm scope) {argument : RawTerm scope} (codomainCode : RawTerm (scope + 1))
    {argsAfter : RawTermChildren [0, 0] scope}
    (childStep : StepChildren
      (.childCons function (.childCons argument .childNil) : RawTermChildren [0, 0] scope) argsAfter) :
    Conv
      (appElimRule.outputType scope argsAfter (.childCons domainCode (.childCons codomainCode .childNil)))
      (appElimRule.outputType scope (.childCons function (.childCons argument .childNil))
        (.childCons domainCode (.childCons codomainCode .childNil))) := by
  cases childStep with
  | here _ _functionStep => exact Conv.refl _
  | there _ tailStep => cases tailStep with
    | here _ argumentStep =>
        exact (appElimRuleOutputType_isConvStableUnderArgumentStep function domainCode codomainCode
          argumentStep).sym
    | there _ emptyTailStep => cases emptyTailStep

/-- **`boolElim`'s output drift under one arg step** (scrutinee at position 1).  Motive / scrutinee step → `subst0`
congruence; then / else branch step → `Conv.refl`. -/
theorem boolElimOutputTypeDriftUnderArgStep {scope : Nat}
    {motive : RawTerm (scope + 1)} {scrutinee thenBranch elseBranch : RawTerm scope}
    (params : RawTermChildren boolElimRule.paramShifts scope)
    {argsAfter : RawTermChildren [1, 0, 0, 0] scope}
    (childStep : StepChildren
      (.childCons motive (.childCons scrutinee (.childCons thenBranch (.childCons elseBranch .childNil)))
        : RawTermChildren [1, 0, 0, 0] scope) argsAfter) :
    Conv (boolElimRule.outputType scope argsAfter params)
      (boolElimRule.outputType scope
        (.childCons motive (.childCons scrutinee (.childCons thenBranch (.childCons elseBranch .childNil))))
        params) := by
  cases childStep with
  | here _ motiveStep =>
      exact (dependentEliminatorOutputType_isConvStableUnderMotiveStep scrutinee motiveStep).sym
  | there _ tail1 => cases tail1 with
    | here _ scrutineeStep =>
        exact (dependentEliminatorOutputType_isConvStableUnderScrutineeStep motive scrutineeStep).sym
    | there _ tail2 => cases tail2 with
      | here _ _thenStep => exact Conv.refl _
      | there _ tail3 => cases tail3 with
        | here _ _elseStep => exact Conv.refl _
        | there _ emptyTailStep => cases emptyTailStep

/-- **`listElim`'s output drift under one arg step** (scrutinee at position 1, like `boolElim`).  Motive / scrutinee
step → `subst0` congruence; nil / cons branch step → `Conv.refl`. -/
theorem listElimOutputTypeDriftUnderArgStep {scope : Nat}
    {motive : RawTerm (scope + 1)} {scrutinee nilBranch consBranch : RawTerm scope}
    (params : RawTermChildren listElimRule.paramShifts scope)
    {argsAfter : RawTermChildren [1, 0, 0, 0] scope}
    (childStep : StepChildren
      (.childCons motive (.childCons scrutinee (.childCons nilBranch (.childCons consBranch .childNil)))
        : RawTermChildren [1, 0, 0, 0] scope) argsAfter) :
    Conv (listElimRule.outputType scope argsAfter params)
      (listElimRule.outputType scope
        (.childCons motive (.childCons scrutinee (.childCons nilBranch (.childCons consBranch .childNil))))
        params) := by
  cases childStep with
  | here _ motiveStep =>
      exact (dependentEliminatorOutputType_isConvStableUnderMotiveStep scrutinee motiveStep).sym
  | there _ tail1 => cases tail1 with
    | here _ scrutineeStep =>
        exact (dependentEliminatorOutputType_isConvStableUnderScrutineeStep motive scrutineeStep).sym
    | there _ tail2 => cases tail2 with
      | here _ _nilStep => exact Conv.refl _
      | there _ tail3 => cases tail3 with
        | here _ _consStep => exact Conv.refl _
        | there _ emptyTailStep => cases emptyTailStep

/-- **`natElim`'s output drift under one arg step** (scrutinee at position 3).  Motive (pos 0) / scrutinee (pos 3)
step → `subst0` congruence; base / step branch step → `Conv.refl`. -/
theorem natElimOutputTypeDriftUnderArgStep {scope : Nat}
    {motive : RawTerm (scope + 1)} {baseBranch scrutinee : RawTerm scope} {stepBranch : RawTerm (scope + 2)}
    (params : RawTermChildren natElimRule.paramShifts scope)
    {argsAfter : RawTermChildren [1, 0, 2, 0] scope}
    (childStep : StepChildren
      (.childCons motive (.childCons baseBranch (.childCons stepBranch (.childCons scrutinee .childNil)))
        : RawTermChildren [1, 0, 2, 0] scope) argsAfter) :
    Conv (natElimRule.outputType scope argsAfter params)
      (natElimRule.outputType scope
        (.childCons motive (.childCons baseBranch (.childCons stepBranch (.childCons scrutinee .childNil))))
        params) := by
  cases childStep with
  | here _ motiveStep =>
      exact (dependentEliminatorOutputType_isConvStableUnderMotiveStep scrutinee motiveStep).sym
  | there _ tail1 => cases tail1 with
    | here _ _baseStep => exact Conv.refl _
    | there _ tail2 => cases tail2 with
      | here _ _stepStep => exact Conv.refl _
      | there _ tail3 => cases tail3 with
        | here _ scrutineeStep =>
            exact (dependentEliminatorOutputType_isConvStableUnderScrutineeStep motive scrutineeStep).sym
        | there _ emptyTailStep => cases emptyTailStep

/-- **`natRec`'s output drift under one arg step** — identical to `natElim` (same arg shape and dependent output). -/
theorem natRecOutputTypeDriftUnderArgStep {scope : Nat}
    {motive : RawTerm (scope + 1)} {baseBranch scrutinee : RawTerm scope} {stepBranch : RawTerm (scope + 2)}
    (params : RawTermChildren natRecElimRule.paramShifts scope)
    {argsAfter : RawTermChildren [1, 0, 2, 0] scope}
    (childStep : StepChildren
      (.childCons motive (.childCons baseBranch (.childCons stepBranch (.childCons scrutinee .childNil)))
        : RawTermChildren [1, 0, 2, 0] scope) argsAfter) :
    Conv (natRecElimRule.outputType scope argsAfter params)
      (natRecElimRule.outputType scope
        (.childCons motive (.childCons baseBranch (.childCons stepBranch (.childCons scrutinee .childNil))))
        params) := by
  cases childStep with
  | here _ motiveStep =>
      exact (dependentEliminatorOutputType_isConvStableUnderMotiveStep scrutinee motiveStep).sym
  | there _ tail1 => cases tail1 with
    | here _ _baseStep => exact Conv.refl _
    | there _ tail2 => cases tail2 with
      | here _ _stepStep => exact Conv.refl _
      | there _ tail3 => cases tail3 with
        | here _ scrutineeStep =>
            exact (dependentEliminatorOutputType_isConvStableUnderScrutineeStep motive scrutineeStep).sym
        | there _ emptyTailStep => cases emptyTailStep

/-- **`optionMatch`'s output drift under one arg step** (scrutinee at position 3).  Motive / scrutinee step → `subst0`
congruence; none / some branch step → `Conv.refl`. -/
theorem optionMatchOutputTypeDriftUnderArgStep {scope : Nat}
    {motive : RawTerm (scope + 1)} {noneBranch someBranch scrutinee : RawTerm scope}
    (params : RawTermChildren optionMatchElimRule.paramShifts scope)
    {argsAfter : RawTermChildren [1, 0, 0, 0] scope}
    (childStep : StepChildren
      (.childCons motive (.childCons noneBranch (.childCons someBranch (.childCons scrutinee .childNil)))
        : RawTermChildren [1, 0, 0, 0] scope) argsAfter) :
    Conv (optionMatchElimRule.outputType scope argsAfter params)
      (optionMatchElimRule.outputType scope
        (.childCons motive (.childCons noneBranch (.childCons someBranch (.childCons scrutinee .childNil))))
        params) := by
  cases childStep with
  | here _ motiveStep =>
      exact (dependentEliminatorOutputType_isConvStableUnderMotiveStep scrutinee motiveStep).sym
  | there _ tail1 => cases tail1 with
    | here _ _noneStep => exact Conv.refl _
    | there _ tail2 => cases tail2 with
      | here _ _someStep => exact Conv.refl _
      | there _ tail3 => cases tail3 with
        | here _ scrutineeStep =>
            exact (dependentEliminatorOutputType_isConvStableUnderScrutineeStep motive scrutineeStep).sym
        | there _ emptyTailStep => cases emptyTailStep

/-- **`eitherMatch`'s output drift under one arg step** (scrutinee at position 3).  Motive / scrutinee step → `subst0`
congruence; left / right branch step → `Conv.refl`. -/
theorem eitherMatchOutputTypeDriftUnderArgStep {scope : Nat}
    {motive : RawTerm (scope + 1)} {leftBranch rightBranch scrutinee : RawTerm scope}
    (params : RawTermChildren eitherMatchElimRule.paramShifts scope)
    {argsAfter : RawTermChildren [1, 0, 0, 0] scope}
    (childStep : StepChildren
      (.childCons motive (.childCons leftBranch (.childCons rightBranch (.childCons scrutinee .childNil)))
        : RawTermChildren [1, 0, 0, 0] scope) argsAfter) :
    Conv (eitherMatchElimRule.outputType scope argsAfter params)
      (eitherMatchElimRule.outputType scope
        (.childCons motive (.childCons leftBranch (.childCons rightBranch (.childCons scrutinee .childNil))))
        params) := by
  cases childStep with
  | here _ motiveStep =>
      exact (dependentEliminatorOutputType_isConvStableUnderMotiveStep scrutinee motiveStep).sym
  | there _ tail1 => cases tail1 with
    | here _ _leftStep => exact Conv.refl _
    | there _ tail2 => cases tail2 with
      | here _ _rightStep => exact Conv.refl _
      | there _ tail3 => cases tail3 with
        | here _ scrutineeStep =>
            exact (dependentEliminatorOutputType_isConvStableUnderScrutineeStep motive scrutineeStep).sym
        | there _ emptyTailStep => cases emptyTailStep

/-- **`idJ`'s output drift under one arg step** (motive at position 0, witness at position 2).  Motive / witness step
→ `Conv.substPair` legs; base-case step → `Conv.refl`.  The output `idJMotiveAt motive rightEndpoint witness` also
reads the `rightEndpoint` PARAM, which never steps under a child step. -/
theorem idJOutputTypeDriftUnderArgStep {scope : Nat}
    {motive : RawTerm (scope + 2)} {baseCase witness : RawTerm scope}
    (typeCode leftEndpoint rightEndpoint : RawTerm scope)
    {argsAfter : RawTermChildren [2, 0, 0] scope}
    (childStep : StepChildren
      (.childCons motive (.childCons baseCase (.childCons witness .childNil))
        : RawTermChildren [2, 0, 0] scope) argsAfter) :
    Conv
      (idJElimRule.outputType scope argsAfter
        (.childCons typeCode (.childCons leftEndpoint (.childCons rightEndpoint .childNil))))
      (idJElimRule.outputType scope (.childCons motive (.childCons baseCase (.childCons witness .childNil)))
        (.childCons typeCode (.childCons leftEndpoint (.childCons rightEndpoint .childNil)))) := by
  cases childStep with
  | here _ motiveStep =>
      exact (idJOutputType_isConvStableUnderMotiveStep rightEndpoint witness motiveStep).sym
  | there _ tail1 => cases tail1 with
    | here _ _baseStep => exact Conv.refl _
    | there _ tail2 => cases tail2 with
      | here _ witnessStep =>
          exact (idJOutputType_isConvStableUnderWitnessStep motive rightEndpoint witnessStep).sym
      | there _ emptyTailStep => cases emptyTailStep

end FX1Poly.Typed
