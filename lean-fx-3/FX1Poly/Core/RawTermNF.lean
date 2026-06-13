import FX1Poly.Core.RawTermFreeVars
import FX1Poly.Core.StepEta
import FX1Poly.Core.StepInversion
import FX1Poly.Core.TableFireRoot

/-! # Foundation/PolyCell/Core/RawTermNF

Raw beta/iota normal-form and closedness predicates for the PolyCell
substrate.

This file intentionally keeps three notions separate:

* `RawTerm.hasRootStepSource` recognizes only the root redexes of the
  current beta+iota `Step` relation.
* `RawTerm.isStepNormalForm` is structural beta+iota normality:
  no root `Step` redex and all children are normal.
* `RawTerm.isClosed` uses the first-principles `RawVarSet`
  characteristic-function substrate from `RawTermFreeVars.lean`.

Eta is not silently folded into beta/iota normality.  Consumers that
need beta+eta normality should define it against `Step.betaEta`.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation

namespace RawVarSet

/-- Boolean emptiness check for first-principles raw variable sets. -/
def isEmpty : {scope : Nat} → RawVarSet scope → Bool
  | 0, _variableSet => true
  | Nat.succ priorScope, variableSet =>
      (!variableSet ⟨0, Nat.zero_lt_succ priorScope⟩) &&
        RawVarSet.isEmpty
          (scope := priorScope)
          (fun priorPosition => variableSet (Fin.succ priorPosition))

/-- Empty-set emptiness smoke. -/
theorem isEmpty_empty {scope : Nat} :
    RawVarSet.isEmpty (RawVarSet.empty : RawVarSet scope) = true := by
  induction scope with
  | zero => rfl
  | succ priorScope priorIH =>
      dsimp only [RawVarSet.isEmpty, RawVarSet.empty]
      change
        (!false &&
            RawVarSet.isEmpty
              (RawVarSet.empty : RawVarSet priorScope)) =
          true
      rw [priorIH]
      rfl

end RawVarSet

namespace RawTerm

/-- Shallow generator test for lambda terms. -/
def isLamSource {scope : Nat} (sourceTerm : RawTerm scope) : Bool :=
  match sourceTerm with
  | .mkGen generator _payload _children =>
      if generator = .gen_lam then true else false

/-- Shallow generator test for `boolTrue`. -/
def isBoolTrueSource {scope : Nat} (sourceTerm : RawTerm scope) : Bool :=
  match sourceTerm with
  | .mkGen generator _payload _children =>
      if generator = .gen_boolTrue then true else false

/-- Shallow generator test for `boolFalse`. -/
def isBoolFalseSource {scope : Nat} (sourceTerm : RawTerm scope) : Bool :=
  match sourceTerm with
  | .mkGen generator _payload _children =>
      if generator = .gen_boolFalse then true else false

/-- Shallow generator test for pair introductions. -/
def isPairSource {scope : Nat} (sourceTerm : RawTerm scope) : Bool :=
  match sourceTerm with
  | .mkGen generator _payload _children =>
      if generator = .gen_pair then true else false

/-- Shallow generator test for `natZero`. -/
def isNatZeroSource {scope : Nat} (sourceTerm : RawTerm scope) : Bool :=
  match sourceTerm with
  | .mkGen generator _payload _children =>
      if generator = .gen_natZero then true else false

/-- Shallow generator test for `natSucc`. -/
def isNatSuccSource {scope : Nat} (sourceTerm : RawTerm scope) : Bool :=
  match sourceTerm with
  | .mkGen generator _payload _children =>
      if generator = .gen_natSucc then true else false

/-- Shallow generator test for `listNil`. -/
def isListNilSource {scope : Nat} (sourceTerm : RawTerm scope) : Bool :=
  match sourceTerm with
  | .mkGen generator _payload _children =>
      if generator = .gen_listNil then true else false

/-- Shallow generator test for `listCons`. -/
def isListConsSource {scope : Nat} (sourceTerm : RawTerm scope) : Bool :=
  match sourceTerm with
  | .mkGen generator _payload _children =>
      if generator = .gen_listCons then true else false

/-- Shallow generator test for `optionNone`. -/
def isOptionNoneSource {scope : Nat} (sourceTerm : RawTerm scope) : Bool :=
  match sourceTerm with
  | .mkGen generator _payload _children =>
      if generator = .gen_optionNone then true else false

/-- Shallow generator test for `optionSome`. -/
def isOptionSomeSource {scope : Nat} (sourceTerm : RawTerm scope) : Bool :=
  match sourceTerm with
  | .mkGen generator _payload _children =>
      if generator = .gen_optionSome then true else false

/-- Shallow generator test for `eitherInl`. -/
def isEitherInlSource {scope : Nat} (sourceTerm : RawTerm scope) : Bool :=
  match sourceTerm with
  | .mkGen generator _payload _children =>
      if generator = .gen_eitherInl then true else false

/-- Shallow generator test for `eitherInr`. -/
def isEitherInrSource {scope : Nat} (sourceTerm : RawTerm scope) : Bool :=
  match sourceTerm with
  | .mkGen generator _payload _children =>
      if generator = .gen_eitherInr then true else false

/-- Shallow generator test for `refl`. -/
def isReflSource {scope : Nat} (sourceTerm : RawTerm scope) : Bool :=
  match sourceTerm with
  | .mkGen generator _payload _children =>
      if generator = .gen_refl then true else false

/-- Shallow generator test for path-lambda terms (the endpoint-beta function head). -/
def isPathLamSource {scope : Nat} (sourceTerm : RawTerm scope) : Bool :=
  match sourceTerm with
  | .mkGen generator _payload _children =>
      if generator = .gen_pathLam then true else false

end RawTerm

namespace RawTermChildren

/-- Transport a children spine across an equality of generator indices. -/
def castToGenerator {scope : Nat} {sourceGenerator targetGenerator : Generator}
    (sourceChildren :
      RawTermChildren sourceGenerator.binderShifts scope)
    (generatorEq : sourceGenerator = targetGenerator) :
    RawTermChildren targetGenerator.binderShifts scope :=
  Eq.rec
    (motive := fun someGenerator _generatorEq =>
      RawTermChildren someGenerator.binderShifts scope)
    sourceChildren generatorEq

/-- Root beta source shape in the children of `gen_app`. -/
def hasAppBetaRoot {scope : Nat}
    (sourceChildren : RawTermChildren [0, 0] scope) : Bool :=
  match sourceChildren with
  | .childCons functionTerm (.childCons _argumentTerm .childNil) =>
      RawTerm.isLamSource functionTerm

/-- Root endpoint-beta source shape in the children of `gen_pathApp`
    (the 17th iota): the path head is a `gen_pathLam` cell. -/
def hasPathAppBetaRoot {scope : Nat}
    (sourceChildren : RawTermChildren [0, 0] scope) : Bool :=
  match sourceChildren with
  | .childCons pathTerm (.childCons _argumentTerm .childNil) =>
      RawTerm.isPathLamSource pathTerm

/-- Root bool-eliminator iota source shape.  Phase-Z spine `[1, 0, 0, 0]`:
    children are `(motive, then, else, scrutinee)` with the scrutinee LAST and
    the motive a term under one binder. -/
def hasBoolElimIotaRoot {scope : Nat}
    (sourceChildren : RawTermChildren [1, 0, 0, 0] scope) : Bool :=
  match sourceChildren with
  | .childCons _motive
      (.childCons _thenBranch (.childCons _elseBranch (.childCons scrutinee .childNil))) =>
      RawTerm.isBoolTrueSource scrutinee ||
        RawTerm.isBoolFalseSource scrutinee

/-- Root pair-projection iota source shape. -/
def hasPairProjectionIotaRoot {scope : Nat}
    (sourceChildren : RawTermChildren [0] scope) : Bool :=
  match sourceChildren with
  | .childCons pairTerm .childNil =>
      RawTerm.isPairSource pairTerm

/-- Root natural-number eliminator iota source shape.  Phase-Z spine
    `[1, 0, 2, 0]`: children are `(motive, zeroBranch, succBranch, scrutinee)`
    with the scrutinee LAST, the motive a term under one binder, and the
    succ-branch a term under TWO binders. -/
def hasNatElimIotaRoot {scope : Nat}
    (sourceChildren : RawTermChildren [1, 0, 2, 0] scope) : Bool :=
  match sourceChildren with
  | .childCons _motive
      (.childCons _zeroBranch (.childCons _succBranch (.childCons scrutinee .childNil))) =>
      RawTerm.isNatZeroSource scrutinee ||
        RawTerm.isNatSuccSource scrutinee

/-- Root list eliminator iota source shape.  Phase-Z spine `[1, 0, 0, 0]`:
    children are `(motive, nil, cons, scrutinee)` with the scrutinee LAST and
    the motive a term under one binder. -/
def hasListElimIotaRoot {scope : Nat}
    (sourceChildren : RawTermChildren [1, 0, 0, 0] scope) : Bool :=
  match sourceChildren with
  | .childCons _motive
      (.childCons _nilBranch (.childCons _consBranch (.childCons scrutinee .childNil))) =>
      RawTerm.isListNilSource scrutinee ||
        RawTerm.isListConsSource scrutinee

/-- Root option matcher iota source shape.  Phase-Z spine `[1, 0, 0, 0]`:
    children are `(motive, none, some, scrutinee)` with the scrutinee LAST and
    the motive a term under one binder. -/
def hasOptionMatchIotaRoot {scope : Nat}
    (sourceChildren : RawTermChildren [1, 0, 0, 0] scope) : Bool :=
  match sourceChildren with
  | .childCons _motive
      (.childCons _noneBranch (.childCons _someBranch (.childCons scrutinee .childNil))) =>
      RawTerm.isOptionNoneSource scrutinee ||
        RawTerm.isOptionSomeSource scrutinee

/-- Root either matcher iota source shape.  Phase-Z spine `[1, 0, 0, 0]`:
    children are `(motive, left, right, scrutinee)` with the scrutinee LAST and
    the motive a term under one binder. -/
def hasEitherMatchIotaRoot {scope : Nat}
    (sourceChildren : RawTermChildren [1, 0, 0, 0] scope) : Bool :=
  match sourceChildren with
  | .childCons _motive
      (.childCons _leftBranch (.childCons _rightBranch (.childCons scrutinee .childNil))) =>
      RawTerm.isEitherInlSource scrutinee ||
        RawTerm.isEitherInrSource scrutinee

/-- Root identity-eliminator iota source shape.  Phase-Z spine `[2, 0, 0]`:
    children are `(motive, baseCase, witness)` with the witness LAST and the
    motive a term under two binders (endpoint + path). -/
def hasIdElimIotaRoot {scope : Nat}
    (sourceChildren : RawTermChildren [2, 0, 0] scope) : Bool :=
  match sourceChildren with
  | .childCons _motive (.childCons _baseCase (.childCons witness .childNil)) =>
      RawTerm.isReflSource witness

end RawTermChildren

namespace RawTerm

/-- Root beta/iota redex detector for the kernel `Step` relation — THE
generic canonical-table walk (`fireTableRedexOver`), shared with the
normalizer (`reduceOnce`) and the one-step enumerator.  Excludes
congruence (handled by recursive normality over `RawTermChildren`) and
eta (the separate `Step.betaEta` relation). -/
def hasRootStepSource {scope : Nat} (sourceTerm : RawTerm scope) : Bool :=
  match sourceTerm with
  | .mkGen generator payload children =>
      (fireTableRedexOver iotaRuleTable generator payload children).isSome

end RawTerm

mutual

/-- Boolean structural beta/iota normality for raw terms. -/
def RawTerm.isStepNormalFormBool {scope : Nat}
    (sourceTerm : RawTerm scope) : Bool :=
  match sourceTerm with
  | .mkGen _generator _payload children =>
      (!RawTerm.hasRootStepSource sourceTerm) &&
        RawTermChildren.areStepNormalFormsBool children

/-- Boolean structural beta/iota normality for raw child spines. -/
def RawTermChildren.areStepNormalFormsBool {binderShifts : List Nat}
    {scope : Nat} (sourceChildren : RawTermChildren binderShifts scope) :
    Bool :=
  match binderShifts, sourceChildren with
  | [], .childNil => true
  | _headShift :: _, .childCons childHead childTail =>
      RawTerm.isStepNormalFormBool childHead &&
        RawTermChildren.areStepNormalFormsBool childTail

end

namespace RawTerm

/-- Structural beta/iota normality for raw terms. -/
def isStepNormalForm {scope : Nat} (sourceTerm : RawTerm scope) : Prop :=
  RawTerm.isStepNormalFormBool sourceTerm = true

/-- Closedness as emptiness of the computable free-variable set. -/
def isClosed {scope : Nat} (sourceTerm : RawTerm scope) : Prop :=
  RawVarSet.isEmpty (RawTerm.freeVars sourceTerm) = true

instance instDecidableIsStepNormalForm {scope : Nat}
    (sourceTerm : RawTerm scope) :
    Decidable (RawTerm.isStepNormalForm sourceTerm) := by
  dsimp only [RawTerm.isStepNormalForm]
  exact inferInstance

instance instDecidableIsClosed {scope : Nat} (sourceTerm : RawTerm scope) :
    Decidable (RawTerm.isClosed sourceTerm) := by
  dsimp only [RawTerm.isClosed]
  exact inferInstance

end RawTerm

namespace RawTermChildren

/-- Structural beta/iota normality for raw child spines. -/
def areStepNormalForms {binderShifts : List Nat} {scope : Nat}
    (sourceChildren : RawTermChildren binderShifts scope) : Prop :=
  RawTermChildren.areStepNormalFormsBool sourceChildren = true

instance instDecidableAreStepNormalForms {binderShifts : List Nat}
    {scope : Nat} (sourceChildren : RawTermChildren binderShifts scope) :
    Decidable
      (RawTermChildren.areStepNormalForms sourceChildren) := by
  dsimp only [RawTermChildren.areStepNormalForms]
  exact inferInstance

end RawTermChildren


/-- A canonical-table root firing forces the root-redex detector: the
detector IS the generic table walk, so the row's own firing makes the
walk return `some` (`fireTableRedexOver_complete`) — no per-row case
analysis. -/
theorem RawTerm.hasRootStepSource_of_firing {scope : Nat}
    {rule : IotaRuleDesc} (isRow : rule ∈ iotaRuleTable)
    (elimPayload : rule.elimGenerator.payload scope)
    {spine : RawTermChildren rule.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (fires : rule.firesOn? elimPayload spine = some reduct) :
    RawTerm.hasRootStepSource
      (.mkGen rule.elimGenerator elimPayload spine) = true := by
  have selfFires :
      rule.fireAtRoot? rule.elimGenerator elimPayload spine = some reduct := by
    dsimp only [IotaRuleDesc.fireAtRoot?]
    rw [dif_pos rfl]
    exact fires
  exact fireTableRedexOver_complete selfFires iotaRuleTable isRow

mutual

/-- A structurally normal raw term blocks every beta/iota `Step`. -/
theorem RawTerm.isStepNormalForm_blocks_step {scope : Nat}
    {sourceTerm : RawTerm scope}
    (normalSource : RawTerm.isStepNormalForm sourceTerm)
    (targetTerm : RawTerm scope) :
    ¬ Step sourceTerm targetTerm := by
  intro reduction
  match sourceTerm with
  | .mkGen generator payload children =>
      dsimp only [RawTerm.isStepNormalForm] at normalSource
      dsimp only [RawTerm.isStepNormalFormBool] at normalSource
      cases rootValue : RawTerm.hasRootStepSource
          (.mkGen generator payload children) <;>
        rw [rootValue] at normalSource
      · cases childrenNormalValue :
            RawTermChildren.areStepNormalFormsBool children <;>
          rw [childrenNormalValue] at normalSource
        · cases normalSource
        · cases reduction with
          | tableRedex isRow elimPayload fires =>
              rw [RawTerm.hasRootStepSource_of_firing
                isRow elimPayload fires] at rootValue
              cases rootValue
          | cong _ _ childStep =>
              exact
                RawTermChildren.areStepNormalForms_blocks_stepChildren
                  (sourceChildren := children) childrenNormalValue _
                  childStep
      · cases normalSource

/-- A structurally normal raw child spine blocks every `StepChildren`. -/
theorem RawTermChildren.areStepNormalForms_blocks_stepChildren
    {binderShifts : List Nat} {scope : Nat}
    {sourceChildren : RawTermChildren binderShifts scope}
    (normalChildren :
      RawTermChildren.areStepNormalForms sourceChildren)
    (targetChildren : RawTermChildren binderShifts scope) :
    ¬ StepChildren sourceChildren targetChildren := by
  intro childReduction
  match binderShifts, sourceChildren with
  | [], .childNil =>
      exact StepChildren.no_step_at_empty_spine childReduction
  | _headShift :: _, .childCons childHead childTail =>
      dsimp only [RawTermChildren.areStepNormalForms] at normalChildren
      change
        (RawTerm.isStepNormalFormBool childHead &&
            RawTermChildren.areStepNormalFormsBool childTail) =
          true at normalChildren
      cases headNormalValue : RawTerm.isStepNormalFormBool childHead <;>
        rw [headNormalValue] at normalChildren
      · cases normalChildren
      · cases tailNormalValue :
            RawTermChildren.areStepNormalFormsBool childTail <;>
          rw [tailNormalValue] at normalChildren
        · cases normalChildren
        · cases childReduction with
          | here _ headStep =>
              exact RawTerm.isStepNormalForm_blocks_step
                (sourceTerm := childHead) headNormalValue _ headStep
          | there _ tailStep =>
              exact
                RawTermChildren.areStepNormalForms_blocks_stepChildren
                  (sourceChildren := childTail) tailNormalValue _ tailStep

end

namespace RawTerm

/-- Unit is closed in every scope. -/
theorem isClosed_unit_smoke {scope : Nat} :
    RawTerm.isClosed
      (.mkGen .gen_unit () .childNil : RawTerm scope) := by
  dsimp only [RawTerm.isClosed]
  dsimp only [RawTerm.freeVars]
  rw [dif_neg]
  · exact RawVarSet.isEmpty_empty
  · intro generatorEq
    cases generatorEq

/-- Unit is a beta/iota normal form. -/
theorem isStepNormalForm_unit_smoke {scope : Nat} :
    RawTerm.isStepNormalForm
      (.mkGen .gen_unit () .childNil : RawTerm scope) := by
  rfl

/-- A lambda applied to an argument is detected as a root beta redex. -/
theorem hasRootStepSource_beta_smoke {scope : Nat}
    (domainAnn : RawTerm scope)
    (body : RawTerm (scope + 1)) (arg : RawTerm scope) :
    RawTerm.hasRootStepSource
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_lam ()
            (.childCons domainAnn (.childCons body .childNil)))
          (.childCons arg .childNil))) =
      true := by
  rfl

/-- **Bridge (directional): a `gen_app` cell whose function is not a lambda is no root redex.**
With `Step` now table-driven, `hasRootStepSource (appCell f a)` is the `gen_app` table walk; the only
`gen_app`-headed row is `betaIotaRow`, and it fires only when slot 0 carries a `gen_lam` head — i.e.
`isLamSource f`.  When `f` is not a lambda the walk misses every row: `betaIotaRow` misses on the
scrutinee (`scrutineesFire = false`), the remaining 20 rows miss on the eliminator head (`gen_app` is not
their `elimGenerator`, by `rfl`).  This is the half `TypedChurchNumeralFaithful` needs for the `appCell`
normality equation under the table swap. -/
theorem hasRootStepSource_app_false_of_not_lamSource {scope : Nat}
    {functionTerm argument : RawTerm scope}
    (notLam : RawTerm.isLamSource functionTerm = false) :
    RawTerm.hasRootStepSource
        (.mkGen .gen_app ()
          (.childCons functionTerm (.childCons argument .childNil))) = false := by
  cases functionTerm with
  | mkGen functionGenerator functionPayload functionChildren =>
    have notLamHead : ¬ (functionGenerator = Generator.gen_lam) := by
      intro isLamHead
      subst isLamHead
      rw [show (RawTerm.mkGen Generator.gen_lam functionPayload functionChildren).isLamSource
            = true from rfl] at notLam
      exact Bool.noConfusion notLam
    have betaMisses :
        betaIotaRow.fireAtRoot? (scope := scope) Generator.gen_app ()
            (RawTermChildren.childCons
              (RawTerm.mkGen functionGenerator functionPayload functionChildren)
              (RawTermChildren.childCons argument RawTermChildren.childNil)) = none := by
      dsimp only [IotaRuleDesc.fireAtRoot?, betaIotaRow]
      rw [dif_pos rfl]
      dsimp only [IotaRuleDesc.firesOn?, IotaRuleDesc.scrutineesFire,
        IotaRuleDesc.scrutineeSpecFires, RawTermChildren.toScopedChildren,
        scopedChildAt?, listEntryAt?, ScopedChild.atShiftZero?, Option.bind]
      split
      · rename_i scrutineeFires
        exact absurd scrutineeFires notLamHead
      · rfl
    dsimp only [RawTerm.hasRootStepSource]
    have walkNone :
        fireTableRedexOver iotaRuleTable Generator.gen_app ()
            (RawTermChildren.childCons
              (RawTerm.mkGen functionGenerator functionPayload functionChildren)
              (RawTermChildren.childCons argument RawTermChildren.childNil)) = none := by
      show (match betaIotaRow.fireAtRoot? Generator.gen_app ()
              (RawTermChildren.childCons
                (RawTerm.mkGen functionGenerator functionPayload functionChildren)
                (RawTermChildren.childCons argument RawTermChildren.childNil)) with
            | some reduct => some reduct
            | none =>
              fireTableRedexOver
                [boolTrueIotaRow, boolFalseIotaRow, fstPairIotaRow, sndPairIotaRow,
                  natElimZeroIotaRow, natRecZeroIotaRow, natElimSuccIotaRow, natRecSuccIotaRow,
                  listElimNilIotaRow, listElimConsIotaRow, optionMatchNoneIotaRow,
                  optionMatchSomeIotaRow, eitherMatchInlIotaRow, eitherMatchInrIotaRow,
                  idJReflIotaRow, idStrictRecReflIotaRow, pathBetaIotaRow, quotRecMkIotaRow,
                  quotElimMkIotaRow, truncRecIntroIotaRow] Generator.gen_app ()
                (RawTermChildren.childCons
                  (RawTerm.mkGen functionGenerator functionPayload functionChildren)
                  (RawTermChildren.childCons argument RawTermChildren.childNil))) = none
      rw [betaMisses]
      rfl
    rw [walkNone]
    rfl

/-- The beta smoke is therefore not structurally normal. -/
theorem not_isStepNormalForm_beta_smoke {scope : Nat}
    (domainAnn : RawTerm scope)
    (body : RawTerm (scope + 1)) (arg : RawTerm scope) :
    RawTerm.isStepNormalForm
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_lam ()
            (.childCons domainAnn (.childCons body .childNil)))
          (.childCons arg .childNil))) →
      False := by
  intro normalSource
  cases normalSource

/-- Pair projection is detected as a root iota redex. -/
theorem hasRootStepSource_fst_pair_smoke {scope : Nat}
    (firstValue secondValue : RawTerm scope) :
    RawTerm.hasRootStepSource
      (.mkGen .gen_fst ()
        (.childCons
          (.mkGen .gen_pair ()
            (.childCons firstValue (.childCons secondValue .childNil)))
          .childNil)) =
      true := by
  rfl

/-- Eta sources are not beta/iota root redexes. -/
theorem hasRootStepSource_etaLamSource_smoke {scope : Nat}
    (domainAnn innerFunction : RawTerm scope) :
    RawTerm.hasRootStepSource
      (RawTerm.etaLamSource domainAnn innerFunction) =
      false := by
  rfl

end RawTerm

end FX1Poly.Core
