import FX1Poly.Core.StepEtaTableSubstitution
import FX1Poly.Core.RawTermSubstPair

/-! # EtaTableStar — ETA-T5 increment 4.1: the table eta star and its
substitution diagonals

The stability induction for the cong cases of the eta/iota
quasi-commutation relates template interpretations by ETA-STAR (the
templates duplicate spine children, so a single child eta step fans
out).  This file ships the star and its engines:

  * `StepEtaOverTableStar` / `StepEtaOverTableChildrenStar` —
    head-oriented reflexive-transitive closures, with concatenation
    and the position lifts (`congLift`, `hereLift`, `thereLift`);
  * closure under renaming (per-step `StepEtaOverTable.rename`);
  * `RawTermSubst.PointwiseEtaStar` with `lift`/`iterateLift`
    preservation — position zero is reflexive, later positions weaken
    (the renaming closure per step);
  * ★ `RawTerm.subst_pointwiseEtaStar` — substituting pointwise
    eta-star-related substitutions into ONE term yields eta-star
    (every copy of a moved variable steps in sequence);
  * the `subst0`/`substPair` argument diagonals — the engines for the
    template arms that substitute a stepped child into a motive or
    body.

Zero-axiom: no `sorry`, no `propext`, no `Quot.sound`, no `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditEtaTableStar.lean`. -/

namespace FX1Poly.Core

open FX1Poly.Foundation (RawRenaming)

/-! ## The stars -/

/-- Head-oriented reflexive-transitive closure of table eta steps. -/
inductive StepEtaOverTableStar (etaTable : List EtaRuleDesc) :
    {scope : Nat} → RawTerm scope → RawTerm scope → Prop where
  | refl {scope : Nat} (term : RawTerm scope) :
      StepEtaOverTableStar etaTable term term
  | head {scope : Nat} {source middleTerm target : RawTerm scope}
      (firstStep : StepEtaOverTable etaTable source middleTerm)
      (restStar : StepEtaOverTableStar etaTable middleTerm target) :
      StepEtaOverTableStar etaTable source target

/-- Spine companion star. -/
inductive StepEtaOverTableChildrenStar (etaTable : List EtaRuleDesc) :
    {parentScope : Nat} → {binderShifts : List Nat} →
    RawTermChildren binderShifts parentScope →
    RawTermChildren binderShifts parentScope → Prop where
  | refl {parentScope : Nat} {binderShifts : List Nat}
      (children : RawTermChildren binderShifts parentScope) :
      StepEtaOverTableChildrenStar etaTable children children
  | head {parentScope : Nat} {binderShifts : List Nat}
      {children middleChildren children' :
        RawTermChildren binderShifts parentScope}
      (firstStep :
        StepEtaOverTableChildren etaTable children middleChildren)
      (restStar :
        StepEtaOverTableChildrenStar etaTable middleChildren children') :
      StepEtaOverTableChildrenStar etaTable children children'

/-- A single step is a star. -/
theorem StepEtaOverTableStar.single {etaTable : List EtaRuleDesc}
    {scope : Nat} {source target : RawTerm scope}
    (etaStep : StepEtaOverTable etaTable source target) :
    StepEtaOverTableStar etaTable source target :=
  .head etaStep (.refl target)

/-- Star concatenation. -/
theorem StepEtaOverTableStar.concat {etaTable : List EtaRuleDesc}
    {scope : Nat} {source middleTerm target : RawTerm scope}
    (frontStar : StepEtaOverTableStar etaTable source middleTerm)
    (backStar : StepEtaOverTableStar etaTable middleTerm target) :
    StepEtaOverTableStar etaTable source target := by
  induction frontStar with
  | refl => exact backStar
  | head firstStep _restStar ih => exact .head firstStep (ih backStar)

/-- Spine star concatenation. -/
theorem StepEtaOverTableChildrenStar.concat
    {etaTable : List EtaRuleDesc}
    {parentScope : Nat} {binderShifts : List Nat}
    {children middleChildren children' :
      RawTermChildren binderShifts parentScope}
    (frontStar :
      StepEtaOverTableChildrenStar etaTable children middleChildren)
    (backStar :
      StepEtaOverTableChildrenStar etaTable middleChildren children') :
    StepEtaOverTableChildrenStar etaTable children children' := by
  induction frontStar with
  | refl => exact backStar
  | head firstStep _restStar ih => exact .head firstStep (ih backStar)

/-! ## Position lifts -/

/-- A spine star lifts to a cell star under any generator. -/
theorem StepEtaOverTableStar.congLift {etaTable : List EtaRuleDesc}
    {scope : Nat} (gen : Generator) (payload : gen.payload scope)
    {children children' : RawTermChildren gen.binderShifts scope}
    (childrenStar :
      StepEtaOverTableChildrenStar etaTable children children') :
    StepEtaOverTableStar etaTable (.mkGen gen payload children)
      (.mkGen gen payload children') := by
  induction childrenStar with
  | refl => exact .refl _
  | head firstStep _restStar ih =>
      exact .head (StepEtaOverTable.cong gen payload firstStep) ih

/-- A head star lifts to a spine star with the rest fixed. -/
theorem StepEtaOverTableChildrenStar.hereLift
    {etaTable : List EtaRuleDesc}
    {parentScope headShift : Nat} {restShifts : List Nat}
    {head head' : RawTerm (parentScope + headShift)}
    (rest : RawTermChildren restShifts parentScope)
    (headStar : StepEtaOverTableStar etaTable head head') :
    StepEtaOverTableChildrenStar etaTable
      (RawTermChildren.childCons head rest)
      (RawTermChildren.childCons head' rest) := by
  induction headStar with
  | refl => exact .refl _
  | head firstStep _restStar ih =>
      exact .head (StepEtaOverTableChildren.here rest firstStep) ih

/-- A rest star lifts to a spine star with the head fixed. -/
theorem StepEtaOverTableChildrenStar.thereLift
    {etaTable : List EtaRuleDesc}
    {parentScope headShift : Nat} {restShifts : List Nat}
    (head : RawTerm (parentScope + headShift))
    {rest rest' : RawTermChildren restShifts parentScope}
    (restStar : StepEtaOverTableChildrenStar etaTable rest rest') :
    StepEtaOverTableChildrenStar etaTable
      (RawTermChildren.childCons head rest)
      (RawTermChildren.childCons head rest') := by
  induction restStar with
  | refl => exact .refl _
  | head firstStep _restStar ih =>
      exact .head (StepEtaOverTableChildren.there head firstStep) ih

/-! ## Renaming closure -/

/-- The star is closed under renaming (per-step `rename`). -/
theorem StepEtaOverTableStar.rename {etaTable : List EtaRuleDesc}
    (rowsAreScopeSafe : ∀ rule, rule ∈ etaTable → rule.IsScopeSafe)
    {scope targetScope : Nat}
    (someRenaming : RawRenaming scope targetScope)
    {source target : RawTerm scope}
    (etaStar : StepEtaOverTableStar etaTable source target) :
    StepEtaOverTableStar etaTable (RawTerm.rename someRenaming source)
      (RawTerm.rename someRenaming target) := by
  induction etaStar with
  | refl => exact .refl _
  | head firstStep _restStar ih =>
      exact .head
        (StepEtaOverTable.rename rowsAreScopeSafe someRenaming firstStep)
        ih

/-- The star is closed under weakening. -/
theorem StepEtaOverTableStar.weaken {etaTable : List EtaRuleDesc}
    (rowsAreScopeSafe : ∀ rule, rule ∈ etaTable → rule.IsScopeSafe)
    {scope : Nat} {source target : RawTerm scope}
    (etaStar : StepEtaOverTableStar etaTable source target) :
    StepEtaOverTableStar etaTable (RawTerm.weaken source)
      (RawTerm.weaken target) :=
  StepEtaOverTableStar.rename rowsAreScopeSafe RawRenaming.weaken etaStar

/-! ## Pointwise eta-star substitutions -/

/-- Two substitutions related pointwise by the eta star. -/
def RawTermSubst.PointwiseEtaStar (etaTable : List EtaRuleDesc)
    {scope targetScope : Nat}
    (sigma tau : RawTermSubst scope targetScope) : Prop :=
  ∀ position : Fin scope,
    StepEtaOverTableStar etaTable (sigma position) (tau position)

/-- Pointwise relatedness survives one binder lift: position zero is
reflexive, later positions weaken. -/
theorem RawTermSubst.lift_pointwiseEtaStar {etaTable : List EtaRuleDesc}
    (rowsAreScopeSafe : ∀ rule, rule ∈ etaTable → rule.IsScopeSafe)
    {scope targetScope : Nat}
    {sigma tau : RawTermSubst scope targetScope}
    (relatedness : RawTermSubst.PointwiseEtaStar etaTable sigma tau) :
    RawTermSubst.PointwiseEtaStar etaTable sigma.lift tau.lift := by
  intro position
  match position with
  | ⟨0, _⟩ => exact .refl _
  | ⟨priorPositionValue + 1, positionBound⟩ =>
      exact StepEtaOverTableStar.weaken rowsAreScopeSafe
        (relatedness
          ⟨priorPositionValue, Nat.lt_of_succ_lt_succ positionBound⟩)

/-- Pointwise relatedness survives any iterated lift. -/
theorem RawTermSubst.iterateLift_pointwiseEtaStar
    {etaTable : List EtaRuleDesc}
    (rowsAreScopeSafe : ∀ rule, rule ∈ etaTable → rule.IsScopeSafe)
    {scope targetScope : Nat}
    {sigma tau : RawTermSubst scope targetScope}
    (relatedness : RawTermSubst.PointwiseEtaStar etaTable sigma tau) :
    (depth : Nat) →
    RawTermSubst.PointwiseEtaStar etaTable
      (iterateLiftRaw sigma depth) (iterateLiftRaw tau depth)
  | 0 => relatedness
  | depth + 1 =>
      RawTermSubst.lift_pointwiseEtaStar rowsAreScopeSafe
        (RawTermSubst.iterateLift_pointwiseEtaStar rowsAreScopeSafe
          relatedness depth)

/-! ## ★ The term-monotone substitution star -/

mutual

/-- ★ **Substituting pointwise eta-star-related substitutions into one
term yields an eta star** — every copy of a moved variable steps in
sequence.  The diagonal's right leg. -/
theorem RawTerm.subst_pointwiseEtaStar {etaTable : List EtaRuleDesc}
    (rowsAreScopeSafe : ∀ rule, rule ∈ etaTable → rule.IsScopeSafe) :
    {scope targetScope : Nat} → (term : RawTerm scope) →
    {sigma tau : RawTermSubst scope targetScope} →
    RawTermSubst.PointwiseEtaStar etaTable sigma tau →
    StepEtaOverTableStar etaTable (RawTerm.subst sigma term)
      (RawTerm.subst tau term)
  | scope, targetScope, .mkGen generator payload children,
      sigma, tau, relatedness => by
      by_cases isVarGen : generator = .gen_var
      case pos =>
        subst isVarGen
        show StepEtaOverTableStar etaTable (sigma payload) (tau payload)
        exact relatedness payload
      case neg =>
        rw [RawTerm.subst_nonVar_reduces sigma isVarGen payload _,
          RawTerm.subst_nonVar_reduces tau isVarGen payload _]
        exact StepEtaOverTableStar.congLift generator _
          (RawTermChildren.subst_pointwiseEtaStar rowsAreScopeSafe
            children relatedness)

/-- Spine companion: per-child stars (iterate-lifted) composed across
positions. -/
theorem RawTermChildren.subst_pointwiseEtaStar
    {etaTable : List EtaRuleDesc}
    (rowsAreScopeSafe : ∀ rule, rule ∈ etaTable → rule.IsScopeSafe) :
    {parentScope parentTargetScope : Nat} → {binderShifts : List Nat} →
    (children : RawTermChildren binderShifts parentScope) →
    {sigma tau : RawTermSubst parentScope parentTargetScope} →
    RawTermSubst.PointwiseEtaStar etaTable sigma tau →
    StepEtaOverTableChildrenStar etaTable
      (RawTermChildren.subst sigma children)
      (RawTermChildren.subst tau children)
  | _, _, _, .childNil, _, _, _ => .refl _
  | _parentScope, _, _,
      @RawTermChildren.childCons _ headShift _ head rest,
      sigma, tau, relatedness =>
      StepEtaOverTableChildrenStar.concat
        (StepEtaOverTableChildrenStar.hereLift
          (RawTermChildren.subst sigma rest)
          (RawTerm.subst_pointwiseEtaStar rowsAreScopeSafe head
            (RawTermSubst.iterateLift_pointwiseEtaStar rowsAreScopeSafe
              relatedness headShift)))
        (StepEtaOverTableChildrenStar.thereLift
          (RawTerm.subst (iterateLiftRaw tau headShift) head)
          (RawTermChildren.subst_pointwiseEtaStar rowsAreScopeSafe rest
            relatedness))

end

/-! ## The argument diagonals -/

/-- The singleton substitutions of star-related arguments are pointwise
related. -/
theorem RawTermSubst.singleton_pointwiseEtaStar
    {etaTable : List EtaRuleDesc} {scope : Nat}
    {arg arg' : RawTerm scope}
    (argStar : StepEtaOverTableStar etaTable arg arg') :
    RawTermSubst.PointwiseEtaStar etaTable
      (RawTermSubst.singleton arg) (RawTermSubst.singleton arg') := by
  intro position
  match position with
  | ⟨0, _⟩ => exact argStar
  | ⟨_ + 1, _⟩ => exact .refl _

/-- The pair substitutions of star-related arguments are pointwise
related. -/
theorem RawTermSubst.pair_pointwiseEtaStar
    {etaTable : List EtaRuleDesc} {scope : Nat}
    {innerArg innerArg' outerArg outerArg' : RawTerm scope}
    (innerStar : StepEtaOverTableStar etaTable innerArg innerArg')
    (outerStar : StepEtaOverTableStar etaTable outerArg outerArg') :
    RawTermSubst.PointwiseEtaStar etaTable
      (RawTermSubst.pair innerArg outerArg)
      (RawTermSubst.pair innerArg' outerArg') := by
  intro position
  match position with
  | ⟨0, _⟩ => exact innerStar
  | ⟨1, _⟩ => exact outerStar
  | ⟨_ + 2, _⟩ => exact .refl _

/-- **The one-binder argument diagonal**: a stepped argument
substitutes into a fixed body as an eta star (one step per copy). -/
theorem StepEtaOverTableStar.subst0_argDiagonal
    {etaTable : List EtaRuleDesc}
    (rowsAreScopeSafe : ∀ rule, rule ∈ etaTable → rule.IsScopeSafe)
    {scope : Nat} (body : RawTerm (scope + 1))
    {arg arg' : RawTerm scope}
    (argStar : StepEtaOverTableStar etaTable arg arg') :
    StepEtaOverTableStar etaTable (RawTerm.subst0 body arg)
      (RawTerm.subst0 body arg') :=
  RawTerm.subst_pointwiseEtaStar rowsAreScopeSafe body
    (RawTermSubst.singleton_pointwiseEtaStar argStar)

/-- **The two-binder argument diagonal**. -/
theorem StepEtaOverTableStar.substPair_argDiagonal
    {etaTable : List EtaRuleDesc}
    (rowsAreScopeSafe : ∀ rule, rule ∈ etaTable → rule.IsScopeSafe)
    {scope : Nat} (body : RawTerm (scope + 2))
    {innerArg innerArg' outerArg outerArg' : RawTerm scope}
    (innerStar : StepEtaOverTableStar etaTable innerArg innerArg')
    (outerStar : StepEtaOverTableStar etaTable outerArg outerArg') :
    StepEtaOverTableStar etaTable
      (RawTerm.substPair body innerArg outerArg)
      (RawTerm.substPair body innerArg' outerArg') :=
  RawTerm.subst_pointwiseEtaStar rowsAreScopeSafe body
    (RawTermSubst.pair_pointwiseEtaStar innerStar outerStar)

/-- **The full one-binder diagonal**: body steps once (substitution
closure), argument stars (copy fan-out). -/
theorem StepEtaOverTableStar.subst0_diagonal
    {etaTable : List EtaRuleDesc}
    (rowsAreScopeSafe : ∀ rule, rule ∈ etaTable → rule.IsScopeSafe)
    {scope : Nat} {body body' : RawTerm (scope + 1)}
    {arg arg' : RawTerm scope}
    (bodyStar : StepEtaOverTableStar etaTable body body')
    (argStar : StepEtaOverTableStar etaTable arg arg') :
    StepEtaOverTableStar etaTable (RawTerm.subst0 body arg)
      (RawTerm.subst0 body' arg') := by
  refine StepEtaOverTableStar.concat
    (StepEtaOverTableStar.subst0_argDiagonal rowsAreScopeSafe body
      argStar) ?_
  induction bodyStar with
  | refl => exact .refl _
  | head firstStep _restStar ih =>
      exact .head
        (StepEtaOverTable.subst rowsAreScopeSafe
          (RawTermSubst.singleton arg') firstStep) ih

end FX1Poly.Core
