import LeanFX2.Reduction.RawPar

/-! # Reduction/RawParInversion — inversion lemmas for RawStep.par

For each `RawTerm` constructor `C`, the lemma `RawStep.par.C_inv`
states: when `RawStep.par (C args) target`, `target` has the same
shape `C args'` with appropriate parallel-step relations on the
sub-terms (or `target = C args` for nullary canonical ctors).

These work because `RawStep.par` is indexed only by `scope : Nat`
(no Ty indices), so Lean's `cases` tactic decomposes the inductive
without dependent-elimination conflicts.  Per
`feedback_lean_match_arity_axioms.md`, single-Nat-indexed inductives
do NOT trigger propext+Quot.sound on `cases`.

These are exactly what `RawStep.par.cd_lemma`'s deep cases need:
from "subterm reduces to canonical via the IH" we recover the
canonical structure of the IH's target, allowing the deep-rule's
contraction shape to be matched.

## Modal ctors

`modIntro_inv`, `modElim_inv`, `subsume_inv` follow the same pattern
as `optionSome_inv` / `eitherInl_inv` (single subterm cong).  No
`iota` rule applies to modal cases since lean-fx-2's RawStep.par
omits `iotaModal*`; the modality reduction lives in Layer 6.
-/

namespace LeanFX2

/-- `RawStep.par (lam body) target → target = lam body' ∧ par body body'`. -/
theorem RawStep.par.lam_inv {scope : Nat} {body : RawTerm (scope + 1)}
    {target : RawTerm scope}
    (parallelStep : RawStep.par (RawTerm.lam body) target) :
    ∃ bodyTarget, target = RawTerm.lam bodyTarget ∧
      RawStep.par body bodyTarget := by
  cases parallelStep with
  | refl _ => exact ⟨body, rfl, RawStep.par.refl _⟩
  | lam bodyStep => exact ⟨_, rfl, bodyStep⟩

/-- `RawStep.par (pair fv sv) target → target = pair fv' sv' ∧ pars`. -/
theorem RawStep.par.pair_inv {scope : Nat}
    {firstValue secondValue : RawTerm scope} {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.pair firstValue secondValue) target) :
    ∃ firstTarget secondTarget,
      target = RawTerm.pair firstTarget secondTarget ∧
        RawStep.par firstValue firstTarget ∧
        RawStep.par secondValue secondTarget := by
  cases parallelStep with
  | refl _ =>
      exact ⟨firstValue, secondValue, rfl,
        RawStep.par.refl _, RawStep.par.refl _⟩
  | pair firstStep secondStep => exact ⟨_, _, rfl, firstStep, secondStep⟩

/-- `RawStep.par (refl rw) target → target = refl rw' ∧ par rw rw'`.
Note that RawStep.par.reflCong's existence makes this distinct from
`pair_inv` — refl is NOT frozen at the raw level. -/
theorem RawStep.par.refl_inv {scope : Nat}
    {rawWitness : RawTerm scope} {target : RawTerm scope}
    (parallelStep : RawStep.par (RawTerm.refl rawWitness) target) :
    ∃ witnessTarget, target = RawTerm.refl witnessTarget ∧
      RawStep.par rawWitness witnessTarget := by
  cases parallelStep with
  | refl _ => exact ⟨rawWitness, rfl, RawStep.par.refl _⟩
  | reflCong witnessStep => exact ⟨_, rfl, witnessStep⟩

/-- `RawStep.par boolTrue target → target = boolTrue` (canonical). -/
theorem RawStep.par.boolTrue_inv {scope : Nat}
    {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.boolTrue : RawTerm scope) target) :
    target = RawTerm.boolTrue := by
  cases parallelStep
  case refl _ => rfl

/-- `RawStep.par boolFalse target → target = boolFalse`. -/
theorem RawStep.par.boolFalse_inv {scope : Nat}
    {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.boolFalse : RawTerm scope) target) :
    target = RawTerm.boolFalse := by
  cases parallelStep
  case refl _ => rfl

/-- `RawStep.par natZero target → target = natZero`. -/
theorem RawStep.par.natZero_inv {scope : Nat}
    {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.natZero : RawTerm scope) target) :
    target = RawTerm.natZero := by
  cases parallelStep
  case refl _ => rfl

/-- `RawStep.par (natSucc p) target → target = natSucc p' ∧ par p p'`. -/
theorem RawStep.par.natSucc_inv {scope : Nat}
    {predecessor : RawTerm scope} {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.natSucc predecessor) target) :
    ∃ predecessorTarget, target = RawTerm.natSucc predecessorTarget ∧
      RawStep.par predecessor predecessorTarget := by
  cases parallelStep with
  | refl _ => exact ⟨predecessor, rfl, RawStep.par.refl _⟩
  | natSucc predecessorStep => exact ⟨_, rfl, predecessorStep⟩

/-- `RawStep.par listNil target → target = listNil`. -/
theorem RawStep.par.listNil_inv {scope : Nat}
    {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.listNil : RawTerm scope) target) :
    target = RawTerm.listNil := by
  cases parallelStep
  case refl _ => rfl

/-- `RawStep.par (listCons h t) target → target = listCons h' t' ∧ pars`. -/
theorem RawStep.par.listCons_inv {scope : Nat}
    {headTerm tailTerm : RawTerm scope} {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.listCons headTerm tailTerm) target) :
    ∃ headTarget tailTarget,
      target = RawTerm.listCons headTarget tailTarget ∧
        RawStep.par headTerm headTarget ∧
        RawStep.par tailTerm tailTarget := by
  cases parallelStep with
  | refl _ =>
      exact ⟨headTerm, tailTerm, rfl,
        RawStep.par.refl _, RawStep.par.refl _⟩
  | listCons headStep tailStep => exact ⟨_, _, rfl, headStep, tailStep⟩

/-- `RawStep.par optionNone target → target = optionNone`. -/
theorem RawStep.par.optionNone_inv {scope : Nat}
    {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.optionNone : RawTerm scope) target) :
    target = RawTerm.optionNone := by
  cases parallelStep
  case refl _ => rfl

/-- `RawStep.par (optionSome v) target → target = optionSome v' ∧ par v v'`. -/
theorem RawStep.par.optionSome_inv {scope : Nat}
    {valueTerm : RawTerm scope} {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.optionSome valueTerm) target) :
    ∃ valueTarget, target = RawTerm.optionSome valueTarget ∧
      RawStep.par valueTerm valueTarget := by
  cases parallelStep with
  | refl _ => exact ⟨valueTerm, rfl, RawStep.par.refl _⟩
  | optionSome valueStep => exact ⟨_, rfl, valueStep⟩

/-- `RawStep.par (eitherInl v) target → target = eitherInl v' ∧ par v v'`. -/
theorem RawStep.par.eitherInl_inv {scope : Nat}
    {valueTerm : RawTerm scope} {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.eitherInl valueTerm) target) :
    ∃ valueTarget, target = RawTerm.eitherInl valueTarget ∧
      RawStep.par valueTerm valueTarget := by
  cases parallelStep with
  | refl _ => exact ⟨valueTerm, rfl, RawStep.par.refl _⟩
  | eitherInl valueStep => exact ⟨_, rfl, valueStep⟩

/-- `RawStep.par (eitherInr v) target → target = eitherInr v' ∧ par v v'`. -/
theorem RawStep.par.eitherInr_inv {scope : Nat}
    {valueTerm : RawTerm scope} {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.eitherInr valueTerm) target) :
    ∃ valueTarget, target = RawTerm.eitherInr valueTarget ∧
      RawStep.par valueTerm valueTarget := by
  cases parallelStep with
  | refl _ => exact ⟨valueTerm, rfl, RawStep.par.refl _⟩
  | eitherInr valueStep => exact ⟨_, rfl, valueStep⟩

/-- `RawStep.par (modIntro inner) target → target = modIntro inner' ∧ par`. -/
theorem RawStep.par.modIntro_inv {scope : Nat}
    {innerTerm : RawTerm scope} {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.modIntro innerTerm) target) :
    ∃ innerTarget, target = RawTerm.modIntro innerTarget ∧
      RawStep.par innerTerm innerTarget := by
  cases parallelStep with
  | refl _ => exact ⟨innerTerm, rfl, RawStep.par.refl _⟩
  | modIntro innerStep => exact ⟨_, rfl, innerStep⟩

/-- `RawStep.par (modElim inner) target` either stays a congruent
`modElim`, or fires modal β after the inner value develops to a
`modIntro`. -/
theorem RawStep.par.modElim_inv {scope : Nat}
    {innerTerm : RawTerm scope} {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.modElim innerTerm) target) :
    (∃ innerTarget, target = RawTerm.modElim innerTarget ∧
      RawStep.par innerTerm innerTarget) ∨
    (∃ payloadTarget, target = payloadTarget ∧
      RawStep.par innerTerm (RawTerm.modIntro payloadTarget)) := by
  cases parallelStep with
  | refl _ => exact Or.inl ⟨innerTerm, rfl, RawStep.par.refl _⟩
  | modElim innerStep => exact Or.inl ⟨_, rfl, innerStep⟩
  | betaModElimIntro innerStep =>
      exact Or.inr ⟨_, rfl, RawStep.par.modIntro innerStep⟩
  | betaModElimIntroDeep innerStep =>
      exact Or.inr ⟨_, rfl, innerStep⟩

/-- `RawStep.par (subsume inner) target → target = subsume inner' ∧ par`. -/
theorem RawStep.par.subsume_inv {scope : Nat}
    {innerTerm : RawTerm scope} {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.subsume innerTerm) target) :
    ∃ innerTarget, target = RawTerm.subsume innerTarget ∧
      RawStep.par innerTerm innerTarget := by
  cases parallelStep with
  | refl _ => exact ⟨innerTerm, rfl, RawStep.par.refl _⟩
  | subsume innerStep => exact ⟨_, rfl, innerStep⟩

/-! ## D1.6 inversion lemmas — 27 new ctors.

Each inversion follows the same skeleton as the existing ctors: `cases`
on the parallel-step, `refl` arm uses the source unchanged, every cong
arm yields the matching reduced shape.  Trivial nullary canonical ctors
(interval0, interval1) just say `target = ctor`.

These are needed by deep-rule cases in cd_lemma when β/ι rules for the
new ctors land at D2.5–D2.7. -/

/-- `RawStep.par interval0 target → target = interval0`. -/
theorem RawStep.par.interval0_inv {scope : Nat}
    {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.interval0 : RawTerm scope) target) :
    target = RawTerm.interval0 := by
  cases parallelStep
  case refl _ => rfl

/-- `RawStep.par interval1 target → target = interval1`. -/
theorem RawStep.par.interval1_inv {scope : Nat}
    {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.interval1 : RawTerm scope) target) :
    target = RawTerm.interval1 := by
  cases parallelStep
  case refl _ => rfl

/-- `RawStep.par (intervalOpp t) target → target = intervalOpp t' ∧ par t t'`. -/
theorem RawStep.par.intervalOpp_inv {scope : Nat}
    {intervalTerm : RawTerm scope} {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.intervalOpp intervalTerm) target) :
    ∃ intervalTarget, target = RawTerm.intervalOpp intervalTarget ∧
      RawStep.par intervalTerm intervalTarget := by
  cases parallelStep with
  | refl _ => exact ⟨intervalTerm, rfl, RawStep.par.refl _⟩
  | intervalOppCong intervalStep => exact ⟨_, rfl, intervalStep⟩

/-- `RawStep.par (intervalMeet l r) target → target = intervalMeet l' r' ∧ pars`. -/
theorem RawStep.par.intervalMeet_inv {scope : Nat}
    {leftInterval rightInterval : RawTerm scope} {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.intervalMeet leftInterval rightInterval) target) :
    ∃ leftTarget rightTarget,
      target = RawTerm.intervalMeet leftTarget rightTarget ∧
        RawStep.par leftInterval leftTarget ∧
        RawStep.par rightInterval rightTarget := by
  cases parallelStep with
  | refl _ =>
      exact ⟨leftInterval, rightInterval, rfl,
        RawStep.par.refl _, RawStep.par.refl _⟩
  | intervalMeetCong leftStep rightStep =>
      exact ⟨_, _, rfl, leftStep, rightStep⟩

/-- `RawStep.par (intervalJoin l r) target → target = intervalJoin l' r' ∧ pars`. -/
theorem RawStep.par.intervalJoin_inv {scope : Nat}
    {leftInterval rightInterval : RawTerm scope} {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.intervalJoin leftInterval rightInterval) target) :
    ∃ leftTarget rightTarget,
      target = RawTerm.intervalJoin leftTarget rightTarget ∧
        RawStep.par leftInterval leftTarget ∧
        RawStep.par rightInterval rightTarget := by
  cases parallelStep with
  | refl _ =>
      exact ⟨leftInterval, rightInterval, rfl,
        RawStep.par.refl _, RawStep.par.refl _⟩
  | intervalJoinCong leftStep rightStep =>
      exact ⟨_, _, rfl, leftStep, rightStep⟩

/-- `RawStep.par (pathLam body) target → target = pathLam body' ∧ par`. -/
theorem RawStep.par.pathLam_inv {scope : Nat}
    {body : RawTerm (scope + 1)} {target : RawTerm scope}
    (parallelStep : RawStep.par (RawTerm.pathLam body) target) :
    ∃ bodyTarget, target = RawTerm.pathLam bodyTarget ∧
      RawStep.par body bodyTarget := by
  cases parallelStep with
  | refl _ => exact ⟨body, rfl, RawStep.par.refl _⟩
  | pathLamCong bodyStep => exact ⟨_, rfl, bodyStep⟩

/-- `RawStep.par (pathApp p i) target` either stays a congruent
`pathApp`, or fires cubical path β after the path develops to a
`pathLam`. -/
theorem RawStep.par.pathApp_inv {scope : Nat}
    {pathTerm intervalArg : RawTerm scope} {target : RawTerm scope}
    (parallelStep : RawStep.par (RawTerm.pathApp pathTerm intervalArg) target) :
    (∃ pathTarget intervalTarget,
      target = RawTerm.pathApp pathTarget intervalTarget ∧
        RawStep.par pathTerm pathTarget ∧
        RawStep.par intervalArg intervalTarget) ∨
    (∃ bodyTarget intervalTarget,
      target = bodyTarget.subst0 intervalTarget ∧
        RawStep.par pathTerm (RawTerm.pathLam bodyTarget) ∧
        RawStep.par intervalArg intervalTarget) := by
  cases parallelStep with
  | refl _ =>
      exact Or.inl ⟨pathTerm, intervalArg, rfl,
        RawStep.par.refl _, RawStep.par.refl _⟩
  | pathAppCong pathStep intervalStep =>
      exact Or.inl ⟨_, _, rfl, pathStep, intervalStep⟩
  | betaPathApp bodyStep intervalStep =>
      exact Or.inr ⟨_, _, rfl, RawStep.par.pathLamCong bodyStep, intervalStep⟩
  | betaPathAppDeep pathStep intervalStep =>
      exact Or.inr ⟨_, _, rfl, pathStep, intervalStep⟩

/-- `RawStep.par (glueIntro b p) target → target = glueIntro b' p' ∧ pars`. -/
theorem RawStep.par.glueIntro_inv {scope : Nat}
    {baseValue partialValue : RawTerm scope} {target : RawTerm scope}
    (parallelStep : RawStep.par (RawTerm.glueIntro baseValue partialValue) target) :
    ∃ baseTarget partialTarget,
      target = RawTerm.glueIntro baseTarget partialTarget ∧
        RawStep.par baseValue baseTarget ∧
        RawStep.par partialValue partialTarget := by
  cases parallelStep with
  | refl _ =>
      exact ⟨baseValue, partialValue, rfl,
        RawStep.par.refl _, RawStep.par.refl _⟩
  | glueIntroCong baseStep partialStep =>
      exact ⟨_, _, rfl, baseStep, partialStep⟩

/-- `RawStep.par (glueElim g) target` either stays a congruent
`glueElim`, or fires Glue β after the glued value develops to a
`glueIntro`. -/
theorem RawStep.par.glueElim_inv {scope : Nat}
    {gluedValue : RawTerm scope} {target : RawTerm scope}
    (parallelStep : RawStep.par (RawTerm.glueElim gluedValue) target) :
    (∃ gluedTarget, target = RawTerm.glueElim gluedTarget ∧
      RawStep.par gluedValue gluedTarget) ∨
    (∃ baseTarget partialTarget,
      target = baseTarget ∧
        RawStep.par gluedValue
          (RawTerm.glueIntro baseTarget partialTarget)) := by
  cases parallelStep with
  | refl _ => exact Or.inl ⟨gluedValue, rfl, RawStep.par.refl _⟩
  | betaGlueElimIntro baseStep partialStep =>
      exact Or.inr ⟨_, _, rfl,
        RawStep.par.glueIntroCong baseStep partialStep⟩
  | betaGlueElimIntroDeep gluedStep =>
      exact Or.inr ⟨_, _, rfl, gluedStep⟩
  | glueElimCong gluedStep => exact Or.inl ⟨_, rfl, gluedStep⟩

/-- Inversion of `RawStep.par` on a `transp` head: either the target
is again a `transp` (refl / transpCong cases), the LHS path was a
constant `pathLam typeRaw.weaken` and the rule fired through
`transpReflBeta`, or the path develops to a constant pathLam-weaken
via parallel step (deep-β `transpReflBetaDeep`). -/
theorem RawStep.par.transp_inv {scope : Nat}
    {pathTerm sourceTerm : RawTerm scope} {target : RawTerm scope}
    (parallelStep : RawStep.par (RawTerm.transp pathTerm sourceTerm) target) :
    (∃ pathTarget sourceTarget,
        target = RawTerm.transp pathTarget sourceTarget ∧
          RawStep.par pathTerm pathTarget ∧
          RawStep.par sourceTerm sourceTarget) ∨
    (∃ (typeRawSource : RawTerm scope) (sourceTarget : RawTerm scope),
        pathTerm = RawTerm.pathLam typeRawSource.weaken ∧
        target = sourceTarget ∧
        RawStep.par sourceTerm sourceTarget) ∨
    (∃ (typeRawTarget : RawTerm scope) (sourceTarget : RawTerm scope),
        target = sourceTarget ∧
        RawStep.par pathTerm (RawTerm.pathLam typeRawTarget.weaken) ∧
        RawStep.par sourceTerm sourceTarget) := by
  cases parallelStep with
  | refl _ =>
      exact Or.inl ⟨pathTerm, sourceTerm, rfl,
        RawStep.par.refl _, RawStep.par.refl _⟩
  | transpCong pathStep sourceStep =>
      exact Or.inl ⟨_, _, rfl, pathStep, sourceStep⟩
  | @transpReflBeta _ typeRawSource _ _ _ _ sourceStep =>
      exact Or.inr (Or.inl ⟨typeRawSource, _, rfl, rfl, sourceStep⟩)
  | @transpReflBetaDeep _ _ typeRawTarget _ _ pathStep sourceStep =>
      exact Or.inr (Or.inr ⟨typeRawTarget, _, rfl, pathStep, sourceStep⟩)

/-- `RawStep.par (hcomp s c) target → target = hcomp s' c' ∧ pars`. -/
theorem RawStep.par.hcomp_inv {scope : Nat}
    {sidesTerm capTerm : RawTerm scope} {target : RawTerm scope}
    (parallelStep : RawStep.par (RawTerm.hcomp sidesTerm capTerm) target) :
    ∃ sidesTarget capTarget,
      target = RawTerm.hcomp sidesTarget capTarget ∧
        RawStep.par sidesTerm sidesTarget ∧
        RawStep.par capTerm capTarget := by
  cases parallelStep with
  | refl _ =>
      exact ⟨sidesTerm, capTerm, rfl,
        RawStep.par.refl _, RawStep.par.refl _⟩
  | hcompCong sidesStep capStep =>
      exact ⟨_, _, rfl, sidesStep, capStep⟩

/-- `RawStep.par (oeqRefl w) target → target = oeqRefl w' ∧ par w w'`. -/
theorem RawStep.par.oeqRefl_inv {scope : Nat}
    {witness : RawTerm scope} {target : RawTerm scope}
    (parallelStep : RawStep.par (RawTerm.oeqRefl witness) target) :
    ∃ witnessTarget, target = RawTerm.oeqRefl witnessTarget ∧
      RawStep.par witness witnessTarget := by
  cases parallelStep with
  | refl _ => exact ⟨witness, rfl, RawStep.par.refl _⟩
  | oeqReflCong witnessStep => exact ⟨_, rfl, witnessStep⟩

/-- `RawStep.par (oeqJ b w) target → target = oeqJ b' w' ∧ pars`. -/
theorem RawStep.par.oeqJ_inv {scope : Nat}
    {baseCase witness : RawTerm scope} {target : RawTerm scope}
    (parallelStep : RawStep.par (RawTerm.oeqJ baseCase witness) target) :
    ∃ baseTarget witnessTarget,
      target = RawTerm.oeqJ baseTarget witnessTarget ∧
        RawStep.par baseCase baseTarget ∧
        RawStep.par witness witnessTarget := by
  cases parallelStep with
  | refl _ =>
      exact ⟨baseCase, witness, rfl,
        RawStep.par.refl _, RawStep.par.refl _⟩
  | oeqJCong baseStep witnessStep =>
      exact ⟨_, _, rfl, baseStep, witnessStep⟩

/-- `RawStep.par (oeqFunext p) target → target = oeqFunext p' ∧ par`. -/
theorem RawStep.par.oeqFunext_inv {scope : Nat}
    {pointwiseEquality : RawTerm scope} {target : RawTerm scope}
    (parallelStep : RawStep.par (RawTerm.oeqFunext pointwiseEquality) target) :
    ∃ pointwiseTarget, target = RawTerm.oeqFunext pointwiseTarget ∧
      RawStep.par pointwiseEquality pointwiseTarget := by
  cases parallelStep with
  | refl _ => exact ⟨pointwiseEquality, rfl, RawStep.par.refl _⟩
  | oeqFunextCong pointwiseStep => exact ⟨_, rfl, pointwiseStep⟩

/-- `RawStep.par (idStrictRefl w) target → target = idStrictRefl w' ∧ par`. -/
theorem RawStep.par.idStrictRefl_inv {scope : Nat}
    {witness : RawTerm scope} {target : RawTerm scope}
    (parallelStep : RawStep.par (RawTerm.idStrictRefl witness) target) :
    ∃ witnessTarget, target = RawTerm.idStrictRefl witnessTarget ∧
      RawStep.par witness witnessTarget := by
  cases parallelStep with
  | refl _ => exact ⟨witness, rfl, RawStep.par.refl _⟩
  | idStrictReflCong witnessStep => exact ⟨_, rfl, witnessStep⟩

/-- `RawStep.par (idStrictRec b w) target` either remains a strict recursor
or fires the strict-id ι rule. -/
theorem RawStep.par.idStrictRec_inv {scope : Nat}
    {baseCase witness : RawTerm scope} {target : RawTerm scope}
    (parallelStep : RawStep.par (RawTerm.idStrictRec baseCase witness) target) :
    (∃ baseTarget witnessTarget,
      target = RawTerm.idStrictRec baseTarget witnessTarget ∧
        RawStep.par baseCase baseTarget ∧
        RawStep.par witness witnessTarget) ∨
    (∃ reflRawArgument baseTarget,
      target = baseTarget ∧
        RawStep.par witness (RawTerm.idStrictRefl reflRawArgument) ∧
        RawStep.par baseCase baseTarget) := by
  cases parallelStep with
  | refl _ =>
      exact Or.inl ⟨baseCase, witness, rfl,
        RawStep.par.refl _, RawStep.par.refl _⟩
  | idStrictRecCong baseStep witnessStep =>
      exact Or.inl ⟨_, _, rfl, baseStep, witnessStep⟩
  | iotaIdStrictRecRefl witnessRaw baseStep =>
      exact Or.inr ⟨witnessRaw, _, rfl, RawStep.par.refl _, baseStep⟩
  | iotaIdStrictRecReflDeep witnessStep baseStep =>
      exact Or.inr ⟨_, _, rfl, witnessStep, baseStep⟩

/-- `RawStep.par (equivIntro f b) target → target = equivIntro f' b' ∧ pars`. -/
theorem RawStep.par.equivIntro_inv {scope : Nat}
    {forwardFn backwardFn : RawTerm scope} {target : RawTerm scope}
    (parallelStep : RawStep.par (RawTerm.equivIntro forwardFn backwardFn) target) :
    ∃ forwardTarget backwardTarget,
      target = RawTerm.equivIntro forwardTarget backwardTarget ∧
        RawStep.par forwardFn forwardTarget ∧
        RawStep.par backwardFn backwardTarget := by
  cases parallelStep with
  | refl _ =>
      exact ⟨forwardFn, backwardFn, rfl,
        RawStep.par.refl _, RawStep.par.refl _⟩
  | equivIntroCong forwardStep backwardStep =>
      exact ⟨_, _, rfl, forwardStep, backwardStep⟩

/-- `RawStep.par (equivApp e a) target → target = equivApp e' a' ∧ pars`. -/
theorem RawStep.par.equivApp_inv {scope : Nat}
    {equivTerm argument : RawTerm scope} {target : RawTerm scope}
    (parallelStep : RawStep.par (RawTerm.equivApp equivTerm argument) target) :
    ∃ equivTarget argumentTarget,
      target = RawTerm.equivApp equivTarget argumentTarget ∧
        RawStep.par equivTerm equivTarget ∧
        RawStep.par argument argumentTarget := by
  cases parallelStep with
  | refl _ =>
      exact ⟨equivTerm, argument, rfl,
        RawStep.par.refl _, RawStep.par.refl _⟩
  | equivAppCong equivStep argumentStep =>
      exact ⟨_, _, rfl, equivStep, argumentStep⟩

/-- `RawStep.par (refineIntro v p) target → target = refineIntro v' p' ∧ pars`. -/
theorem RawStep.par.refineIntro_inv {scope : Nat}
    {rawValue predicateProof : RawTerm scope} {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.refineIntro rawValue predicateProof) target) :
    ∃ valueTarget proofTarget,
      target = RawTerm.refineIntro valueTarget proofTarget ∧
        RawStep.par rawValue valueTarget ∧
        RawStep.par predicateProof proofTarget := by
  cases parallelStep with
  | refl _ =>
      exact ⟨rawValue, predicateProof, rfl,
        RawStep.par.refl _, RawStep.par.refl _⟩
  | refineIntroCong valueStep proofStep =>
      exact ⟨_, _, rfl, valueStep, proofStep⟩

/-- `RawStep.par (refineElim r) target` either stays a congruent
`refineElim`, or fires refinement β after the refined value develops
to a `refineIntro`. -/
theorem RawStep.par.refineElim_inv {scope : Nat}
    {refinedValue : RawTerm scope} {target : RawTerm scope}
    (parallelStep : RawStep.par (RawTerm.refineElim refinedValue) target) :
    (∃ refinedTarget, target = RawTerm.refineElim refinedTarget ∧
      RawStep.par refinedValue refinedTarget) ∨
    (∃ valueTarget proofTarget,
      target = valueTarget ∧
        RawStep.par refinedValue
          (RawTerm.refineIntro valueTarget proofTarget)) := by
  cases parallelStep with
  | refl _ => exact Or.inl ⟨refinedValue, rfl, RawStep.par.refl _⟩
  | betaRefineElimIntro valueStep proofStep =>
      exact Or.inr ⟨_, _, rfl,
        RawStep.par.refineIntroCong valueStep proofStep⟩
  | betaRefineElimIntroDeep refinedStep =>
      exact Or.inr ⟨_, _, rfl, refinedStep⟩
  | refineElimCong refinedStep => exact Or.inl ⟨_, rfl, refinedStep⟩

/-- `RawStep.par (recordIntro f) target → target = recordIntro f' ∧ par`. -/
theorem RawStep.par.recordIntro_inv {scope : Nat}
    {firstField : RawTerm scope} {target : RawTerm scope}
    (parallelStep : RawStep.par (RawTerm.recordIntro firstField) target) :
    ∃ firstTarget, target = RawTerm.recordIntro firstTarget ∧
      RawStep.par firstField firstTarget := by
  cases parallelStep with
  | refl _ => exact ⟨firstField, rfl, RawStep.par.refl _⟩
  | recordIntroCong firstStep => exact ⟨_, rfl, firstStep⟩

/-- `RawStep.par (recordProj r) target` either stays a congruent
`recordProj`, or fires record β after the record develops to a
`recordIntro`. -/
theorem RawStep.par.recordProj_inv {scope : Nat}
    {recordValue : RawTerm scope} {target : RawTerm scope}
    (parallelStep : RawStep.par (RawTerm.recordProj recordValue) target) :
    (∃ recordTarget, target = RawTerm.recordProj recordTarget ∧
      RawStep.par recordValue recordTarget) ∨
    (∃ firstTarget, target = firstTarget ∧
      RawStep.par recordValue (RawTerm.recordIntro firstTarget)) := by
  cases parallelStep with
  | refl _ => exact Or.inl ⟨recordValue, rfl, RawStep.par.refl _⟩
  | betaRecordProjIntro firstStep =>
      exact Or.inr ⟨_, rfl, RawStep.par.recordIntroCong firstStep⟩
  | betaRecordProjIntroDeep recordStep =>
      exact Or.inr ⟨_, rfl, recordStep⟩
  | recordProjCong recordStep => exact Or.inl ⟨_, rfl, recordStep⟩

/-- `RawStep.par (codataUnfold s t) target → target = codataUnfold s' t' ∧ pars`. -/
theorem RawStep.par.codataUnfold_inv {scope : Nat}
    {initialState transition : RawTerm scope} {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.codataUnfold initialState transition) target) :
    ∃ stateTarget transitionTarget,
      target = RawTerm.codataUnfold stateTarget transitionTarget ∧
        RawStep.par initialState stateTarget ∧
        RawStep.par transition transitionTarget := by
  cases parallelStep with
  | refl _ =>
      exact ⟨initialState, transition, rfl,
        RawStep.par.refl _, RawStep.par.refl _⟩
  | codataUnfoldCong stateStep transitionStep =>
      exact ⟨_, _, rfl, stateStep, transitionStep⟩

/-- `RawStep.par (codataDest c) target` either stays a congruent
`codataDest`, or fires codata β after the codata value develops to an
unfold. -/
theorem RawStep.par.codataDest_inv {scope : Nat}
    {codataValue : RawTerm scope} {target : RawTerm scope}
    (parallelStep : RawStep.par (RawTerm.codataDest codataValue) target) :
    (∃ codataTarget, target = RawTerm.codataDest codataTarget ∧
      RawStep.par codataValue codataTarget) ∨
    (∃ stateTarget transitionTarget,
      target = RawTerm.app transitionTarget stateTarget ∧
        RawStep.par codataValue
          (RawTerm.codataUnfold stateTarget transitionTarget)) := by
  cases parallelStep with
  | refl _ => exact Or.inl ⟨codataValue, rfl, RawStep.par.refl _⟩
  | betaCodataDestUnfold stateStep transitionStep =>
      exact Or.inr ⟨_, _, rfl,
        RawStep.par.codataUnfoldCong stateStep transitionStep⟩
  | betaCodataDestUnfoldDeep codataStep =>
      exact Or.inr ⟨_, _, rfl, codataStep⟩
  | codataDestCong codataStep => exact Or.inl ⟨_, rfl, codataStep⟩

/-- `RawStep.par (sessionSend c p) target → target = sessionSend c' p' ∧ pars`. -/
theorem RawStep.par.sessionSend_inv {scope : Nat}
    {channel payload : RawTerm scope} {target : RawTerm scope}
    (parallelStep : RawStep.par (RawTerm.sessionSend channel payload) target) :
    ∃ channelTarget payloadTarget,
      target = RawTerm.sessionSend channelTarget payloadTarget ∧
        RawStep.par channel channelTarget ∧
        RawStep.par payload payloadTarget := by
  cases parallelStep with
  | refl _ =>
      exact ⟨channel, payload, rfl,
        RawStep.par.refl _, RawStep.par.refl _⟩
  | sessionSendCong channelStep payloadStep =>
      exact ⟨_, _, rfl, channelStep, payloadStep⟩

/-- `RawStep.par (sessionRecv c) target → target = sessionRecv c' ∧ par`. -/
theorem RawStep.par.sessionRecv_inv {scope : Nat}
    {channel : RawTerm scope} {target : RawTerm scope}
    (parallelStep : RawStep.par (RawTerm.sessionRecv channel) target) :
    ∃ channelTarget, target = RawTerm.sessionRecv channelTarget ∧
      RawStep.par channel channelTarget := by
  cases parallelStep with
  | refl _ => exact ⟨channel, rfl, RawStep.par.refl _⟩
  | sessionRecvCong channelStep => exact ⟨_, rfl, channelStep⟩

/-- `RawStep.par (effectPerform o a) target → target = effectPerform o' a' ∧ pars`. -/
theorem RawStep.par.effectPerform_inv {scope : Nat}
    {operationTag arguments : RawTerm scope} {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.effectPerform operationTag arguments) target) :
    ∃ operationTarget argumentsTarget,
      target = RawTerm.effectPerform operationTarget argumentsTarget ∧
        RawStep.par operationTag operationTarget ∧
        RawStep.par arguments argumentsTarget := by
  cases parallelStep with
  | refl _ =>
      exact ⟨operationTag, arguments, rfl,
        RawStep.par.refl _, RawStep.par.refl _⟩
  | effectPerformCong operationStep argumentsStep =>
      exact ⟨_, _, rfl, operationStep, argumentsStep⟩

/-! ## Redex-parent inversions used by `RawParWeakenInv`.

For each ctor that may fire a redex / Deep par rule, the inversion
returns a disjunction: cong arm vs each redex / Deep variant. -/

/-- `RawStep.par (app f a) target` — refl, cong, shallow β, deep β. -/
theorem RawStep.par.app_inv {scope : Nat}
    {functionTerm argumentTerm : RawTerm scope} {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.app functionTerm argumentTerm) target) :
    (∃ functionTarget argumentTarget,
      target = RawTerm.app functionTarget argumentTarget ∧
        RawStep.par functionTerm functionTarget ∧
        RawStep.par argumentTerm argumentTarget) ∨
    (∃ bodyTarget argumentTarget,
      target = bodyTarget.subst0 argumentTarget ∧
        RawStep.par functionTerm (RawTerm.lam bodyTarget) ∧
        RawStep.par argumentTerm argumentTarget) := by
  cases parallelStep with
  | refl _ =>
      exact Or.inl ⟨functionTerm, argumentTerm, rfl,
        RawStep.par.refl _, RawStep.par.refl _⟩
  | app functionStep argumentStep =>
      exact Or.inl ⟨_, _, rfl, functionStep, argumentStep⟩
  | betaApp bodyStep argumentStep =>
      exact Or.inr ⟨_, _, rfl, RawStep.par.lam bodyStep, argumentStep⟩
  | betaAppDeep functionStep argumentStep =>
      exact Or.inr ⟨_, _, rfl, functionStep, argumentStep⟩

/-- `RawStep.par (fst p) target` — refl, cong, shallow β, deep β. -/
theorem RawStep.par.fst_inv {scope : Nat}
    {pairTerm : RawTerm scope} {target : RawTerm scope}
    (parallelStep : RawStep.par (RawTerm.fst pairTerm) target) :
    (∃ pairTarget,
      target = RawTerm.fst pairTarget ∧
        RawStep.par pairTerm pairTarget) ∨
    (∃ firstTarget secondTarget,
      target = firstTarget ∧
        RawStep.par pairTerm (RawTerm.pair firstTarget secondTarget)) := by
  cases parallelStep with
  | refl _ =>
      exact Or.inl ⟨pairTerm, rfl, RawStep.par.refl _⟩
  | fst pairStep =>
      exact Or.inl ⟨_, rfl, pairStep⟩
  | betaFstPair secondRaw firstStep =>
      exact Or.inr ⟨_, secondRaw, rfl,
        RawStep.par.pair firstStep (RawStep.par.refl _)⟩
  | betaFstPairDeep pairStep =>
      exact Or.inr ⟨_, _, rfl, pairStep⟩

/-- `RawStep.par (snd p) target` — refl, cong, shallow β, deep β. -/
theorem RawStep.par.snd_inv {scope : Nat}
    {pairTerm : RawTerm scope} {target : RawTerm scope}
    (parallelStep : RawStep.par (RawTerm.snd pairTerm) target) :
    (∃ pairTarget,
      target = RawTerm.snd pairTarget ∧
        RawStep.par pairTerm pairTarget) ∨
    (∃ firstTarget secondTarget,
      target = secondTarget ∧
        RawStep.par pairTerm (RawTerm.pair firstTarget secondTarget)) := by
  cases parallelStep with
  | refl _ =>
      exact Or.inl ⟨pairTerm, rfl, RawStep.par.refl _⟩
  | snd pairStep =>
      exact Or.inl ⟨_, rfl, pairStep⟩
  | betaSndPair firstRaw secondStep =>
      exact Or.inr ⟨firstRaw, _, rfl,
        RawStep.par.pair (RawStep.par.refl _) secondStep⟩
  | betaSndPairDeep pairStep =>
      exact Or.inr ⟨_, _, rfl, pairStep⟩

/-- `RawStep.par (boolElim s t e) target` — refl, cong, true-ι, false-ι,
plus their deep variants. -/
theorem RawStep.par.boolElim_inv {scope : Nat}
    {scrutinee thenBranch elseBranch : RawTerm scope}
    {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.boolElim scrutinee thenBranch elseBranch) target) :
    (∃ scrutineeTarget thenTarget elseTarget,
      target = RawTerm.boolElim scrutineeTarget thenTarget elseTarget ∧
        RawStep.par scrutinee scrutineeTarget ∧
        RawStep.par thenBranch thenTarget ∧
        RawStep.par elseBranch elseTarget) ∨
    (∃ thenTarget,
      target = thenTarget ∧
        RawStep.par scrutinee RawTerm.boolTrue ∧
        RawStep.par thenBranch thenTarget) ∨
    (∃ elseTarget,
      target = elseTarget ∧
        RawStep.par scrutinee RawTerm.boolFalse ∧
        RawStep.par elseBranch elseTarget) := by
  cases parallelStep with
  | refl _ =>
      exact Or.inl ⟨scrutinee, thenBranch, elseBranch, rfl,
        RawStep.par.refl _, RawStep.par.refl _, RawStep.par.refl _⟩
  | boolElim scrutineeStep thenStep elseStep =>
      exact Or.inl ⟨_, _, _, rfl, scrutineeStep, thenStep, elseStep⟩
  | iotaBoolElimTrue _elseRaw thenStep =>
      exact Or.inr (Or.inl ⟨_, rfl, RawStep.par.refl _, thenStep⟩)
  | iotaBoolElimFalse _thenRaw elseStep =>
      exact Or.inr (Or.inr ⟨_, rfl, RawStep.par.refl _, elseStep⟩)
  | iotaBoolElimTrueDeep _elseRaw scrutineeStep thenStep =>
      exact Or.inr (Or.inl ⟨_, rfl, scrutineeStep, thenStep⟩)
  | iotaBoolElimFalseDeep _thenRaw scrutineeStep elseStep =>
      exact Or.inr (Or.inr ⟨_, rfl, scrutineeStep, elseStep⟩)

/-- `RawStep.par (natElim s z c) target` — refl, cong, zero-ι, succ-ι,
plus their deep variants. -/
theorem RawStep.par.natElim_inv {scope : Nat}
    {scrutinee zeroBranch succBranch : RawTerm scope}
    {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.natElim scrutinee zeroBranch succBranch) target) :
    (∃ scrutineeTarget zeroTarget succTarget,
      target = RawTerm.natElim scrutineeTarget zeroTarget succTarget ∧
        RawStep.par scrutinee scrutineeTarget ∧
        RawStep.par zeroBranch zeroTarget ∧
        RawStep.par succBranch succTarget) ∨
    (∃ zeroTarget,
      target = zeroTarget ∧
        RawStep.par scrutinee RawTerm.natZero ∧
        RawStep.par zeroBranch zeroTarget) ∨
    (∃ predRaw succTarget,
      target = RawTerm.app succTarget predRaw ∧
        RawStep.par scrutinee (RawTerm.natSucc predRaw) ∧
        RawStep.par succBranch succTarget) := by
  cases parallelStep with
  | refl _ =>
      exact Or.inl ⟨scrutinee, zeroBranch, succBranch, rfl,
        RawStep.par.refl _, RawStep.par.refl _, RawStep.par.refl _⟩
  | natElim scrutineeStep zeroStep succStep =>
      exact Or.inl ⟨_, _, _, rfl, scrutineeStep, zeroStep, succStep⟩
  | iotaNatElimZero _succRaw zeroStep =>
      exact Or.inr (Or.inl ⟨_, rfl, RawStep.par.refl _, zeroStep⟩)
  | iotaNatElimSucc _zeroRaw predStep succStep =>
      exact Or.inr (Or.inr ⟨_, _, rfl, RawStep.par.natSucc predStep, succStep⟩)
  | iotaNatElimZeroDeep _succRaw scrutineeStep zeroStep =>
      exact Or.inr (Or.inl ⟨_, rfl, scrutineeStep, zeroStep⟩)
  | iotaNatElimSuccDeep _zeroRaw scrutineeStep succStep =>
      exact Or.inr (Or.inr ⟨_, _, rfl, scrutineeStep, succStep⟩)

/-- `RawStep.par (natRec s z c) target` — refl, cong, zero-ι, succ-ι,
plus their deep variants. -/
theorem RawStep.par.natRec_inv {scope : Nat}
    {scrutinee zeroBranch succBranch : RawTerm scope}
    {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.natRec scrutinee zeroBranch succBranch) target) :
    (∃ scrutineeTarget zeroTarget succTarget,
      target = RawTerm.natRec scrutineeTarget zeroTarget succTarget ∧
        RawStep.par scrutinee scrutineeTarget ∧
        RawStep.par zeroBranch zeroTarget ∧
        RawStep.par succBranch succTarget) ∨
    (∃ zeroTarget,
      target = zeroTarget ∧
        RawStep.par scrutinee RawTerm.natZero ∧
        RawStep.par zeroBranch zeroTarget) ∨
    (∃ predRaw zeroTarget succTarget,
      target = RawTerm.app (RawTerm.app succTarget predRaw)
                            (RawTerm.natRec predRaw zeroTarget succTarget) ∧
        RawStep.par scrutinee (RawTerm.natSucc predRaw) ∧
        RawStep.par zeroBranch zeroTarget ∧
        RawStep.par succBranch succTarget) := by
  cases parallelStep with
  | refl _ =>
      exact Or.inl ⟨scrutinee, zeroBranch, succBranch, rfl,
        RawStep.par.refl _, RawStep.par.refl _, RawStep.par.refl _⟩
  | natRec scrutineeStep zeroStep succStep =>
      exact Or.inl ⟨_, _, _, rfl, scrutineeStep, zeroStep, succStep⟩
  | iotaNatRecZero _succRaw zeroStep =>
      exact Or.inr (Or.inl ⟨_, rfl, RawStep.par.refl _, zeroStep⟩)
  | iotaNatRecSucc predStep zeroStep succStep =>
      exact Or.inr (Or.inr ⟨_, _, _, rfl, RawStep.par.natSucc predStep,
                              zeroStep, succStep⟩)
  | iotaNatRecZeroDeep _succRaw scrutineeStep zeroStep =>
      exact Or.inr (Or.inl ⟨_, rfl, scrutineeStep, zeroStep⟩)
  | iotaNatRecSuccDeep scrutineeStep zeroStep succStep =>
      exact Or.inr (Or.inr ⟨_, _, _, rfl, scrutineeStep, zeroStep, succStep⟩)

/-- `RawStep.par (listElim s n c) target` — refl, cong, nil-ι, cons-ι,
plus their deep variants. -/
theorem RawStep.par.listElim_inv {scope : Nat}
    {scrutinee nilBranch consBranch : RawTerm scope}
    {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.listElim scrutinee nilBranch consBranch) target) :
    (∃ scrutineeTarget nilTarget consTarget,
      target = RawTerm.listElim scrutineeTarget nilTarget consTarget ∧
        RawStep.par scrutinee scrutineeTarget ∧
        RawStep.par nilBranch nilTarget ∧
        RawStep.par consBranch consTarget) ∨
    (∃ nilTarget,
      target = nilTarget ∧
        RawStep.par scrutinee RawTerm.listNil ∧
        RawStep.par nilBranch nilTarget) ∨
    (∃ headRaw tailRaw consTarget,
      target = RawTerm.app (RawTerm.app consTarget headRaw) tailRaw ∧
        RawStep.par scrutinee (RawTerm.listCons headRaw tailRaw) ∧
        RawStep.par consBranch consTarget) := by
  cases parallelStep with
  | refl _ =>
      exact Or.inl ⟨scrutinee, nilBranch, consBranch, rfl,
        RawStep.par.refl _, RawStep.par.refl _, RawStep.par.refl _⟩
  | listElim scrutineeStep nilStep consStep =>
      exact Or.inl ⟨_, _, _, rfl, scrutineeStep, nilStep, consStep⟩
  | iotaListElimNil _consRaw nilStep =>
      exact Or.inr (Or.inl ⟨_, rfl, RawStep.par.refl _, nilStep⟩)
  | iotaListElimCons _nilRaw headStep tailStep consStep =>
      exact Or.inr (Or.inr ⟨_, _, _, rfl,
        RawStep.par.listCons headStep tailStep, consStep⟩)
  | iotaListElimNilDeep _consRaw scrutineeStep nilStep =>
      exact Or.inr (Or.inl ⟨_, rfl, scrutineeStep, nilStep⟩)
  | iotaListElimConsDeep _nilRaw scrutineeStep consStep =>
      exact Or.inr (Or.inr ⟨_, _, _, rfl, scrutineeStep, consStep⟩)

/-- `RawStep.par (optionMatch s n s') target` — refl, cong, none-ι, some-ι,
plus their deep variants. -/
theorem RawStep.par.optionMatch_inv {scope : Nat}
    {scrutinee noneBranch someBranch : RawTerm scope}
    {target : RawTerm scope}
    (parallelStep :
      RawStep.par
        (RawTerm.optionMatch scrutinee noneBranch someBranch) target) :
    (∃ scrutineeTarget noneTarget someTarget,
      target = RawTerm.optionMatch scrutineeTarget noneTarget someTarget ∧
        RawStep.par scrutinee scrutineeTarget ∧
        RawStep.par noneBranch noneTarget ∧
        RawStep.par someBranch someTarget) ∨
    (∃ noneTarget,
      target = noneTarget ∧
        RawStep.par scrutinee RawTerm.optionNone ∧
        RawStep.par noneBranch noneTarget) ∨
    (∃ valueRaw someTarget,
      target = RawTerm.app someTarget valueRaw ∧
        RawStep.par scrutinee (RawTerm.optionSome valueRaw) ∧
        RawStep.par someBranch someTarget) := by
  cases parallelStep with
  | refl _ =>
      exact Or.inl ⟨scrutinee, noneBranch, someBranch, rfl,
        RawStep.par.refl _, RawStep.par.refl _, RawStep.par.refl _⟩
  | optionMatch scrutineeStep noneStep someStep =>
      exact Or.inl ⟨_, _, _, rfl, scrutineeStep, noneStep, someStep⟩
  | iotaOptionMatchNone _someRaw noneStep =>
      exact Or.inr (Or.inl ⟨_, rfl, RawStep.par.refl _, noneStep⟩)
  | iotaOptionMatchSome _noneRaw valueStep someStep =>
      exact Or.inr (Or.inr ⟨_, _, rfl,
        RawStep.par.optionSome valueStep, someStep⟩)
  | iotaOptionMatchNoneDeep _someRaw scrutineeStep noneStep =>
      exact Or.inr (Or.inl ⟨_, rfl, scrutineeStep, noneStep⟩)
  | iotaOptionMatchSomeDeep _noneRaw scrutineeStep someStep =>
      exact Or.inr (Or.inr ⟨_, _, rfl, scrutineeStep, someStep⟩)

/-- `RawStep.par (eitherMatch s l r) target` — refl, cong, inl-ι, inr-ι,
plus their deep variants. -/
theorem RawStep.par.eitherMatch_inv {scope : Nat}
    {scrutinee leftBranch rightBranch : RawTerm scope}
    {target : RawTerm scope}
    (parallelStep :
      RawStep.par
        (RawTerm.eitherMatch scrutinee leftBranch rightBranch) target) :
    (∃ scrutineeTarget leftTarget rightTarget,
      target = RawTerm.eitherMatch scrutineeTarget leftTarget rightTarget ∧
        RawStep.par scrutinee scrutineeTarget ∧
        RawStep.par leftBranch leftTarget ∧
        RawStep.par rightBranch rightTarget) ∨
    (∃ valueRaw leftTarget,
      target = RawTerm.app leftTarget valueRaw ∧
        RawStep.par scrutinee (RawTerm.eitherInl valueRaw) ∧
        RawStep.par leftBranch leftTarget) ∨
    (∃ valueRaw rightTarget,
      target = RawTerm.app rightTarget valueRaw ∧
        RawStep.par scrutinee (RawTerm.eitherInr valueRaw) ∧
        RawStep.par rightBranch rightTarget) := by
  cases parallelStep with
  | refl _ =>
      exact Or.inl ⟨scrutinee, leftBranch, rightBranch, rfl,
        RawStep.par.refl _, RawStep.par.refl _, RawStep.par.refl _⟩
  | eitherMatch scrutineeStep leftStep rightStep =>
      exact Or.inl ⟨_, _, _, rfl, scrutineeStep, leftStep, rightStep⟩
  | iotaEitherMatchInl _rightRaw valueStep leftStep =>
      exact Or.inr (Or.inl ⟨_, _, rfl,
        RawStep.par.eitherInl valueStep, leftStep⟩)
  | iotaEitherMatchInr _leftRaw valueStep rightStep =>
      exact Or.inr (Or.inr ⟨_, _, rfl,
        RawStep.par.eitherInr valueStep, rightStep⟩)
  | iotaEitherMatchInlDeep _rightRaw scrutineeStep leftStep =>
      exact Or.inr (Or.inl ⟨_, _, rfl, scrutineeStep, leftStep⟩)
  | iotaEitherMatchInrDeep _leftRaw scrutineeStep rightStep =>
      exact Or.inr (Or.inr ⟨_, _, rfl, scrutineeStep, rightStep⟩)

/-- `RawStep.par (idJ b w) target` — refl, cong, refl-ι, deep refl-ι. -/
theorem RawStep.par.idJ_inv {scope : Nat}
    {baseCase witness : RawTerm scope}
    {target : RawTerm scope}
    (parallelStep : RawStep.par (RawTerm.idJ baseCase witness) target) :
    (∃ baseTarget witnessTarget,
      target = RawTerm.idJ baseTarget witnessTarget ∧
        RawStep.par baseCase baseTarget ∧
        RawStep.par witness witnessTarget) ∨
    (∃ witnessRaw baseTarget,
      target = baseTarget ∧
        RawStep.par witness (RawTerm.refl witnessRaw) ∧
        RawStep.par baseCase baseTarget) := by
  cases parallelStep with
  | refl _ =>
      exact Or.inl ⟨baseCase, witness, rfl,
        RawStep.par.refl _, RawStep.par.refl _⟩
  | idJ baseStep witnessStep =>
      exact Or.inl ⟨_, _, rfl, baseStep, witnessStep⟩
  | iotaIdJRefl witnessRaw baseStep =>
      exact Or.inr ⟨witnessRaw, _, rfl,
        RawStep.par.refl _, baseStep⟩
  | iotaIdJReflDeep witnessStep baseStep =>
      exact Or.inr ⟨_, _, rfl, witnessStep, baseStep⟩

end LeanFX2
