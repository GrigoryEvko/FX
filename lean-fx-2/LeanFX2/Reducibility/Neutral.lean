import LeanFX2.Reducibility.Basic

/-! # LeanFX2.Reducibility.Neutral — neutral terms under parallel reduction

This module hosts the `RawTerm.IsNeutral` predicate (K12.20.U2)
plus the closure cascade proving every parallel-reduction step out
of a neutral term lands on another neutral term.

A neutral term is one whose head has no rewrite rule firing on it
yet — variables, applications/eliminators/projections stuck on a
neutral head, and the destructor side of every Tait pair / record /
codata / modal / refine / session / interval / cubical primitive.
Tait reducibility candidates need the closure property because the
generic compound CR3 step argues "if `term` reduces to some `term'`,
then `term'` is still neutral and the IH on the reduct re-applies".

## What ships

* `RawTerm.IsNeutral` — inductive predicate over `RawTerm scope` that
  classifies the neutral fragment.  32 constructor arms cover every
  destructor / variable / accumulator shape across the kernel.
* `RawTerm.IsNeutral.<ctor>_par_preserves` — 32 closure lemmas, one
  per arm.  Each shows that if a neutral term takes one
  `RawStep.par` step, the result remains neutral.  Proofs are
  inversion-driven: `RawStep.par` cases out, the redex-firing arms
  are absurd (head was neutral, no redex), and the cong arms hand
  back the same IsNeutral.<ctor> with the appropriate sub-IsNeutral
  recursively preserved.

## Zero-axiom discipline

The induction proceeds by structural recursion on `RawStep.par`
followed by ctor analysis.  No `propext`, no `Quot.sound`, no
`Classical.choice` involved — verified by `Smoke/AuditPhase2Neutral`
(reviewer log) and the per-decl `#assert_no_axioms` gates in
`Tools/AuditAll/AuditReducibility.lean`.

## Root status

Layer 3 metatheory leaf.  Stable across the K12.20 cascade; this
module's only consumer is the top-level `Reducibility.lean`'s
compound CR3 arms (arrow / sigmaTy / piTy / interval / refine etc.). -/

namespace LeanFX2


/-! ## K12.20.U2 neutral vocabulary

CR3 needs a syntactic class of neutral terms: variables and terms
stuck on an eliminator whose principal scrutinee is neutral.  This
predicate deliberately excludes introduction forms (`lam`, `pair`,
constructors, records, refinements, codes) because those either are
values or have their own beta/iota head rule.

The predicate carries only neutrality, not strong-normalization of
side arguments.  Later CR3 lemmas combine this neutral shape with the
CR3 premise "every reduct is reducible" and the existing neutral-head
SN helper family below. -/
inductive RawTerm.IsNeutral : ∀ {scope : Nat}, RawTerm scope → Prop
  | var {scope : Nat} (position : Fin scope) :
      RawTerm.IsNeutral (RawTerm.var position)
  | app {scope : Nat} {functionTerm argumentTerm : RawTerm scope}
      (functionIsNeutral : RawTerm.IsNeutral functionTerm) :
      RawTerm.IsNeutral (RawTerm.app functionTerm argumentTerm)
  | fst {scope : Nat} {pairTerm : RawTerm scope}
      (pairIsNeutral : RawTerm.IsNeutral pairTerm) :
      RawTerm.IsNeutral (RawTerm.fst pairTerm)
  | snd {scope : Nat} {pairTerm : RawTerm scope}
      (pairIsNeutral : RawTerm.IsNeutral pairTerm) :
      RawTerm.IsNeutral (RawTerm.snd pairTerm)
  | boolElim {scope : Nat}
      {scrutinee thenBranch elseBranch : RawTerm scope}
      (scrutineeIsNeutral : RawTerm.IsNeutral scrutinee) :
      RawTerm.IsNeutral
        (RawTerm.boolElim scrutinee thenBranch elseBranch)
  | natElim {scope : Nat}
      {scrutinee zeroBranch succBranch : RawTerm scope}
      (scrutineeIsNeutral : RawTerm.IsNeutral scrutinee) :
      RawTerm.IsNeutral
        (RawTerm.natElim scrutinee zeroBranch succBranch)
  | natRec {scope : Nat}
      {scrutinee zeroBranch succBranch : RawTerm scope}
      (scrutineeIsNeutral : RawTerm.IsNeutral scrutinee) :
      RawTerm.IsNeutral
        (RawTerm.natRec scrutinee zeroBranch succBranch)
  | listElim {scope : Nat}
      {scrutinee nilBranch consBranch : RawTerm scope}
      (scrutineeIsNeutral : RawTerm.IsNeutral scrutinee) :
      RawTerm.IsNeutral
        (RawTerm.listElim scrutinee nilBranch consBranch)
  | optionMatch {scope : Nat}
      {scrutinee noneBranch someBranch : RawTerm scope}
      (scrutineeIsNeutral : RawTerm.IsNeutral scrutinee) :
      RawTerm.IsNeutral
        (RawTerm.optionMatch scrutinee noneBranch someBranch)
  | eitherMatch {scope : Nat}
      {scrutinee leftBranch rightBranch : RawTerm scope}
      (scrutineeIsNeutral : RawTerm.IsNeutral scrutinee) :
      RawTerm.IsNeutral
        (RawTerm.eitherMatch scrutinee leftBranch rightBranch)
  | pathApp {scope : Nat}
      {pathTerm intervalArg : RawTerm scope}
      (pathIsNeutral : RawTerm.IsNeutral pathTerm) :
      RawTerm.IsNeutral (RawTerm.pathApp pathTerm intervalArg)
  | glueElim {scope : Nat} {gluedValue : RawTerm scope}
      (gluedValueIsNeutral : RawTerm.IsNeutral gluedValue) :
      RawTerm.IsNeutral (RawTerm.glueElim gluedValue)
  | transp {scope : Nat} {path source : RawTerm scope}
      (pathIsNeutral : RawTerm.IsNeutral path) :
      RawTerm.IsNeutral (RawTerm.transp path source)
  | hcomp {scope : Nat} {sides cap : RawTerm scope}
      (sidesIsNeutral : RawTerm.IsNeutral sides) :
      RawTerm.IsNeutral (RawTerm.hcomp sides cap)
  | idJ {scope : Nat} {baseCase witness : RawTerm scope}
      (witnessIsNeutral : RawTerm.IsNeutral witness) :
      RawTerm.IsNeutral (RawTerm.idJ baseCase witness)
  | oeqJ {scope : Nat} {baseCase witness : RawTerm scope}
      (witnessIsNeutral : RawTerm.IsNeutral witness) :
      RawTerm.IsNeutral (RawTerm.oeqJ baseCase witness)
  | idStrictRec {scope : Nat} {baseCase witness : RawTerm scope}
      (witnessIsNeutral : RawTerm.IsNeutral witness) :
      RawTerm.IsNeutral (RawTerm.idStrictRec baseCase witness)
  | equivApp {scope : Nat} {equivTerm argument : RawTerm scope}
      (equivIsNeutral : RawTerm.IsNeutral equivTerm) :
      RawTerm.IsNeutral (RawTerm.equivApp equivTerm argument)
  | equivApply {scope : Nat} {equivRaw argRaw : RawTerm scope}
      (equivIsNeutral : RawTerm.IsNeutral equivRaw) :
      RawTerm.IsNeutral (RawTerm.equivApply equivRaw argRaw)
  | modElim {scope : Nat} {raw : RawTerm scope}
      (rawIsNeutral : RawTerm.IsNeutral raw) :
      RawTerm.IsNeutral (RawTerm.modElim raw)
  | subsume {scope : Nat} {raw : RawTerm scope}
      (rawIsNeutral : RawTerm.IsNeutral raw) :
      RawTerm.IsNeutral (RawTerm.subsume raw)
  | refineElim {scope : Nat} {refinedValue : RawTerm scope}
      (refinedValueIsNeutral : RawTerm.IsNeutral refinedValue) :
      RawTerm.IsNeutral (RawTerm.refineElim refinedValue)
  | recordProj {scope : Nat} {recordValue : RawTerm scope}
      (recordValueIsNeutral : RawTerm.IsNeutral recordValue) :
      RawTerm.IsNeutral (RawTerm.recordProj recordValue)
  | codataDest {scope : Nat} {codataValue : RawTerm scope}
      (codataValueIsNeutral : RawTerm.IsNeutral codataValue) :
      RawTerm.IsNeutral (RawTerm.codataDest codataValue)
  | sessionSend {scope : Nat} {channel payload : RawTerm scope}
      (channelIsNeutral : RawTerm.IsNeutral channel) :
      RawTerm.IsNeutral (RawTerm.sessionSend channel payload)
  | sessionRecv {scope : Nat} {channel : RawTerm scope}
      (channelIsNeutral : RawTerm.IsNeutral channel) :
      RawTerm.IsNeutral (RawTerm.sessionRecv channel)
  | effectPerform {scope : Nat}
      {operationTag arguments : RawTerm scope}
      (operationIsNeutral : RawTerm.IsNeutral operationTag) :
      RawTerm.IsNeutral
        (RawTerm.effectPerform operationTag arguments)

/-- Neutral raw terms are never lambda-shaped. -/
theorem RawTerm.IsNeutral.not_lam {scope : Nat}
    {source : RawTerm scope}
    (sourceIsNeutral : RawTerm.IsNeutral source)
    {bodyRaw : RawTerm (scope + 1)} :
    source ≠ RawTerm.lam bodyRaw := by
  intro sourceEq
  cases sourceIsNeutral <;> cases sourceEq

/-- Neutral raw terms are never pair-shaped. -/
theorem RawTerm.IsNeutral.not_pair {scope : Nat}
    {source firstRaw secondRaw : RawTerm scope}
    (sourceIsNeutral : RawTerm.IsNeutral source) :
    source ≠ RawTerm.pair firstRaw secondRaw := by
  intro sourceEq
  cases sourceIsNeutral <;> cases sourceEq

/-- Neutral raw terms are never `true`. -/
theorem RawTerm.IsNeutral.not_boolTrue {scope : Nat}
    {source : RawTerm scope}
    (sourceIsNeutral : RawTerm.IsNeutral source) :
    source ≠ RawTerm.boolTrue := by
  intro sourceEq
  cases sourceIsNeutral <;> cases sourceEq

/-- Neutral raw terms are never `false`. -/
theorem RawTerm.IsNeutral.not_boolFalse {scope : Nat}
    {source : RawTerm scope}
    (sourceIsNeutral : RawTerm.IsNeutral source) :
    source ≠ RawTerm.boolFalse := by
  intro sourceEq
  cases sourceIsNeutral <;> cases sourceEq

/-- Neutral raw terms are never `natZero`. -/
theorem RawTerm.IsNeutral.not_natZero {scope : Nat}
    {source : RawTerm scope}
    (sourceIsNeutral : RawTerm.IsNeutral source) :
    source ≠ RawTerm.natZero := by
  intro sourceEq
  cases sourceIsNeutral <;> cases sourceEq

/-- Neutral raw terms are never successor-shaped. -/
theorem RawTerm.IsNeutral.not_natSucc {scope : Nat}
    {source predecessorRaw : RawTerm scope}
    (sourceIsNeutral : RawTerm.IsNeutral source) :
    source ≠ RawTerm.natSucc predecessorRaw := by
  intro sourceEq
  cases sourceIsNeutral <;> cases sourceEq

/-- Neutral raw terms are never empty-list-shaped. -/
theorem RawTerm.IsNeutral.not_listNil {scope : Nat}
    {source : RawTerm scope}
    (sourceIsNeutral : RawTerm.IsNeutral source) :
    source ≠ RawTerm.listNil := by
  intro sourceEq
  cases sourceIsNeutral <;> cases sourceEq

/-- Neutral raw terms are never list-cons-shaped. -/
theorem RawTerm.IsNeutral.not_listCons {scope : Nat}
    {source headRaw tailRaw : RawTerm scope}
    (sourceIsNeutral : RawTerm.IsNeutral source) :
    source ≠ RawTerm.listCons headRaw tailRaw := by
  intro sourceEq
  cases sourceIsNeutral <;> cases sourceEq

/-- Neutral raw terms are never option-none-shaped. -/
theorem RawTerm.IsNeutral.not_optionNone {scope : Nat}
    {source : RawTerm scope}
    (sourceIsNeutral : RawTerm.IsNeutral source) :
    source ≠ RawTerm.optionNone := by
  intro sourceEq
  cases sourceIsNeutral <;> cases sourceEq

/-- Neutral raw terms are never option-some-shaped. -/
theorem RawTerm.IsNeutral.not_optionSome {scope : Nat}
    {source valueRaw : RawTerm scope}
    (sourceIsNeutral : RawTerm.IsNeutral source) :
    source ≠ RawTerm.optionSome valueRaw := by
  intro sourceEq
  cases sourceIsNeutral <;> cases sourceEq

/-- Neutral raw terms are never either-left-shaped. -/
theorem RawTerm.IsNeutral.not_eitherInl {scope : Nat}
    {source valueRaw : RawTerm scope}
    (sourceIsNeutral : RawTerm.IsNeutral source) :
    source ≠ RawTerm.eitherInl valueRaw := by
  intro sourceEq
  cases sourceIsNeutral <;> cases sourceEq

/-- Neutral raw terms are never either-right-shaped. -/
theorem RawTerm.IsNeutral.not_eitherInr {scope : Nat}
    {source valueRaw : RawTerm scope}
    (sourceIsNeutral : RawTerm.IsNeutral source) :
    source ≠ RawTerm.eitherInr valueRaw := by
  intro sourceEq
  cases sourceIsNeutral <;> cases sourceEq

/-- Neutral raw terms are never cubical-path-lambda-shaped. -/
theorem RawTerm.IsNeutral.not_pathLam {scope : Nat}
    {source : RawTerm scope}
    (sourceIsNeutral : RawTerm.IsNeutral source)
    {bodyRaw : RawTerm (scope + 1)} :
    source ≠ RawTerm.pathLam bodyRaw := by
  intro sourceEq
  cases sourceIsNeutral <;> cases sourceEq

/-- Neutral raw terms are never glue-intro-shaped. -/
theorem RawTerm.IsNeutral.not_glueIntro {scope : Nat}
    {source baseRaw partialRaw : RawTerm scope}
    (sourceIsNeutral : RawTerm.IsNeutral source) :
    source ≠ RawTerm.glueIntro baseRaw partialRaw := by
  intro sourceEq
  cases sourceIsNeutral <;> cases sourceEq

/-- Neutral raw terms are never identity-refl-shaped. -/
theorem RawTerm.IsNeutral.not_refl {scope : Nat}
    {source witnessRaw : RawTerm scope}
    (sourceIsNeutral : RawTerm.IsNeutral source) :
    source ≠ RawTerm.refl witnessRaw := by
  intro sourceEq
  cases sourceIsNeutral <;> cases sourceEq

/-- Neutral raw terms are never observational-refl-shaped. -/
theorem RawTerm.IsNeutral.not_oeqRefl {scope : Nat}
    {source witnessRaw : RawTerm scope}
    (sourceIsNeutral : RawTerm.IsNeutral source) :
    source ≠ RawTerm.oeqRefl witnessRaw := by
  intro sourceEq
  cases sourceIsNeutral <;> cases sourceEq

/-- Neutral raw terms are never strict-identity-refl-shaped. -/
theorem RawTerm.IsNeutral.not_idStrictRefl {scope : Nat}
    {source witnessRaw : RawTerm scope}
    (sourceIsNeutral : RawTerm.IsNeutral source) :
    source ≠ RawTerm.idStrictRefl witnessRaw := by
  intro sourceEq
  cases sourceIsNeutral <;> cases sourceEq

/-- Neutral raw terms are never equivalence-intro-shaped. -/
theorem RawTerm.IsNeutral.not_equivIntro {scope : Nat}
    {source forwardRaw backwardRaw : RawTerm scope}
    (sourceIsNeutral : RawTerm.IsNeutral source) :
    source ≠ RawTerm.equivIntro forwardRaw backwardRaw := by
  intro sourceEq
  cases sourceIsNeutral <;> cases sourceEq

/-- Neutral raw terms are never univalence-to-equivalence shaped. -/
theorem RawTerm.IsNeutral.not_uaToEquiv {scope : Nat}
    {source proofRaw : RawTerm scope}
    (sourceIsNeutral : RawTerm.IsNeutral source) :
    source ≠ RawTerm.uaToEquiv proofRaw := by
  intro sourceEq
  cases sourceIsNeutral <;> cases sourceEq

/-- Neutral raw terms are never path-composition shaped. -/
theorem RawTerm.IsNeutral.not_pathCompose {scope : Nat}
    {source leftRaw rightRaw : RawTerm scope}
    (sourceIsNeutral : RawTerm.IsNeutral source) :
    source ≠ RawTerm.pathCompose leftRaw rightRaw := by
  intro sourceEq
  cases sourceIsNeutral <;> cases sourceEq

/-- Neutral raw terms are never modal-intro-shaped. -/
theorem RawTerm.IsNeutral.not_modIntro {scope : Nat}
    {source valueRaw : RawTerm scope}
    (sourceIsNeutral : RawTerm.IsNeutral source) :
    source ≠ RawTerm.modIntro valueRaw := by
  intro sourceEq
  cases sourceIsNeutral <;> cases sourceEq

/-- Neutral raw terms are never refinement-intro-shaped. -/
theorem RawTerm.IsNeutral.not_refineIntro {scope : Nat}
    {source valueRaw proofRaw : RawTerm scope}
    (sourceIsNeutral : RawTerm.IsNeutral source) :
    source ≠ RawTerm.refineIntro valueRaw proofRaw := by
  intro sourceEq
  cases sourceIsNeutral <;> cases sourceEq

/-- Neutral raw terms are never record-intro-shaped. -/
theorem RawTerm.IsNeutral.not_recordIntro {scope : Nat}
    {source fieldRaw : RawTerm scope}
    (sourceIsNeutral : RawTerm.IsNeutral source) :
    source ≠ RawTerm.recordIntro fieldRaw := by
  intro sourceEq
  cases sourceIsNeutral <;> cases sourceEq

/-- Neutral raw terms are never codata-unfold-shaped. -/
theorem RawTerm.IsNeutral.not_codataUnfold {scope : Nat}
    {source initialRaw transitionRaw : RawTerm scope}
    (sourceIsNeutral : RawTerm.IsNeutral source) :
    source ≠ RawTerm.codataUnfold initialRaw transitionRaw := by
  intro sourceEq
  cases sourceIsNeutral <;> cases sourceEq

/-! ### K12.20.U2 neutral preservation under raw parallel development

These higher-order one-step preservation lemmas are the local shape
facts needed by compound CR3.  Each lemma assumes preservation for the
principal neutral subterm and proves preservation for one eliminator
wrapper.  Keeping the lemmas higher-order mirrors the `varShape` and
`step_preserves` architecture: the later global CR3/par-preservation
dispatcher supplies the recursive hook, while these atoms discharge the
constructor-specific beta/iota-impossible cases exactly once.
-/

/-- A variable can only parallel-develop to itself, so neutrality is
preserved by one raw parallel step from a variable. -/
theorem RawTerm.IsNeutral.var_par_preserves {scope : Nat}
    {position : Fin scope} {targetRaw : RawTerm scope}
    (parallelStep : RawStep.par (RawTerm.var position) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  have targetEq : targetRaw = RawTerm.var position :=
    RawStep.par.var_inv parallelStep
  subst targetEq
  exact RawTerm.IsNeutral.var position

/-- Neutrality is preserved by one raw parallel step from a neutral
application, assuming preservation for the function head. -/
theorem RawTerm.IsNeutral.app_par_preserves {scope : Nat}
    {functionRaw argumentRaw targetRaw : RawTerm scope}
    (functionParPreserves :
      ∀ {functionTarget : RawTerm scope},
        RawStep.par functionRaw functionTarget →
        RawTerm.IsNeutral functionTarget)
    (parallelStep :
      RawStep.par (RawTerm.app functionRaw argumentRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  rcases RawStep.par.app_inv parallelStep with
    ⟨functionTarget, argumentTarget, targetEq,
      functionStep, _argumentStep⟩
    | ⟨bodyTarget, _argumentTarget, _targetEq,
        functionStep, _argumentStep⟩
  · subst targetEq
    exact RawTerm.IsNeutral.app (functionParPreserves functionStep)
  · exact (RawTerm.IsNeutral.not_lam
      (functionParPreserves functionStep) rfl).elim

/-- Neutrality is preserved by one raw parallel step from `fst` of a
neutral pair scrutinee. -/
theorem RawTerm.IsNeutral.fst_par_preserves {scope : Nat}
    {pairRaw targetRaw : RawTerm scope}
    (pairParPreserves :
      ∀ {pairTarget : RawTerm scope},
        RawStep.par pairRaw pairTarget →
        RawTerm.IsNeutral pairTarget)
    (parallelStep : RawStep.par (RawTerm.fst pairRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  rcases RawStep.par.fst_inv parallelStep with
    ⟨pairTarget, targetEq, pairStep⟩
    | ⟨firstTarget, secondTarget, _targetEq, pairStep⟩
  · subst targetEq
    exact RawTerm.IsNeutral.fst (pairParPreserves pairStep)
  · exact (RawTerm.IsNeutral.not_pair
      (pairParPreserves pairStep)
      (firstRaw := firstTarget) (secondRaw := secondTarget) rfl).elim

/-- Neutrality is preserved by one raw parallel step from `snd` of a
neutral pair scrutinee. -/
theorem RawTerm.IsNeutral.snd_par_preserves {scope : Nat}
    {pairRaw targetRaw : RawTerm scope}
    (pairParPreserves :
      ∀ {pairTarget : RawTerm scope},
        RawStep.par pairRaw pairTarget →
        RawTerm.IsNeutral pairTarget)
    (parallelStep : RawStep.par (RawTerm.snd pairRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  rcases RawStep.par.snd_inv parallelStep with
    ⟨pairTarget, targetEq, pairStep⟩
    | ⟨firstTarget, secondTarget, _targetEq, pairStep⟩
  · subst targetEq
    exact RawTerm.IsNeutral.snd (pairParPreserves pairStep)
  · exact (RawTerm.IsNeutral.not_pair
      (pairParPreserves pairStep)
      (firstRaw := firstTarget) (secondRaw := secondTarget) rfl).elim

/-- Neutrality is preserved by one raw parallel step from `boolElim`
with a neutral scrutinee. -/
theorem RawTerm.IsNeutral.boolElim_par_preserves {scope : Nat}
    {scrutineeRaw thenRaw elseRaw targetRaw : RawTerm scope}
    (scrutineeParPreserves :
      ∀ {scrutineeTarget : RawTerm scope},
        RawStep.par scrutineeRaw scrutineeTarget →
        RawTerm.IsNeutral scrutineeTarget)
    (parallelStep :
      RawStep.par
        (RawTerm.boolElim scrutineeRaw thenRaw elseRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  rcases RawStep.par.boolElim_inv parallelStep with
    ⟨scrutineeTarget, thenTarget, elseTarget, targetEq,
      scrutineeStep, _thenStep, _elseStep⟩
    | ⟨_thenTarget, _targetEq, scrutineeStep, _thenStep⟩
    | ⟨_elseTarget, _targetEq, scrutineeStep, _elseStep⟩
  · subst targetEq
    exact RawTerm.IsNeutral.boolElim
      (scrutineeParPreserves scrutineeStep)
  · exact (RawTerm.IsNeutral.not_boolTrue
      (scrutineeParPreserves scrutineeStep) rfl).elim
  · exact (RawTerm.IsNeutral.not_boolFalse
      (scrutineeParPreserves scrutineeStep) rfl).elim

/-- Neutrality is preserved by one raw parallel step from `natElim`
with a neutral scrutinee. -/
theorem RawTerm.IsNeutral.natElim_par_preserves {scope : Nat}
    {scrutineeRaw zeroRaw succRaw targetRaw : RawTerm scope}
    (scrutineeParPreserves :
      ∀ {scrutineeTarget : RawTerm scope},
        RawStep.par scrutineeRaw scrutineeTarget →
        RawTerm.IsNeutral scrutineeTarget)
    (parallelStep :
      RawStep.par
        (RawTerm.natElim scrutineeRaw zeroRaw succRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  rcases RawStep.par.natElim_inv parallelStep with
    ⟨scrutineeTarget, zeroTarget, succTarget, targetEq,
      scrutineeStep, _zeroStep, _succStep⟩
    | ⟨_zeroTarget, _targetEq, scrutineeStep, _zeroStep⟩
    | ⟨predecessorRaw, _succTarget, _targetEq,
        scrutineeStep, _succStep⟩
  · subst targetEq
    exact RawTerm.IsNeutral.natElim
      (scrutineeParPreserves scrutineeStep)
  · exact (RawTerm.IsNeutral.not_natZero
      (scrutineeParPreserves scrutineeStep) rfl).elim
  · exact (RawTerm.IsNeutral.not_natSucc
      (scrutineeParPreserves scrutineeStep)
      (predecessorRaw := predecessorRaw) rfl).elim

/-- Neutrality is preserved by one raw parallel step from `natRec`
with a neutral scrutinee. -/
theorem RawTerm.IsNeutral.natRec_par_preserves {scope : Nat}
    {scrutineeRaw zeroRaw succRaw targetRaw : RawTerm scope}
    (scrutineeParPreserves :
      ∀ {scrutineeTarget : RawTerm scope},
        RawStep.par scrutineeRaw scrutineeTarget →
        RawTerm.IsNeutral scrutineeTarget)
    (parallelStep :
      RawStep.par
        (RawTerm.natRec scrutineeRaw zeroRaw succRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  rcases RawStep.par.natRec_inv parallelStep with
    ⟨scrutineeTarget, zeroTarget, succTarget, targetEq,
      scrutineeStep, _zeroStep, _succStep⟩
    | ⟨_zeroTarget, _targetEq, scrutineeStep, _zeroStep⟩
    | ⟨predecessorRaw, _zeroTarget, _succTarget, _targetEq,
        scrutineeStep, _zeroStep, _succStep⟩
  · subst targetEq
    exact RawTerm.IsNeutral.natRec
      (scrutineeParPreserves scrutineeStep)
  · exact (RawTerm.IsNeutral.not_natZero
      (scrutineeParPreserves scrutineeStep) rfl).elim
  · exact (RawTerm.IsNeutral.not_natSucc
      (scrutineeParPreserves scrutineeStep)
      (predecessorRaw := predecessorRaw) rfl).elim

/-- Neutrality is preserved by one raw parallel step from `listElim`
with a neutral scrutinee. -/
theorem RawTerm.IsNeutral.listElim_par_preserves {scope : Nat}
    {scrutineeRaw nilRaw consRaw targetRaw : RawTerm scope}
    (scrutineeParPreserves :
      ∀ {scrutineeTarget : RawTerm scope},
        RawStep.par scrutineeRaw scrutineeTarget →
        RawTerm.IsNeutral scrutineeTarget)
    (parallelStep :
      RawStep.par
        (RawTerm.listElim scrutineeRaw nilRaw consRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  rcases RawStep.par.listElim_inv parallelStep with
    ⟨scrutineeTarget, nilTarget, consTarget, targetEq,
      scrutineeStep, _nilStep, _consStep⟩
    | ⟨_nilTarget, _targetEq, scrutineeStep, _nilStep⟩
    | ⟨headRaw, tailRaw, _consTarget, _targetEq,
        scrutineeStep, _consStep⟩
  · subst targetEq
    exact RawTerm.IsNeutral.listElim
      (scrutineeParPreserves scrutineeStep)
  · exact (RawTerm.IsNeutral.not_listNil
      (scrutineeParPreserves scrutineeStep) rfl).elim
  · exact (RawTerm.IsNeutral.not_listCons
      (scrutineeParPreserves scrutineeStep)
      (headRaw := headRaw) (tailRaw := tailRaw) rfl).elim

/-- Neutrality is preserved by one raw parallel step from `optionMatch`
with a neutral scrutinee. -/
theorem RawTerm.IsNeutral.optionMatch_par_preserves {scope : Nat}
    {scrutineeRaw noneRaw someRaw targetRaw : RawTerm scope}
    (scrutineeParPreserves :
      ∀ {scrutineeTarget : RawTerm scope},
        RawStep.par scrutineeRaw scrutineeTarget →
        RawTerm.IsNeutral scrutineeTarget)
    (parallelStep :
      RawStep.par
        (RawTerm.optionMatch scrutineeRaw noneRaw someRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  rcases RawStep.par.optionMatch_inv parallelStep with
    ⟨scrutineeTarget, noneTarget, someTarget, targetEq,
      scrutineeStep, _noneStep, _someStep⟩
    | ⟨_noneTarget, _targetEq, scrutineeStep, _noneStep⟩
    | ⟨valueRaw, _someTarget, _targetEq, scrutineeStep, _someStep⟩
  · subst targetEq
    exact RawTerm.IsNeutral.optionMatch
      (scrutineeParPreserves scrutineeStep)
  · exact (RawTerm.IsNeutral.not_optionNone
      (scrutineeParPreserves scrutineeStep) rfl).elim
  · exact (RawTerm.IsNeutral.not_optionSome
      (scrutineeParPreserves scrutineeStep)
      (valueRaw := valueRaw) rfl).elim

/-- Neutrality is preserved by one raw parallel step from `eitherMatch`
with a neutral scrutinee. -/
theorem RawTerm.IsNeutral.eitherMatch_par_preserves {scope : Nat}
    {scrutineeRaw leftRaw rightRaw targetRaw : RawTerm scope}
    (scrutineeParPreserves :
      ∀ {scrutineeTarget : RawTerm scope},
        RawStep.par scrutineeRaw scrutineeTarget →
        RawTerm.IsNeutral scrutineeTarget)
    (parallelStep :
      RawStep.par
        (RawTerm.eitherMatch scrutineeRaw leftRaw rightRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  rcases RawStep.par.eitherMatch_inv parallelStep with
    ⟨scrutineeTarget, leftTarget, rightTarget, targetEq,
      scrutineeStep, _leftStep, _rightStep⟩
    | ⟨valueRaw, _leftTarget, _targetEq,
        scrutineeStep, _leftStep⟩
    | ⟨valueRaw, _rightTarget, _targetEq,
        scrutineeStep, _rightStep⟩
  · subst targetEq
    exact RawTerm.IsNeutral.eitherMatch
      (scrutineeParPreserves scrutineeStep)
  · exact (RawTerm.IsNeutral.not_eitherInl
      (scrutineeParPreserves scrutineeStep)
      (valueRaw := valueRaw) rfl).elim
  · exact (RawTerm.IsNeutral.not_eitherInr
      (scrutineeParPreserves scrutineeStep)
      (valueRaw := valueRaw) rfl).elim

/-- Neutrality is preserved by one raw parallel step from `pathApp`
with a neutral path head. -/
theorem RawTerm.IsNeutral.pathApp_par_preserves {scope : Nat}
    {pathRaw intervalRaw targetRaw : RawTerm scope}
    (pathParPreserves :
      ∀ {pathTarget : RawTerm scope},
        RawStep.par pathRaw pathTarget →
        RawTerm.IsNeutral pathTarget)
    (parallelStep :
      RawStep.par (RawTerm.pathApp pathRaw intervalRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  rcases RawStep.par.pathApp_inv parallelStep with
    ⟨pathTarget, intervalTarget, targetEq,
      pathStep, _intervalStep⟩
    | ⟨bodyTarget, _intervalTarget, _targetEq,
        pathStep, _intervalStep⟩
  · subst targetEq
    exact RawTerm.IsNeutral.pathApp (pathParPreserves pathStep)
  · exact (RawTerm.IsNeutral.not_pathLam
      (pathParPreserves pathStep)
      (bodyRaw := bodyTarget) rfl).elim

/-- Neutrality is preserved by one raw parallel step from `glueElim`
with a neutral glued value. -/
theorem RawTerm.IsNeutral.glueElim_par_preserves {scope : Nat}
    {gluedRaw targetRaw : RawTerm scope}
    (gluedParPreserves :
      ∀ {gluedTarget : RawTerm scope},
        RawStep.par gluedRaw gluedTarget →
        RawTerm.IsNeutral gluedTarget)
    (parallelStep : RawStep.par (RawTerm.glueElim gluedRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  rcases RawStep.par.glueElim_inv parallelStep with
    ⟨gluedTarget, targetEq, gluedStep⟩
    | ⟨baseTarget, partialTarget, _targetEq, gluedStep⟩
  · subst targetEq
    exact RawTerm.IsNeutral.glueElim (gluedParPreserves gluedStep)
  · exact (RawTerm.IsNeutral.not_glueIntro
      (gluedParPreserves gluedStep)
      (baseRaw := baseTarget) (partialRaw := partialTarget) rfl).elim

/-- Neutrality is preserved by one raw parallel step from `hcomp`
with neutral sides. -/
theorem RawTerm.IsNeutral.hcomp_par_preserves {scope : Nat}
    {sidesRaw capRaw targetRaw : RawTerm scope}
    (sidesParPreserves :
      ∀ {sidesTarget : RawTerm scope},
        RawStep.par sidesRaw sidesTarget →
        RawTerm.IsNeutral sidesTarget)
    (parallelStep : RawStep.par (RawTerm.hcomp sidesRaw capRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  obtain ⟨sidesTarget, capTarget, targetEq,
      sidesStep, _capStep⟩ :=
    RawStep.par.hcomp_inv parallelStep
  subst targetEq
  exact RawTerm.IsNeutral.hcomp (sidesParPreserves sidesStep)

/-- Neutrality is preserved by one raw parallel step from `transp`
with a neutral path line.  The non-congruent D3.6 arms are impossible
because the path source or path target would have to be canonical. -/
theorem RawTerm.IsNeutral.transp_par_preserves {scope : Nat}
    {pathRaw sourceRaw targetRaw : RawTerm scope}
    (pathIsNeutral : RawTerm.IsNeutral pathRaw)
    (pathParPreserves :
      ∀ {pathTarget : RawTerm scope},
        RawStep.par pathRaw pathTarget →
        RawTerm.IsNeutral pathTarget)
    (parallelStep : RawStep.par (RawTerm.transp pathRaw sourceRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  rcases RawStep.par.transp_inv parallelStep with
    ⟨pathTarget, sourceTarget, targetEq,
      pathStep, _sourceStep⟩
    | ⟨typeRawSource, _sourceTarget, pathEq,
        _targetEq, _sourceStep⟩
    | ⟨typeRawTarget, _sourceTarget, _targetEq,
        pathStep, _sourceStep⟩
    | ⟨proofRawSource, _proofRawTarget, _sourceTarget,
        pathEq, _targetEq, _proofStep, _sourceStep⟩
    | ⟨proofRawTarget, _sourceTarget, _targetEq,
        pathStep, _sourceStep⟩
    | ⟨leftRawSource, _leftRawTarget, rightRawSource,
        _rightRawTarget, _sourceTarget, pathEq,
        _targetEq, _leftStep, _rightStep, _sourceStep⟩
    | ⟨leftRawTarget, rightRawTarget, _sourceTarget, _targetEq,
        pathStep, _sourceStep⟩
  · subst targetEq
    exact RawTerm.IsNeutral.transp (pathParPreserves pathStep)
  · exact (RawTerm.IsNeutral.not_pathLam pathIsNeutral
      (bodyRaw := typeRawSource.weaken) pathEq).elim
  · exact (RawTerm.IsNeutral.not_pathLam
      (pathParPreserves pathStep)
      (bodyRaw := typeRawTarget.weaken) rfl).elim
  · exact (RawTerm.IsNeutral.not_uaToEquiv pathIsNeutral
      (proofRaw := proofRawSource) pathEq).elim
  · exact (RawTerm.IsNeutral.not_uaToEquiv
      (pathParPreserves pathStep)
      (proofRaw := proofRawTarget) rfl).elim
  · exact (RawTerm.IsNeutral.not_pathCompose pathIsNeutral
      (leftRaw := leftRawSource) (rightRaw := rightRawSource)
      pathEq).elim
  · exact (RawTerm.IsNeutral.not_pathCompose
      (pathParPreserves pathStep)
      (leftRaw := leftRawTarget) (rightRaw := rightRawTarget) rfl).elim

/-- Neutrality is preserved by one raw parallel step from `idJ`
with a neutral equality witness. -/
theorem RawTerm.IsNeutral.idJ_par_preserves {scope : Nat}
    {baseRaw witnessRaw targetRaw : RawTerm scope}
    (witnessParPreserves :
      ∀ {witnessTarget : RawTerm scope},
        RawStep.par witnessRaw witnessTarget →
        RawTerm.IsNeutral witnessTarget)
    (parallelStep : RawStep.par (RawTerm.idJ baseRaw witnessRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  rcases RawStep.par.idJ_inv parallelStep with
    ⟨baseTarget, witnessTarget, targetEq,
      _baseStep, witnessStep⟩
    | ⟨witnessTarget, _baseTarget, _targetEq,
        witnessStep, _baseStep⟩
  · subst targetEq
    exact RawTerm.IsNeutral.idJ (witnessParPreserves witnessStep)
  · exact (RawTerm.IsNeutral.not_refl
      (witnessParPreserves witnessStep)
      (witnessRaw := witnessTarget) rfl).elim

/-- Neutrality is preserved by one raw parallel step from `oeqJ`
with a neutral observational-equality witness. -/
theorem RawTerm.IsNeutral.oeqJ_par_preserves {scope : Nat}
    {baseRaw witnessRaw targetRaw : RawTerm scope}
    (witnessParPreserves :
      ∀ {witnessTarget : RawTerm scope},
        RawStep.par witnessRaw witnessTarget →
        RawTerm.IsNeutral witnessTarget)
    (parallelStep : RawStep.par (RawTerm.oeqJ baseRaw witnessRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  obtain ⟨baseTarget, witnessTarget, targetEq,
      _baseStep, witnessStep⟩ :=
    RawStep.par.oeqJ_inv parallelStep
  subst targetEq
  exact RawTerm.IsNeutral.oeqJ (witnessParPreserves witnessStep)

/-- Neutrality is preserved by one raw parallel step from `idStrictRec`
with a neutral strict-identity witness. -/
theorem RawTerm.IsNeutral.idStrictRec_par_preserves {scope : Nat}
    {baseRaw witnessRaw targetRaw : RawTerm scope}
    (witnessParPreserves :
      ∀ {witnessTarget : RawTerm scope},
        RawStep.par witnessRaw witnessTarget →
        RawTerm.IsNeutral witnessTarget)
    (parallelStep :
      RawStep.par (RawTerm.idStrictRec baseRaw witnessRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  rcases RawStep.par.idStrictRec_inv parallelStep with
    ⟨baseTarget, witnessTarget, targetEq,
      _baseStep, witnessStep⟩
    | ⟨witnessTarget, _baseTarget, _targetEq,
        witnessStep, _baseStep⟩
  · subst targetEq
    exact RawTerm.IsNeutral.idStrictRec
      (witnessParPreserves witnessStep)
  · exact (RawTerm.IsNeutral.not_idStrictRefl
      (witnessParPreserves witnessStep)
      (witnessRaw := witnessTarget) rfl).elim

/-- Neutrality is preserved by one raw parallel step from `equivApp`
with a neutral equivalence head. -/
theorem RawTerm.IsNeutral.equivApp_par_preserves {scope : Nat}
    {equivRaw argumentRaw targetRaw : RawTerm scope}
    (equivParPreserves :
      ∀ {equivTarget : RawTerm scope},
        RawStep.par equivRaw equivTarget →
        RawTerm.IsNeutral equivTarget)
    (parallelStep :
      RawStep.par (RawTerm.equivApp equivRaw argumentRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  obtain ⟨equivTarget, argumentTarget, targetEq,
      equivStep, _argumentStep⟩ :=
    RawStep.par.equivApp_inv parallelStep
  subst targetEq
  exact RawTerm.IsNeutral.equivApp (equivParPreserves equivStep)

/-- Neutrality is preserved by one raw parallel step from `equivApply`
with a neutral equivalence head.  The univalence-reflexivity β arms are
impossible because the equivalence source or target would have to be
`uaToEquiv _`. -/
theorem RawTerm.IsNeutral.equivApply_par_preserves {scope : Nat}
    {equivRaw argumentRaw targetRaw : RawTerm scope}
    (equivIsNeutral : RawTerm.IsNeutral equivRaw)
    (equivParPreserves :
      ∀ {equivTarget : RawTerm scope},
        RawStep.par equivRaw equivTarget →
        RawTerm.IsNeutral equivTarget)
    (parallelStep :
      RawStep.par (RawTerm.equivApply equivRaw argumentRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  rcases RawStep.par.equivApply_inv parallelStep with
    ⟨equivTarget, argumentTarget, targetEq,
      equivStep, _argumentStep⟩
    | ⟨witnessSource, _witnessTarget, _sourceTarget,
        equivEq, _targetEq, _witnessStep, _argumentStep⟩
    | ⟨witnessTarget, _sourceTarget, _targetEq,
        equivStep, _argumentStep⟩
  · subst targetEq
    exact RawTerm.IsNeutral.equivApply
      (equivParPreserves equivStep)
  · exact (RawTerm.IsNeutral.not_uaToEquiv equivIsNeutral
      (proofRaw := RawTerm.oeqRefl witnessSource) equivEq).elim
  · exact (RawTerm.IsNeutral.not_uaToEquiv
      (equivParPreserves equivStep)
      (proofRaw := RawTerm.oeqRefl witnessTarget) rfl).elim

/-- Neutrality is preserved by one raw parallel step from `modElim`
with a neutral modal value. -/
theorem RawTerm.IsNeutral.modElim_par_preserves {scope : Nat}
    {modalRaw targetRaw : RawTerm scope}
    (modalParPreserves :
      ∀ {modalTarget : RawTerm scope},
        RawStep.par modalRaw modalTarget →
        RawTerm.IsNeutral modalTarget)
    (parallelStep : RawStep.par (RawTerm.modElim modalRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  rcases RawStep.par.modElim_inv parallelStep with
    ⟨modalTarget, targetEq, modalStep⟩
    | ⟨payloadTarget, _targetEq, modalStep⟩
  · subst targetEq
    exact RawTerm.IsNeutral.modElim (modalParPreserves modalStep)
  · exact (RawTerm.IsNeutral.not_modIntro
      (modalParPreserves modalStep)
      (valueRaw := payloadTarget) rfl).elim

/-- Neutrality is preserved by one raw parallel step from `subsume`
with a neutral inner term. -/
theorem RawTerm.IsNeutral.subsume_par_preserves {scope : Nat}
    {innerRaw targetRaw : RawTerm scope}
    (innerParPreserves :
      ∀ {innerTarget : RawTerm scope},
        RawStep.par innerRaw innerTarget →
        RawTerm.IsNeutral innerTarget)
    (parallelStep : RawStep.par (RawTerm.subsume innerRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  obtain ⟨innerTarget, targetEq, innerStep⟩ :=
    RawStep.par.subsume_inv parallelStep
  subst targetEq
  exact RawTerm.IsNeutral.subsume (innerParPreserves innerStep)

/-- Neutrality is preserved by one raw parallel step from `refineElim`
with a neutral refined value. -/
theorem RawTerm.IsNeutral.refineElim_par_preserves {scope : Nat}
    {refinedRaw targetRaw : RawTerm scope}
    (refinedParPreserves :
      ∀ {refinedTarget : RawTerm scope},
        RawStep.par refinedRaw refinedTarget →
        RawTerm.IsNeutral refinedTarget)
    (parallelStep : RawStep.par (RawTerm.refineElim refinedRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  rcases RawStep.par.refineElim_inv parallelStep with
    ⟨refinedTarget, targetEq, refinedStep⟩
    | ⟨valueTarget, proofTarget, _targetEq, refinedStep⟩
  · subst targetEq
    exact RawTerm.IsNeutral.refineElim
      (refinedParPreserves refinedStep)
  · exact (RawTerm.IsNeutral.not_refineIntro
      (refinedParPreserves refinedStep)
      (valueRaw := valueTarget) (proofRaw := proofTarget) rfl).elim

/-- Neutrality is preserved by one raw parallel step from `recordProj`
with a neutral record value. -/
theorem RawTerm.IsNeutral.recordProj_par_preserves {scope : Nat}
    {recordRaw targetRaw : RawTerm scope}
    (recordParPreserves :
      ∀ {recordTarget : RawTerm scope},
        RawStep.par recordRaw recordTarget →
        RawTerm.IsNeutral recordTarget)
    (parallelStep : RawStep.par (RawTerm.recordProj recordRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  rcases RawStep.par.recordProj_inv parallelStep with
    ⟨recordTarget, targetEq, recordStep⟩
    | ⟨fieldTarget, _targetEq, recordStep⟩
  · subst targetEq
    exact RawTerm.IsNeutral.recordProj
      (recordParPreserves recordStep)
  · exact (RawTerm.IsNeutral.not_recordIntro
      (recordParPreserves recordStep)
      (fieldRaw := fieldTarget) rfl).elim

/-- Neutrality is preserved by one raw parallel step from `codataDest`
with a neutral codata value. -/
theorem RawTerm.IsNeutral.codataDest_par_preserves {scope : Nat}
    {codataRaw targetRaw : RawTerm scope}
    (codataParPreserves :
      ∀ {codataTarget : RawTerm scope},
        RawStep.par codataRaw codataTarget →
        RawTerm.IsNeutral codataTarget)
    (parallelStep : RawStep.par (RawTerm.codataDest codataRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  rcases RawStep.par.codataDest_inv parallelStep with
    ⟨codataTarget, targetEq, codataStep⟩
    | ⟨stateTarget, transitionTarget, _targetEq, codataStep⟩
  · subst targetEq
    exact RawTerm.IsNeutral.codataDest
      (codataParPreserves codataStep)
  · exact (RawTerm.IsNeutral.not_codataUnfold
      (codataParPreserves codataStep)
      (initialRaw := stateTarget) (transitionRaw := transitionTarget) rfl).elim

/-- Neutrality is preserved by one raw parallel step from `sessionSend`
with a neutral channel. -/
theorem RawTerm.IsNeutral.sessionSend_par_preserves {scope : Nat}
    {channelRaw payloadRaw targetRaw : RawTerm scope}
    (channelParPreserves :
      ∀ {channelTarget : RawTerm scope},
        RawStep.par channelRaw channelTarget →
        RawTerm.IsNeutral channelTarget)
    (parallelStep :
      RawStep.par (RawTerm.sessionSend channelRaw payloadRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  obtain ⟨channelTarget, payloadTarget, targetEq,
      channelStep, _payloadStep⟩ :=
    RawStep.par.sessionSend_inv parallelStep
  subst targetEq
  exact RawTerm.IsNeutral.sessionSend
    (channelParPreserves channelStep)

/-- Neutrality is preserved by one raw parallel step from `sessionRecv`
with a neutral channel. -/
theorem RawTerm.IsNeutral.sessionRecv_par_preserves {scope : Nat}
    {channelRaw targetRaw : RawTerm scope}
    (channelParPreserves :
      ∀ {channelTarget : RawTerm scope},
        RawStep.par channelRaw channelTarget →
        RawTerm.IsNeutral channelTarget)
    (parallelStep : RawStep.par (RawTerm.sessionRecv channelRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  obtain ⟨channelTarget, targetEq, channelStep⟩ :=
    RawStep.par.sessionRecv_inv parallelStep
  subst targetEq
  exact RawTerm.IsNeutral.sessionRecv
    (channelParPreserves channelStep)

/-- Neutrality is preserved by one raw parallel step from `effectPerform`
with a neutral operation tag. -/
theorem RawTerm.IsNeutral.effectPerform_par_preserves {scope : Nat}
    {operationRaw argumentsRaw targetRaw : RawTerm scope}
    (operationParPreserves :
      ∀ {operationTarget : RawTerm scope},
        RawStep.par operationRaw operationTarget →
        RawTerm.IsNeutral operationTarget)
    (parallelStep :
      RawStep.par
        (RawTerm.effectPerform operationRaw argumentsRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  obtain ⟨operationTarget, argumentsTarget, targetEq,
      operationStep, _argumentsStep⟩ :=
    RawStep.par.effectPerform_inv parallelStep
  subst targetEq
  exact RawTerm.IsNeutral.effectPerform
    (operationParPreserves operationStep)

/-- One raw parallel step preserves neutral shape.

This is the global dispatcher over the `RawTerm.IsNeutral` syntax class.
Each eliminator case delegates to its local preservation atom, and the
recursive hypothesis supplies preservation for the principal neutral
subterm. -/
theorem RawTerm.IsNeutral.par_preserves {scope : Nat}
    {sourceRaw targetRaw : RawTerm scope}
    (sourceIsNeutral : RawTerm.IsNeutral sourceRaw)
    (parallelStep : RawStep.par sourceRaw targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  induction sourceIsNeutral generalizing targetRaw with
  | var position =>
      exact RawTerm.IsNeutral.var_par_preserves parallelStep
  | app functionIsNeutral functionParPreserves =>
      exact RawTerm.IsNeutral.app_par_preserves
        (fun functionStep => functionParPreserves functionStep)
        parallelStep
  | fst pairIsNeutral pairParPreserves =>
      exact RawTerm.IsNeutral.fst_par_preserves
        (fun pairStep => pairParPreserves pairStep)
        parallelStep
  | snd pairIsNeutral pairParPreserves =>
      exact RawTerm.IsNeutral.snd_par_preserves
        (fun pairStep => pairParPreserves pairStep)
        parallelStep
  | boolElim scrutineeIsNeutral scrutineeParPreserves =>
      exact RawTerm.IsNeutral.boolElim_par_preserves
        (fun scrutineeStep => scrutineeParPreserves scrutineeStep)
        parallelStep
  | natElim scrutineeIsNeutral scrutineeParPreserves =>
      exact RawTerm.IsNeutral.natElim_par_preserves
        (fun scrutineeStep => scrutineeParPreserves scrutineeStep)
        parallelStep
  | natRec scrutineeIsNeutral scrutineeParPreserves =>
      exact RawTerm.IsNeutral.natRec_par_preserves
        (fun scrutineeStep => scrutineeParPreserves scrutineeStep)
        parallelStep
  | listElim scrutineeIsNeutral scrutineeParPreserves =>
      exact RawTerm.IsNeutral.listElim_par_preserves
        (fun scrutineeStep => scrutineeParPreserves scrutineeStep)
        parallelStep
  | optionMatch scrutineeIsNeutral scrutineeParPreserves =>
      exact RawTerm.IsNeutral.optionMatch_par_preserves
        (fun scrutineeStep => scrutineeParPreserves scrutineeStep)
        parallelStep
  | eitherMatch scrutineeIsNeutral scrutineeParPreserves =>
      exact RawTerm.IsNeutral.eitherMatch_par_preserves
        (fun scrutineeStep => scrutineeParPreserves scrutineeStep)
        parallelStep
  | pathApp pathIsNeutral pathParPreserves =>
      exact RawTerm.IsNeutral.pathApp_par_preserves
        (fun pathStep => pathParPreserves pathStep)
        parallelStep
  | glueElim gluedValueIsNeutral gluedParPreserves =>
      exact RawTerm.IsNeutral.glueElim_par_preserves
        (fun gluedStep => gluedParPreserves gluedStep)
        parallelStep
  | transp pathIsNeutral pathParPreserves =>
      exact RawTerm.IsNeutral.transp_par_preserves
        pathIsNeutral
        (fun pathStep => pathParPreserves pathStep)
        parallelStep
  | hcomp sidesIsNeutral sidesParPreserves =>
      exact RawTerm.IsNeutral.hcomp_par_preserves
        (fun sidesStep => sidesParPreserves sidesStep)
        parallelStep
  | idJ witnessIsNeutral witnessParPreserves =>
      exact RawTerm.IsNeutral.idJ_par_preserves
        (fun witnessStep => witnessParPreserves witnessStep)
        parallelStep
  | oeqJ witnessIsNeutral witnessParPreserves =>
      exact RawTerm.IsNeutral.oeqJ_par_preserves
        (fun witnessStep => witnessParPreserves witnessStep)
        parallelStep
  | idStrictRec witnessIsNeutral witnessParPreserves =>
      exact RawTerm.IsNeutral.idStrictRec_par_preserves
        (fun witnessStep => witnessParPreserves witnessStep)
        parallelStep
  | equivApp equivIsNeutral equivParPreserves =>
      exact RawTerm.IsNeutral.equivApp_par_preserves
        (fun equivStep => equivParPreserves equivStep)
        parallelStep
  | equivApply equivIsNeutral equivParPreserves =>
      exact RawTerm.IsNeutral.equivApply_par_preserves
        equivIsNeutral
        (fun equivStep => equivParPreserves equivStep)
        parallelStep
  | modElim rawIsNeutral rawParPreserves =>
      exact RawTerm.IsNeutral.modElim_par_preserves
        (fun rawStep => rawParPreserves rawStep)
        parallelStep
  | subsume rawIsNeutral rawParPreserves =>
      exact RawTerm.IsNeutral.subsume_par_preserves
        (fun rawStep => rawParPreserves rawStep)
        parallelStep
  | refineElim refinedValueIsNeutral refinedParPreserves =>
      exact RawTerm.IsNeutral.refineElim_par_preserves
        (fun refinedStep => refinedParPreserves refinedStep)
        parallelStep
  | recordProj recordValueIsNeutral recordParPreserves =>
      exact RawTerm.IsNeutral.recordProj_par_preserves
        (fun recordStep => recordParPreserves recordStep)
        parallelStep
  | codataDest codataValueIsNeutral codataParPreserves =>
      exact RawTerm.IsNeutral.codataDest_par_preserves
        (fun codataStep => codataParPreserves codataStep)
        parallelStep
  | sessionSend channelIsNeutral channelParPreserves =>
      exact RawTerm.IsNeutral.sessionSend_par_preserves
        (fun channelStep => channelParPreserves channelStep)
        parallelStep
  | sessionRecv channelIsNeutral channelParPreserves =>
      exact RawTerm.IsNeutral.sessionRecv_par_preserves
        (fun channelStep => channelParPreserves channelStep)
        parallelStep
  | effectPerform operationIsNeutral operationParPreserves =>
      exact RawTerm.IsNeutral.effectPerform_par_preserves
        (fun operationStep => operationParPreserves operationStep)
        parallelStep

end LeanFX2
