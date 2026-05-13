import LeanFX2.Reducibility.Basic

/-! # LeanFX2.Reducibility.Neutral.NeutralCore

The `RawTerm.IsNeutral` inductive predicate plus the
impossibility lemmas `not_<ctor>` for every non-neutral form
(constructors of intro shape — `lam` / `pair` / `boolTrue` /
etc.).  The not-lemmas serve as inversion atoms for the
preservation cascade in the sibling sub-modules.

## Root status

Layer 3 metatheory leaf.  First slice of `Neutral`. -/

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

/-- Neutrality is preserved by every renaming.

Every neutral form is congruence-shaped under `RawTerm.rename`: the
principal scrutinee is the recursive subterm, so the renamed term is
the same neutral form whose principal scrutinee remains neutral by
structural induction. -/
theorem RawTerm.IsNeutral.rename {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    {source : RawTerm sourceScope}
    (sourceIsNeutral : RawTerm.IsNeutral source) :
    RawTerm.IsNeutral (source.rename rho) := by
  induction sourceIsNeutral with
  | var position => exact RawTerm.IsNeutral.var (rho position)
  | app _ functionIH => exact RawTerm.IsNeutral.app functionIH
  | fst _ pairIH => exact RawTerm.IsNeutral.fst pairIH
  | snd _ pairIH => exact RawTerm.IsNeutral.snd pairIH
  | boolElim _ scrutineeIH =>
      exact RawTerm.IsNeutral.boolElim scrutineeIH
  | natElim _ scrutineeIH =>
      exact RawTerm.IsNeutral.natElim scrutineeIH
  | natRec _ scrutineeIH =>
      exact RawTerm.IsNeutral.natRec scrutineeIH
  | listElim _ scrutineeIH =>
      exact RawTerm.IsNeutral.listElim scrutineeIH
  | optionMatch _ scrutineeIH =>
      exact RawTerm.IsNeutral.optionMatch scrutineeIH
  | eitherMatch _ scrutineeIH =>
      exact RawTerm.IsNeutral.eitherMatch scrutineeIH
  | pathApp _ pathIH => exact RawTerm.IsNeutral.pathApp pathIH
  | glueElim _ gluedValueIH =>
      exact RawTerm.IsNeutral.glueElim gluedValueIH
  | transp _ pathIH => exact RawTerm.IsNeutral.transp pathIH
  | hcomp _ sidesIH => exact RawTerm.IsNeutral.hcomp sidesIH
  | idJ _ witnessIH => exact RawTerm.IsNeutral.idJ witnessIH
  | oeqJ _ witnessIH => exact RawTerm.IsNeutral.oeqJ witnessIH
  | idStrictRec _ witnessIH =>
      exact RawTerm.IsNeutral.idStrictRec witnessIH
  | equivApp _ equivIH => exact RawTerm.IsNeutral.equivApp equivIH
  | equivApply _ equivIH =>
      exact RawTerm.IsNeutral.equivApply equivIH
  | modElim _ rawIH => exact RawTerm.IsNeutral.modElim rawIH
  | subsume _ rawIH => exact RawTerm.IsNeutral.subsume rawIH
  | refineElim _ refinedValueIH =>
      exact RawTerm.IsNeutral.refineElim refinedValueIH
  | recordProj _ recordValueIH =>
      exact RawTerm.IsNeutral.recordProj recordValueIH
  | codataDest _ codataValueIH =>
      exact RawTerm.IsNeutral.codataDest codataValueIH
  | sessionSend _ channelIH =>
      exact RawTerm.IsNeutral.sessionSend channelIH
  | sessionRecv _ channelIH =>
      exact RawTerm.IsNeutral.sessionRecv channelIH
  | effectPerform _ operationIH =>
      exact RawTerm.IsNeutral.effectPerform operationIH


end LeanFX2
