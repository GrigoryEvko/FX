import LeanFX.Syntax.Reduction.Congruence.IdJStepStar

/-! # Eliminator congruence umbrella module.

Re-exports the per-eliminator `Conv` and `StepStar` congruence
families.  Two parallel chains land here:

  * **Conv side** (`Conv`-valued congruences):
    `Basic` (header rules — `Conv.refl`, `Conv.sym`, `Conv.trans`)
    → `Bool` (boolElim) → `NatConv` (natRec) → `List` (listElim,
    listMatch) → `OptionConv` (optionMatch) → `EitherConv`
    (eitherMatch) → `IdJConv` (idJ).
  * **StepStar side** (multi-step `StepStar`-valued congruences):
    `NatStepStar` → `OptionStepStar` → `EitherStepStar` →
    `IdJStepStar` (the file this umbrella imports).

Every theorem here threads reduction through one constructor
position at a time — `boolElim_cong_scrut`, `natRec_cong_zero`,
etc.  The pattern: induction on the reduction relation with
`refl`/`step`/`trans` arms; each step arm calls the matching
single-step rule from `Reduction/Step.lean`.

Convention: zero axioms, gated per file in
`Tools/AuditAll.lean`.  These congruences are load-bearing for
the eventual `Conv` decision procedure and for the
parallel-reduction `Step.parStar` chain congruences in
`Reduction/ParSubst.lean`. -/
