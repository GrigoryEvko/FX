import FX1Poly.Core.ReflCanonicalFormsCandidate
import FX1Poly.Core.WeakHeadStepCommute

/-! # FX1Poly/Core/IdentityEliminatorCanonicalComputation
    — closed `idJ` / `idStrictRec` on a canonical `refl` witness COMPUTE to the base case (the identity-eliminator computation core)

`ReflCanonicalFormsCandidate.lean` ships identity data canonicity: a closed member of the identity candidate
reduces to a `refl` constructor (`reflClosedReducesToValue`).  This file pushes that into the identity
ELIMINATORS: a closed `idJ` / `idStrictRec` whose witness (the proof argument) is a canonical `refl` member
reduces to its base case.  The identity-eliminator analog of `BoolElimCanonicalComputation` (branch selection)
and `SigmaProjectionCanonicalComputation` (component projection), and a fundamental-free step toward `idJ` /
`idStrictRec` reducibility.  These are the last NON-GROWING eliminators — their ι SELECTS the
base case from the WITNESS position (vs. the growing recursors that apply a branch to a payload).

* `StepStar.idJWitness` / `StepStar.idStrictRecWitness` — the witness-position (second-child) chain congruences:
  a `StepStar` in the witness lifts to the whole `idJ` / `idStrictRec` cell (base case fixed).  Built from the
  generic one-hole-context chain lifter `StepStar.congAt` with `Step.cong … (StepChildren.there base (here …))`
  reaching past the base case into the witness child.
* `idJCanonicalWitnessReducesToBase` / `idStrictRecCanonicalWitnessReducesToBase` — the headline: a closed `idJ`
  / `idStrictRec` on a canonical `refl` witness reduces to its base case.  The witness reduces to a `refl`
  (identity data canonicity), the witness congruence carries that under the eliminator, and the matching ι rule
  (`Step.iotaIdJRefl` / `Step.iotaIdStrictRecRefl`) selects the base case.

## Zero-axiom verification

`StepStar.congAt` (chain induction), `reflClosedReducesToValue` (identity data canonicity via the candidate),
`Step.cong` / `StepChildren.there` / `StepChildren.here` (the witness congruence step), and the
`Step.iotaIdJRefl` / `Step.iotaIdStrictRecRefl` ι constructors, chained by `StepStar.transLast`.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation

/-- The `idJ` cell over its two children (base case, witness) — base case first, the eliminated proof second. -/
private abbrev idJCellOn {scope : Nat} (baseCase witness : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_idJ () (.childCons baseCase (.childCons witness .childNil))

/-- The `idStrictRec` cell over its two children (base case, witness) — same spine as `idJ`. -/
private abbrev idStrictRecCellOn {scope : Nat} (baseCase witness : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_idStrictRec () (.childCons baseCase (.childCons witness .childNil))

/-- **Witness-position chain congruence for `idJ`.**  A reduction chain in the witness (the second child) lifts
to the whole `idJ` cell (base case fixed).  Instantiates the generic one-hole-context chain lifter
`StepStar.congAt` with the `idJ` wrapper and `Step.cong … (StepChildren.there base (here …))` reaching past the
base case into the witness child. -/
theorem StepStar.idJWitness {scope : Nat} {baseCase witness witnessReduct : RawTerm scope}
    (witnessChain : StepStar witness witnessReduct) :
    StepStar (idJCellOn baseCase witness) (idJCellOn baseCase witnessReduct) :=
  StepStar.congAt
    (fun hole => idJCellOn baseCase hole)
    (fun stepInWitness => by
      apply Step.cong .gen_idJ ()
      exact StepChildren.there (headShift := 0) baseCase (StepChildren.here .childNil stepInWitness))
    witnessChain

/-- **Witness-position chain congruence for `idStrictRec`.**  Symmetric to `StepStar.idJWitness`. -/
theorem StepStar.idStrictRecWitness {scope : Nat} {baseCase witness witnessReduct : RawTerm scope}
    (witnessChain : StepStar witness witnessReduct) :
    StepStar (idStrictRecCellOn baseCase witness) (idStrictRecCellOn baseCase witnessReduct) :=
  StepStar.congAt
    (fun hole => idStrictRecCellOn baseCase hole)
    (fun stepInWitness => by
      apply Step.cong .gen_idStrictRec ()
      exact StepChildren.there (headShift := 0) baseCase (StepChildren.here .childNil stepInWitness))
    witnessChain

/-- **Closed `idJ` on a canonical `refl` witness computes to the base case.**  The identity-eliminator analog of
closed-bool elimination canonicity: a closed `idJ` whose witness is a member of the identity candidate
`StepStar`-reduces to its base case.  The witness reduces to a `refl` (`reflClosedReducesToValue`),
`StepStar.idJWitness` carries that reduction under the `idJ`, and `Step.iotaIdJRefl` selects the base case.
Fundamental-free — it uses only identity data canonicity plus the witness congruence and the ι rule, no fundamental
theorem. -/
theorem idJCanonicalWitnessReducesToBase {baseCase witness : RawTerm 0}
    (witnessMember : CanonicalFormsPredicate isReflValue witness) :
    StepStar (idJCellOn baseCase witness) baseCase := by
  obtain ⟨value, witnessReducesToValue, rawWitness, valueIsRefl, _rawWitnessNormal⟩ :=
    reflClosedReducesToValue witnessMember
  subst valueIsRefl
  exact StepStar.transLast (StepStar.idJWitness witnessReducesToValue) Step.iotaIdJRefl

/-- **Closed `idStrictRec` on a canonical `refl` witness computes to the base case.**  Symmetric to
`idJCanonicalWitnessReducesToBase` — the strict identity eliminator has the same `(base, witness)` spine and the
same single ι rule (`idStrictRec base (refl w) ↝ base`), inverted by `Step.iotaIdStrictRecRefl`. -/
theorem idStrictRecCanonicalWitnessReducesToBase {baseCase witness : RawTerm 0}
    (witnessMember : CanonicalFormsPredicate isReflValue witness) :
    StepStar (idStrictRecCellOn baseCase witness) baseCase := by
  obtain ⟨value, witnessReducesToValue, rawWitness, valueIsRefl, _rawWitnessNormal⟩ :=
    reflClosedReducesToValue witnessMember
  subst valueIsRefl
  exact StepStar.transLast (StepStar.idStrictRecWitness witnessReducesToValue) Step.iotaIdStrictRecRefl

end FX1Poly.Core
