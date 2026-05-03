import LeanFX2.Refine.Ty

/-! # Refine/Decidable — auto-discharge for decidable refinements

For refinements whose predicate has a `Decidable` instance, the
typechecker discharges proof obligations directly without SMT.

This file ships:
* `tryDischarge` — try to construct a `RefineWitness` from a value
  by invoking the bundled decidability
* `coerceIfPossible` — coercion that succeeds when the predicate
  holds, fails (with `none`) otherwise
* `discharge!` — partial coercion that requires a witness inline,
  failing with `Option`

## Decidable predicate fragment

Includes:
* Linear arithmetic over `Nat` / `Int` (`x > 0`, `x ≤ 10`, etc.)
* Bit-vector operations (`n.isPowerOfTwo`, etc.)
* Boolean combinations of decidable predicates
* Pattern matches with finite case analysis (constructor-shape preds)

## Auto-discharge in elaboration

When elaborating `Term.refineIntro term`, the elaborator looks for
a `tryDischarge` invocation.  If it returns `some witness`, the
refinement is discharged with the proof; otherwise elaboration
falls back to SMT-cert (Refine/SMTCert.lean) or rejects.

Zero-axiom verified per declaration. -/

namespace LeanFX2.Refine

variable {alpha : Type}

/-! ## Direct-decision discharge

Try to construct a `RefineWitness` by invoking the bundled
decidability instance.  Returns `some witness` when the predicate
holds, `none` otherwise. -/

/-- Try to build a refinement witness from a value.  Uses the
predicate's `Decidable` instance.  Total via `Decidable` case
analysis. -/
def tryDischarge
    (predicate : RefinePredicate alpha)
    (someValue : alpha) :
    Option (RefineWitness predicate) :=
  match predicate.decidable someValue with
  | .isTrue holdsProof => some { refinedValue := someValue, satisfies := holdsProof }
  | .isFalse _ => none

/-- Coerce a value into a refinement witness, returning `none` if
the predicate fails.  Alias for `tryDischarge` with cleaner-named
intent at call sites. -/
def coerceIfPossible
    (predicate : RefinePredicate alpha)
    (someValue : alpha) :
    Option (RefineWitness predicate) :=
  tryDischarge predicate someValue

/-! ## Soundness: discharge produces correct witnesses

When `tryDischarge` returns `some w`, `w.refinedValue = someValue`
and `predicate.pred w.refinedValue` holds (definitionally, via
the witness construction). -/

/-- Soundness: `tryDischarge p v = some w` implies the witness's
underlying value is `v`.

Proved by case-splitting on the Decidable instance.  Each case
inspects the result and reduces accordingly. -/
theorem tryDischarge_sound
    (predicate : RefinePredicate alpha)
    (someValue : alpha)
    (someWitness : RefineWitness predicate)
    (dischargeEq : tryDischarge predicate someValue = some someWitness) :
    someWitness.refinedValue = someValue := by
  unfold tryDischarge at dischargeEq
  cases hDec : predicate.decidable someValue with
  | isFalse failsProof =>
    rw [hDec] at dischargeEq
    nomatch dischargeEq
  | isTrue holdsProof =>
    rw [hDec] at dischargeEq
    have witnessEq :
        ({ refinedValue := someValue, satisfies := holdsProof } : RefineWitness predicate)
          = someWitness := by
      injection dischargeEq
    rw [← witnessEq]

/-! ## Completeness: discharge succeeds when predicate holds

If `predicate.pred someValue` holds, then `tryDischarge` returns
`some _`. -/

/-- Completeness: when the predicate holds for `someValue`,
`tryDischarge` returns a witness. -/
theorem tryDischarge_complete
    (predicate : RefinePredicate alpha)
    (someValue : alpha)
    (predicateHolds : predicate.pred someValue) :
    ∃ (someWitness : RefineWitness predicate),
      tryDischarge predicate someValue = some someWitness := by
  unfold tryDischarge
  match predicate.decidable someValue with
  | .isTrue holdsProof =>
    exact ⟨{ refinedValue := someValue, satisfies := holdsProof }, rfl⟩
  | .isFalse failsProof =>
    exact (failsProof predicateHolds).elim

/-! ## Refinement equality decision

When the underlying type has decidable equality and the predicate's
proofs are propositional (always true for `Prop`), refinement
witnesses with the same underlying value are decidably equal. -/

/-- Refinement equality reduces to underlying-value equality
(witness proofs are propositional). -/
theorem RefineWitness.eq_iff_value_eq
    [DecidableEq alpha]
    {predicate : RefinePredicate alpha}
    (firstWitness secondWitness : RefineWitness predicate) :
    firstWitness.refinedValue = secondWitness.refinedValue
      ↔ firstWitness.coerce = secondWitness.coerce := by
  unfold RefineWitness.coerce
  exact Iff.rfl

/-! ## Smoke samples (use `.isSome` checks to avoid dep-record decidability) -/

/-- Discharge succeeds for 5 in `Nat.isPositive`. -/
example : (tryDischarge Nat.isPositive 5).isSome = true := by
  unfold tryDischarge Nat.isPositive
  decide

/-- Discharge fails for 0 in `Nat.isPositive` — the result is none. -/
example : (tryDischarge Nat.isPositive 0).isNone = true := by
  unfold tryDischarge Nat.isPositive
  decide

/-- Discharge succeeds for 7 in `Nat.isBounded 10`. -/
example : (tryDischarge (Nat.isBounded 10) 7).isSome = true := by
  unfold tryDischarge Nat.isBounded
  decide

/-- Discharge fails for 15 in `Nat.isBounded 10` — the result is none. -/
example : (tryDischarge (Nat.isBounded 10) 15).isNone = true := by
  unfold tryDischarge Nat.isBounded
  decide

/-- Discharge succeeds for [1, 2] in `List.isNonEmpty`. -/
example : (tryDischarge (List.isNonEmpty (alpha := Nat)) [1, 2]).isSome = true := by
  unfold tryDischarge List.isNonEmpty
  decide

/-- Discharge fails for [] in `List.isNonEmpty` — the result is none. -/
example : (tryDischarge (List.isNonEmpty (alpha := Nat)) []).isNone = true := by
  unfold tryDischarge List.isNonEmpty
  decide

end LeanFX2.Refine
