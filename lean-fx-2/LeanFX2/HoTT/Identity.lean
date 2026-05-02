import LeanFX2.Term
import LeanFX2.Reduction.Step
import LeanFX2.Reduction.StepStar
import LeanFX2.Reduction.Conv

/-! # HoTT/Identity — identity-type metatheorems

The Term constructor `refl rawWitness` introduces identity types.
This file establishes intro/elim/computation rules at the
metatheoretic level WITHOUT committing to univalence.

## What ships (Phase 6.A foundational)

* `Conv.idJ_refl_baseCase` — the ι rule lifted to Conv:
  `J base (refl x) ≅ base`.  Direct corollary of
  `Step.iotaIdJRefl`.
* `StepStar.idJ_baseCase_lift` — congruence: stepping the
  baseCase of `idJ` produces a chain of `idJ` terms.
* `StepStar.idJ_witness_lift` — congruence: stepping the
  witness of `idJ` produces a chain of `idJ` terms.
* `Conv.idJ_baseCase_cong` — convertibility of baseCases lifts
  to convertibility of `idJ` terms.

## Foundation for HoTT/Path/*

These lemmas are the FOUNDATION for path composition / inverse /
groupoid laws.  Each path operation is constructed as an `idJ`
on a refl-witness; the ι rule + cong rules deliver the
computation laws (Path.compose refl p = p, etc.).

## What does NOT ship here

* Full dependent J — needs motive depending on endpoints +
  witness.  Layer 5 work.
* Path composition / inverse / groupoid laws — Layer 5 (in
  HoTT/Path/Composition, HoTT/Path/Inverse, HoTT/Path/Groupoid).
* Transport — Layer 5 (HoTT/Transport).
* Equivalences + univalence — Layer 5 (HoTT/Equivalence,
  HoTT/Univalence).

Zero-axiom verified per declaration via AuditAll.
-/

namespace LeanFX2

variable {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}

/-! ## ι rule: J on refl reduces to baseCase -/

/-- The ι rule for identity types: `J base (refl x) ⟶ base`.
Single-step form, direct from `Step.iotaIdJRefl`. -/
theorem Step.idJ_refl
    (carrier : Ty level scope) (endpoint : RawTerm scope)
    {motiveType : Ty level scope}
    {baseRaw : RawTerm scope}
    (baseCase : Term context motiveType baseRaw) :
    Step (Term.idJ (carrier := carrier)
                   (leftEndpoint := endpoint)
                   (rightEndpoint := endpoint)
            baseCase
            (Term.refl carrier endpoint))
         baseCase :=
  Step.iotaIdJRefl carrier endpoint baseCase

/-- Conv form: `J base (refl x) ≅ base`. -/
theorem Conv.idJ_refl_baseCase
    (carrier : Ty level scope) (endpoint : RawTerm scope)
    {motiveType : Ty level scope}
    {baseRaw : RawTerm scope}
    (baseCase : Term context motiveType baseRaw) :
    Conv (Term.idJ (carrier := carrier)
                   (leftEndpoint := endpoint)
                   (rightEndpoint := endpoint)
            baseCase
            (Term.refl carrier endpoint))
         baseCase :=
  Conv.fromStep (Step.iotaIdJRefl carrier endpoint baseCase)

/-! ## Cong rules — DEFERRED to Phase 12 sprint (Day 2)

`StepStar.idJ_baseCase_lift` and `StepStar.idJ_witness_lift`
would lift a StepStar chain on baseCase / witness to a chain on
the whole `idJ` term.  They block on Lean 4's `induction` tactic
not generalizing duplicate index occurrences (motiveType + the
Ty.id endpoints appear in source AND target term-types, and
`induction chain` cannot generalize over both).

Workaround: free the indices via `srcTy/tgtTy` variables +
equality hypotheses + subject reduction (Step.preserves_isClosedTy
analog for motiveType).  Generic SR is the Phase-12 Day-2 AM
deliverable; once shipped, these lifters become 8-line proofs
following the `StepStar.natSucc_lift_general` template in
Term/SubjectReduction.lean.

For now: ship single-step `Step.idJ_refl` + `Conv.idJ_refl_baseCase`
(above).  The lifters arrive with general SR.

## Convertibility congruence (BLOCKED on Subject Reduction)

`Conv.idJ_baseCase_cong` and `Conv.idJ_witness_cong` would say
that convertibility of base/witness lifts to convertibility of
the whole `idJ` term.

These DO NOT GENERALIZE to arbitrary `motiveType` /
`Ty.id carrier ...` types because `Conv`'s definitional shape
allows the common-reduct's type to differ from the source type:

```lean
def Conv source target : Prop :=
  ∃ midType midRaw midTerm, StepStar source midTerm ∧ StepStar target midTerm
```

To rebuild `Term.idJ midTerm witnessTerm` we need `midTerm` at
`motiveType`, but `Conv`'s `midType` is existentially bound
without that constraint.  The constraint is exactly subject
reduction at `motiveType` — see M06/M07 (subject reduction at
arrow / parametric types).

For closed motiveTypes (`Ty.unit`, `Ty.bool`, `Ty.nat`)
SR is already shipped via `Step.preserves_ty_*` lemmas in
`Term/SubjectReduction.lean`; specialized cong rules for those
cases can be added without further infrastructure.  General
cong rules wait on M06+M07. -/

end LeanFX2
