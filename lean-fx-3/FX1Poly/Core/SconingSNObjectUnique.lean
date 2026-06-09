import FX1Poly.Core.SconingTaitCrossLeg

/-! # FX1Poly/Core/SconingSNObjectUnique
    — the sconing leg can NEVER be an independent strong-normalization proof: SN is a Prop, so every
    sconing construction extracts the SAME SN object

`SconingTaitCrossLeg.lean` proves `sconingSN_eq_taitComposition`: the SHIPPED `reducibilityScone`'s extracted
strong normalization is the Tait `CR1 ∘ fundamental` witness, by `rfl`.  A skeptic might hope a DIFFERENT
sconing construction would give an INDEPENDENT second SN proof, flipping the parity cell from `bridgedToTait`
to `provenIndependent`.

This file rules that out at full generality.  Strong normalization (`IsStronglyNormalizing`, an `Acc`-based
predicate) is a `Prop`, so by Lean's DEFINITIONAL proof irrelevance any two of its proofs are definitionally
equal.  Hence:

  * `sconingSN_objectUnique` — ANY two sconing witnesses for the SN-canonicity statement extract the IDENTICAL
    SN proof for every well-typed term.  No sconing construction is a distinct SN object.
  * `anySconingSN_eq_taitComposition` — consequently ANY SN-scone's extracted SN IS the Tait `CR1 ∘
    fundamental` witness, generalizing `sconingSN_eq_taitComposition` from the one `reducibilityScone`
    constructor to every `SconingWitness … IsStronglyNormalizing`.
  * `sconingSN_eq_taitComposition_ofGeneral` — the shipped specific lemma recovered as an instance of the
    general one (the general subsumes the specific).

## Why this forces bridgedToTait (and where genuine independence could live)

Because SN is a proposition, "strong normalization proven two INDEPENDENT ways" is not a meaningful
object-level distinction: every proof of `IsStronglyNormalizing term` is the same object.  So the sconing leg's
SN endpoint cannot be `provenIndependent` as a proof object — it is `bridgedToTait` not by stipulation but
because the extracted SN is forced equal to the Tait witness.

The only place genuine independence could live is the DISPLAYED COMPUTABILITY predicate (the logical relation
itself, `SconingWitness.computable`), not the extracted SN.  The shipped scone's computability IS the Path-A
reducibility candidate (`sconingScone_computable_eq_candidate`), so it carries no SN-content beyond Tait; an
independent route would need a NON-candidate computability predicate — the synthetic Sterling-Tait closed
modality — which is zero-axiom-blocked (a higher-inductive quotient pulling `Quot.sound`), exactly as
`SconingTaitCrossLeg` records.  This file pins the SN-endpoint half of that boundary as a theorem.

## Zero-axiom verification

Both headline theorems are `rfl`, discharged by Lean's definitional proof irrelevance for the `Prop`
`IsStronglyNormalizing term`; the third is an application of the second.  No induction, no `funext`, no
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

open StepStar

/-- **No sconing construction is a distinct SN object.**  Any two sconing witnesses for the
strong-normalization canonicity statement extract the IDENTICAL strong-normalization proof for every
well-typed term — definitional proof irrelevance, since `IsStronglyNormalizing term` is a `Prop`. -/
theorem sconingSN_objectUnique {scope : Nat} {isWellTyped : RawTerm scope → Prop}
    (witnessOne witnessTwo : SconingWitness isWellTyped IsStronglyNormalizing)
    (term : RawTerm scope) (typed : isWellTyped term) :
    witnessOne.canonicity term typed = witnessTwo.canonicity term typed :=
  rfl

/-- **★ Every SN-scone is the Tait composition.**  ANY sconing witness for the SN-canonicity statement
extracts exactly the Tait `CR1 ∘ fundamental` strong-normalization witness — generalizing
`sconingSN_eq_taitComposition` from the single `reducibilityScone` constructor to the whole class of SN-scones.
The sconing SN endpoint is forced equal to Tait's, never an independent object. -/
theorem anySconingSN_eq_taitComposition {scope : Nat} {candidate : RawTerm scope → Prop}
    (candidateIsReducibility : IsReducibilityCandidate candidate)
    {isWellTyped : RawTerm scope → Prop}
    (fundamental : ∀ term : RawTerm scope, isWellTyped term → candidate term)
    (anyWitness : SconingWitness isWellTyped IsStronglyNormalizing)
    (term : RawTerm scope) (typed : isWellTyped term) :
    anyWitness.canonicity term typed
      = candidateIsReducibility.stronglyNormalizing (fundamental term typed) :=
  rfl

/-- The shipped `sconingSN_eq_taitComposition` recovered as an instance of the general theorem at
`anyWitness := reducibilityScone …`: the general subsumes the specific. -/
theorem sconingSN_eq_taitComposition_ofGeneral {scope : Nat} {candidate : RawTerm scope → Prop}
    (candidateIsReducibility : IsReducibilityCandidate candidate)
    {isWellTyped : RawTerm scope → Prop}
    (fundamental : ∀ term : RawTerm scope, isWellTyped term → candidate term)
    (term : RawTerm scope) (typed : isWellTyped term) :
    (reducibilityScone candidateIsReducibility fundamental).canonicity term typed
      = candidateIsReducibility.stronglyNormalizing (fundamental term typed) :=
  anySconingSN_eq_taitComposition candidateIsReducibility fundamental
    (reducibilityScone candidateIsReducibility fundamental) term typed

end FX1Poly.Core
