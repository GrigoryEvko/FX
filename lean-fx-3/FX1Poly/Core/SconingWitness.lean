import FX1Poly.Core.ReducibilityCandidate

/-! # Foundation/PolyCell/Core/SconingWitness
    — Path C: internal sconing as a proof-relevant logical predicate (BKS "sconing is enough")

polycell.md §3.0.2 commits to the Bocquet-Kaposi-Sattler thesis (FSCD 2023, `arXiv:2302.05190`):
**sconing alone is enough for the metatheory** — for each obligation, exhibit a sconing witness and
canonicity / normalization / parametricity are DERIVED from one boilerplate-free induction principle.
polycell.md §3.12 notes the synthetic (STC) realization uses a closed modality that is a higher
inductive quotient — which in Lean pulls `Quot.sound` and would break the zero-axiom discipline.  So
this file realizes sconing the OTHER way the thesis allows: as a **proof-relevant logical predicate**
(the "scone" as a `RawTerm → Prop`), not as a HIT.

A `SconingWitness`, relative to a notion of well-typedness and a notion of canonical form, bundles the
displayed "computability" predicate over cells with the two gluing obligations: every well-typed cell
is computable (the FUNDAMENTAL obligation — the fundamental theorem of a reducibility logical
relation, the leg shared with Path A) and every computable cell is canonical (the EXTRACTION
obligation — "consult the closed phase").  `SconingWitness.canonicity` is then the boilerplate-free
derivation: canonicity is `extraction ∘ fundamental`.

The concrete witness `reducibilityScone` closes the loop with Path A: a reducibility candidate IS a
sconing witness for the strong-normalization canonicity statement (CR1 discharges extraction).  So the
reducibility logical relation (Path A) and the internal sconing (Path C) construct the SAME object —
the cross-path agreement that is the certainty thesis.  This complements the `FX1Poly.Tier0`
construction-level ledger (which tracks WHICH obligations a profile has discharged) with the actual
logical-predicate content.

## Zero-axiom verification

A `Type`-valued structure (the `computable` field is predicate data) plus a composition theorem and a
record literal discharging extraction by `IsReducibilityCandidate.stronglyNormalizing`.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Swept per declaration by
`#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation
open StepStar

/-- A proof-relevant internal-sconing witness, relative to a notion of well-typedness and a notion of
canonical form: the displayed "computability" predicate over cells (the scone) plus the two gluing
obligations.  Realized as a logical predicate, NOT the synthetic STC closed modality (a higher
inductive quotient that would pull `Quot.sound`). -/
structure SconingWitness {scope : Nat} (isWellTyped : RawTerm scope → Prop)
    (isCanonical : RawTerm scope → Prop) where
  /-- The displayed "computability" predicate — the scone over the syntax. -/
  computable : RawTerm scope → Prop
  /-- FUNDAMENTAL obligation: every well-typed cell is computable.  This is the fundamental theorem of
  the logical relation (Path A), the reducibility leg shared across the metatheory paths. -/
  fundamental : ∀ term : RawTerm scope, isWellTyped term → computable term
  /-- EXTRACTION obligation: every computable cell is canonical — "consult the closed phase". -/
  extraction : ∀ term : RawTerm scope, computable term → isCanonical term

/-- **Sconing implies canonicity** (the BKS boilerplate-free derivation): given a sconing witness,
every well-typed cell is canonical, by composing the fundamental and extraction obligations.  Once a
witness exists this IS canonicity; the witness's `fundamental` field is the only hard obligation. -/
theorem SconingWitness.canonicity {scope : Nat} {isWellTyped isCanonical : RawTerm scope → Prop}
    (witness : SconingWitness isWellTyped isCanonical)
    (term : RawTerm scope) (typed : isWellTyped term) : isCanonical term :=
  witness.extraction term (witness.fundamental term typed)

/-- **A reducibility candidate is a sconing witness for strong-normalization canonicity** — the
concrete Path-A ↔ Path-C bridge.  Given a reducibility candidate and the fundamental obligation (every
well-typed cell lies in the candidate — the fundamental theorem), the extraction obligation is
discharged for free by CR1 (`stronglyNormalizing`): candidate membership entails strong
normalization.  So the reducibility logical relation (Path A) IS an internal-sconing witness (Path C)
for "every well-typed cell is strongly normalizing" — two methods, one object. -/
def reducibilityScone {scope : Nat} {candidate : RawTerm scope → Prop}
    (candidateIsReducibility : IsReducibilityCandidate candidate)
    {isWellTyped : RawTerm scope → Prop}
    (fundamental : ∀ term : RawTerm scope, isWellTyped term → candidate term) :
    SconingWitness isWellTyped IsStronglyNormalizing :=
  { computable := candidate
    fundamental := fundamental
    extraction := fun _term reducible => candidateIsReducibility.stronglyNormalizing reducible }

end FX1Poly.Core
