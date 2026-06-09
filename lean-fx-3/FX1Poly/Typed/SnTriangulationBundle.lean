import FX1Poly.Typed.OpenStronglyNormalizingUnconditional
import FX1Poly.Core.SconingSNObjectUnique
import FX1Poly.Typed.RawBetaNotRpoOrientable
import FX1Poly.Typed.MilestoneAParityMatrix

/-! # FX1Poly/Typed/SnTriangulationBundle
    — strong normalization proven ONCE (Tait), triangulated TWICE, in one honest module

The strong-normalization endpoint of Milestone A is targeted by three routes.  This module consolidates
their honest statuses — exactly the `parityCell _ .strongNormalization` column — with each cell's backing
theorem cited in the SAME file, so the "SN once, triangulated twice" reading is machine-checkable rather than
prose.

  * **Leg 1 — Tait reducibility (the ONE independent proof).**  `snPrimaryTait` re-exports the unconditional
    grown closure `HasTypeDescPi.stronglyNormalizingOfWfContextDesc`: every grown-well-typed subject in a
    well-formed context is strongly normalizing.  This is the self-contained logical-relation argument; the
    ledger marks it `provenIndependent`.

  * **Leg 2 — sconing (bridged to Tait, NOT independent).**  `snConfirmSconingBridged` cites
    `anySconingSN_eq_taitComposition`: because `IsStronglyNormalizing` is a `Prop`, any sconing witness's
    extracted SN is the IDENTICAL object as the Tait `CR1 ∘ fundamental` witness — so the sconing route is a
    re-packaging, not a second proof.  The ledger marks it `bridgedToTait`.

  * **Leg 3 — recursive path order (a Tait-free FRAGMENT, β-imported).**  `snConfirmRpoFragment` cites
    `iotaEta_noInfiniteReduction`: the ι∪η reduction admits no infinite sequence, oriented by one recursive
    path order over the erased syntax, with NO typing hypothesis.  `snRpoBetaBoundary` cites
    `betaNotOrientableByErasure`: no well-founded order on the erased syntax can orient raw β (Ω self-loops),
    so the route covers only the ι∪η fragment and β stays Tait-imported.  The ledger marks it
    `partialFragment`.

`snColumnIsHonest` pins the three statuses `(provenIndependent, bridgedToTait, partialFragment)` by `rfl`
against the parity ledger — the consolidation the honest-capstone sign-off consumes.  The honest reading: SN is
proven once (Leg 1); Legs 2 and 3 are a same-object bridge and a Tait-free fragment respectively, i.e. two
CONFIRMATIONS, not two independent proofs.

## Zero-axiom verification

`snColumnIsHonest` is `⟨rfl, rfl, rfl⟩` on the full-enum ledger; the four leg theorems are thin re-exports of
the shipped `stronglyNormalizingOfWfContextDesc` / `anySconingSN_eq_taitComposition` /
`iotaEta_noInfiniteReduction` / `betaNotOrientableByErasure`, each already zero-axiom.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core.ParityMatrix

open FX1Poly.Core FX1Poly.Typed StepStar

/-- **The SN column of the parity ledger is honest.**  The three strong-normalization cells are exactly
`(provenIndependent, bridgedToTait, partialFragment)` — Tait independent, sconing bridged, RPO a fragment.
Pinned by `rfl`; if a future edit flips any SN cell this fails to recompute, forcing the column to stay
honest. -/
theorem snColumnIsHonest :
    parityCell .taitReducibility .strongNormalization = .provenIndependent ∧
    parityCell .sconingViaSTC .strongNormalization = .bridgedToTait ∧
    parityCell .rpoWordRewriting .strongNormalization = .partialFragment :=
  ⟨rfl, rfl, rfl⟩

/-- **Leg 1 (Tait — the ONE independent SN proof).**  Every grown-well-typed subject in a well-formed context
is strongly normalizing: the self-contained reducibility-logical-relation closure
(`HasTypeDescPi.stronglyNormalizingOfWfContextDesc`). -/
theorem snPrimaryTait {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (wellFormed : WfContextDesc context)
    (derivation : HasTypeDescPi profile context subject classifier) :
    IsStronglyNormalizing subject :=
  HasTypeDescPi.stronglyNormalizingOfWfContextDesc wellFormed derivation

/-- **Leg 2 (sconing — bridged to Tait).**  Any sconing witness for the SN-canonicity statement extracts the
IDENTICAL object as the Tait `CR1 ∘ fundamental` witness — so the sconing route confirms, but does not
independently re-prove, strong normalization (`anySconingSN_eq_taitComposition`). -/
theorem snConfirmSconingBridged {scope : Nat} {candidate : RawTerm scope → Prop}
    (candidateIsReducibility : IsReducibilityCandidate candidate)
    {isWellTyped : RawTerm scope → Prop}
    (fundamental : ∀ term : RawTerm scope, isWellTyped term → candidate term)
    (anyWitness : SconingWitness isWellTyped IsStronglyNormalizing)
    (term : RawTerm scope) (typed : isWellTyped term) :
    anyWitness.canonicity term typed
      = candidateIsReducibility.stronglyNormalizing (fundamental term typed) :=
  anySconingSN_eq_taitComposition candidateIsReducibility fundamental anyWitness term typed

/-- **Leg 3a (RPO — the Tait-free fragment).**  The ι∪η reduction admits no infinite sequence, by one
recursive path order over the erased syntax with no typing hypothesis (`iotaEta_noInfiniteReduction`). -/
theorem snConfirmRpoFragment {scope : Nat} (reductionSequence : Nat → RawTerm scope)
    (eachStepsToNext : ∀ index, IotaEtaStep (reductionSequence index) (reductionSequence (index + 1))) :
    False :=
  iotaEta_noInfiniteReduction reductionSequence eachStepsToNext

/-- **Leg 3b (RPO — the β boundary).**  No well-founded order on the erased syntax can orient raw β (Ω
self-loops), so the recursive-path-order route covers only the ι∪η fragment; β stays Tait-imported
(`betaNotOrientableByErasure`). -/
theorem snRpoBetaBoundary
    {roseOrder : RpoInductive.RoseTerm Generator → RpoInductive.RoseTerm Generator → Prop}
    (wellFounded : WellFounded roseOrder)
    (orientsRawBeta : ∀ {redex reduct : RawTerm 0},
        Step redex reduct → roseOrder (RawIotaRpo.eraseToRose reduct) (RawIotaRpo.eraseToRose redex)) :
    False :=
  RawIotaRpo.betaNotOrientableByErasure wellFounded orientsRawBeta

end FX1Poly.Core.ParityMatrix
