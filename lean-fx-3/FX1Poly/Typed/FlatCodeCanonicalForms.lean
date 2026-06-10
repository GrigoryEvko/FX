import FX1Poly.Typed.DenoteKeyedBoundedReducibility
import FX1Poly.Typed.DenoteKeyedBoundedReducibleEnv
import FX1Poly.Typed.HasTypeDescPairIntro
import FX1Poly.Typed.HasTypeDescEitherIntro

/-! # FX1Poly/Typed/FlatCodeCanonicalForms — the FLAT-CANON payoff (CAN-6, closes the #936 residual)

With the `dataFlat` arm landed in both `ReducibleTypeStepDenote` and `ReducibleTypeStepBounded`, the §5
candidate bridge now covers the five FLAT data type-code formers exactly as it covers `emptyTypeCell`.
This file harvests the bridge — the per-code candidate IDENTIFICATIONS and the closed-member CANONICITY
that #936 asked for:

  * `flatCode_isReducibleTypeAtBounded` — non-vacuity: every flat-code-rooted type cell IS
    bounded-reducible-as-type at every bound, via the dedicated `dataFlat` arm (NOT the now-gated
    generic `neutral` arm).
  * `flatCode_candidate_isFlatTaitCandidate` — the candidate bridge, the obstruction REVERSED: ANY
    candidate a flat-code-rooted cell is bounded-reducible-as-type to agrees pointwise with the pinned
    `dataTaitCandidate (flatCodeValuePredicate root)`.  Before the edit the `neutral` arm collapsed every
    flat code's candidate onto the whole `IsStronglyNormalizing` set (which contains every closed value),
    making per-code canonicity through the model unprovable.
  * `flatCode_memberIsFlatTaitCandidate` — the member form the canonicity extraction consumes.
  * `closedProductMemberReducesToPair` / `closedEitherMemberReducesToInjection` — ★ closed flat-code
    canonicity at the two flat codes WITH live intro engines: a closed member of the model candidate of
    `productTypeCell A B` reduces to a PAIR value; of `eitherTypeCell L R` to an `inl`/`inr` value.
  * `closedSumMemberRefuted` — the sum lane: `gen_sumCode` has NO intro generators (honest empty value
    predicate), so its candidate has no closed member — the empty-type-like consistency of the sum lane.

## Honest scope

These are MODEL-level (sconing-leg) statements: the candidate bridge pins the reducibility candidate, and
`dataTaitCandidate.closedReducesToValue` extracts canonicity for closed candidate MEMBERS.  Connecting
ENGINE-typed terms to candidate membership is the fundamental-theorem leg: the grown FT never types members
at flat classifiers (flat codes are not formation-telescope-reachable, TELESCOPE-REACH), and the standalone
intro engines (pair/either) sit outside the bounded FT — the intro-engine member bridge is future work, not
silently claimed here.

## Zero-axiom verification

Direct applications of the family determinism (`ReducibleTypeAtBounded.deterministic`) against the
`dataFlat`-derived candidate, plus the generic `dataTaitCandidate.closedReducesToValue`; the per-code value
predicates compute by `rfl` through the `flatCodeValuePredicate` dispatch.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Non-vacuity: a flat-code-rooted type cell IS bounded-reducible-as-type at every bound**, with the
pinned flat Tait candidate, via the dedicated `dataFlat` arm. -/
theorem flatCode_isReducibleTypeAtBounded {scope : Nat} (env : Nat → Nat) (bound : Nat)
    {typeCode : RawTerm scope} (flatPinned : typeCode.rootGenerator.isFlatDataCode = true) :
    IsReducibleTypeAtBounded env bound typeCode :=
  ⟨dataTaitCandidate (flatCodeValuePredicate typeCode.rootGenerator),
    ReducibleTypeStepBounded.dataFlat flatPinned⟩

/-- **The flat candidate bridge: a flat-code-rooted cell's reducibility candidate IS the pinned flat Tait
candidate** (up to pointwise iff) — family determinism against the `dataFlat`-derived candidate, the flat
twin of `emptyTypeCell_candidate_isEmptyCandidate`. -/
theorem flatCode_candidate_isFlatTaitCandidate {scope : Nat} (env : Nat → Nat) (bound : Nat)
    {typeCode : RawTerm scope} (flatPinned : typeCode.rootGenerator.isFlatDataCode = true)
    {candidate : RawTerm scope → Prop}
    (reducible : ReducibleTypeAtBounded env bound typeCode candidate) :
    PointwiseIff candidate (dataTaitCandidate (flatCodeValuePredicate typeCode.rootGenerator)) :=
  ReducibleTypeAtBounded.deterministic reducible (ReducibleTypeStepBounded.dataFlat flatPinned)

/-- **The member form of the flat candidate bridge** — a bounded-reducible member of a flat-code-rooted
type is a member of the pinned flat Tait candidate (the flat twin of `emptyTypeCell_memberIsEmptyCandidate`,
the identity the canonicity extraction consumes). -/
theorem flatCode_memberIsFlatTaitCandidate {scope : Nat} (env : Nat → Nat) (bound : Nat)
    {typeCode : RawTerm scope} (flatPinned : typeCode.rootGenerator.isFlatDataCode = true)
    {term : RawTerm scope}
    (member : IsReducibleMemberAtBounded env bound typeCode term) :
    dataTaitCandidate (flatCodeValuePredicate typeCode.rootGenerator) term := by
  obtain ⟨candidate, candidateReducible, memberInCandidate⟩ := member
  exact (flatCode_candidate_isFlatTaitCandidate env bound flatPinned candidateReducible term).mp
    memberInCandidate

/-- **★ Closed PRODUCT canonicity (model level): a closed bounded-reducible member of a product type cell
reduces to a PAIR value.**  The candidate bridge pins the candidate to `dataTaitCandidate isPairValue`
(the dispatch row for `gen_productCode` computes by `rfl`), and the generic closed-member extraction rules
out the neutral disjunct (`IsNeutral.noClosed`). -/
theorem closedProductMemberReducesToPair (env : Nat → Nat) (bound : Nat)
    {firstType secondType : RawTerm 0} {term : RawTerm 0}
    (member : IsReducibleMemberAtBounded env bound (productTypeCell firstType secondType) term) :
    ∃ value : RawTerm 0, StepStar term value ∧ isPairValue value ∧
      RawTerm.isStepNormalForm value := by
  have memberFlat := flatCode_memberIsFlatTaitCandidate env bound
    (show (productTypeCell firstType secondType).rootGenerator.isFlatDataCode = true from rfl) member
  have dispatchComputes :
      flatCodeValuePredicate (scope := 0)
          ((productTypeCell firstType secondType).rootGenerator)
        = isPairValue := rfl
  rw [dispatchComputes] at memberFlat
  exact dataTaitCandidate.closedReducesToValue memberFlat

/-- **★ Closed EITHER canonicity (model level): a closed bounded-reducible member of an either type cell
reduces to an `inl`/`inr` value.**  Twin of the product extraction at the coproduct row. -/
theorem closedEitherMemberReducesToInjection (env : Nat → Nat) (bound : Nat)
    {leftType rightType : RawTerm 0} {term : RawTerm 0}
    (member : IsReducibleMemberAtBounded env bound (eitherTypeCell leftType rightType) term) :
    ∃ value : RawTerm 0, StepStar term value ∧ isEitherValue value ∧
      RawTerm.isStepNormalForm value := by
  have memberFlat := flatCode_memberIsFlatTaitCandidate env bound
    (show (eitherTypeCell leftType rightType).rootGenerator.isFlatDataCode = true from rfl) member
  have dispatchComputes :
      flatCodeValuePredicate (scope := 0) ((eitherTypeCell leftType rightType).rootGenerator)
        = isEitherValue := rfl
  rw [dispatchComputes] at memberFlat
  exact dataTaitCandidate.closedReducesToValue memberFlat

/-- A sum type cell (binary, both children explicit). -/
abbrev sumTypeCell {scope : Nat} (leftType rightType : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_sumCode () (.childCons leftType (.childCons rightType .childNil))

/-- **The SUM lane is empty-type-like: no closed bounded-reducible member.**  HONEST status: the Generator
table has no sum-injection intro generators, so `flatCodeValuePredicate gen_sumCode` is the EMPTY value
predicate — a closed candidate member would reduce to a value satisfying `False`.  If sum intro forms ever
land, the dispatch row must change WITH them and this refutation becomes the corresponding canonicity. -/
theorem closedSumMemberRefuted (env : Nat → Nat) (bound : Nat)
    {leftType rightType : RawTerm 0} {term : RawTerm 0}
    (member : IsReducibleMemberAtBounded env bound (sumTypeCell leftType rightType) term) :
    False := by
  have memberFlat := flatCode_memberIsFlatTaitCandidate env bound
    (show (sumTypeCell leftType rightType).rootGenerator.isFlatDataCode = true from rfl) member
  have dispatchComputes :
      flatCodeValuePredicate (scope := 0) ((sumTypeCell leftType rightType).rootGenerator)
        = fun _ => False := rfl
  rw [dispatchComputes] at memberFlat
  obtain ⟨_value, _chain, valueSatisfiesEmpty, _valueNormal⟩ :=
    dataTaitCandidate.closedReducesToValue memberFlat
  exact valueSatisfiesEmpty

end FX1Poly.Typed
