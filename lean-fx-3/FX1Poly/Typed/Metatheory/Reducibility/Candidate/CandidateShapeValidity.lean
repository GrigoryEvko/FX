import FX1Poly.Typed.Metatheory.Reducibility.Candidate.CandidateDenotation
import FX1Poly.Core.Metatheory.Reducibility.Candidates.DataTaitCandidate
import FX1Poly.Core.Metatheory.Reducibility.Candidates.EmptyTaitCandidate

/-! # FX1Poly/Typed/Metatheory/Reducibility/Candidate/CandidateShapeValidity
    — per-shape `CandidateValidity` (FTGEN-2): every data-like shape is valid UNCONDITIONALLY

FTGEN-1 shipped the descriptor + the interface (`CandidateValidity = IsReducibilityCandidate`) + the
`neutralSaturated` base and the `derivedUnfold` inheritance.  This file discharges `CandidateValidity` for the
DATA-LIKE descriptor shapes by reusing the kernel's weak Tait candidate `dataTaitCandidate`, whose Girard CR
validity (`dataTaitCandidate_isReducibilityCandidate`) holds for ANY value predicate with NO hypotheses.

Crucially this is consistent with the kernel: the shipped `ReducibleTypeStepBounded.dataFlat` arm IS
`dataTaitCandidate (flatCodeValuePredicate …)` — the weak "reduces to a value-or-neutral" set, NOT the
component-tracking strong set.  Component tracking is the eliminator-reducibility layer (FTGEN-11), not the
candidate definition.  So every data former's candidate validity is unconditional here, and the in-arc
frontier formers `gelCode` (relationalSaturated) and `sprop` (strictPropIrrelevant) are covered too.

## Shape coverage after this file

  * `neutralSaturated`  — VALID (FTGEN-1, the SN base).
  * `derivedUnfold`     — VALID (FTGEN-1, the equiv⇒Σ inheritance).
  * `inductiveSaturated`— VALID here (`dataTaitCandidate` over "head ∈ the constructor specs").
  * `emptyData`         — VALID here (`emptyTaitCandidate`; the empty constructor list degenerates to this).
  * `dependentSum`      — VALID here (Tait set over `gen_pair`; weak Σ candidate, kernel-consistent).
  * `identitySaturated` — VALID here (Tait set over `gen_refl`).
  * `relationalSaturated` — VALID here (Tait set over `gen_gel`) — the gelCode in-arc frontier (FTGEN-GEL).
  * `strictPropIrrelevant` — VALID here (the SN candidate; proof-irrelevance is the conv layer, EXT-6) —
    the sprop in-arc frontier.
  * `dependentProduct`  — VALID in Core: `isDependentArrowReducible_isReducibilityCandidate` (the conditional
    function-space candidate; exposed via the FT formation arm FTGEN-4, not re-stated here).
  * `universeCandidate` — VALID in Core (the universe-interface candidate; FTGEN-4).
  * `coinductiveSaturated` / `quotientByRelation` / `propTruncated` / `modalCandidate` — reserved frontier; no
    live former yet (FTGEN-2 when their formers enter the bundle).

## Zero-axiom verification

Each validity is the unconditional `dataTaitCandidate_isReducibilityCandidate` / `emptyTaitCandidate_is
ReducibilityCandidate` / the SN base, at a concrete value predicate.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core
open StepStar

/-- The value predicate of an `inductiveSaturated` shape: a term is a value when its head is one of the
shape's listed constructors.  Drives the Tait candidate directly from the descriptor's constructor specs. -/
def constructorHeadValue {scope : Nat} (constructors : List CandidateConstructorSpec)
    (term : RawTerm scope) : Prop :=
  ∃ spec : CandidateConstructorSpec, spec ∈ constructors ∧ spec.constructorGenerator = term.rootGenerator

/-- The `inductiveSaturated` shape's candidate: the weak Tait saturated set over its constructor heads. -/
def inductiveSaturatedCandidate {scope : Nat} (constructors : List CandidateConstructorSpec) :
    RawTerm scope → Prop :=
  dataTaitCandidate (constructorHeadValue constructors)

/-- **★ `inductiveSaturated` is a valid candidate — unconditionally.**  The generic data Tait candidate is a
Girard CR for any value predicate, so every inductive former (bool/nat/list/option/either/sum/product/unit/…)
gets validity with no premises. -/
theorem inductiveSaturatedCandidate_valid {scope : Nat} (constructors : List CandidateConstructorSpec) :
    CandidateValidity (inductiveSaturatedCandidate (scope := scope) constructors) :=
  dataTaitCandidate_isReducibilityCandidate

/-- A single-headed data candidate: the Tait set over terms whose head is exactly `head`.  The shape for the
unary data-like formers (identity refl, relational gel, dependent-sum pair). -/
def singleHeadCandidate {scope : Nat} (head : Generator) : RawTerm scope → Prop :=
  dataTaitCandidate (fun term => term.rootGenerator = head)

/-- **★ A single-headed data candidate is valid — unconditionally.** -/
theorem singleHeadCandidate_valid {scope : Nat} (head : Generator) :
    CandidateValidity (singleHeadCandidate (scope := scope) head) :=
  dataTaitCandidate_isReducibilityCandidate

/-- The `dependentSum` shape's candidate (weak): the Tait set over `gen_pair`.  Component tracking is the
eliminator layer (FTGEN-11), not the candidate. -/
def dependentSumCandidate (scope : Nat) : RawTerm scope → Prop :=
  singleHeadCandidate .gen_pair

/-- **★ `dependentSum` is a valid candidate.** -/
theorem dependentSumCandidate_valid {scope : Nat} :
    CandidateValidity (dependentSumCandidate scope) :=
  singleHeadCandidate_valid _

/-- The `identitySaturated` shape's candidate: the Tait set over `gen_refl`. -/
def identitySaturatedCandidate (scope : Nat) : RawTerm scope → Prop :=
  singleHeadCandidate .gen_refl

/-- **★ `identitySaturated` (Id / Bridge) is a valid candidate.** -/
theorem identitySaturatedCandidate_valid {scope : Nat} :
    CandidateValidity (identitySaturatedCandidate scope) :=
  singleHeadCandidate_valid _

/-- The `relationalSaturated` shape's candidate: the Tait set over `gen_gel` — the gelCode in-arc frontier
former (FTGEN-GEL). -/
def relationalSaturatedCandidate (scope : Nat) : RawTerm scope → Prop :=
  singleHeadCandidate .gen_gel

/-- **★ `relationalSaturated` (gel / transpension) is a valid candidate** — the gelCode frontier former's
candidate, valid unconditionally. -/
theorem relationalSaturatedCandidate_valid {scope : Nat} :
    CandidateValidity (relationalSaturatedCandidate scope) :=
  singleHeadCandidate_valid _

/-- The `emptyData` shape's candidate: the kernel empty Tait candidate. -/
def emptyDataCandidate (scope : Nat) : RawTerm scope → Prop :=
  emptyTaitCandidate

/-- **★ `emptyData` is a valid candidate.** -/
theorem emptyDataCandidate_valid {scope : Nat} :
    CandidateValidity (emptyDataCandidate scope) :=
  emptyTaitCandidate_isReducibilityCandidate

/-- The `strictPropIrrelevant` shape's candidate (sprop in-arc frontier): the SN candidate.  A strict prop's
reducibility content is just strong normalization — proof irrelevance (any two members convertible) is the
conversion-layer obligation discharged in EXT-6, not the candidate. -/
def strictPropIrrelevantCandidate (scope : Nat) : RawTerm scope → Prop :=
  IsStronglyNormalizing

/-- **★ `strictPropIrrelevant` (sprop) is a valid candidate** — the SN base. -/
theorem strictPropIrrelevantCandidate_valid {scope : Nat} :
    CandidateValidity (strictPropIrrelevantCandidate scope) :=
  isStronglyNormalizing_isReducibilityCandidate

end FX1Poly.Typed
