import FX1Poly.Tier0.AxisObligation
import FX1Poly.Typed.SconingIsEnoughThesis
import FX1Poly.Typed.ClosedBoolCanonicity
import FX1Poly.Typed.HasTypeDescPiSubjectReductionUnconditional
import FX1Poly.Core.RawConfluence
import FX1Poly.Typed.HasTypeDescDecidable

/-! # FX1Poly/Typed/TypeAxisObligation
    — ★ the FX type-axis AxisObligation: all eight capabilities flipped, each flip BACKED (SN-103, #606)

The Tier-0 `AxisObligation` interface records, per axis, a `MetatheoreticCapabilities` ledger the
profile-extension calculus meets against.  This file builds the FX TYPE-AXIS obligation — the first
concrete `AxisObligation` instance with non-bottom capabilities — and discharges the honesty
constraint: every `.available` field is conjoined with the SHIPPED THEOREM that backs it, so the
ledger is not a slogan but a machine-checked index into the proven metatheory.

  * `fxTypeAxisCapabilities` — ALL EIGHT fields `.available` (= `MetatheoreticCapabilities.top`,
    pinned by `rfl`): canonicity, normalization, parametricity, subject reduction, confluence,
    strong normalization, decidable conversion, decidable typechecking.
  * `fxTypeAxisObligation` — the obligation record: axis id `.universe` (the dependent type axis:
    universe tower + Π/Σ + the data formers over the grown/formation engines), no Fire-Triangle
    restriction (the pure type axis restricts no leg; the effect/eval-axis restriction is SN-104's,
    a separate axis), zero estimated REMAINING lines (the axis is discharged), precedents citing
    Tait / Girard / Atkey / Wood-Atkey / Uemura / Bocquet-Kaposi-Sattler.
  * ★ the eight `fxTypeAxis_*_isBacked` theorems — **the backed flips**: each one conjoins the
    ledger field's `.available` value (`rfl`) with the named shipped metatheorem, restated and
    proved by direct application.  The honesty constraint of SN-103: NOT a bare flip.
      - canonicity      ← `closedBoolCanonicalForms` (closed 3-engine bool canonicity)
      - normalization   ← `HasTypeDescPi.normalizationTransfer` (SN-094, wf-open)
      - parametricity   ← `HasTypeDescPi.closedBoundedReducibleMember` (BFT-13, discharged unary)
      - subject reduction ← `HasTypeDescPi.subjectReduction` (SR-U4, unconditional master)
      - confluence      ← `StepStar.rawConfluence` (the unconditional Takahashi raw confluence)
      - strong normalization ← `HasTypeDescPi.stronglyNormalizingOfWfContextDesc` (OB-5 open SN)
      - decidable conversion ← `Conv.decidableOfHasTypeDesc` (typed-classifier Conv decider)
      - decidable typechecking ← `HasTypeDesc.decidableOfWellFormed` (the P11 engine decider)
  * `fxTypeAxis_meetPreservesCapabilities` — the SN-108 hook: meeting ANY capability ledger against
    the type axis is the identity (the type axis never degrades an extension's capabilities) —
    the algebraic face of "the base theory's metatheory is fully discharged".

## Honest scope boundary

The decidability fields are backed on their proven fragments — decidable conversion for the
CLASSIFIERS of `HasTypeDesc`-typed subjects (each classifier SN by native validity, decided by
normalize-and-compare), decidable typechecking over well-formed contexts; both stated as `Nonempty
(Decidable …)` because deciders are data.  Subject reduction is backed over `WfContextDescPi`, the
grown wf predicate; SN/normalization over `WfContextDesc`, the formation wf predicate — the two wf
hypotheses are quoted exactly as the shipped theorems carry them.  `CapabilityStatus` remains (per
its own docstring) a computable BOUND for extension bookkeeping; the backing theorems here are what
make the bound truthful for this axis.

## Zero-axiom verification

A capabilities literal, an obligation record, eight conjunction theorems each closed by `rfl` and a
direct application of a shipped result, and one meet-identity lemma by enum case analysis.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/AuditTypedSubstVecCwR.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Tier0
open StepStar

/-- **The FX type-axis capability ledger**: all eight metatheoretic capabilities available — the
top of the capability lattice, each field backed by the corresponding theorem below. -/
def fxTypeAxisCapabilities : MetatheoreticCapabilities :=
  MetatheoreticCapabilities.top

/-- The type-axis ledger is the TOP of the capability lattice (every field `.available`). -/
theorem fxTypeAxisCapabilities_eq_top :
    fxTypeAxisCapabilities = MetatheoreticCapabilities.top := rfl

/-- ★ **The FX type-axis obligation** — the first concrete `AxisObligation` with non-bottom
capabilities: the dependent type axis (universe tower + Π/Σ + data formers over the grown and
formation engines), fully discharged, with the classical precedents on record. -/
def fxTypeAxisObligation : AxisObligation where
  axisName := "FX dependent type axis (universe tower + Pi/Sigma + data formers, grown engine)"
  axisId := .universe
  fireTriangleRestriction := none
  capabilities := fxTypeAxisCapabilities
  estimatedLinesOfCode := 0
  precedents :=
    [⟨"W. W. Tait", "Intensional interpretations of functionals of finite type I", none, 1967⟩,
     ⟨"J.-Y. Girard", "Interpretation fonctionnelle et elimination des coupures de l'arithmetique d'ordre superieur", none, 1972⟩,
     ⟨"R. Atkey", "Syntax and Semantics of Quantitative Type Theory", none, 2018⟩,
     ⟨"J. Wood, R. Atkey", "A Framework for Substructural Type Systems", none, 2022⟩,
     ⟨"T. Uemura", "A General Framework for the Semantics of Type Theory", some "1904.04097", 2019⟩,
     ⟨"R. Bocquet, A. Kaposi, C. Sattler", "For the Metatheory of Type Theory, Internal Sconing Is Enough", some "2302.05190", 2023⟩]

/-- **Backed flip (canonicity)**: the ledger field is `.available` AND closed bool canonicity holds
— every closed term typed at the bool code by any of the three engines reduces to `true` or
`false` (`closedBoolCanonicalForms`). -/
theorem fxTypeAxis_canonicity_isBacked :
    fxTypeAxisObligation.capabilities.canonicityStatus = .available
      ∧ (∀ {profile : PolyProfile} {subject : RawTerm 0},
          (HasTypeDescDataIntro profile (TypingContext.empty : TypingContext profile 0)
              subject boolTypeCell
            ∨ HasTypeDescBaseType profile (TypingContext.empty : TypingContext profile 0)
                subject boolTypeCell
            ∨ HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0)
                subject boolTypeCell) →
          ∃ value : RawTerm 0, StepStar subject value
            ∧ (value = boolTrueCell ∨ value = boolFalseCell)) :=
  ⟨rfl, fun typed => closedBoolCanonicalForms typed⟩

/-- **Backed flip (normalization)**: the ledger field is `.available` AND every well-typed term
over a well-formed context reduces to a normal form (`HasTypeDescPi.normalizationTransfer`,
SN-094). -/
theorem fxTypeAxis_normalization_isBacked :
    fxTypeAxisObligation.capabilities.normalizationStatus = .available
      ∧ (∀ {profile : PolyProfile} {scope : Nat}
          {context : TypingContext profile scope} {subject classifier : RawTerm scope},
          WfContextDesc context →
          HasTypeDescPi profile context subject classifier →
          ∃ normalForm : RawTerm scope,
            StepStar subject normalForm ∧ RawTerm.isStepNormalForm normalForm) :=
  ⟨rfl, fun contextWellFormed typed => typed.normalizationTransfer contextWellFormed⟩

/-- **Backed flip (parametricity)**: the ledger field is `.available` AND every closed well-typed
term is a bounded-reducible member of its classifier's relational interpretation
(`HasTypeDescPi.closedBoundedReducibleMember`, BFT-13 — the discharged unary parametricity). -/
theorem fxTypeAxis_parametricity_isBacked :
    fxTypeAxisObligation.capabilities.parametricityStatus = .available
      ∧ (∀ {profile : PolyProfile} (env : Nat → Nat) {subject classifier : RawTerm 0},
          HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0)
            subject classifier →
          ∃ bound : Nat,
            IsReducibleMemberAtBounded env bound
              (RawTerm.subst (Fin.elim0 : RawTermSubst 0 1) classifier)
              (RawTerm.subst (Fin.elim0 : RawTermSubst 0 1) subject)) :=
  ⟨rfl, fun {profile} env {subject} {classifier} typed =>
    HasTypeDescPi.closedBoundedReducibleMember (profile := profile)
      (subject := subject) (classifier := classifier) env typed⟩

/-- **Backed flip (subject reduction)**: the ledger field is `.available` AND the unconditional
master subject reduction holds over well-formed grown contexts (`HasTypeDescPi.subjectReduction`,
SR-U4). -/
theorem fxTypeAxis_subjectReduction_isBacked :
    fxTypeAxisObligation.capabilities.subjectReductionStatus = .available
      ∧ (∀ {profile : PolyProfile} {scope : Nat}
          {context : TypingContext profile scope} {subject classifier : RawTerm scope},
          HasTypeDescPi profile context subject classifier →
          WfContextDescPi context →
          ∀ reduct : RawTerm scope, Step subject reduct →
            HasTypeDescPi profile context reduct classifier) :=
  ⟨rfl, fun typed wellFormed => typed.subjectReduction wellFormed⟩

/-- **Backed flip (confluence)**: the ledger field is `.available` AND raw reduction is globally
confluent, unconditionally (`StepStar.rawConfluence` — the Takahashi complete-development
diamond). -/
theorem fxTypeAxis_confluence_isBacked :
    fxTypeAxisObligation.capabilities.confluenceStatus = .available
      ∧ StepStar.HasConfluence :=
  ⟨rfl, StepStar.rawConfluence⟩

/-- **Backed flip (strong normalization)**: the ledger field is `.available` AND every well-typed
term over a well-formed context is strongly normalizing
(`HasTypeDescPi.stronglyNormalizingOfWfContextDesc`, the OB-5 open SN-043). -/
theorem fxTypeAxis_strongNormalization_isBacked :
    fxTypeAxisObligation.capabilities.strongNormalizationStatus = .available
      ∧ (∀ {profile : PolyProfile} {scope : Nat}
          {context : TypingContext profile scope} {subject classifier : RawTerm scope},
          WfContextDesc context →
          HasTypeDescPi profile context subject classifier →
          IsStronglyNormalizing subject) :=
  ⟨rfl, fun contextWellFormed typed =>
    typed.stronglyNormalizingOfWfContextDesc contextWellFormed⟩

/-- **Backed flip (decidable conversion)**: the ledger field is `.available` AND convertibility of
the CLASSIFIERS of typed subjects is decidable (`Conv.decidableOfHasTypeDesc` — each classifier SN
by native validity, decided by normalize-and-compare).  Stated through `Nonempty` because a decider
is data. -/
theorem fxTypeAxis_decidableConversion_isBacked :
    fxTypeAxisObligation.capabilities.decidableConversionStatus = .available
      ∧ (∀ {profile : PolyProfile} {scope : Nat}
          {context : TypingContext profile scope}
          {firstSubject firstClassifier secondSubject secondClassifier : RawTerm scope},
          WfContextDesc context →
          HasTypeDesc profile context firstSubject firstClassifier →
          HasTypeDesc profile context secondSubject secondClassifier →
          Nonempty (Decidable (Conv firstClassifier secondClassifier))) :=
  ⟨rfl, fun wellFormed firstTyped secondTyped =>
    ⟨Conv.decidableOfHasTypeDesc wellFormed firstTyped secondTyped⟩⟩

/-- **Backed flip (decidable typechecking)**: the ledger field is `.available` AND the description
engine's typing judgment is decidable over well-formed contexts
(`HasTypeDesc.decidableOfWellFormed`, the P11 deliverable).  Stated through `Nonempty` because a
decider is data. -/
theorem fxTypeAxis_decidableTypechecking_isBacked :
    fxTypeAxisObligation.capabilities.decidableTypecheckingStatus = .available
      ∧ (∀ {profile : PolyProfile} {scope : Nat}
          {context : TypingContext profile scope},
          WfContextDesc context →
          ∀ subject classifier : RawTerm scope,
            Nonempty (Decidable (HasTypeDesc profile context subject classifier))) :=
  ⟨rfl, fun wellFormed subject classifier =>
    ⟨HasTypeDesc.decidableOfWellFormed wellFormed subject classifier⟩⟩

/-- Meeting a capability status against `.available` is the identity — the per-field half of the
SN-108 hook. -/
theorem CapabilityStatus.meet_available_right (status : CapabilityStatus) :
    status.meet .available = status := by
  cases status <;> rfl

/-- **The SN-108 hook**: meeting ANY capability ledger against the type axis is the identity — the
fully-discharged type axis never degrades an extension's capabilities.  This is the algebraic form
the extension calculus (`extendProfile_preserves_admissible`) consumes. -/
theorem fxTypeAxis_meetPreservesCapabilities (cap : MetatheoreticCapabilities) :
    cap.meet fxTypeAxisObligation.capabilities = cap := by
  cases cap
  dsimp only [MetatheoreticCapabilities.meet, fxTypeAxisObligation, fxTypeAxisCapabilities,
    MetatheoreticCapabilities.top]
  congr 1 <;> apply CapabilityStatus.meet_available_right

end FX1Poly.Typed
