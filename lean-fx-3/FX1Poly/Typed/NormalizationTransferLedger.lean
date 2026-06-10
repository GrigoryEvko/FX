import FX1Poly.Tier0.FxBaseSubstCanonicityExtraction
import FX1Poly.Core.NormalizeMeta
import FX1Poly.Typed.GluedModelTypeFormers
import FX1Poly.Typed.OpenStronglyNormalizingUnconditional

/-! # FX1Poly/Typed/NormalizationTransferLedger
    — the NormalizationExtraction laws carry no content; the honest reduction-sound form + the typed transfer (SN-094, #597)

The companion to SN-093's canonicity verdict, for normalization.  `InternalSconing.lean`'s
`NormalizationExtraction` record carries `NormalForm`/`normalize`/`embed` with ONE law,
`normalizeIdempotent : normalize (embed nf) = nf`.  Unlike `CanonicityExtraction` (refuted), this
record IS inhabitable — but its law constrains `normalize` only on the embedded image, never tying
it to REDUCTION.  This file makes that diagnosis a theorem and ships the honest form:

  * `punitNormalizationExtraction` — a FULLY LAWFUL instance whose normal-form family is the
    SINGLETON `PUnit` at every object: `normalize` identifies ALL sections
    (`punitNormalizationExtraction_identifiesEverything`, `rfl`).  A record satisfied by the
    everything-collapsing normalizer carries no normalization content.
  * `identityNormalizationExtraction` — the other extreme (NormalForm := the sections themselves,
    normalize = embed = `id`): also fully lawful.  The record does not determine the normal forms
    even up to size — singleton and full-sections families both satisfy it.
  * `ReductionSoundNormalization domain` — **the honest record**: the two laws the Tier-0 record is
    missing — `reaches` (the term REDUCES to its normal form, `StepStar`) and `isNormal` (the
    output IS a normal form) — over an explicit domain.
  * ★ `snReductionSoundNormalization` — the GENUINE instance over the SN fragment: `normalFormOf` is
    the shipped `RawTerm.normalize` (its `Acc` parameter IS `IsStronglyNormalizing`,
    definitionally), with `reaches`/`isNormal` the shipped soundness laws and the fixed-point law
    on already-normal inputs.  The domain restriction is essential: the raw calculus has non-SN
    closed terms (`curryOmega_notStronglyNormalizing`), so no reduction-sound normalizer is total
    on the full sections.
  * ★ `HasTypeDescPi.normalizationTransfer` — **the typed transfer theorem** (the ledger's
    namesake): every well-typed term over a well-formed context reduces to a normal form — typed SN
    (SN-043 open form) feeding the genuine normalizer.
  * `GluedTypeCell.normalizationTransfer` — the glued-model form: through any glued type's scone
    (in particular the SN-091 Π/Σ/universe lifts), well-typedness transfers to
    reaches-a-normal-form, completing the canonicity/normalization transfer pair of
    `GluedTypeCell`.

## Honest scope boundary

The full-domain refutation of `ReductionSoundNormalization` (no reduction-sound normalizer on ALL
closed terms) needs "Ω never reaches a normal form" — not-WN, strictly stronger than the shipped
not-SN — and is a recorded follow-on (provable for the classic Ω by `Step` inversion: its only
reduct is itself).  The `fxSconingConstructionLevel` ledger advances to
`.normalizationTransferTheorem` on this package (see `InternalSconing.lean`); parametricity
(SN-095) and the BKS bundle (SN-096) remain.

## Zero-axiom verification

The two diagnosis instances are structure literals with `rfl` laws; the genuine instance and both
transfer theorems are direct applications of the shipped `RawTerm.normalize` laws and the SN-043
open form.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/AuditTypedSubstVecCwR.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Tier0
open StepStar

/-- **The singleton-collapse instance**: a fully lawful `NormalizationExtraction` whose normal-form
family is `PUnit` at every object — `normalize` identifies all sections, `embed` returns the
constant all-unit closing substitution, and the one law closes by `PUnit` eta.  Lawful and
content-free: the record's law does not tie `normalize` to reduction. -/
def punitNormalizationExtraction : NormalizationExtraction fxBaseSubstGlobalSections where
  NormalForm := fun _objectA => PUnit
  normalize := fun _objectA _closedSection => PUnit.unit
  embed := fun _objectA _normalForm =>
    SubstVec.tabulate (fun _position => RawTerm.mkGen .gen_unit () .childNil)
  normalizeIdempotent := fun _objectA _normalForm => rfl

/-- **The identity instance**: normal forms = the sections themselves, normalize = embed = the
identity.  Also fully lawful — together with the singleton instance this shows the record does not
determine the normal-form family even up to size. -/
def identityNormalizationExtraction : NormalizationExtraction fxBaseSubstGlobalSections where
  NormalForm := fun objectA => fxBaseSubstGlobalSections.sections objectA
  normalize := fun _objectA closedSection => closedSection
  embed := fun _objectA normalForm => normalForm
  normalizeIdempotent := fun _objectA _normalForm => rfl

/-- **The diagnosis made a theorem**: the singleton instance's `normalize` identifies EVERY pair of
sections — a lawful inhabitant of the record may collapse everything, so inhabiting
`NormalizationExtraction` certifies no normalization content. -/
theorem punitNormalizationExtraction_identifiesEverything (objectA : Nat)
    (firstSection secondSection : fxBaseSubstGlobalSections.sections objectA) :
    punitNormalizationExtraction.normalize objectA firstSection
      = punitNormalizationExtraction.normalize objectA secondSection := rfl

/-- **The honest reduction-sound normalization record** over an explicit domain: the two laws the
Tier-0 record is missing — the term REDUCES to its assigned normal form, and the assigned form IS
normal. -/
structure ReductionSoundNormalization {scope : Nat} (domain : RawTerm scope → Prop) where
  /-- The normal form assigned to each domain member. -/
  normalFormOf : (term : RawTerm scope) → domain term → RawTerm scope
  /-- SOUNDNESS (reduction): the term reduces to its assigned normal form. -/
  reaches : ∀ (term : RawTerm scope) (isInDomain : domain term),
    StepStar term (normalFormOf term isInDomain)
  /-- SOUNDNESS (normality): the assigned form admits no further step. -/
  isNormal : ∀ (term : RawTerm scope) (isInDomain : domain term),
    RawTerm.isStepNormalForm (normalFormOf term isInDomain)

/-- ★ **The genuine reduction-sound normalization over the SN fragment**: `normalFormOf` is the
shipped `RawTerm.normalize` — its accessibility parameter IS `IsStronglyNormalizing`,
definitionally — with the shipped soundness laws.  The domain restriction is essential
(`curryOmega_notStronglyNormalizing`: the raw calculus has non-SN closed terms). -/
def snReductionSoundNormalization {scope : Nat} :
    ReductionSoundNormalization (IsStronglyNormalizing (scope := scope)) where
  normalFormOf := fun term isInDomain => RawTerm.normalize term isInDomain
  reaches := fun term isInDomain => RawTerm.normalize_reducesTo term isInDomain
  isNormal := fun term isInDomain => RawTerm.normalize_isStepNormalForm term isInDomain

/-- The genuine instance is the identity on already-normal inputs (the fixed-point law the Tier-0
record's `normalizeIdempotent` gestures at, now with reduction content behind it). -/
theorem snReductionSoundNormalization_eq_self_ofNormal {scope : Nat}
    (term : RawTerm scope) (isInDomain : IsStronglyNormalizing term)
    (isAlreadyNormal : RawTerm.isStepNormalForm term) :
    snReductionSoundNormalization.normalFormOf term isInDomain = term :=
  RawTerm.normalize_eq_self_of_isStepNormalForm term isInDomain isAlreadyNormal

/-- ★ **The typed normalization TRANSFER theorem** (the ledger's namesake): every well-typed term
over a well-formed context reduces to a normal form — typed SN (the SN-043 open form) feeding the
genuine reduction-sound normalizer. -/
theorem HasTypeDescPi.normalizationTransfer {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (contextWellFormed : WfContextDesc context)
    (typed : HasTypeDescPi profile context subject classifier) :
    ∃ normalForm : RawTerm scope,
      StepStar subject normalForm ∧ RawTerm.isStepNormalForm normalForm :=
  have isSubjectNormalizing := typed.stronglyNormalizingOfWfContextDesc contextWellFormed
  ⟨RawTerm.normalize subject isSubjectNormalizing,
    RawTerm.normalize_reducesTo subject isSubjectNormalizing,
    RawTerm.normalize_isStepNormalForm subject isSubjectNormalizing⟩

/-- **The glued-model normalization transfer**: through any glued type's scone — in particular the
SN-091 Π/Σ/universe lifts — well-typedness transfers to reaches-a-normal-form, completing the
canonicity/normalization transfer pair of `GluedTypeCell`. -/
theorem GluedTypeCell.normalizationTransfer {scope : Nat} (glued : GluedTypeCell (scope + 1))
    {isWellTyped : RawTerm (scope + 1) → Prop}
    (fundamental : ∀ term : RawTerm (scope + 1), isWellTyped term → glued.computable term)
    (term : RawTerm (scope + 1)) (typed : isWellTyped term) :
    ∃ normalForm : RawTerm (scope + 1),
      StepStar term normalForm ∧ RawTerm.isStepNormalForm normalForm :=
  have isTermNormalizing := glued.canonicityTransfer fundamental term typed
  ⟨RawTerm.normalize term isTermNormalizing,
    RawTerm.normalize_reducesTo term isTermNormalizing,
    RawTerm.normalize_isStepNormalForm term isTermNormalizing⟩

end FX1Poly.Typed
