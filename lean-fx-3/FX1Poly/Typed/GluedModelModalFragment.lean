import FX1Poly.Typed.BksMetatheoryPackage
import FX1Poly.Typed.TypedBySomeEngine
import FX1Poly.Core.ModalCanonicityViaSconing
import FX1Poly.Core.StrongNormalizationConstructors
import FX1Poly.Core.StrongNormalizationModalEliminators

/-! # FX1Poly/Typed/GluedModelModalFragment
    — ★ the sconing witness extends to the MODAL fragment: the first joint pair beyond MLTT (ONORM-M1, #1211)

The O-NORM increment: SN-091/SN-096 closed the glued model over the MLTT formers (Π/Σ/universe) and
bundled the three transfer theorems behind ONE package with ONE fundamental-hypothesis shape.  This
file extends that SAME functor to the modal fragment — the first theorem of the form "MLTT and
another feature under ONE gluing", the shape every future profile extension repeats:

  * `ModalityFormer` — the six one-child modality TYPE formers of the generator table (the cohesive
    trio shape/flat/sharp, the linear exponentials bang/whyNot, and the provability box), enumerated
    the way `DataFormerFamily` enumerates the data formers.  Adding a former without a lift fails to
    compile — the enumeration is the coverage gate.
  * ★ `GluedTypeCell.modalityLift` — **the modal type-former lifts to the glued model**, through the
    model's `neutral` arm exactly as SN-091's `sigmaLift`: a modality cell is weak-head normal (no β
    head, no root ι, no eliminator scrutinee — `ModalityFormer.formerCell_noWeakHeadStep`) and not
    Π-rooted, so the model assigns it the strong-normalization scone.  ONE definition covers all six
    formers.
  * ★ `jointPair_mlttAndModal_underOnePackage` — **the joint-pair headline**: the SN-096 package
    instance `fxBksGluedMetatheoryPackage` — built with zero modal knowledge — discharges canonicity
    for an MLTT lift AND the modal lift in one conjunction.  The three per-transfer corollaries
    (`modalityLift_canonicityTransfer` / `_normalizationTransfer` / `_parametricityTransfer`) are
    each a one-line application of the same package.
  * `modalBoxValueScone` — **the #721 categorical twin at the VALUE level**: the `SconingWitness`
    whose computability predicate is the shipped modal Tait candidate
    (`CanonicalFormsPredicate isModIntroValue`) and whose canonical phase is
    reaches-a-`modIntro`-value — strictly finer than the SN scone.
  * ★ `modalSconeConfinement` — **the semantic O-FIRE confinement**: every closed well-typed term of
    box type lands under a `modIntro` ROOT (with normal payload).  This is the semantic content of
    the legacy O-FIRE gate (M44-T1), recovered at the candidate layer: the box interior never
    escapes — anything classified by the box reduces into the box constructor.
  * `modalCandidate_refinesModalityLiftScone` — the COHERENCE of the two halves: the value candidate
    refines the type-level lift's SN scone (CR1), so the modal box carries a two-level scone
    (SN outer, canonical-forms inner) over the same glued object.
  * `modIntro_preservesModalityLiftScone` / `modElim_preservesModalityLiftScone` /
    `subsume_preservesModalityLiftScone` — the modal OPERATIONS preserve the lift's scone (the
    shipped one-child congruence SN closures, #721/#722, re-read as scone closure).

## Honest scope boundary (the live-signature index)

The modal fragment is STATICALLY UNTYPED today: `hasSomeTypingRule` is `false` for
`gen_modIntro`/`gen_modElim`/`gen_subsume` AND for all six modality type formers
(`modalTermFragment_isStaticallyUntypedToday` / `modalityFormers_haveNoFormationRowToday`, both by
`rfl` — the legacy modal typing rules of M44-T1 died with the engine deletion HT-C, and no rule-table
row has replaced them).  The joint pair therefore lives at the SEMANTIC layer: the fundamental
obligations are explicit hypotheses (exactly as for the data scones), not discharged by a typing
engine.  Wiring a modal formation/intro/elim row into the rule tables is the recorded follow-on that
would discharge them.  The modal ELIMINATOR carries no β/ι rule (`modIntro (modElim m) ↝ m` is raw
η), so eliminator PROGRESS does not transfer — only SN-closure does.

## Zero-axiom verification

A 6-ctor enum with full-enumeration dispatches (no wildcard — propext-clean recursor), the lift via
one `ReducibleType.neutral` constructor per former (weak-head-normality by the `cases … with |
rootIota` script, non-Π-rootedness by `nomatch`), package applications, and `rfl` honesty pins.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/AuditTypedSubstVecCwR.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Tier0
open StepStar

/-- **The one-child modality TYPE formers of the generator table**: the cohesive trio
(shape `∫`, flat `♭`, sharp `♯`), the linear-logic exponentials (`!`, `?`), and the provability box.
Each takes exactly one carrier child at shift 0 with `Unit` payload.  Enumerated the way
`DataFormerFamily` enumerates the data formers — the coverage gate for the modal glued lifts. -/
inductive ModalityFormer where
  | shapeModality
  | flatModality
  | sharpModality
  | bangModality
  | whyNotModality
  | provabilityModality

/-- The generator each modality former names. -/
def ModalityFormer.generator : ModalityFormer → Generator
  | .shapeModality => .gen_shapeModality
  | .flatModality => .gen_flatModality
  | .sharpModality => .gen_sharpModality
  | .bangModality => .gen_bangModality
  | .whyNotModality => .gen_whyNotModality
  | .provabilityModality => .gen_provabilityModality

/-- The modality TYPE cell over a carrier code — `□(carrier)` at the former's generator.  Each arm
is the concrete one-child `mkGen` cell (full enumeration, so every consumer reduces definitionally
per former). -/
def ModalityFormer.formerCell {scope : Nat} :
    ModalityFormer → RawTerm scope → RawTerm scope
  | .shapeModality, carrierCode =>
      .mkGen .gen_shapeModality () (.childCons carrierCode .childNil)
  | .flatModality, carrierCode =>
      .mkGen .gen_flatModality () (.childCons carrierCode .childNil)
  | .sharpModality, carrierCode =>
      .mkGen .gen_sharpModality () (.childCons carrierCode .childNil)
  | .bangModality, carrierCode =>
      .mkGen .gen_bangModality () (.childCons carrierCode .childNil)
  | .whyNotModality, carrierCode =>
      .mkGen .gen_whyNotModality () (.childCons carrierCode .childNil)
  | .provabilityModality, carrierCode =>
      .mkGen .gen_provabilityModality () (.childCons carrierCode .childNil)

/-- **Every modality former cell is weak-head normal**: no β head step (not `gen_app`-rooted), no
root ι (no iota rule fires at a modality root), no eliminator scrutinee congruence (not
eliminator-rooted).  Per former the `cases` unification dismisses every `WeakHeadStep` arm except
`rootIota`, whose `IotaHeadStep` premise has no constructor at a modality root. -/
theorem ModalityFormer.formerCell_noWeakHeadStep {scope : Nat} :
    (former : ModalityFormer) → (carrierCode : RawTerm scope) →
      ∀ reduct : RawTerm scope,
        ¬ WeakHeadStep (former.formerCell carrierCode) reduct
  | .shapeModality, _carrierCode, _reduct, weakHeadStep => by
      cases weakHeadStep with | rootIota iotaStep => cases iotaStep
  | .flatModality, _carrierCode, _reduct, weakHeadStep => by
      cases weakHeadStep with | rootIota iotaStep => cases iotaStep
  | .sharpModality, _carrierCode, _reduct, weakHeadStep => by
      cases weakHeadStep with | rootIota iotaStep => cases iotaStep
  | .bangModality, _carrierCode, _reduct, weakHeadStep => by
      cases weakHeadStep with | rootIota iotaStep => cases iotaStep
  | .whyNotModality, _carrierCode, _reduct, weakHeadStep => by
      cases weakHeadStep with | rootIota iotaStep => cases iotaStep
  | .provabilityModality, _carrierCode, _reduct, weakHeadStep => by
      cases weakHeadStep with | rootIota iotaStep => cases iotaStep

/-- **No modality former is Π-rooted** — the second `neutral`-arm side condition, per former by
constructor disjointness. -/
theorem ModalityFormer.formerCell_notPiRooted {scope : Nat} :
    (former : ModalityFormer) → (carrierCode : RawTerm scope) →
      (former.formerCell carrierCode).rootGenerator ≠ Generator.gen_piTyCode
  | .shapeModality, _carrierCode => fun absurdEq => nomatch absurdEq
  | .flatModality, _carrierCode => fun absurdEq => nomatch absurdEq
  | .sharpModality, _carrierCode => fun absurdEq => nomatch absurdEq
  | .bangModality, _carrierCode => fun absurdEq => nomatch absurdEq
  | .whyNotModality, _carrierCode => fun absurdEq => nomatch absurdEq
  | .provabilityModality, _carrierCode => fun absurdEq => nomatch absurdEq

/-- ★ **The modal type-former lifts to the glued model** — the BKS preservation lemma at the modal
box, through the model's `neutral` arm exactly as SN-091's `sigmaLift`: the modality cell is
weak-head normal and not Π-rooted, so the model assigns it the strong-normalization scone.  ONE
definition covers all six modality formers — the modal half of the first joint pair. -/
def GluedTypeCell.modalityLift {scope : Nat} (former : ModalityFormer)
    (carrierCode : RawTerm scope) : GluedTypeCell scope where
  typeCell := former.formerCell carrierCode
  computable := IsStronglyNormalizing
  isModeled := ReducibleType.neutral
    (former.formerCell_noWeakHeadStep carrierCode)
    (former.formerCell_notPiRooted carrierCode)

/-- **Preservation payoff (modal)**: the lifted modality's scone is again a full Girard reducibility
candidate — the glued model is closed under all six modality formers. -/
theorem GluedTypeCell.modalityLift_isCandidate {scope : Nat} (former : ModalityFormer)
    (carrierCode : RawTerm scope) :
    IsReducibilityCandidate (GluedTypeCell.modalityLift former carrierCode).computable :=
  isStronglyNormalizing_isReducibilityCandidate

/-- **Canonicity transfer for the modal lift, through the SHARED package**: the SN-096 instance
`fxBksGluedMetatheoryPackage` — built with zero modal knowledge — discharges the modal box.  The
joint pair is not a new theorem; it is the OLD package consuming a NEW object. -/
theorem GluedTypeCell.modalityLift_canonicityTransfer {scope : Nat} (former : ModalityFormer)
    (carrierCode : RawTerm (scope + 1))
    {isWellTyped : RawTerm (scope + 1) → Prop}
    (fundamental : ∀ term : RawTerm (scope + 1), isWellTyped term →
      (GluedTypeCell.modalityLift former carrierCode).computable term)
    (term : RawTerm (scope + 1)) (typed : isWellTyped term) :
    IsStronglyNormalizing term :=
  fxBksGluedMetatheoryPackage.canonicityTransfer
    (GluedTypeCell.modalityLift former carrierCode) fundamental term typed

/-- **Normalization transfer for the modal lift** — the same shared package, second field. -/
theorem GluedTypeCell.modalityLift_normalizationTransfer {scope : Nat} (former : ModalityFormer)
    (carrierCode : RawTerm (scope + 1))
    {isWellTyped : RawTerm (scope + 1) → Prop}
    (fundamental : ∀ term : RawTerm (scope + 1), isWellTyped term →
      (GluedTypeCell.modalityLift former carrierCode).computable term)
    (term : RawTerm (scope + 1)) (typed : isWellTyped term) :
    ∃ normalForm : RawTerm (scope + 1),
      StepStar term normalForm ∧ RawTerm.isStepNormalForm normalForm :=
  fxBksGluedMetatheoryPackage.normalizationTransfer
    (GluedTypeCell.modalityLift former carrierCode) fundamental term typed

/-- **Parametricity transfer for the modal lift** — the same shared package, third field. -/
theorem GluedTypeCell.modalityLift_parametricityTransfer {scope : Nat} (former : ModalityFormer)
    (carrierCode : RawTerm (scope + 1))
    {isWellTyped : RawTerm (scope + 1) → Prop}
    (fundamental : ∀ term : RawTerm (scope + 1), isWellTyped term →
      (GluedTypeCell.modalityLift former carrierCode).computable term)
    (term : RawTerm (scope + 1)) (typed : isWellTyped term) :
    (GluedTypeCell.modalityLift former carrierCode).computable term
      ∧ IsStronglyNormalizing term :=
  fxBksGluedMetatheoryPackage.parametricityTransfer
    (GluedTypeCell.modalityLift former carrierCode) fundamental term typed

/-- ★ **The joint-pair headline**: ONE package instance discharges canonicity for an MLTT former
lift (the SN-091 Σ) AND the modal former lift, in one conjunction proved by the same field twice.
"MLTT and the modal layer under ONE functor" — the first genuine O-NORM increment beyond MLTT, and
the shape every future profile extension repeats. -/
theorem jointPair_mlttAndModal_underOnePackage {scope : Nat}
    (domainCode : RawTerm (scope + 1)) (codomainCode : RawTerm (scope + 1 + 1))
    (former : ModalityFormer) (carrierCode : RawTerm (scope + 1))
    {isWellTypedSigma isWellTypedModal : RawTerm (scope + 1) → Prop}
    (sigmaFundamental : ∀ term : RawTerm (scope + 1), isWellTypedSigma term →
      (GluedTypeCell.sigmaLift domainCode codomainCode).computable term)
    (modalFundamental : ∀ term : RawTerm (scope + 1), isWellTypedModal term →
      (GluedTypeCell.modalityLift former carrierCode).computable term) :
    (∀ term : RawTerm (scope + 1), isWellTypedSigma term → IsStronglyNormalizing term)
      ∧ (∀ term : RawTerm (scope + 1), isWellTypedModal term → IsStronglyNormalizing term) :=
  ⟨fun term typed => fxBksGluedMetatheoryPackage.canonicityTransfer
      (GluedTypeCell.sigmaLift domainCode codomainCode) sigmaFundamental term typed,
   fun term typed => fxBksGluedMetatheoryPackage.canonicityTransfer
      (GluedTypeCell.modalityLift former carrierCode) modalFundamental term typed⟩

/-- **The modal VALUE scone** — the #721 categorical twin: the `SconingWitness` whose computability
predicate is the shipped modal Tait candidate (`CanonicalFormsPredicate isModIntroValue`) and whose
canonical phase is reaches-a-`modIntro`-value, strictly finer than the SN scone.  The extraction is
fundamental-free (`closedReducesToValue`); the fundamental is the one genuine obligation, exactly as
for the data-type value scones. -/
def modalBoxValueScone {isWellTyped : RawTerm 0 → Prop}
    (fundamental : ∀ term : RawTerm 0, isWellTyped term →
      CanonicalFormsPredicate isModIntroValue term) :
    SconingWitness isWellTyped
      (fun term => ∃ value : RawTerm 0, StepStar term value ∧ isModIntroValue value) where
  computable := CanonicalFormsPredicate isModIntroValue
  fundamental := fundamental
  extraction := fun _term member => CanonicalFormsPredicate.closedReducesToValue member

/-- ★ **The semantic O-FIRE confinement**: every closed well-typed term of box type lands under a
`modIntro` ROOT with a normal payload — the box interior never escapes.  This is the semantic
content of the legacy O-FIRE gate (M44-T1), recovered at the candidate layer through the value
scone's canonicity. -/
theorem modalSconeConfinement {isWellTyped : RawTerm 0 → Prop}
    (fundamental : ∀ term : RawTerm 0, isWellTyped term →
      CanonicalFormsPredicate isModIntroValue term)
    (term : RawTerm 0) (typed : isWellTyped term) :
    ∃ payload : RawTerm 0,
      StepStar term (modIntroCell payload) ∧ RawTerm.isStepNormalForm payload := by
  obtain ⟨value, reachesValue, valueIsModIntro⟩ :=
    (modalBoxValueScone fundamental).canonicity term typed
  obtain ⟨payload, valueEq, payloadNormal⟩ := valueIsModIntro
  subst valueEq
  exact ⟨payload, reachesValue, payloadNormal⟩

/-- **Coherence of the two modal scones**: the value candidate refines the type-level lift's SN
scone (CR1 of the canonical-forms candidate) — the modal box carries a two-level scone, SN outer and
canonical-forms inner, over the same glued object. -/
theorem modalCandidate_refinesModalityLiftScone {scope : Nat} (former : ModalityFormer)
    (carrierCode : RawTerm scope) {term : RawTerm scope}
    (member : CanonicalFormsPredicate isModIntroValue term) :
    (GluedTypeCell.modalityLift former carrierCode).computable term :=
  member.stronglyNormalizing

/-- **The modal introduction preserves the lift's scone** — `modIntro` of a scone member is a scone
member (the shipped one-child congruence SN closure, #721 re-read as scone closure). -/
theorem modIntro_preservesModalityLiftScone {scope : Nat} (former : ModalityFormer)
    (carrierCode : RawTerm scope) {payload : RawTerm scope}
    (payloadInScone : (GluedTypeCell.modalityLift former carrierCode).computable payload) :
    (GluedTypeCell.modalityLift former carrierCode).computable
      (.mkGen .gen_modIntro () (.childCons payload .childNil)) :=
  modIntro_isStronglyNormalizing_of_value payloadInScone

/-- **The modal elimination preserves the lift's scone** — `modElim` of a scone member is a scone
member (#722; `modElim` has no β/ι root rule, so only its child reduces). -/
theorem modElim_preservesModalityLiftScone {scope : Nat} (former : ModalityFormer)
    (carrierCode : RawTerm scope) {modalTerm : RawTerm scope}
    (modalInScone : (GluedTypeCell.modalityLift former carrierCode).computable modalTerm) :
    (GluedTypeCell.modalityLift former carrierCode).computable
      (.mkGen .gen_modElim () (.childCons modalTerm .childNil)) :=
  modElim_isStronglyNormalizing_of_child modalInScone

/-- **The modality subsumption preserves the lift's scone** — `subsume` of a scone member is a
scone member (#722, the third modal operation). -/
theorem subsume_preservesModalityLiftScone {scope : Nat} (former : ModalityFormer)
    (carrierCode : RawTerm scope) {subsumedTerm : RawTerm scope}
    (subsumedInScone : (GluedTypeCell.modalityLift former carrierCode).computable subsumedTerm) :
    (GluedTypeCell.modalityLift former carrierCode).computable
      (.mkGen .gen_subsume () (.childCons subsumedTerm .childNil)) :=
  subsume_isStronglyNormalizing_of_child subsumedInScone

/-- **HONESTY (the live-signature index, term half)**: the modal TERM fragment is statically untyped
today — no engine carries a rule for `gen_modIntro`/`gen_modElim`/`gen_subsume` (the legacy M44-T1
modal typing died with the engine deletion HT-C).  The joint pair therefore lives at the semantic
layer; its fundamental obligations are explicit hypotheses. -/
theorem modalTermFragment_isStaticallyUntypedToday :
    hasSomeTypingRule .gen_modIntro = false
      ∧ hasSomeTypingRule .gen_modElim = false
      ∧ hasSomeTypingRule .gen_subsume = false :=
  ⟨rfl, rfl, rfl⟩

/-- **HONESTY (the live-signature index, type half)**: no modality TYPE former has a formation row
in any rule table today — the glued lifts classify cells the engines cannot yet type.  Wiring a
modal formation row is the recorded follow-on. -/
theorem modalityFormers_haveNoFormationRowToday :
    (former : ModalityFormer) → hasSomeTypingRule former.generator = false
  | .shapeModality => rfl
  | .flatModality => rfl
  | .sharpModality => rfl
  | .bangModality => rfl
  | .whyNotModality => rfl
  | .provabilityModality => rfl

end FX1Poly.Typed
