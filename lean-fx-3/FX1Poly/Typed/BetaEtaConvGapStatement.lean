import FX1Poly.Typed.WfContextBetaEtaConfluenceUnconditional
import FX1Poly.Core.RawConfluence

/-! # FX1Poly/Typed/BetaEtaConvGapStatement
   — the βη-conversion gap statement (ETA-1): what is decided, what is decidable-pending-a-reducer,
     and what genuinely needs the type-directed η-long route

## The census verdict this module commits (reconciling tracker #806 against the #364 spec)

**Correction of record**: tracker #806 ("decidable βη-Conv on the WfContext fragment") OVERSTATES
what shipped.  `WfContextBetaEtaConfluence.lean` says so itself: weak βη-normalization and
decidable βη-Conv were explicitly DEFERRED ("this file does NOT fake them from confluence alone").
What the βη campaign + BECR-1 actually shipped is the complete DECISION METATHEORY: typed βη-SN,
typed βη-CR (annotation-guard-free), unique typed βη-NF, and βη star-rigidity — bundled and
re-verified here as `BetaEtaDeciderMetatheoryPrerequisites`.

**The relation, made first-class**: FX's raw `Conv` is JOIN-based by definition
(`Conv = StepStar.Join`), with transitivity recovered from RAW confluence.  This module defines the
βη analogue the same way — `BetaEtaConv = Step.betaEtaStar.Join` — and proves the exact parallel
package: reflexivity and symmetry structurally, `Conv ⊆ BetaEtaConv` (the η extension is
conservative over β/ι-conversion), STRICTNESS (an η-contraction pair is `BetaEtaConv` but provably
NOT `Conv`), and — the typed-fragment crux — transitivity THROUGH A WELL-TYPED MIDDLE
(`transAtTypedMiddle`, via typed βη-CR).  Unrestricted transitivity is NOT provable this way: raw
βη-CR is FALSE (Nederpelt, `NederpeltNonJoinability`), so βη join-conversion is an equivalence
only where typing supplies confluence — Geuvers' "the maximum one can expect".

## The gap statement for #364 (★ typed decidable Conv with η)

Splitting #364's remaining content by what it actually requires:

  1. **Decidable `BetaEtaConv` on the wf-typed fragment** — needs ONLY a computable βη one-step
     reducer (`reduceOnceBetaEta` + soundness/completeness, the ETA-2 target): every metatheory
     leg is in `betaEtaDeciderMetatheoryPrerequisitesHold`, and the `NormalizeSteps`-style
     `Acc.rec` normalizer pattern transfers verbatim over the shipped typed βη-SN.  No
     type-directed quote is needed for the 5 SYNTACTIC η rules (lam/pair/pathLam/modIntro/
     glueIntro).
  2. **Type-directed η beyond the syntactic rules** — unit-η (any two terms equal at `Unit`) and
     its SProp/modal kin are NOT `Step.eta` rules (deliberately: unconditional raw unit-η is
     unsound), are NOT in `BetaEtaConv` at all, and genuinely need the η-long type-directed
     readback (η-M15d/e) — judgmental-equality EXTENSION territory, not decision-procedure
     territory.
  3. **#364's spec text is stale** on top of this split: it cites the deleted `HasType` engine,
     `LeanFX2` paths, and assumes the raw-layer NbE quote (M13) can carry η — it cannot; η-long
     readback is type-indexed by construction.

## Zero-axiom verification

The equivalence-package proofs are structural join manipulations + the shipped typed βη-CR; the
strictness witness closes by `decide` on closed normality/inequality facts +
`Conv.iff_normalForms_eq_of_confluence` at reflexive chains.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Core

/-- **βη-conversion, join-based** — the βη analogue of the kernel's own `Conv` (which is
DEFINITIONALLY `StepStar.Join`): two terms are βη-convertible when they βη-reduce to a common
reduct. -/
def BetaEtaConv {scope : Nat} (leftTerm rightTerm : RawTerm scope) : Prop :=
  Step.betaEtaStar.Join leftTerm rightTerm

namespace BetaEtaConv

/-- Reflexivity (shared reduct: the term itself). -/
theorem refl {scope : Nat} (term : RawTerm scope) : BetaEtaConv term term :=
  ⟨term, .refl _, .refl _⟩

/-- Symmetry (swap the two chains). -/
theorem sym {scope : Nat} {leftTerm rightTerm : RawTerm scope}
    (convertible : BetaEtaConv leftTerm rightTerm) : BetaEtaConv rightTerm leftTerm :=
  Exists.elim convertible (fun commonTerm chains => ⟨commonTerm, chains.2, chains.1⟩)

/-- A βη-star chain induces βη-conversion. -/
theorem fromBetaEtaStar {scope : Nat} {sourceTerm targetTerm : RawTerm scope}
    (chain : Step.betaEtaStar sourceTerm targetTerm) : BetaEtaConv sourceTerm targetTerm :=
  ⟨targetTerm, chain, .refl _⟩

/-- **β/ι-conversion embeds in βη-conversion** — the η extension is conservative over the
kernel's `Conv`: both joining chains transport through `betaEtaStar.ofStepStar`. -/
theorem ofConv {scope : Nat} {leftTerm rightTerm : RawTerm scope}
    (convertible : Conv leftTerm rightTerm) : BetaEtaConv leftTerm rightTerm :=
  Exists.elim convertible
    (fun commonTerm chains =>
      ⟨commonTerm, Step.betaEtaStar.ofStepStar chains.1, Step.betaEtaStar.ofStepStar chains.2⟩)
-- (`Step.betaEtaStar.ofStepStar` is the shipped stepwise `Or.inl` embedding.)

end BetaEtaConv

end FX1Poly.Core

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The η extension is STRICT**: an η-contraction pair (`λx. T x` vs `T` at a universe-code
function) is βη-convertible but provably NOT β/ι-convertible — both sides are β/ι-normal and
distinct, so `Conv` would force their equality.  The machine-checked non-vacuity of everything
this module is about. -/
theorem _root_.FX1Poly.Core.BetaEtaConv.strictlyExtendsConv :
    ∃ leftTerm rightTerm : RawTerm 0,
      BetaEtaConv leftTerm rightTerm ∧ ¬ Conv leftTerm rightTerm := by
  refine ⟨RawTerm.etaLamSource
      (universeCodeCell LevelExpr.lzero UniverseFlag.standard)
      (universeCodeCell LevelExpr.lzero UniverseFlag.standard),
    universeCodeCell LevelExpr.lzero UniverseFlag.standard,
    ⟨universeCodeCell LevelExpr.lzero UniverseFlag.standard,
      Step.betaEtaStar.ofEta (Step.eta.etaLam _ _), .refl _⟩,
    fun convertible => ?_⟩
  have hFormsEqual :=
    (Conv.iff_normalForms_eq_of_confluence
      (StepStar.refl _) (by decide) (StepStar.refl _) (by decide)).mp convertible
  exact absurd hFormsEqual (by decide)

/-- **Transitivity of βη-conversion through a WELL-TYPED middle term** — the typed-fragment
equivalence leg.  Raw βη confluence is FALSE (Nederpelt), so unlike the kernel's `Conv.trans`
(which discharges its peak with RAW confluence), the βη peak at the middle term is discharged by
TYPED βη Church-Rosser — typing is load-bearing exactly here. -/
theorem BetaEtaConv.transAtTypedMiddle {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {middleTerm classifier : RawTerm scope}
    (contextWellFormed : WfContextDesc context)
    (middleTyped : HasTypeDescPi profile context middleTerm classifier)
    {leftTerm rightTerm : RawTerm scope}
    (leftToMiddle : BetaEtaConv leftTerm middleTerm)
    (middleToRight : BetaEtaConv middleTerm rightTerm) :
    BetaEtaConv leftTerm rightTerm := by
  obtain ⟨leftCommon, leftChain, middleChainLeft⟩ := leftToMiddle
  obtain ⟨rightCommon, middleChainRight, rightChain⟩ := middleToRight
  obtain ⟨apex, leftCommonToApex, rightCommonToApex⟩ :=
    HasTypeDescPi.subjectBetaEtaConfluenceTypedUnconditional contextWellFormed middleTyped
      middleChainLeft middleChainRight
  exact ⟨apex,
    Step.betaEtaStar.trans_compose leftChain leftCommonToApex,
    Step.betaEtaStar.trans_compose rightChain rightCommonToApex⟩

/-- **The complete decision METATHEORY for βη-conversion on the wf-typed fragment** — the four
legs a normalize-and-compare `BetaEtaConv` decider needs, every one already shipped.  What is
MISSING is exactly one computable artifact: a sound+complete βη one-step reducer (the ETA-2
target); the `Acc.rec` normalizer pattern then transfers verbatim over `typedBetaEtaSn`. -/
structure BetaEtaDeciderMetatheoryPrerequisites (profile : PolyProfile) : Prop where
  /-- Typed βη strong normalization (OSN-1): the normalizer's termination certificate. -/
  typedBetaEtaSn : ∀ {scope : Nat} {context : TypingContext profile scope}
    {subject classifier : RawTerm scope},
    WfContextDesc context → HasTypeDescPi profile context subject classifier →
    Step.betaEtaStar.IsStronglyNormalizing subject
  /-- Typed βη Church-Rosser (BECR-1, annotation-guard-free): well-definedness of the decision. -/
  typedBetaEtaConfluence : ∀ {scope : Nat} {context : TypingContext profile scope}
    {subject classifier leftReduct rightReduct : RawTerm scope},
    WfContextDesc context → HasTypeDescPi profile context subject classifier →
    Step.betaEtaStar subject leftReduct → Step.betaEtaStar subject rightReduct →
    Step.betaEtaStar.Join leftReduct rightReduct
  /-- Unique typed βη normal form: the compared representatives are canonical. -/
  uniqueBetaEtaNormalForm : ∀ {scope : Nat} {context : TypingContext profile scope}
    {subject classifier normalFormLeft normalFormRight : RawTerm scope},
    WfContextDesc context → HasTypeDescPi profile context subject classifier →
    Step.betaEtaStar subject normalFormLeft →
    (∀ reduct : RawTerm scope, ¬ Step.betaEta normalFormLeft reduct) →
    Step.betaEtaStar subject normalFormRight →
    (∀ reduct : RawTerm scope, ¬ Step.betaEta normalFormRight reduct) →
    normalFormLeft = normalFormRight
  /-- βη star-rigidity: chains halt exactly at βη-normal forms. -/
  starRigidity : ∀ {scope : Nat} {startTerm endTerm : RawTerm scope},
    (∀ reduct : RawTerm scope, ¬ Step.betaEta startTerm reduct) →
    Step.betaEtaStar startTerm endTerm → startTerm = endTerm

/-- **The four legs hold** — each field is the shipped named theorem. -/
theorem betaEtaDeciderMetatheoryPrerequisitesHold {profile : PolyProfile} :
    BetaEtaDeciderMetatheoryPrerequisites profile where
  typedBetaEtaSn contextWellFormed typed :=
    HasTypeDescPi.betaEtaStronglyNormalizingOfWfContextDesc contextWellFormed typed
  typedBetaEtaConfluence contextWellFormed typed subjectToLeft subjectToRight :=
    HasTypeDescPi.subjectBetaEtaConfluenceTypedUnconditional contextWellFormed typed
      subjectToLeft subjectToRight
  uniqueBetaEtaNormalForm contextWellFormed typed subjectToLeft leftNoStep
      subjectToRight rightNoStep :=
    HasTypeDescPi.uniqueBetaEtaNormalFormTypedUnconditional contextWellFormed typed
      subjectToLeft leftNoStep subjectToRight rightNoStep
  starRigidity noStep chain := Step.betaEtaStar.eq_of_noBetaEtaStep noStep chain

end FX1Poly.Typed
