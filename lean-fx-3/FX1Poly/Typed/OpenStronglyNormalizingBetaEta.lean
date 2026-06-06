import FX1Poly.Typed.OpenStronglyNormalizingUnconditional
import FX1Poly.Core.StrongNormalizationEta
import FX1Poly.Core.StrongNormalizationBetaEtaUnion
import FX1Poly.Core.EtaPostponementOverBeta

/-! # FX1Poly/Typed/OpenStronglyNormalizingBetaEta
    — OSN-1 scaffolding: the precise remaining crux for open βη strong normalization

Open SN-043 (`HasTypeDescPi.stronglyNormalizingOfWfContext`, OB-5) gives β-strong-normalization for every
well-typed term in a well-formed context.  OSN-1 asks for the FULL βη relation: `Step.betaEta = Step ∪ Step.eta`.
This file scaffolds that goal honestly.

## What is already in hand (both components SN, separately)

  * β-strong-normalization: OB-5 (`HasTypeDescPi.stronglyNormalizingOfWfContext`).
  * η-strong-normalization: UNCONDITIONAL for every raw term — `Step.etaStar.isStronglyNormalizing`, because
    every η constructor strictly contracts `RawTerm.size` (`Step.eta.size_decreases`).

`componentwiseStronglyNormalizingOfWfContext` bundles these: a well-typed open term is strongly normalizing
under β AND under η, taken separately.

## The remaining crux (the sole missing ingredient for the UNION)

The union βη-SN is NOT the conjunction of the two component SNs: β and η INTERLEAVE, and no single measure
decreases on both (β can duplicate and grow `size`; η shrinks `size` but need not lower the β-reduction rank).
The classical resolution is η-postponement over β.  Two framings of the missing ingredient appear here.  The
WEAKER one — **η-reducts of β-SN terms stay β-SN** — is `EtaPreservesBetaStronglyNormalizing`.  The framing
actually used by the proof is the Bachmair-Dershowitz / Geser QUASI-COMMUTATION of η over β,
`FX1Poly.Core.EtaQuasiCommutesOverBeta`: the abstract SN-of-union criterion `accUnion` (shipped, Init-only,
zero-axiom in `StrongNormalizationUnion`) takes β-SN + η-SN-everywhere + quasi-commutation and yields βη-SN —
no ordinal-rank / `Prod.Lex` machinery needed.  So the βη-SN assembly itself is DONE; the sole remaining OSN-1
work is the quasi-commutation crux, a multi-case β/η critical-pair analysis (one obligation per η constructor,
OSN-B3..B6).  This file does not assume it — it is taken as an explicit hypothesis.

`etaReductOfWellTypedIsBetaStronglyNormalizing` records the weaker crux's payoff;
`betaEtaStronglyNormalizingOfWfContext_of_etaQuasiCommutes` is the full conditional βη-SN assembly via the
Geser route.

## Zero-axiom verification

`componentwiseStronglyNormalizingOfWfContext` pairs OB-5 with the shipped unconditional η-SN; the crux-consuming
lemma is a one-line application.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- **The precise remaining crux for open βη-SN.**  η-reducts of β-strongly-normalizing terms are themselves
β-strongly-normalizing — the η-postponement consequence that, together with the β reduction tree and the
size measure, yields strong normalization of the union `Step.betaEta`.  Stated as a predicate so the
downstream βη-SN assembly can consume it as one explicit hypothesis (the way the typed-SN package consumed a
single SN hypothesis before OB-5 discharged it). -/
def EtaPreservesBetaStronglyNormalizing : Prop :=
  ∀ {scope : Nat} {sourceTerm targetTerm : RawTerm scope},
    Step.eta sourceTerm targetTerm →
    StepStar.IsStronglyNormalizing sourceTerm →
    StepStar.IsStronglyNormalizing targetTerm

/-- **Well-typed open terms are strongly normalizing under β AND under η, separately.**  The β component is
open SN-043 (OB-5, `HasTypeDescPi.stronglyNormalizingOfWfContext`); the η component is the unconditional
`Step.etaStar.isStronglyNormalizing` (every raw term, since η strictly shrinks `RawTerm.size`).  This is the
honest componentwise SN bundle for the WfContext fragment — the UNION βη-SN additionally requires
`EtaPreservesBetaStronglyNormalizing` (the η-postponement crux). -/
theorem HasTypeDescPi.componentwiseStronglyNormalizingOfWfContext {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (contextWellFormed : WfContext context)
    (typed : HasTypeDescPi profile context subject classifier) :
    StepStar.IsStronglyNormalizing subject ∧ Step.etaStar.IsStronglyNormalizing subject :=
  ⟨HasTypeDescPi.stronglyNormalizingOfWfContext contextWellFormed typed,
   Step.etaStar.isStronglyNormalizing subject⟩

/-- **The crux's payoff for well-typed terms.**  Given `EtaPreservesBetaStronglyNormalizing`, every η-reduct
of a well-typed open term is β-strongly-normalizing — composing the crux with OB-5.  The step that keeps the
β reduction tree finite across η-contractions in the eventual βη-SN assembly. -/
theorem HasTypeDescPi.etaReductOfWellTypedIsBetaStronglyNormalizing
    (etaPreserves : EtaPreservesBetaStronglyNormalizing)
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier reduct : RawTerm scope}
    (contextWellFormed : WfContext context)
    (typed : HasTypeDescPi profile context subject classifier)
    (etaStep : Step.eta subject reduct) :
    StepStar.IsStronglyNormalizing reduct :=
  etaPreserves etaStep (HasTypeDescPi.stronglyNormalizingOfWfContext contextWellFormed typed)

/-- **Conditional open βη strong normalization — the OSN-1 assembly.**  Given the η-postponement crux
`EtaQuasiCommutesOverBeta`, every well-typed term in a well-formed context is strongly normalizing under the
FULL βη relation `Step.betaEta = Step ∪ Step.eta`.  This is the Geser SN-of-union criterion
(`FX1Poly.Core.accUnionBetaEta`) fed by OB-5 (β-SN, `HasTypeDescPi.stronglyNormalizingOfWfContext`) and the
unconditional shipped η-SN (`Step.etaStar.isStronglyNormalizing`).  The lone remaining hypothesis
`EtaQuasiCommutesOverBeta` is the per-η-constructor postponement (OSN-B3..B6); discharging it makes this
theorem UNCONDITIONAL (OSN-B7, closing #796).  Zero-axiom: a direct application of the zero-axiom
`accUnionBetaEta` to the zero-axiom OB-5. -/
theorem HasTypeDescPi.betaEtaStronglyNormalizingOfWfContext_of_etaQuasiCommutes
    (etaQuasiCommutes : EtaQuasiCommutesOverBeta)
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (contextWellFormed : WfContext context)
    (typed : HasTypeDescPi profile context subject classifier) :
    Step.betaEtaStar.IsStronglyNormalizing subject :=
  accUnionBetaEta etaQuasiCommutes
    (HasTypeDescPi.stronglyNormalizingOfWfContext contextWellFormed typed)

/-- **★ Open βη strong normalization (OSN-1, #796) — UNCONDITIONAL.**  Every well-typed term in a
well-formed context is strongly normalizing under the FULL βη relation `Step.betaEta = Step ∪ Step.eta`
(really βιη, since `Step` carries β and ι).  This is the conditional
`betaEtaStronglyNormalizingOfWfContext_of_etaQuasiCommutes` fed by the now-DISCHARGED η-postponement crux
`etaQuasiCommutesOverBeta` (OSN-B6, the per-η-constructor critical-pair assembly).  The three ingredients:
β-SN is OB-5 (`HasTypeDescPi.stronglyNormalizingOfWfContext`, the Tait reducibility argument); η-SN is the
shipped unconditional `Step.etaStar.isStronglyNormalizing` (η strictly shrinks `RawTerm.size`); the union is
the Geser SN-of-union criterion (`accUnionBetaEta`).  Zero-axiom throughout. -/
theorem HasTypeDescPi.betaEtaStronglyNormalizingOfWfContext
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (contextWellFormed : WfContext context)
    (typed : HasTypeDescPi profile context subject classifier) :
    Step.betaEtaStar.IsStronglyNormalizing subject :=
  HasTypeDescPi.betaEtaStronglyNormalizingOfWfContext_of_etaQuasiCommutes
    etaQuasiCommutesOverBeta contextWellFormed typed

/-! ## Bridge-free `WfContextDesc` twins (HT-B spine step 4 — the βη leg)

The componentwise + conditional + headline open βη-SN results, ported to the `HasTypeDesc`-defined
`WfContextDesc` by routing the β-SN component through the bridge-free `stronglyNormalizingOfWfContextDesc`
(spine step 2) — the η-SN component (`Step.etaStar.isStronglyNormalizing`) and the Geser union criterion
(`accUnionBetaEta`) are context-predicate-agnostic, so no `HasType` appears on the path. -/

/-- **Componentwise open SN under β and η, bridge-free over `WfContextDesc`** — the twin of
`componentwiseStronglyNormalizingOfWfContext`. -/
theorem HasTypeDescPi.componentwiseStronglyNormalizingOfWfContextDesc {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (contextWellFormed : WfContextDesc context)
    (typed : HasTypeDescPi profile context subject classifier) :
    StepStar.IsStronglyNormalizing subject ∧ Step.etaStar.IsStronglyNormalizing subject :=
  ⟨HasTypeDescPi.stronglyNormalizingOfWfContextDesc contextWellFormed typed,
   Step.etaStar.isStronglyNormalizing subject⟩

/-- **Conditional open βη-SN, bridge-free over `WfContextDesc`** — the twin of
`betaEtaStronglyNormalizingOfWfContext_of_etaQuasiCommutes`: the Geser SN-of-union (`accUnionBetaEta`) fed the
`WfContextDesc` β-SN witness + the η-postponement crux. -/
theorem HasTypeDescPi.betaEtaStronglyNormalizingOfWfContextDesc_of_etaQuasiCommutes
    (etaQuasiCommutes : EtaQuasiCommutesOverBeta)
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (contextWellFormed : WfContextDesc context)
    (typed : HasTypeDescPi profile context subject classifier) :
    Step.betaEtaStar.IsStronglyNormalizing subject :=
  accUnionBetaEta etaQuasiCommutes
    (HasTypeDescPi.stronglyNormalizingOfWfContextDesc contextWellFormed typed)

/-- **★ Open βη strong normalization (OSN-1), bridge-free over `WfContextDesc`** — the twin of the OSN-1 headline
`betaEtaStronglyNormalizingOfWfContext`: the conditional twin fed the discharged `etaQuasiCommutesOverBeta`, with
the β-SN component now routed through `stronglyNormalizingOfWfContextDesc`.  The βη open-SN spine point the
βη-convergence leg + the SN-051/052 βη qualifier-drops migrate onto before HT-C. -/
theorem HasTypeDescPi.betaEtaStronglyNormalizingOfWfContextDesc
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (contextWellFormed : WfContextDesc context)
    (typed : HasTypeDescPi profile context subject classifier) :
    Step.betaEtaStar.IsStronglyNormalizing subject :=
  HasTypeDescPi.betaEtaStronglyNormalizingOfWfContextDesc_of_etaQuasiCommutes
    etaQuasiCommutesOverBeta contextWellFormed typed

end FX1Poly.Typed
