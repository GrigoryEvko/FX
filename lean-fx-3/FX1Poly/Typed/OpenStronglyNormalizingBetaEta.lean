import FX1Poly.Typed.OpenStronglyNormalizingUnconditional
import FX1Poly.Core.StrongNormalizationEta
import FX1Poly.Core.StrongNormalizationBetaEtaUnion
import FX1Poly.Core.EtaPostponementOverBeta

/-! # FX1Poly/Typed/OpenStronglyNormalizingBetaEta
    — open βη strong normalization

Open strong normalization (`HasTypeDescPi.stronglyNormalizingOfWfContextDesc`) gives β-strong-normalization for
every well-typed term in a well-formed context.  The FULL βη relation is `Step.betaEta = Step ∪ Step.eta`.
This file establishes open βη-SN over the `HasTypeDesc`-defined `WfContextDesc`.

## What is already in hand (both components SN, separately)

  * β-strong-normalization: `HasTypeDescPi.stronglyNormalizingOfWfContextDesc`.
  * η-strong-normalization: UNCONDITIONAL for every raw term — `Step.etaStar.isStronglyNormalizing`, because
    every η constructor strictly contracts `RawTerm.size` (`Step.eta.size_decreases`).

`componentwiseStronglyNormalizingOfWfContextDesc` bundles these: a well-typed open term is strongly normalizing
under β AND under η, taken separately.

## The remaining crux (the sole missing ingredient for the UNION)

The union βη-SN is NOT the conjunction of the two component SNs: β and η INTERLEAVE, and no single measure
decreases on both (β can duplicate and grow `size`; η shrinks `size` but need not lower the β-reduction rank).
The classical resolution is η-postponement over β.  Two framings of the missing ingredient appear here.  The
WEAKER one — **η-reducts of β-SN terms stay β-SN** — is `EtaPreservesBetaStronglyNormalizing`.  The framing
actually used by the proof is the Bachmair-Dershowitz / Geser QUASI-COMMUTATION of η over β,
`FX1Poly.Core.EtaQuasiCommutesOverBeta`: the abstract SN-of-union criterion `accUnion` (shipped, Init-only,
zero-axiom in `StrongNormalizationUnion`) takes β-SN + η-SN-everywhere + quasi-commutation and yields βη-SN —
no ordinal-rank / `Prod.Lex` machinery needed.  The quasi-commutation crux is a multi-case β/η critical-pair
analysis (one obligation per η constructor).  This file takes it as an explicit hypothesis.

`etaReductOfWellTypedIsBetaStronglyNormalizing` records the weaker crux's payoff;
`betaEtaStronglyNormalizingOfWfContextDesc_of_etaQuasiCommutes` is the full conditional βη-SN assembly via the
Geser route.

## Zero-axiom verification

`componentwiseStronglyNormalizingOfWfContextDesc` pairs open β-SN with the unconditional η-SN; the
crux-consuming lemma is a one-line application.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- **The precise remaining crux for open βη-SN.**  η-reducts of β-strongly-normalizing terms are themselves
β-strongly-normalizing — the η-postponement consequence that, together with the β reduction tree and the
size measure, yields strong normalization of the union `Step.betaEta`.  Stated as a predicate so the
downstream βη-SN assembly can consume it as one explicit hypothesis. -/
def EtaPreservesBetaStronglyNormalizing : Prop :=
  ∀ {scope : Nat} {sourceTerm targetTerm : RawTerm scope},
    Step.eta sourceTerm targetTerm →
    StepStar.IsStronglyNormalizing sourceTerm →
    StepStar.IsStronglyNormalizing targetTerm

/-- **The crux's payoff for well-typed terms.**  Given `EtaPreservesBetaStronglyNormalizing`, every η-reduct
of a well-typed open term is β-strongly-normalizing — composing the crux with open β-SN.  The step that keeps
the β reduction tree finite across η-contractions in the eventual βη-SN assembly.  Over the
`HasTypeDesc`-defined `WfContextDesc`, routing β-SN through `stronglyNormalizingOfWfContextDesc`. -/
theorem HasTypeDescPi.etaReductOfWellTypedIsBetaStronglyNormalizing
    (etaPreserves : EtaPreservesBetaStronglyNormalizing)
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier reduct : RawTerm scope}
    (contextWellFormed : WfContextDesc context)
    (typed : HasTypeDescPi profile context subject classifier)
    (etaStep : Step.eta subject reduct) :
    StepStar.IsStronglyNormalizing reduct :=
  etaPreserves etaStep (HasTypeDescPi.stronglyNormalizingOfWfContextDesc contextWellFormed typed)

/-! ## `WfContextDesc` βη-SN results — the βη leg

The componentwise + conditional + headline open βη-SN results over the `HasTypeDesc`-defined `WfContextDesc`,
routing the β-SN component through `stronglyNormalizingOfWfContextDesc` — the η-SN component
(`Step.etaStar.isStronglyNormalizing`) and the Geser union criterion (`accUnionBetaEta`) are
context-predicate-agnostic. -/

/-- **Componentwise open SN under β and η over `WfContextDesc`** — a well-typed open term is
strongly normalizing under β (`stronglyNormalizingOfWfContextDesc`) AND under η (the unconditional
`Step.etaStar.isStronglyNormalizing`), taken separately. -/
theorem HasTypeDescPi.componentwiseStronglyNormalizingOfWfContextDesc {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (contextWellFormed : WfContextDesc context)
    (typed : HasTypeDescPi profile context subject classifier) :
    StepStar.IsStronglyNormalizing subject ∧ Step.etaStar.IsStronglyNormalizing subject :=
  ⟨HasTypeDescPi.stronglyNormalizingOfWfContextDesc contextWellFormed typed,
   Step.etaStar.isStronglyNormalizing subject⟩

/-- **Conditional open βη-SN over `WfContextDesc`** — given the η-postponement crux
`EtaQuasiCommutesOverBeta`, the Geser SN-of-union (`accUnionBetaEta`) fed the `WfContextDesc` β-SN witness
(`stronglyNormalizingOfWfContextDesc`) yields βη-SN for every well-typed term in a well-formed context. -/
theorem HasTypeDescPi.betaEtaStronglyNormalizingOfWfContextDesc_of_etaQuasiCommutes
    (etaQuasiCommutes : EtaQuasiCommutesOverBeta)
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (contextWellFormed : WfContextDesc context)
    (typed : HasTypeDescPi profile context subject classifier) :
    Step.betaEtaStar.IsStronglyNormalizing subject :=
  accUnionBetaEta etaQuasiCommutes
    (HasTypeDescPi.stronglyNormalizingOfWfContextDesc contextWellFormed typed)

/-- **★ Open βη strong normalization over `WfContextDesc`** — the
conditional assembly fed the discharged η-postponement crux `etaQuasiCommutesOverBeta`, with the β-SN component
routed through `stronglyNormalizingOfWfContextDesc`.  Every well-typed term in a well-formed context is strongly
normalizing under the FULL βη relation `Step.betaEta = Step ∪ Step.eta` (really βιη, since `Step` carries β and
ι).  The βη open-SN point the βη-convergence leg + the βη conversion-decidability results compose with. -/
theorem HasTypeDescPi.betaEtaStronglyNormalizingOfWfContextDesc
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (contextWellFormed : WfContextDesc context)
    (typed : HasTypeDescPi profile context subject classifier) :
    Step.betaEtaStar.IsStronglyNormalizing subject :=
  HasTypeDescPi.betaEtaStronglyNormalizingOfWfContextDesc_of_etaQuasiCommutes
    etaQuasiCommutesOverBeta contextWellFormed typed

end FX1Poly.Typed
