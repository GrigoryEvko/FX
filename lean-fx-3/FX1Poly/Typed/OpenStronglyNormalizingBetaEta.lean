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

Both components are SN, taken separately: a well-typed open term is strongly normalizing under β AND under η.

## The remaining crux (the sole missing ingredient for the UNION)

The union βη-SN is NOT the conjunction of the two component SNs: β and η INTERLEAVE, and no single measure
decreases on both (β can duplicate and grow `size`; η shrinks `size` but need not lower the β-reduction rank).
The classical resolution is η-postponement over β.  The framing actually used by the proof is the
Bachmair-Dershowitz / Geser QUASI-COMMUTATION of η over β, `FX1Poly.Core.EtaQuasiCommutesOverBeta`: the
abstract SN-of-union criterion `accUnion` (shipped, Init-only, zero-axiom in `StrongNormalizationUnion`) takes
β-SN + η-SN-everywhere + quasi-commutation and yields βη-SN — no ordinal-rank / `Prod.Lex` machinery needed.
The quasi-commutation crux is a multi-case β/η critical-pair analysis (one obligation per η constructor).  This
file takes it as an explicit hypothesis.

`betaEtaStronglyNormalizingOfWfContextDesc_of_etaQuasiCommutes` is the full conditional βη-SN assembly via the
Geser route.

## Zero-axiom verification

The βη-SN assembly pairs open β-SN with the unconditional η-SN; the
crux-consuming lemma is a one-line application.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core

/-! ## `WfContextDesc` βη-SN results — the βη leg

The componentwise + conditional + headline open βη-SN results over the `HasTypeDesc`-defined `WfContextDesc`,
routing the β-SN component through `stronglyNormalizingOfWfContextDesc` — the η-SN component
(`Step.etaStar.isStronglyNormalizing`) and the Geser union criterion (`accUnionBetaEta`) are
context-predicate-agnostic. -/

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
