import FX1Poly.Typed.OpenStronglyNormalizingUnconditional
import FX1Poly.Core.StrongNormalizationEta

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
The classical resolution is η-postponement over β — equivalently, that **η-reducts of β-SN terms stay β-SN**,
isolated here as `EtaPreservesBetaStronglyNormalizing`.  With it, the βη relation is the lexicographic
combination of the β reduction tree and `size`, and βη-SN follows.  That lexicographic SN-of-union assembly
needs ordinal-rank / `Prod.Lex` well-foundedness machinery beyond `Init`, and the crux itself is a multi-case
β/η critical-pair analysis (one obligation per η constructor) — both are the genuinely remaining OSN-1 work,
tracked separately; this file does not assume them.

`etaReductOfWellTypedIsBetaStronglyNormalizing` records the crux's immediate payoff for well-typed terms.

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

end FX1Poly.Typed
