import FX1Poly.Core.StepWordRewriteSoundness
import FX1Poly.Core.StepStarConfluence

/-! # FX1Poly/Core/ConvWordJoinableBridge
    — Conv ⟹ word joinability under the generated system (SN-129, #632)

FX `Conv` is term JOINABILITY: `Conv a b := StepStar.Join a b := ∃ commonTerm, StepStar a commonTerm ∧
StepStar b commonTerm` (`StepStarConfluence.lean`).  This file gives the ConvertibleModulo notion for the FX
term-code word monoid — `FxWordJoinable`, word joinability under a rule system — and the FORWARD half of the
SN-129 bridge: `Conv a b ⟹ FxWordJoinable fxStepSystem a.toCode b.toCode`.

The forward map is clean: a common term reduct `c` (from `Conv`) encodes to a common WORD reduct `c.toCode`, and
each `StepStar` leg maps to a `FxWordRewritesMany` leg via SN-127's `StepStar.toWordRewrites`.

## The honest scope: forward only

This is the `⟹` direction.  The reverse `FxWordJoinable fxStepSystem a.toCode b.toCode ⟹ Conv a b` would need the
word→term completeness blocked in SN-128 (`StepWordRewriteEquivariance.lean`): the free word monoid is more
permissive than terms and `RawTerm.toCode` collapses non-`Nat`/`Fin` payloads, so a common WORD reduct need not
decode to a common TERM reduct.  The reverse is deferred to the typed-SN critical path (per
`core_raw_sn_false_natrec`); stating the forward bridge honestly beats faking the biconditional.

`FxWordJoinable` is reflexive and symmetric (proved here); transitivity would need confluence of the FX word
system (SN-132/133, also typed-SN-gated), so it is NOT claimed.  This is exactly the joinability shape the
OmegacE `decidableConvertibleModulo_ofConvergent` (SN-118/119/120) consumes — SN-134 will instantiate the FX
word decider on it once termination + confluence land.

## What is proved

* `FxWordJoinable` — word joinability (common reduct) under an `FxTermRewriteRule` system: the ConvertibleModulo.
* `FxWordJoinable.refl` / `FxWordJoinable.symm` — reflexivity / symmetry of word joinability.
* `FxWordJoinable.ofWordRewritesMany` — a one-directional reduction is joinable (common = the target).
* `Conv.toWordJoinable` — **the forward bridge**: `Conv a b ⟹ FxWordJoinable fxStepSystem a.toCode b.toCode`.
* `Step.toWordJoinable` — a single FX reduction's endpoints are word-joinable.

## Zero-axiom verification

`FxWordJoinable` is a plain `∃`; `refl`/`symm`/`ofWordRewritesMany` are anonymous-constructor / `obtain`+swap; the
forward bridge destructures `Conv` (which whnf-unfolds to the `Join` existential) and maps both legs via
SN-127's soundness.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration gated in `FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

/-- **Word joinability** (the ConvertibleModulo for the FX term-code word monoid): two words join when they reduce
to a common word reduct under the rule system. -/
def FxWordJoinable (system : FxTermRewriteRule → Prop) (leftWord rightWord : List Nat) : Prop :=
  ∃ commonWord : List Nat,
    FxWordRewritesMany system leftWord commonWord ∧ FxWordRewritesMany system rightWord commonWord

/-- Word joinability is reflexive (a word joins itself at itself). -/
theorem FxWordJoinable.refl {system : FxTermRewriteRule → Prop} (word : List Nat) :
    FxWordJoinable system word word :=
  ⟨word, FxWordRewritesMany.refl word, FxWordRewritesMany.refl word⟩

/-- Word joinability is symmetric (swap the two reduction legs). -/
theorem FxWordJoinable.symm {system : FxTermRewriteRule → Prop} {leftWord rightWord : List Nat}
    (joinable : FxWordJoinable system leftWord rightWord) :
    FxWordJoinable system rightWord leftWord := by
  obtain ⟨commonWord, leftChain, rightChain⟩ := joinable
  exact ⟨commonWord, rightChain, leftChain⟩

/-- A one-directional reduction makes its endpoints joinable (the common reduct is the target). -/
theorem FxWordJoinable.ofWordRewritesMany {system : FxTermRewriteRule → Prop}
    {leftWord rightWord : List Nat}
    (reduction : FxWordRewritesMany system leftWord rightWord) :
    FxWordJoinable system leftWord rightWord :=
  ⟨rightWord, reduction, FxWordRewritesMany.refl rightWord⟩

/-- **The forward Conv bridge**: convertible terms have word-joinable codes under the generated system.  A common
term reduct encodes to a common word reduct, and each `StepStar` leg maps via SN-127's `StepStar.toWordRewrites`. -/
theorem Conv.toWordJoinable {scope : Nat} {leftTerm rightTerm : RawTerm scope}
    (conv : Conv leftTerm rightTerm) :
    FxWordJoinable fxStepSystem leftTerm.toCode rightTerm.toCode := by
  obtain ⟨commonTerm, leftChain, rightChain⟩ := conv
  exact ⟨commonTerm.toCode, leftChain.toWordRewrites, rightChain.toWordRewrites⟩

/-- A single FX reduction's endpoints are word-joinable (reduce the redex's code to the reduct's, join there). -/
theorem Step.toWordJoinable {scope : Nat} {redex reduct : RawTerm scope}
    (step : Step redex reduct) :
    FxWordJoinable fxStepSystem redex.toCode reduct.toCode :=
  FxWordJoinable.ofWordRewritesMany (FxWordRewritesMany.single step.toWordRewrite)

end FX1Poly.Core
