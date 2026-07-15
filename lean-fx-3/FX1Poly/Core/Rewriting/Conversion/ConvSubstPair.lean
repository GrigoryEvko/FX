import FX1Poly.Core.Rewriting.Conversion.ConvSubstRename
import FX1Poly.Axis.Term.Subst.RawTermSubstPair

/-! # ConvSubstPair — two-variable substitution congruence for raw conversion

The two-substituent analog of `Conv.subst0` (`ConvSubstRename.lean`): when the body and BOTH
substituents of a `RawTerm.substPair` are independently `Conv`, the `substPair` results are `Conv`.

`substPair body inner outer = subst (pair inner outer) body` is the two-variable parallel substitution
the two-binder eliminators use (the natElim/natRec succ-iota contractum and `idJ`'s dependent output type
`idJMotiveAt motive point path = substPair motive path point`).  When a child of such an eliminator cell
steps, the dependent output type drifts, and its `Conv`-stability — the output-type-congruence ingredient
of the native eliminator subject reduction (#1740, gate 2 of #1697) — reduces to `Conv.substPair`.

## Proof technique (mirrors `Conv.subst0`)

`Conv.subst0` traversed the arg side of a one-variable substitution via
`RawTermSubst.singleton_pointwise_stepStar`.  Here the substitution has TWO non-trivial positions, so the
bridging helper is `RawTermSubst.pair_pointwise_stepStar`: from `StepStar innerLeft innerRight` and
`StepStar outerLeft outerRight` it builds a `PointwiseStepStar (pair innerLeft outerLeft)
(pair innerRight outerRight)` — position 0 via the inner chain, position 1 via the outer chain, position
k+2 by reflexivity.  Each `Conv.substPair` leg then composes `StepStar.subst` (the body chain) with
`RawTerm.subst_pointwise_stepStar` (the two substituent chains) at the common reduct, exactly as the
single-variable case.

## Zero-axiom verification

A composition of `StepStar.subst` / `RawTerm.subst_pointwise_stepStar` / `StepStar.trans_compose` plus a
per-position `Fin` `match` closing by `rfl` / the supplied chains.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration audit-gated in `FX1PolyAudit`. -/

namespace FX1Poly.Core

open FX1Poly.Axis.Syntax

/-- **The two-substituent substitution is pointwise `StepStar`-related when its substituents are.**  The
`pair` analog of `RawTermSubst.singleton_pointwise_stepStar`: `pair inner outer = cons inner (singleton
outer)` maps position 0 to `inner`, position 1 to `outer`, and position k+2 to `var k`.  So from chains on
both substituents, every position of `pair innerLeft outerLeft` reduces to the matching position of
`pair innerRight outerRight` — position 0 via `innerChain`, position 1 via `outerChain`, position k+2 by
reflexivity (both produce the same scope-invariant `var k`). -/
theorem RawTermSubst.pair_pointwise_stepStar {scope : Nat}
    {innerLeft innerRight outerLeft outerRight : RawTerm scope}
    (innerChain : StepStar innerLeft innerRight)
    (outerChain : StepStar outerLeft outerRight) :
    RawTermSubst.PointwiseStepStar
      (RawTermSubst.pair innerLeft outerLeft)
      (RawTermSubst.pair innerRight outerRight) := by
  intro position
  match position with
  | ⟨0, _⟩ => exact innerChain
  | ⟨1, _⟩ => exact outerChain
  | ⟨_ + 2, _⟩ => exact StepStar.refl _

/-- **Conv preserved by two-variable substitution at the succ-iota / `idJ`-output shape.**  Three-arg form:
if the body and both substituents are independently `Conv`, then their `substPair` results are `Conv`.  The
two-substituent analog of `Conv.subst0`, and the congruence the two-binder dependent eliminators' output
types consume when a cell child steps.

Proof structure (per leg, mirroring `Conv.subst0`):
* Body chain: `StepStar.subst (pair innerX outerX) bodyXChain` reduces the body side while fixing the pair.
* Substituent chains: `subst_pointwise_stepStar (pair_pointwise_stepStar innerXChain outerXChain)
  bodyCommon` reduces both substituent sides while fixing the (already-reduced) common body.
* `StepStar.trans_compose` chains them to the common reduct `substPair bodyCommon innerCommon outerCommon`. -/
theorem Conv.substPair {scope : Nat}
    {bodyLeft bodyRight : RawTerm (scope + 2)}
    {innerLeft innerRight outerLeft outerRight : RawTerm scope}
    (bodyConv : Conv bodyLeft bodyRight)
    (innerConv : Conv innerLeft innerRight)
    (outerConv : Conv outerLeft outerRight) :
    Conv (RawTerm.substPair bodyLeft innerLeft outerLeft)
         (RawTerm.substPair bodyRight innerRight outerRight) := by
  obtain ⟨bodyCommon, bodyLeftChain, bodyRightChain⟩ := bodyConv
  obtain ⟨innerCommon, innerLeftChain, innerRightChain⟩ := innerConv
  obtain ⟨outerCommon, outerLeftChain, outerRightChain⟩ := outerConv
  refine ⟨RawTerm.substPair bodyCommon innerCommon outerCommon, ?_, ?_⟩
  · -- left leg: substPair bodyLeft innerLeft outerLeft →* substPair bodyCommon innerCommon outerCommon
    exact StepStar.trans_compose
      (StepStar.subst (RawTermSubst.pair innerLeft outerLeft) bodyLeftChain)
      (RawTerm.subst_pointwise_stepStar
        (RawTermSubst.pair_pointwise_stepStar innerLeftChain outerLeftChain) bodyCommon)
  · -- right leg: substPair bodyRight innerRight outerRight →* substPair bodyCommon innerCommon outerCommon
    exact StepStar.trans_compose
      (StepStar.subst (RawTermSubst.pair innerRight outerRight) bodyRightChain)
      (RawTerm.subst_pointwise_stepStar
        (RawTermSubst.pair_pointwise_stepStar innerRightChain outerRightChain) bodyCommon)

end FX1Poly.Core
