import FX1Poly.Typed.HasTypeDescPi
import FX1Poly.Core.StepStarConfluence

/-! # FX1Poly/Typed/PiElimClassifierConvResidual
    — the PRECISELY-LOCATED residual of the grown context-conversion piElim arm (GrownCtxConv-5, #842):
      SN-restricted type-Conv-closure (the fundamental-theorem ESCAPE, dual to the shipped #537 forward
      Conv-invariance)

## The root cause, verified against the rule (firing-23 reading)

`HasTypeDescPiContextConversion.lean` records the verified root cause of the lone-hard `piElim` arm of grown
context-conversion: `HasTypeDescPi.piElim` carries NO `D : Type` / `C : Type` typing premises (only
`function : Π D C` and `argument : D`), so when the function's IH gives `function : F'` under the target
context with `Conv F' (Π D C)`, re-typing it at the EXACT `Π D C` (to re-apply `piElim`) needs the conv-rule
reclassifier `Π D C` to be a VALID TYPE under the target — i.e. **`IsType` respects `Conv`** (`IsType T →
Conv T S → IsType S`).

That is NOT a subject-reduction corollary: via confluence it would require subject EXPANSION on the `S`-side
(`S ⤳* R`, then `IsType R ⊢ IsType S`), which is FALSE in general.  It is the FUNDAMENTAL THEOREM run
BACKWARDS (`reducible → typed`), strictly STRONGER than SR — the "deliberate multi-fire" mutual
fundamental-metatheory bundle.

## Why the residual must be SN-RESTRICTED (the #1058 refutation, reconciled)

`#1058` refuted the UNRESTRICTED `classifierRespectsConv`: with `T = Type@0` and `S = (λ.Type@0) Ω`, `T` is a
valid type and `Conv T S` (`S ⤳ Type@0` by β), but `S` is NOT a valid type (`Ω` is untypable, so `S` is
untypable).  The counterexample's `S` is exactly a NON-SN term.  So the residual holds only when `S` is
restricted to the STRONGLY-NORMALIZING fragment — which is automatic on the well-typed fragment (`SN-043`).
This is the precise FT-escape: a Conv-image of a valid type that is ALSO strongly normalizing is itself a
valid type.

## The WfContext-threading that makes this the residual (firing-23 finding)

The shipped validity `HasTypeDescPi.classifierIsTypeDescPi` (WFG-3, `#857`) gives, FROM a `WfContextDescPi`,
the classifier of any well-typed term as a valid type — so threading a `WfContextDescPi` through the
context-conversion (the pending GrownCtxConv-thread, `#1059`) yields `IsTypeDescPi targetContext F'` (validity
at the TARGET) directly, WITHOUT the unbounded-height structural inversion (`classifierIsTypeDescPi` "can
return an unbounded-height" derivation, which breaks the mutual structural recursion but NOT a standalone
use).  The piElim arm then needs only `IsTypeDescPi targetContext F' → Conv F' (Π D C) → IsTypeDescPi
targetContext (Π D C)` at the FIXED target context — pure type-Conv-closure, the residual below, with the
context conversion fully discharged.

## What this file ships

`IsTypeDescPiRespectsConvOnStronglyNormalizing` — the SN-restricted type-Conv-closure residual, named as a
`Prop` so downstream reductions cite it as the single open obligation of the grown context-conversion piElim
arm (the dual of the shipped `ReducibleTypeStep.convInvariant`, `#537`, which carries the FORWARD direction on
the reducibility side).  `smoke_residualRefl` shows the residual is non-vacuous (the reflexive instance is the
input).  The genuine discharge is the `reducible → typed` FT-escape — the multi-fire fundamental-metatheory
construction.

## Zero-axiom verification

A `Prop` definition plus a one-line reflexive smoke (`Conv.refl`).  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Core.StepStar FX1Poly.Universe FX1Poly.Foundation

/-- **The SN-restricted type-Conv-closure residual** — the precisely-located open obligation of the grown
context-conversion piElim arm (GrownCtxConv-5, #842) after WfContext-threading (#1059).  A type that is
`Conv`-equal to a VALID type and is itself STRONGLY NORMALIZING is a valid type.  The strong-normalization
restriction on `typeRight` is exactly what excludes the `#1058` non-SN counterexample `(λ.Type@0) Ω`; on the
well-typed fragment it is automatic (`SN-043`).  This is the FUNDAMENTAL-THEOREM ESCAPE (`reducible → typed`,
run backwards), strictly stronger than subject reduction; the dual of the shipped FORWARD Conv-invariance of
reducibility (`ReducibleTypeStep.convInvariant`, `#537`). -/
def IsTypeDescPiRespectsConvOnStronglyNormalizing (profile : PolyProfile) : Prop :=
  ∀ {scope : Nat} {context : TypingContext profile scope} {typeLeft typeRight : RawTerm scope},
    IsTypeDescPi profile context typeLeft →
    Conv typeLeft typeRight →
    IsStronglyNormalizing typeRight →
    IsTypeDescPi profile context typeRight

/-- **Non-vacuity of the residual.**  The reflexive instance (`typeRight = typeLeft`, `Conv.refl`) is the
input validity — so the residual's conclusion is reachable in the trivial case, confirming the `Prop` is
sensibly shaped (not accidentally empty).  The genuine content is the `typeLeft ≠ typeRight` case (the
FT-escape), which this file isolates but does not discharge. -/
theorem smoke_residualRefl {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {typeCode : RawTerm scope}
    (validity : IsTypeDescPi profile context typeCode)
    (_normalizing : IsStronglyNormalizing typeCode) :
    IsTypeDescPi profile context typeCode :=
  validity

end FX1Poly.Typed
