import FX1Poly.Core.StratifiedReducibleTypeNeutral
import FX1Poly.Typed.ConvContextPreservesPiValidityFormationFragment

/-! # FX1Poly/Typed/ConvContextPiValidityModelNeutral
    — semantic neutral-type validity is CONTEXT-UNIFORM (the model's load-bearing property for GCC-5's open core)

## Where this sits

`ConvContextPreservesPiValidity` (`#1092`) is the single residual to which both open grown-metatheory
release blockers reduce — GCC-5 grown context-conversion (`#842`) AND SRD-2 master subject reduction
(`#845`), unified in `#1098`: a `Π`-type-code's GROWN validity (`IsTypeDescPi`, i.e. `∃ universe,
HasTypeDescPi ctx (Π D C) universe`) is stable under pointwise context conversion.

`ConvContextPreservesPiValidityFormationFragment` (`#1099`) pinned the boundary: the residual is
UNCONDITIONALLY FREE for the FORMATION fragment (domain/codomain are variables, universe codes, or nested
formers — no type-level computation), and its genuinely-open core is EXACTLY the type-level NEUTRAL
applications `(var f) (var a)` at a universe (typed via `piElim` at the type level) — "there is no further
syntactic fragment to peel off."  That open-neutral case needs the OPEN-context semantic model (a Kripke /
sconing logical relation carrying typing witnesses); the bounded reducibility model is closed-substitution-
based and unfit, and reflection fails at the neutral base case.

## What this file pins (the SEMANTIC half of the neutral reflection)

The open obligation splits into a SEMANTIC side (the type's reducibility interpretation) and a SYNTACTIC
side (transporting the typing WITNESS under context conversion).  This file discharges the SEMANTIC side for
neutral type codes, UNCONDITIONALLY:

  `ReducibleTypeStep` (the stratified reducible-TYPE relation, `StratifiedReducibleType.lean`) is
  **context-free** — its judgment `ReducibleTypeStep lowerReducible typeCode candidate` carries NO typing
  context.  So a NEUTRAL type code's semantic validity (a reducibility candidate, via the shipped
  unconditional `ReducibleTypeStep.reducibleOfNeutral`) holds UNIFORMLY in every context — the
  context-uniformity the open logical relation requires of the neutral-type interpretation.  This is the
  reason the model's neutral case is "free on the semantic side": context conversion is invisible to the
  semantic interpretation of a neutral type.

What this does NOT yet supply (the genuine residual `#1092`, still open): the SYNTACTIC reflection — carrying
the TYPING WITNESS (`IsTypeDescPi` derivation) of a neutral type-level application across the context
conversion.  That witness is what the SN candidate alone does not carry; transporting it for `(var f)(var a)`
re-assembles the type-level `piElim` under the target, which IS GCC-5.  The open logical relation must be a
TYPED reducibility (pairing the semantic candidate with a typing derivation), and its neutral reflection
reconstructs the typing from the var rules for `f` / `a` (context-conversion-trivial) plus `Π`-shape
preservation across `Conv` (the shipped `Conv.piTyCode_injective`, `#865`) — that reconstruction is the
remaining model brick.

## Substrate in hand for the typed model (firings landing toward `#842`)

  * `Step.reflectRename` (`StepRenameReflectAssembly.lean`) — the full arbitrary-renaming `Step`
    reflection-with-image, the Kripke-arrow-CR3 ingredient.
  * `kripkeArrow_neutralBackwardClosure` (`KripkeCandidateRenameClosure.lean`) — CR3 for the Kripke arrow,
    completing its CR bundle (CR1/CR2/CR3); the neutral-application reducibility member at the term level.
  * `Conv.piTyCode_injective` (`#865`) — `Π`-shape preservation across `Conv`, for the neutral reflection's
    function re-typing.

## Zero-axiom verification

`ReducibleTypeStep.reducibleOfNeutral` is the shipped unconditional neutral-type reducibility (induction on
`IsNeutral`, no context); this file only instantiates it at two distinct contexts to expose the
context-uniformity.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **Semantic neutral-type validity is CONTEXT-FREE.**  A neutral type code is `ReducibleTypeStep`-reducible
(with a reducibility candidate) — and crucially this judgment carries NO typing context (note this theorem
takes NONE), so the semantic validity holds identically under ANY context, in particular under both sides of
the pointwise-`Conv` context conversion of the `ConvContextPreservesPiValidity` residual (`#1092`).  Context
conversion acts as the IDENTITY on the semantic neutral-type interpretation — this is the SEMANTIC half of the
residual's open neutral core, discharged unconditionally by the shipped unconditional
`ReducibleTypeStep.reducibleOfNeutral` (the `noWeakHeadStep` weak-head-normality plus the non-`Π` /
non-universe root guards).  The genuinely-open residual is therefore isolated entirely to the SYNTACTIC
reflection that carries the `IsTypeDescPi` typing WITNESS across the conversion — the typed neutral
reflection, which (re-assembling the type-level `piElim` for `(var f)(var a)` under the converted context) is
GCC-5 itself, the irreducible open obligation for the typed logical relation. -/
theorem neutralTypeCodeSemanticReducibilityIsContextFree {scope : Nat}
    {lowerReducible : RawTerm scope → (RawTerm scope → Prop) → Prop}
    {typeCode : RawTerm scope} (neutral : IsNeutral typeCode) :
    ∃ candidate : RawTerm scope → Prop, ReducibleTypeStep lowerReducible typeCode candidate :=
  ReducibleTypeStep.reducibleOfNeutral neutral

/-- **Smoke: a variable type code is semantically reducible, context-free.**  The simplest neutral type code
— a bare de Bruijn variable `var index` used as a type — is `ReducibleTypeStep`-reducible with NO typing
context, so its semantic validity is identical under any two `Conv`-related contexts.  A variable is the base
case the open type-level neutral reflection bottoms out at: under context conversion its typing transfers by
the var rule + the pointwise `Conv` on the looked-up classifier (the non-circular leaf), whereas the neutral
APPLICATION `(var f)(var a)` re-assembles the type-level `piElim` (the genuinely-open residual = GCC-5). -/
theorem smoke_variableTypeCodeSemanticReducibilityIsContextFree {scope : Nat}
    {lowerReducible : RawTerm scope → (RawTerm scope → Prop) → Prop} (index : Fin scope) :
    ∃ candidate : RawTerm scope → Prop,
      ReducibleTypeStep lowerReducible (.mkGen .gen_var index .childNil) candidate :=
  neutralTypeCodeSemanticReducibilityIsContextFree (IsNeutral.var index)

end FX1Poly.Typed
