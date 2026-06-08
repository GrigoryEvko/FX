import FX1Poly.Typed.HasTypeDescPi
import FX1Poly.Core.StepStarConfluence

/-! # FX1Poly/Typed/PiElimClassifierConvResidual
    — ★ a REFUTED over-approximation of the grown context-conversion piElim residual (GrownCtxConv-5, #842):
      the SN-only type-Conv-closure is TOO WEAK (false); the genuine residual is the TYPED-reducibility logical
      relation, NOT a context-free reducibility/SN escape

## The root cause, verified against the rule

`HasTypeDescPiContextConversion.lean` records the verified root cause of the lone-hard `piElim` arm of grown
context-conversion: `HasTypeDescPi.piElim` carries NO `D : Type` / `C : Type` typing premises (only
`function : Π D C` and `argument : D`), so when the function's IH gives `function : F'` under the target
context with `Conv F' (Π D C)`, re-typing it at the EXACT `Π D C` (to re-apply `piElim`) needs the conv-rule
reclassifier `Π D C` to be a VALID TYPE under the target — i.e. **`IsType` respects `Conv`** (`IsType T →
Conv T S → IsType S`).  Via confluence this would require subject EXPANSION on the `S`-side, which is FALSE in
general — so it must come from VALIDITY-via-the-fundamental-theorem, strictly stronger than SR.

## ★ Firing-24 correction: the SN-restricted simplification is UNSOUND

A first cut (firing-23) tried to simplify, after WfContext-threading, to a pure type-Conv-closure restricted
to STRONGLY-NORMALIZING `S`: `IsTypeDescPi T → Conv T S → IsStronglyNormalizing S → IsTypeDescPi S`.  That is
FALSE.  COUNTEREXAMPLE: `T = Type@0` and `S = (λx. Type@0) (λz. z z)`.

  * `λz. z z` is a NORMAL FORM (its body `z z` is a neutral application of a variable — no β-redex), so `S`
    β-reduces in ONE step to `Type@0` (the `λx`-body, with the unused `x`), which is normal — `S` is SN.
  * `S ⤳β Type@0 = T`, so `Conv T S`.
  * `T = Type@0` is a valid type (`Type@0 : Type@1`).
  * yet `S` is UNTYPED: the only rule typing an application is `piElim`, which would need the argument
    `λz. z z : D`; but `λz. z z` is untypable (the self-application `z z` forces `z : Π D' C'` AND `z : D'`,
    whence `Π D' C' ≡ D'` by uniqueness, impossible — the occurs-check).

So strong normalization (and, equally, context-FREE reducibility — the same `S` is `ReducibleTypeStep`-reducible
by head-expanding to the universe `Type@0`) does NOT imply typedness.  The restriction must be to the genuine
WELL-TYPED / TYPED-reducible fragment, where the type's COMPONENTS are themselves typed — which is exactly the
fundamental theorem, NOT a side condition layerable onto context-free reducibility.

## What this means for GrownCtxConv-5

The `reducible → typed` ESCAPE is FALSE for context-free reducibility (and for bare SN).  Hence GrownCtxConv-5
is NOT reducible to an SN/reducibility Conv-closure; its genuine residual remains the context conversion of
`Π`-validity `ConvContextPreservesPiValidity` (#1092) — discharged only by the TYPED logical relation that
carries typing alongside reducibility (the `TypedTypeValidityBoxed` direction, #1110), with validity DERIVED
structurally (not a context-free escape).  This file is retained as a NEGATIVE result pinning down why the
tempting SN/reducibility simplification fails — a guardrail against re-deriving it.

## What this file ships

`IsTypeDescPiRespectsConvOnStronglyNormalizing` — the SN-only type-Conv-closure, named so the negative finding
above can refer to it (it is the FALSE over-approximation, NOT a sound residual).  `smoke_residualRefl` is the
true reflexive instance (the only case that holds unconditionally).

## Zero-axiom verification

A `Prop` definition plus a one-line reflexive smoke.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Core.StepStar FX1Poly.Universe FX1Poly.Foundation

/-- **★ The SN-only type-Conv-closure — a REFUTED over-approximation, NOT a sound residual.**  Reads: a type
`Conv`-equal to a VALID type and itself STRONGLY NORMALIZING is a valid type.  This is FALSE (see the file
header's counterexample `(λx. Type@0) (λz. z z)`, which is SN and `Conv Type@0` yet untyped): strong
normalization (and context-free reducibility) does NOT imply typedness, because ill-typed terms can be SN and
can head-expand to universes.  Named only so the negative finding can cite it.  The GENUINE residual of the
grown context-conversion piElim arm (GrownCtxConv-5, #842) is the context conversion of `Π`-validity
(`ConvContextPreservesPiValidity`, #1092), discharged by the TYPED-reducibility logical relation
(`TypedTypeValidityBoxed`, #1110) with validity DERIVED — never by this context-free SN escape. -/
def IsTypeDescPiRespectsConvOnStronglyNormalizing (profile : PolyProfile) : Prop :=
  ∀ {scope : Nat} {context : TypingContext profile scope} {typeLeft typeRight : RawTerm scope},
    IsTypeDescPi profile context typeLeft →
    Conv typeLeft typeRight →
    IsStronglyNormalizing typeRight →
    IsTypeDescPi profile context typeRight

/-- **The only unconditionally-true instance of the over-approximation: the reflexive case.**  When
`typeRight = typeLeft` (`Conv.refl`) the conclusion IS the input validity.  This is the sole case that holds;
the general statement is false (file header).  Confirms the `Prop` is not accidentally empty without claiming
it as a residual. -/
theorem smoke_residualRefl {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {typeCode : RawTerm scope}
    (validity : IsTypeDescPi profile context typeCode)
    (_normalizing : IsStronglyNormalizing typeCode) :
    IsTypeDescPi profile context typeCode :=
  validity

end FX1Poly.Typed
