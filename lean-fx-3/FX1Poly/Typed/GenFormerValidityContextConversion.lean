import FX1Poly.Typed.HasTypeDescPiContextConversion
import FX1Poly.Typed.HasTypeDescContextConversion
import FX1Poly.Typed.HasTypeDescPiVarInversion

/-! # FX1Poly/Typed/GenFormerValidityContextConversion
    — the TABLE-GENERIC genFormationPi former step of the GrownCtxConv-5 residual

The GrownCtxConv-5 residual `ConvContextPreservesPiValidity` (`#1092`) recurses structurally on a type code; its
former arm must transport a `genFormationPi` former's validity across a context conversion.  The per-former Π
(`#1120`) and Σ (`#1121`) steps did this for the two-child formers `piTyCodeCell` / `sigmaTyCodeCell` via their
bespoke component inversions.  This file ships the TABLE-GENERIC version — ONE theorem covering EVERY
`genFormationPi` type-code former (Π, Σ, list, option, id, equiv, and any future row of `typingRuleDescOf`) — by
operating on the premise telescope directly rather than per-former component inversions.  It is the cascade-free
consolidation (FRAME-2 / `#882`): adding a new type-code former to `typingRuleDescOf` needs ZERO new
context-conversion arms — this theorem already covers it.

## The two pieces

  * `DescTelescopePi.convTelescopeFromChildIH` — the telescope-validity transport, the reusable primitive.  A
    grown premise telescope (the cumulative dependent spine of a former's children, each a type at its level)
    transports across a pointwise-`Conv` context conversion GIVEN a per-child type-code-validity IH
    (`childConverts`, universe-code-PRESERVING and scope-polymorphic).  Structural recursion over the telescope:
    each head re-types via the IH, each tail recurses under the cons-lifted condition `convContextCondition_cons`.
    The validity-rebuild analogue of `convTelescopeOfPiElimArm` (GrownCtxConv-3), gated on the recursive
    type-code IH instead of the general `piElimArm`.

  * `HasTypeDescPi.genFormerValidityContextConversion` — the generic former step.  A `genFormationPi`-formed
    former `mkGen generator payload children` (premises in hand as the constructor field) re-forms under the
    converted target by transporting its premise telescope (via `convTelescopeFromChildIH childConverts`) and
    re-firing `genFormationPi`.  Conclusion is at the SAME `rule.outputType` (a universe code for type-code
    formers).  This is the `genFormationPi` arm of the eventual recursive `TypeCodeValidityContextConversion`
    assembly: there the `childConverts` is the assembly's own recursive call on the structurally-smaller telescope
    children.

## Why "semantic types are Conv-closed by construction" — generically

A former's validity under the target is REBUILT from its (transported) premise children via the formation rule,
never carried as a black box.  This is the same insight as the Π step (`#1120`), now uniform across the whole
`typingRuleDescOf` table — the telescope carries arbitrarily many children at cumulative binder depths, and the
transport threads the per-child IH through them with the cons-lift at each level.

## Coverage and the open core

With this generic former step + the universe leaf (free) + the bare-var leaf (`varConvertedUnderContextConv`,
`#1119` substrate, unconditional), the residual's recursion is covered on EVERY arm EXCEPT the app-headed neutral
leaf (a type-level neutral application whose argument is an arbitrary term) — that lone leaf is the GTL-20 mutual
fundamental-metatheory bundle (`#1098`).  The flat data formers (product/sum/either/arrow/equiv, the
`HasTypeDescFlat` engine) are NOT on this residual's path — `HasTypeDescPi`'s former arm is exactly
`genFormationPi`, whose formers are only the `typingRuleDescOf` rows.

## Zero-axiom verification

`convTelescopeFromChildIH`: structural recursion over `DescTelescopePi` (nil → nil, cons → IH-head + cons-lifted
recursive tail).  `genFormerValidityContextConversion`: `genFormationPi` re-fired on the transported telescope.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration
audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **The telescope-validity transport** (the reusable primitive).  A grown premise telescope transports across a
pointwise-`Conv` context conversion GIVEN a scope-polymorphic, universe-code-PRESERVING per-child IH
`childConverts`: each head re-types via the IH, each tail recurses under the cons-lifted condition
`convContextCondition_cons`.  The validity-rebuild analogue of `convTelescopeOfPiElimArm` (GrownCtxConv-3), gated
on the recursive type-code IH rather than the general `piElimArm`. -/
theorem DescTelescopePi.convTelescopeFromChildIH {profile : PolyProfile}
    (childConverts : ∀ {childScope : Nat}
        {childSource childTarget : TypingContext profile childScope}
        {childCode : RawTerm childScope} {childLevel : LevelExpr} {childFlag : UniverseFlag},
        HasTypeDescPi profile childSource childCode (universeCodeCell childLevel childFlag) →
        (∀ index : Fin childScope, Conv (childSource.lookup index) (childTarget.lookup index)) →
        HasTypeDescPi profile childTarget childCode (universeCodeCell childLevel childFlag))
    {baseScope currentDepth : Nat} {binderShifts : List Nat}
    {sourceContext : TypingContext profile (baseScope + currentDepth)}
    {levels : List LevelExpr} {flag : UniverseFlag}
    {children : RawTermChildren binderShifts baseScope}
    (telescope : DescTelescopePi profile sourceContext levels flag children) :
    ∀ (targetContext : TypingContext profile (baseScope + currentDepth)),
      (∀ index : Fin (baseScope + currentDepth),
        Conv (sourceContext.lookup index) (targetContext.lookup index)) →
      DescTelescopePi profile targetContext levels flag children :=
  match telescope with
  | .nil _sourceContext flag => fun targetContext _contextConv =>
      DescTelescopePi.nil targetContext flag
  | .cons _sourceContext head headLevel restLevels flag rest headTyped restTyped =>
      fun targetContext contextConv =>
        DescTelescopePi.cons targetContext head headLevel restLevels flag rest
          (childConverts headTyped contextConv)
          (DescTelescopePi.convTelescopeFromChildIH childConverts restTyped
            (targetContext.cons head) (convContextCondition_cons head contextConv))

/-- **The table-generic genFormationPi former step.**  A `genFormationPi`-formed former `mkGen generator payload
children` (premise telescope in hand) re-forms under any pointwise-`Conv`-converted target by transporting its
premise telescope (via `convTelescopeFromChildIH` with the per-child IH `childConverts`) and re-firing
`genFormationPi` — at the SAME `rule.outputType` (a universe code for type-code formers).  ONE theorem covering
EVERY `genFormationPi` type-code former (Π, Σ, list, option, id, equiv, …); the cascade-free consolidation of the
per-former Π (`#1120`) and Σ (`#1121`) steps.  In the eventual recursive `TypeCodeValidityContextConversion`
assembly this is the `genFormationPi` arm, with `childConverts` the assembly's recursive call on the structurally
smaller telescope children. -/
theorem HasTypeDescPi.genFormerValidityContextConversion {profile : PolyProfile}
    (childConverts : ∀ {childScope : Nat}
        {childSource childTarget : TypingContext profile childScope}
        {childCode : RawTerm childScope} {childLevel : LevelExpr} {childFlag : UniverseFlag},
        HasTypeDescPi profile childSource childCode (universeCodeCell childLevel childFlag) →
        (∀ index : Fin childScope, Conv (childSource.lookup index) (childTarget.lookup index)) →
        HasTypeDescPi profile childTarget childCode (universeCodeCell childLevel childFlag))
    {scope : Nat} {sourceContext targetContext : TypingContext profile scope}
    (generator : Generator) (payload : generator.payload scope)
    (children : RawTermChildren generator.binderShifts scope)
    (levels : List LevelExpr) (flag : UniverseFlag)
    (rule : TypingRuleDesc) (isFormation : typingRuleDescOf generator = some rule)
    (premises : DescTelescopePi profile (currentDepth := 0) sourceContext levels flag children)
    (contextConv : ∀ index : Fin scope,
      Conv (sourceContext.lookup index) (targetContext.lookup index)) :
    HasTypeDescPi profile targetContext (.mkGen generator payload children)
      (rule.outputType scope levels flag) :=
  HasTypeDescPi.genFormationPi targetContext generator payload children levels flag rule isFormation
    (DescTelescopePi.convTelescopeFromChildIH childConverts premises targetContext contextConv)

/-- **The universe-preserving bare-variable `childConverts` case.**  A variable typed AS A TYPE CODE (at a
universe) under the source is typed at the SAME universe code under any pointwise-`Conv` target: `invertVar`
(`#1118`) gives `Conv (universe level flag) (sourceContext.lookup index)`, composed with the context-conversion
`Conv` at `index` and re-applying the var rule under the target, then `convBackToUniverseCode` pins the
classifier back to the exact universe code.  The unconditional bare-variable case of the per-child IH
`childConverts` that `genFormerValidityContextConversion` consumes — a type variable's universe membership
transports under context conversion. -/
theorem HasTypeDescPi.variableTypeCodeContextConversion {profile : PolyProfile} {scope : Nat}
    {sourceContext targetContext : TypingContext profile scope}
    {index : Fin scope} {level : LevelExpr} {flag : UniverseFlag}
    (typed : HasTypeDescPi profile sourceContext (variableCell index) (universeCodeCell level flag))
    (contextConv : ∀ idx : Fin scope, Conv (sourceContext.lookup idx) (targetContext.lookup idx)) :
    HasTypeDescPi profile targetContext (variableCell index) (universeCodeCell level flag) :=
  (HasTypeDescPi.ofFormation (HasTypeDesc.var targetContext index)).convBackToUniverseCode
    (Conv.trans typed.invertVar (contextConv index))

end FX1Poly.Typed
