import FX1Poly.Typed.HasTypeDesc
import FX1Poly.Core.ConvSubstRename
import FX1Poly.Core.RawConfluence

/-! # FX1Poly/Typed/HasTypeDescContextConversion — CONTEXT-CONVERSION for the FORMATION engine (#814, part 1)
    (typing stable under a pointwise-`Conv`-replaced context, leaf fragment — the clean half)

CONTEXT-CONVERSION — typing preserved when the context is replaced by a pointwise-`Conv`-related one —
is the brick that unblocks the former-DOMAIN SR congruence (#458/SN-055): when a type-former's domain
steps (`domain ⤳ domain'`, so `Conv domain domain'`), the codomain typed under `cons domain` must
re-type under `cons domain'`.

The full grown-engine version (`HasTypeDescPi`) needs the Π-reconstruction validity (its `piIntro` /
`piElim` arms) and, for its `ofFormation` arm, THIS lemma — the FORMATION engine's context-conversion.
`HasTypeDesc` is the leaf fragment (only `var` / `conv` / `universeFormation` / `genFormation`; no
`piIntro` / `piElim` / `ofFormation`), so its context-conversion needs NO `WfContext` and no Π
reconstruction — the clean half, shipped here; the grown half follows.

## The existential formulation

`HasTypeDesc Γ t T → (∀ i, Conv (Γ.lookup i) (Γ'.lookup i)) → ∃ T', Conv T T' ∧ HasTypeDesc Γ' t T'`.
The existential keeps the `var` arm a one-liner (`var Γ' i` types at `Γ'.lookup i`, related by
`contextConv i`) — no need to type the OLD entry under the NEW context (the circularity that sinks the
exact-classifier var arm).

## Structure (mutual, mirroring renameRespectingContext ⋈ renameRespectingTelescope)

`HasTypeDesc.convContext` (4 arms) ⋈ `DescTelescope.convTelescope` (nil/cons).  The TELESCOPE conclusion
is EXACT: heads sit at universe codes, conv-backed inline through `convBackToUniverseCode`
(`universeFormation` supplies the reclassifier typing), so the spine reconstructs exactly — what
`genFormation` re-fires against.

  * `var` — `var Γ' index` + `contextConv index`.
  * `conv` — recurse the premise; compose the conversions.
  * `universeFormation` — context-insensitive (no variable); re-fire at the same level.
  * `genFormation` — recurse the premise spine through `convTelescope`, re-fire `genFormation`.

## Zero-axiom verification

Self-recursion + the `conv` rule + `universeFormation` + `Conv.rename`/`Conv.refl`/`Conv.sym`/`Conv.trans`
+ the `lookup`-of-`cons` definitional unfolds.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Audit-gated.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **Conv-back to a universe code (formation engine).**  A subject typed at any classifier `reachedCode`
convertible FROM the universe code `Type@(level, flag)` is typed at that universe code itself —
`universeFormation` supplies the reclassifier typing, so the `conv` rule closes it. -/
theorem HasTypeDesc.convBackToUniverseCode {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject reachedCode : RawTerm scope}
    {level : LevelExpr} {flag : UniverseFlag}
    (typedAtReached : HasTypeDesc profile context subject reachedCode)
    (universeConvToReached : Conv (universeCodeCell level flag) reachedCode) :
    HasTypeDesc profile context subject (universeCodeCell level flag) :=
  HasTypeDesc.conv level.lsucc flag typedAtReached universeConvToReached.sym
    (HasTypeDesc.universeFormation context level flag)

/-- **The context-condition extends under a shared binding.**  A pointwise-`Conv`-related context
survives consing the SAME `bindingType` on both: index `0` looks up the shared `bindingType` (weakened)
on both sides (`Conv.refl`); index `k+1` looks up the related entries (weakened), `Conv`-related by
`Conv.rename` of the original condition.  Generator-agnostic — reused by the grown-engine version. -/
theorem convContextCondition_cons {profile : PolyProfile} {scope : Nat}
    {sourceContext targetContext : TypingContext profile scope} (bindingType : RawTerm scope)
    (contextConv : ∀ index : Fin scope,
      Conv (sourceContext.lookup index) (targetContext.lookup index)) :
    ∀ index : Fin (scope + 1),
      Conv ((sourceContext.cons bindingType).lookup index)
        ((targetContext.cons bindingType).lookup index) := by
  intro index
  obtain ⟨indexValue, indexBound⟩ := index
  cases indexValue with
  | zero =>
      show Conv (RawTerm.rename RawRenaming.weaken bindingType)
        (RawTerm.rename RawRenaming.weaken bindingType)
      exact Conv.refl _
  | succ k =>
      show Conv (RawTerm.rename RawRenaming.weaken
            (sourceContext.lookup ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩))
        (RawTerm.rename RawRenaming.weaken
            (targetContext.lookup ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩))
      exact Conv.rename RawRenaming.weaken (contextConv ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩)

mutual

/-- **Context-conversion for the formation engine (existential classifier).**  A `HasTypeDesc`
derivation survives replacing the context by a pointwise-`Conv`-related one — the subject is typed at a
`Conv`-equal classifier under the new context.  Recursion on the derivation. -/
theorem HasTypeDesc.convContext {profile : PolyProfile} {scope : Nat}
    {sourceContext : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDesc profile sourceContext subject classifier) :
    ∀ (targetContext : TypingContext profile scope),
      (∀ index : Fin scope, Conv (sourceContext.lookup index) (targetContext.lookup index)) →
      ∃ classifier', Conv classifier classifier' ∧
        HasTypeDesc profile targetContext subject classifier' :=
  match derivation with
  | .var context index => fun targetContext contextConv =>
      ⟨targetContext.lookup index, contextConv index, HasTypeDesc.var targetContext index⟩
  | .conv levelExpr flag typed converts _reclassifierTyped => fun targetContext contextConv => by
      obtain ⟨classifier', convClassifierToClassifier', typedAtClassifier'⟩ :=
        HasTypeDesc.convContext typed targetContext contextConv
      exact ⟨classifier', Conv.trans converts.sym convClassifierToClassifier', typedAtClassifier'⟩
  | .universeFormation _context levelExpr flag => fun targetContext _contextConv =>
      ⟨universeCodeCell levelExpr.lsucc flag, Conv.refl _,
        HasTypeDesc.universeFormation targetContext levelExpr flag⟩
  | .genFormation _context generator payload children levels flag rule isFormation premises =>
      fun targetContext contextConv =>
      ⟨rule.outputType scope levels flag, Conv.refl _,
        HasTypeDesc.genFormation targetContext generator payload children levels flag rule isFormation
          (DescTelescope.convTelescope premises targetContext contextConv)⟩

/-- **Context-conversion for the formation premise telescope (exact).**  Mirrors `convContext` over the
spine; each head re-typed at its own universe code via `convBackToUniverseCode`. -/
theorem DescTelescope.convTelescope {profile : PolyProfile}
    {baseScope currentDepth : Nat} {binderShifts : List Nat}
    {sourceContext : TypingContext profile (baseScope + currentDepth)}
    {levels : List LevelExpr} {flag : UniverseFlag}
    {children : RawTermChildren binderShifts baseScope}
    (telescope : DescTelescope profile sourceContext levels flag children) :
    ∀ (targetContext : TypingContext profile (baseScope + currentDepth)),
      (∀ index : Fin (baseScope + currentDepth),
        Conv (sourceContext.lookup index) (targetContext.lookup index)) →
      DescTelescope profile targetContext levels flag children :=
  match telescope with
  | .nil _sourceContext flag => fun targetContext _contextConv =>
      DescTelescope.nil targetContext flag
  | .cons _sourceContext head headLevel restLevels flag rest headTyped restTyped =>
      fun targetContext contextConv => by
        obtain ⟨headClassifier', headConv', headAtClassifier'⟩ :=
          HasTypeDesc.convContext headTyped targetContext contextConv
        have headTyped' :
            HasTypeDesc profile targetContext head (universeCodeCell headLevel flag) :=
          headAtClassifier'.convBackToUniverseCode headConv'
        refine DescTelescope.cons targetContext head headLevel restLevels flag rest headTyped' ?_
        exact DescTelescope.convTelescope restTyped (targetContext.cons head)
          (convContextCondition_cons head contextConv)

end

end FX1Poly.Typed
