import FX1Poly.Typed.FlatDescTelescope

/-! # FX1Poly/Typed/HasTypeDescFlat
    — the FLAT-former typing judgment: the non-dependent `[0,0]` type-code formers now TYPE

`DescTelescopeReach` proved the formation engine's premise telescope forces CUMULATIVE binderShifts, so the
non-dependent two-child formers `product` / `sum` / `either` / `arrow` / `equiv` (all binderShifts `[0,0]`) are
structurally unreachable by `genFormation` — adding a `typingRuleDescOf` row for them would be vacuous.
`FlatDescTelescope` (the prior increment) supplied the flat premise shape — all sibling children typed under the
SAME base context — that DOES represent `[0,0]`.  This file closes the #934 capability: a standalone typing
judgment `HasTypeDescFlat` that types the flat formers via a `FlatDescTelescope` premise.

## Why a standalone judgment (not a new `HasTypeDesc` arm)

The non-dependent formers genuinely need a NEW typing rule (the cumulative `genFormation` premise can't be
built for them).  Adding that rule as a constructor to the `HasTypeDesc` / `DescTelescope` MUTUAL block would
regenerate the block's recursor and risk every match-recursion over it (`convTelescope`, telescope SR, the FT
arms).  Instead `HasTypeDescFlat` is STANDALONE — defined after the mutual block, referencing `HasTypeDesc` only
inside its `FlatDescTelescope` premise (the children's typings).  This is exactly the project's existing pattern:
the grown `HasTypeDescPi` is likewise a separate engine layer, not an arm of `HasTypeDesc`.  So the flat engine
is purely ADDITIVE — zero cascade, zero mutual-block change — and its children still flow through the main
`HasTypeDesc`, so it is a genuine extension layer, not a disconnected judgment.

## The capability and the partition

`productFlatFormationSmoke` is the headline: `product (Type@0) (Type@0)` TYPES (at `Type@(lmax 1 1)`) — the
non-dependent former `DescTelescope.noFlatTwoChildTelescope` proved unreachable now has a typing derivation.
`typingRuleDescOf_productCode_none` + `flatTypingRuleDescOf_productCode` record the honest PARTITION: the
cumulative table (`typingRuleDescOf`) and the flat table (`flatTypingRuleDescOf`) have disjoint domains — Π/Σ/
list/option are cumulative, product/sum/either/arrow/equiv are flat — so the two engines cover the type-formers
without overlap.

## Zero-axiom verification

`flatTypingRuleDescOf_outputIsUniverseFormer` mirrors the shipped `typingRuleDescOf_outputIsUniverseFormer`
(nested `by_cases` over the five flat formers, `subst` + `Option.some.inj` + `rw`, the `exfalso` non-former
branch via `unfold` + `if_neg` chain + `contradiction`).  The `rfl` table lemmas and the smoke are direct
constructor applications.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- The per-generator description table for the FLAT (non-dependent) type-code formers — the `[0,0]` formers
`DescTelescope` cannot reach.  All five (`product` / `sum` / `either` / `arrow` / `equiv`) share
`universeFormerOutput` (the former lives at the `lmax` of its children's levels, exactly as the dependent
formers).  The flat analogue of `typingRuleDescOf`; its domain is disjoint from `typingRuleDescOf`'s. -/
def flatTypingRuleDescOf (generator : Generator) : Option TypingRuleDesc :=
  if generator = .gen_productCode then some { outputType := universeFormerOutput }
  else if generator = .gen_sumCode then some { outputType := universeFormerOutput }
  else if generator = .gen_eitherCode then some { outputType := universeFormerOutput }
  else if generator = .gen_arrowCode then some { outputType := universeFormerOutput }
  else if generator = .gen_equivCode then some { outputType := universeFormerOutput }
  else none

/-- `gen_productCode` is a flat former (metadata check). -/
theorem flatTypingRuleDescOf_productCode :
    flatTypingRuleDescOf .gen_productCode = some { outputType := universeFormerOutput } := rfl

/-- `gen_sumCode` is a flat former (metadata check). -/
theorem flatTypingRuleDescOf_sumCode :
    flatTypingRuleDescOf .gen_sumCode = some { outputType := universeFormerOutput } := rfl

/-- `gen_eitherCode` is a flat former (metadata check). -/
theorem flatTypingRuleDescOf_eitherCode :
    flatTypingRuleDescOf .gen_eitherCode = some { outputType := universeFormerOutput } := rfl

/-- `gen_arrowCode` is a flat former (metadata check). -/
theorem flatTypingRuleDescOf_arrowCode :
    flatTypingRuleDescOf .gen_arrowCode = some { outputType := universeFormerOutput } := rfl

/-- `gen_equivCode` is a flat former (metadata check). -/
theorem flatTypingRuleDescOf_equivCode :
    flatTypingRuleDescOf .gen_equivCode = some { outputType := universeFormerOutput } := rfl

/-- **The flat/cumulative partition.**  `gen_productCode` is NOT a cumulative former — `typingRuleDescOf`
returns `none` for it (it lives in `flatTypingRuleDescOf` instead).  Witnesses that the two engines cover the
type-formers without overlap. -/
theorem typingRuleDescOf_productCode_none :
    typingRuleDescOf .gen_productCode = none := rfl

/-- **Every flat formation rule outputs a universe code.**  The flat analogue of
`typingRuleDescOf_outputIsUniverseFormer`: the cascade-death metadata for the flat-former family. -/
theorem flatTypingRuleDescOf_outputIsUniverseFormer {generator : Generator} {rule : TypingRuleDesc}
    (isFlatFormation : flatTypingRuleDescOf generator = some rule) :
    rule.outputType = universeFormerOutput := by
  by_cases hProduct : generator = .gen_productCode
  · subst hProduct
    have hRule : rule = { outputType := universeFormerOutput } := Option.some.inj isFlatFormation.symm
    rw [hRule]
  · by_cases hSum : generator = .gen_sumCode
    · subst hSum
      have hRule : rule = { outputType := universeFormerOutput } := Option.some.inj isFlatFormation.symm
      rw [hRule]
    · by_cases hEither : generator = .gen_eitherCode
      · subst hEither
        have hRule : rule = { outputType := universeFormerOutput } := Option.some.inj isFlatFormation.symm
        rw [hRule]
      · by_cases hArrow : generator = .gen_arrowCode
        · subst hArrow
          have hRule : rule = { outputType := universeFormerOutput } := Option.some.inj isFlatFormation.symm
          rw [hRule]
        · by_cases hEquiv : generator = .gen_equivCode
          · subst hEquiv
            have hRule : rule = { outputType := universeFormerOutput } := Option.some.inj isFlatFormation.symm
            rw [hRule]
          · exfalso
            dsimp only [flatTypingRuleDescOf] at isFlatFormation
            rw [if_neg hProduct, if_neg hSum, if_neg hEither, if_neg hArrow, if_neg hEquiv] at isFlatFormation
            contradiction

/-- **A flat formation rule's generator is not `gen_var`.**  The flat twin of `formationRuleImpliesNotVariable`:
`gen_var` is not one of the five flat formers, so `flatTypingRuleDescOf gen_var = none ≠ some rule`.  Consumed by
the flat renaming/weakening cell-reconstruction (`RawTerm.rename_mkGen_of_ne_var` needs `generator ≠ gen_var`). -/
theorem flatFormationRuleImpliesNotVariable {generator : Generator} {rule : TypingRuleDesc}
    (isFlatFormation : flatTypingRuleDescOf generator = some rule) :
    generator ≠ Generator.gen_var := by
  intro isVariable
  subst isVariable
  dsimp only [flatTypingRuleDescOf] at isFlatFormation
  rw [if_neg (fun isProduct => Generator.noConfusion isProduct),
    if_neg (fun isSum => Generator.noConfusion isSum),
    if_neg (fun isEither => Generator.noConfusion isEither),
    if_neg (fun isArrow => Generator.noConfusion isArrow),
    if_neg (fun isEquiv => Generator.noConfusion isEquiv)] at isFlatFormation
  cases isFlatFormation

/-- **A flat formation rule IS the universe-former rule (full structure).**  The flat twin of
`formationRuleIsUniverseFormer`: since `TypingRuleDesc` has exactly the `outputType` field, the output-type
equation (`flatTypingRuleDescOf_outputIsUniverseFormer`) upgrades to the structure equation
`rule = { outputType := universeFormerOutput }`, what a cell-RECONSTRUCTION consumer needs (`obtain rfl`). -/
theorem flatFormationRuleIsUniverseFormer {generator : Generator} {rule : TypingRuleDesc}
    (isFlatFormation : flatTypingRuleDescOf generator = some rule) :
    rule = { outputType := universeFormerOutput } := by
  have outputIsFormer : rule.outputType = universeFormerOutput :=
    flatTypingRuleDescOf_outputIsUniverseFormer isFlatFormation
  cases rule
  rw [← outputIsFormer]

/-- **The flat-former typing judgment.**  A standalone layer (NOT mutual with `HasTypeDesc`, mirroring the grown
`HasTypeDescPi`) that types the non-dependent `[0,0]` type-code formers via a `FlatDescTelescope` premise — each
child a type under the SAME base context.  The children's typings flow through the main `HasTypeDesc` (inside the
`FlatDescTelescope`), so this is a genuine extension layer.  One arm `flatFormation`, table-driven over
`flatTypingRuleDescOf` (P13 — a future flat former is one more table row, never a new arm). -/
inductive HasTypeDescFlat (profile : PolyProfile) :
    {scope : Nat} → TypingContext profile scope → RawTerm scope → RawTerm scope → Prop where
  | flatFormation {scope : Nat} (context : TypingContext profile scope)
      (generator : Generator) (payload : generator.payload scope)
      (children : RawTermChildren generator.binderShifts scope)
      (levels : List LevelExpr) (flag : UniverseFlag) (rule : TypingRuleDesc)
      (isFlatFormation : flatTypingRuleDescOf generator = some rule)
      (premise : FlatDescTelescope profile context flag levels children) :
      HasTypeDescFlat profile context (.mkGen generator payload children)
        (rule.outputType scope levels flag)

/-- **★ THE #934 CAPABILITY.**  `product (Type@0) (Type@0)` TYPES at `Type@(lmax 1 1)` in the flat engine — the
non-dependent former `DescTelescope.noFlatTwoChildTelescope` proved unreachable by the cumulative engine now has
a typing derivation, via the flat premise (`productTypeZeroFlatPremise`) and the `gen_productCode` table row. -/
theorem productFlatFormationSmoke (profile : PolyProfile) (flag : UniverseFlag) :
    HasTypeDescFlat profile TypingContext.empty
      (.mkGen .gen_productCode () (flatProductTypeZeroChildren flag))
      (universeCodeCell (lmaxAll [LevelExpr.lzero.lsucc, LevelExpr.lzero.lsucc]) flag) :=
  HasTypeDescFlat.flatFormation TypingContext.empty .gen_productCode ()
    (flatProductTypeZeroChildren flag) [LevelExpr.lzero.lsucc, LevelExpr.lzero.lsucc] flag
    { outputType := universeFormerOutput } flatTypingRuleDescOf_productCode
    (productTypeZeroFlatPremise profile flag)

/-- **`sum (Type@0) (Type@0)` TYPES** at `Type@(lmax 1 1)` in the flat engine — the `gen_sumCode` twin of
`productFlatFormationSmoke`.  The children (`flatProductTypeZeroChildren`) and the premise
(`productTypeZeroFlatPremise`) are FORMER-AGNOSTIC — they type two `Type@0` codes under the base context, never
mentioning the generator — so the same witnesses feed every flat former; only the generator and its
`flatTypingRuleDescOf` row differ. -/
theorem sumFlatFormationSmoke (profile : PolyProfile) (flag : UniverseFlag) :
    HasTypeDescFlat profile TypingContext.empty
      (.mkGen .gen_sumCode () (flatProductTypeZeroChildren flag))
      (universeCodeCell (lmaxAll [LevelExpr.lzero.lsucc, LevelExpr.lzero.lsucc]) flag) :=
  HasTypeDescFlat.flatFormation TypingContext.empty .gen_sumCode ()
    (flatProductTypeZeroChildren flag) [LevelExpr.lzero.lsucc, LevelExpr.lzero.lsucc] flag
    { outputType := universeFormerOutput } flatTypingRuleDescOf_sumCode
    (productTypeZeroFlatPremise profile flag)

/-- **`either (Type@0) (Type@0)` TYPES** at `Type@(lmax 1 1)` in the flat engine (the `gen_eitherCode` twin). -/
theorem eitherFlatFormationSmoke (profile : PolyProfile) (flag : UniverseFlag) :
    HasTypeDescFlat profile TypingContext.empty
      (.mkGen .gen_eitherCode () (flatProductTypeZeroChildren flag))
      (universeCodeCell (lmaxAll [LevelExpr.lzero.lsucc, LevelExpr.lzero.lsucc]) flag) :=
  HasTypeDescFlat.flatFormation TypingContext.empty .gen_eitherCode ()
    (flatProductTypeZeroChildren flag) [LevelExpr.lzero.lsucc, LevelExpr.lzero.lsucc] flag
    { outputType := universeFormerOutput } flatTypingRuleDescOf_eitherCode
    (productTypeZeroFlatPremise profile flag)

/-- **`arrow (Type@0) (Type@0)` TYPES** at `Type@(lmax 1 1)` in the flat engine — the non-dependent function-type
code (`gen_arrowCode`, distinct from the dependent `piTyCode`). -/
theorem arrowFlatFormationSmoke (profile : PolyProfile) (flag : UniverseFlag) :
    HasTypeDescFlat profile TypingContext.empty
      (.mkGen .gen_arrowCode () (flatProductTypeZeroChildren flag))
      (universeCodeCell (lmaxAll [LevelExpr.lzero.lsucc, LevelExpr.lzero.lsucc]) flag) :=
  HasTypeDescFlat.flatFormation TypingContext.empty .gen_arrowCode ()
    (flatProductTypeZeroChildren flag) [LevelExpr.lzero.lsucc, LevelExpr.lzero.lsucc] flag
    { outputType := universeFormerOutput } flatTypingRuleDescOf_arrowCode
    (productTypeZeroFlatPremise profile flag)

/-- **`equiv (Type@0) (Type@0)` TYPES** at `Type@(lmax 1 1)` in the flat engine (the `gen_equivCode` twin) —
completing the five-former flat-formation corpus (product / sum / either / arrow / equiv all TYPE). -/
theorem equivFlatFormationSmoke (profile : PolyProfile) (flag : UniverseFlag) :
    HasTypeDescFlat profile TypingContext.empty
      (.mkGen .gen_equivCode () (flatProductTypeZeroChildren flag))
      (universeCodeCell (lmaxAll [LevelExpr.lzero.lsucc, LevelExpr.lzero.lsucc]) flag) :=
  HasTypeDescFlat.flatFormation TypingContext.empty .gen_equivCode ()
    (flatProductTypeZeroChildren flag) [LevelExpr.lzero.lsucc, LevelExpr.lzero.lsucc] flag
    { outputType := universeFormerOutput } flatTypingRuleDescOf_equivCode
    (productTypeZeroFlatPremise profile flag)

end FX1Poly.Typed
