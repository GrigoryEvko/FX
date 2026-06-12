import FX1Poly.Typed.HasTypeDescPi

/-! # FX1Poly/Typed/HasTypeDescPairIntro — the standalone n-ary data-constructor introduction judgment
    for the PAIR value (DI-2: `pair(a, b) : product(A, B)`).

`HasTypeDescDataIntro` (DI-1) types the NULLARY data constructors (`boolTrue` / `boolFalse : boolCode`)
through a fixed-output table — no premise, the constructor is a closed leaf.  The n-ary non-recursive
constructors carry a PREMISE TELESCOPE: `pair(a, b)` inhabits `product(A, B)` only when its components are
typed, `a : A` and `b : B`.  Following the established cascade-free pattern (`HasTypeDescBaseType` for the
nullary base type codes), this is a brand-new standalone judgment — NOT mutual with, NOT an arm of,
`HasTypeDescDataIntro` or `HasTypeDescPi` — so it disturbs no existing recursor and no data-head-untyped
refutation: `pair` is still UNTYPED in the grown engine (`HasTypeDescPi.pairCellHasNoTyping`); this judgment
is a different relation about a different thing.

The components are typed by the GROWN engine `HasTypeDescPi` (the engine that types general terms): a pair of
arbitrary grown-typed terms.  This is what makes the n-ary arm heavier than the nullary / base-type ones —
they were leaves (childless), the pair carries two grown sub-derivations.

  * `pairCell` / `productTypeCell` — the value/type cells (`gen_pair` / `gen_productCode`, both arity-2 with
    `binderShifts = [0, 0]`), inline `mkGen` constructors (no named cell shipped, as for the flat type codes).
  * `HasTypeDescPairIntro` — the judgment: one `pairIntro` arm typing `pair(a, b)` at `product(A, B)` from
    grown `a : A`, `b : B`.
  * `HasTypeDescPairIntro.pairOfUniverseCodesTyped` (★) — the non-vacuous smoke: `pair(Type@0, Type@0) :
    product(Type@1, Type@1)`, the components typed by `ofFormation (universeFormation)`.
  * `HasTypeDescPairIntro.subjectIsPair` / `classifierIsProduct` — the closed-forms inversions (the subject IS
    a `pairCell`, the classifier IS a `productTypeCell`), the DI-2 analogues of
    `HasTypeDescDataIntro.subjectIsBoolConstructor` and the base-type `subjectIsBaseTypeCode`.  These are the
    SR-free canonicity ingredients: a `HasTypeDescPairIntro` derivation pins both subject and classifier
    shapes by a single-arm `cases`.

## Scope and the SR deferral

This file ships the JUDGMENT, the smoke, and the inversions — all SR-free (no reduction step is typed).  The
structural metatheory (SR / SN) of a pair is GrownCtxConv-5-ENTANGLED: `pair(a, b)` steps when a component steps
(`a ↝ a'`), and the reduct `pair(a', b)` re-types only if `a' : A` holds — i.e. it consumes the GROWN master
subject-reduction dispatcher (`SN-055` / GrownCtxConv-5 #842), the known blocker.  So the SR/SN quartet is the
deliberate deferral; the canonicity-relevant inversions are here and unconditional.

## Zero-axiom

A single positive inductive arm; the smoke is a direct `pairIntro` application with `ofFormation`
`universeFormation` sub-derivations; the inversions are single-arm `cases` with `rfl`.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The PAIR introduction judgment.**  A standalone layer (NOT mutual with / NOT an arm of
`HasTypeDescDataIntro` or `HasTypeDescPi`, mirroring `HasTypeDescBaseType`) typing the pair VALUE constructor
at its product type code.  The sole arm: `pair(a, b)` introduces a member of `product(A, B)` from grown
component derivations `a : A` and `b : B`.  Unlike the nullary `HasTypeDescDataIntro`, this carries a premise
telescope (the two grown sub-derivations) — the n-ary shape. -/
inductive HasTypeDescPairIntro (profile : PolyProfile) :
    {scope : Nat} → TypingContext profile scope → RawTerm scope → RawTerm scope → Prop where
  | pairIntro {scope : Nat} (context : TypingContext profile scope)
      (firstValue secondValue firstType secondType : RawTerm scope)
      (firstTyped : HasTypeDescPi profile context firstValue firstType)
      (secondTyped : HasTypeDescPi profile context secondValue secondType) :
      HasTypeDescPairIntro profile context
        (pairCell firstValue secondValue) (productTypeCell firstType secondType)

/-- **★ A pair of universe codes is typed.**  `pair(Type@0, Type@0) : product(Type@1, Type@1)` — the
non-vacuous smoke (the components typed by `ofFormation (universeFormation)`, `Type@0 : Type@1`).  The first
concrete Σ-value the kernel types: data canonicity at the product type is now NON-VACUOUS (there exists a
typed pair to be the canonical form). -/
theorem HasTypeDescPairIntro.pairOfUniverseCodesTyped {profile : PolyProfile} (flag : UniverseFlag) :
    HasTypeDescPairIntro profile (TypingContext.empty : TypingContext profile 0)
      (pairCell (universeCodeCell LevelExpr.lzero flag) (universeCodeCell LevelExpr.lzero flag))
      (productTypeCell (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)
        (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)) :=
  HasTypeDescPairIntro.pairIntro TypingContext.empty
    (universeCodeCell LevelExpr.lzero flag) (universeCodeCell LevelExpr.lzero flag)
    (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)
    (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)
    (HasTypeDescPi.ofFormation (HasTypeDesc.universeFormation TypingContext.empty LevelExpr.lzero flag))
    (HasTypeDescPi.ofFormation (HasTypeDesc.universeFormation TypingContext.empty LevelExpr.lzero flag))

/-- **★ Closed forms (subject): a pair-intro-typed subject is a `pairCell`.**  Every term typed by
`HasTypeDescPairIntro` is `pair(a, b)` for some components — the n-ary analogue of
`HasTypeDescDataIntro.subjectIsBoolConstructor`.  Single-arm `cases`; the SR-free canonicity ingredient. -/
theorem HasTypeDescPairIntro.subjectIsPair {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescPairIntro profile context subject classifier) :
    ∃ (firstValue secondValue : RawTerm scope), subject = pairCell firstValue secondValue := by
  cases derivation with
  | pairIntro firstValue secondValue _firstType _secondType _firstTyped _secondTyped =>
      exact ⟨firstValue, secondValue, rfl⟩

/-- **★ Closed forms (classifier): a pair-intro classifier is a `productTypeCell`.**  Every classifier a
`HasTypeDescPairIntro` derivation reaches is `product(A, B)` for some component types — the classifier-side
companion of `subjectIsPair`.  Single-arm `cases`. -/
theorem HasTypeDescPairIntro.classifierIsProduct {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescPairIntro profile context subject classifier) :
    ∃ (firstType secondType : RawTerm scope), classifier = productTypeCell firstType secondType := by
  cases derivation with
  | pairIntro _firstValue _secondValue firstType secondType _firstTyped _secondTyped =>
      exact ⟨firstType, secondType, rfl⟩

end FX1Poly.Typed
