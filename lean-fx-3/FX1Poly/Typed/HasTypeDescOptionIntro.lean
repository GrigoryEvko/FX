import FX1Poly.Typed.HasTypeDescPi

/-! # FX1Poly/Typed/HasTypeDescOptionIntro — the standalone Option introduction judgment
    (DI-2c, the option half: `optionNone : option(A)` and `optionSome(a) : option(A)`).

The coproduct-introduction (`HasTypeDescEitherIntro`, DI-2b) typed the two sum-VALUE constructors; this is the
OPTION twin, typing `optionNone` / `optionSome` at the option type code.  Same cascade-free pattern (a brand-new
standalone judgment, NOT mutual with / NOT an arm of any existing engine), so it disturbs no recursor and no
data-head-untyped refutation.  This is the scrutinee-typing prerequisite for the option ELIMINATOR
(`HasTypeDescOptionMatch`, DI-5c, the next brick) — optionMatch's scrutinee premise needs an engine that types
`optionNone` / `optionSome`, exactly as eitherMatch's needs `HasTypeDescEitherIntro`.

## The free-type premise (the `None` asymmetry)

`optionNone : option(A)` is asymmetric just like `eitherInl(a) : either(A, B)`: the value carries no payload, so
`A` is FREE — `optionNone` says nothing about it.  For the result type `option(A)` to be well-formed, `A` must BE
a type, so the rule carries a type-formedness premise (`A : Type@_`).  `optionSome(a) : option(A)` is the pinned
side: `a : A` fixes `A`, so its only premise is the value typing (no separate formedness premise — the exact
mirror of `eitherInlIntro`'s pinned `leftValue` vs free `rightType`).

  * `optionNoneCell` / `optionSomeCell` / `optionTypeCell` — the value/type cells (`gen_optionNone`, arity 0;
    `gen_optionSome`, arity 1 `[0]`; `gen_optionCode`, arity 1 `[0]`), inline `mkGen`.
  * `HasTypeDescOptionIntro` — the judgment, two arms (`optionNoneIntro` / `optionSomeIntro`): the `None` arm
    carries a type-formedness premise for the free element type, the `Some` arm a value premise that pins it.
  * `HasTypeDescOptionIntro.{optionNoneOfUniverseCodeTyped, optionSomeOfUniverseCodeTyped}` (★) — the non-vacuous
    smokes: `optionNone : option(Type@0)` and `optionSome(Type@0) : option(Type@1)`.
  * `HasTypeDescOptionIntro.subjectIsOptionConstructor` / `classifierIsOption` — the closed-forms inversions (the
    subject IS an `optionNoneCell` or `optionSomeCell`; the classifier IS an `optionTypeCell`).  The SR-free
    canonicity ingredients (the option twins of `HasTypeDescEitherIntro.subjectIsEitherInjection`).

## SR deferral (same as DI-2b)

Judgment + smokes + inversions are SR-free.  The SR/SN quartet is GrownCtxConv-5-ENTANGLED (an option value steps when its
value/type component steps, re-typing only via the grown master subject-reduction dispatcher, `SN-055` /
GrownCtxConv-5 #842) — the deliberate deferral.

## Zero-axiom

A two-arm positive inductive; the smokes are direct arm applications with `ofFormation universeFormation`
sub-derivations; the inversions are free-index `cases` with `rfl`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The Option introduction judgment.**  A standalone layer (NOT mutual with / NOT an arm of any existing
engine, mirroring `HasTypeDescEitherIntro`) typing the two option-value constructors at their option type code.
`optionNone` needs only a type-formedness witness for the free element component `A`; `optionSome(a)` needs a
value premise `a : A` that pins `A`. -/
inductive HasTypeDescOptionIntro (profile : PolyProfile) :
    {scope : Nat} → TypingContext profile scope → RawTerm scope → RawTerm scope → Prop where
  | optionNoneIntro {scope : Nat} (context : TypingContext profile scope)
      (elementType : RawTerm scope) (elementLevel : LevelExpr) (flag : UniverseFlag)
      (elementTypeFormed :
        HasTypeDescPi profile context elementType (universeCodeCell elementLevel flag)) :
      HasTypeDescOptionIntro profile context optionNoneCell (optionTypeCell elementType)
  | optionSomeIntro {scope : Nat} (context : TypingContext profile scope)
      (value elementType : RawTerm scope)
      (valueTyped : HasTypeDescPi profile context value elementType) :
      HasTypeDescOptionIntro profile context (optionSomeCell value) (optionTypeCell elementType)

/-- **★ The empty option of a universe code is typed.**  `optionNone : option(Type@0)` — the non-vacuous `None`
smoke (the free element component `Type@0` formed at `Type@1`).  The first option value the kernel types. -/
theorem HasTypeDescOptionIntro.optionNoneOfUniverseCodeTyped {profile : PolyProfile} (flag : UniverseFlag) :
    HasTypeDescOptionIntro profile (TypingContext.empty : TypingContext profile 0)
      optionNoneCell (optionTypeCell (universeCodeCell LevelExpr.lzero flag)) :=
  HasTypeDescOptionIntro.optionNoneIntro TypingContext.empty
    (universeCodeCell LevelExpr.lzero flag) (LevelExpr.lsucc LevelExpr.lzero) flag
    (HasTypeDescPi.ofFormation (HasTypeDesc.universeFormation TypingContext.empty LevelExpr.lzero flag))

/-- **★ The present option of a universe code is typed.**  `optionSome(Type@0) : option(Type@1)` — the
non-vacuous `Some` smoke (the value `Type@0 : Type@1` pins the element type `Type@1`). -/
theorem HasTypeDescOptionIntro.optionSomeOfUniverseCodeTyped {profile : PolyProfile} (flag : UniverseFlag) :
    HasTypeDescOptionIntro profile (TypingContext.empty : TypingContext profile 0)
      (optionSomeCell (universeCodeCell LevelExpr.lzero flag))
      (optionTypeCell (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)) :=
  HasTypeDescOptionIntro.optionSomeIntro TypingContext.empty
    (universeCodeCell LevelExpr.lzero flag) (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)
    (HasTypeDescPi.ofFormation (HasTypeDesc.universeFormation TypingContext.empty LevelExpr.lzero flag))

/-- **★ Closed forms (subject): an option-intro-typed subject is `optionNone` or `optionSome`.**  Every term
typed by `HasTypeDescOptionIntro` is `optionNone` or `optionSome(a)` — the option analogue of
`HasTypeDescEitherIntro.subjectIsEitherInjection`.  Two-arm free-index `cases`; the SR-free canonicity
ingredient. -/
theorem HasTypeDescOptionIntro.subjectIsOptionConstructor {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescOptionIntro profile context subject classifier) :
    subject = optionNoneCell ∨ (∃ value : RawTerm scope, subject = optionSomeCell value) := by
  cases derivation with
  | optionNoneIntro _elementType _elementLevel _flag _elementTypeFormed =>
      exact Or.inl rfl
  | optionSomeIntro value _elementType _valueTyped =>
      exact Or.inr ⟨value, rfl⟩

/-- **★ Closed forms (classifier): an option-intro classifier is an `optionTypeCell`.**  Every classifier a
`HasTypeDescOptionIntro` derivation reaches is `option(A)` for some element type — the classifier-side companion
of `subjectIsOptionConstructor`.  Two-arm `cases`. -/
theorem HasTypeDescOptionIntro.classifierIsOption {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescOptionIntro profile context subject classifier) :
    ∃ elementType : RawTerm scope, classifier = optionTypeCell elementType := by
  cases derivation with
  | optionNoneIntro elementType _elementLevel _flag _elementTypeFormed =>
      exact ⟨elementType, rfl⟩
  | optionSomeIntro _value elementType _valueTyped =>
      exact ⟨elementType, rfl⟩

end FX1Poly.Typed
