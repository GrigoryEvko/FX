import FX1Poly.Typed.HasTypeDescPi

/-! # FX1Poly/Typed/HasTypeDescEitherIntro — the standalone coproduct (Either) introduction judgment
    (DI-2, the sum half: `eitherInl(a) : either(A, B)` and `eitherInr(b) : either(A, B)`).

The pair-introduction (`HasTypeDescPairIntro`, DI-2a) typed the Σ-VALUE; this is the COPRODUCT twin, typing
the two sum-VALUE constructors `eitherInl` / `eitherInr` at the either type code.  Following the same
cascade-free pattern (a brand-new standalone judgment, NOT mutual with / NOT an arm of any existing engine),
so it disturbs no recursor and no data-head-untyped refutation.

## The free-type premise

A coproduct introduction is asymmetric in its un-injected component: `eitherInl(a) : either(A, B)` pins `A`
from `a : A`, but `B` is FREE — `a` says nothing about it.  For the result type `either(A, B)` to be
well-formed, `B` must BE a type, so the rule carries an EXTRA premise that the OTHER component is universe-
typed (`B : Type@_`).  This is the structural difference from `pairIntro` (whose two components are both
pinned by their values): each Either arm has ONE value premise and ONE type-formedness premise.

  * `eitherInlCell` / `eitherInrCell` / `eitherTypeCell` — the value/type cells (`gen_eitherInl` /
    `gen_eitherInr`, arity 1 `[0]`; `gen_eitherCode`, arity 2 `[0, 0]`), inline `mkGen`.
  * `HasTypeDescEitherIntro` — the judgment, two arms (`eitherInlIntro` / `eitherInrIntro`), each with a value
    premise + a type-formedness premise for the un-injected side.
  * `HasTypeDescEitherIntro.{eitherInlOfUniverseCodeTyped, eitherInrOfUniverseCodeTyped}` (★) — the non-vacuous
    smokes: `eitherInl(Type@0) : either(Type@1, Type@1)` and the `inr` twin (the value typed by
    `ofFormation (universeFormation)`, the un-injected side formed at the next universe).
  * `HasTypeDescEitherIntro.subjectIsEitherInjection` / `classifierIsEither` — the closed-forms inversions
    (the subject IS an `eitherInlCell` or `eitherInrCell`; the classifier IS an `eitherTypeCell`).  The
    SR-free canonicity ingredients (the coproduct twins of `HasTypeDescPairIntro.subjectIsPair`).

## SR deferral (same as DI-2a)

Judgment + smokes + inversions are SR-free.  The SR/SN quartet is GCC-5-ENTANGLED (an injection steps when
its value/type component steps, re-typing only via the grown master subject-reduction dispatcher, `SN-055` /
GCC-5 #842) — the deliberate deferral.

## Zero-axiom

A two-arm positive inductive; the smokes are direct arm applications with `ofFormation universeFormation`
sub-derivations; the inversions are free-index `cases` with `rfl`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- The left coproduct injection cell `eitherInl(value)` — `gen_eitherInl` (arity 1, `binderShifts = [0]`). -/
def eitherInlCell {scope : Nat} (value : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_eitherInl () (.childCons value .childNil)

/-- The right coproduct injection cell `eitherInr(value)` — `gen_eitherInr` (arity 1, `binderShifts = [0]`). -/
def eitherInrCell {scope : Nat} (value : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_eitherInr () (.childCons value .childNil)

/-- The coproduct type code `either(leftType, rightType)` — `gen_eitherCode` (arity 2, `binderShifts =
[0, 0]`), the non-dependent sum type that classifies the injection cells. -/
def eitherTypeCell {scope : Nat} (leftType rightType : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_eitherCode () (.childCons leftType (.childCons rightType .childNil))

/-- **The coproduct introduction judgment.**  A standalone layer (NOT mutual with / NOT an arm of any
existing engine, mirroring `HasTypeDescPairIntro`) typing the two sum-value constructors at their either type
code.  `eitherInl(a)` needs `a : A` plus a type-formedness witness for the free right component `B`;
`eitherInr(b)` is the mirror (a `b : B` value premise plus a left-component formedness witness). -/
inductive HasTypeDescEitherIntro (profile : PolyProfile) :
    {scope : Nat} → TypingContext profile scope → RawTerm scope → RawTerm scope → Prop where
  | eitherInlIntro {scope : Nat} (context : TypingContext profile scope)
      (leftValue leftType rightType : RawTerm scope) (rightLevel : LevelExpr) (flag : UniverseFlag)
      (leftTyped : HasTypeDescPi profile context leftValue leftType)
      (rightTypeFormed :
        HasTypeDescPi profile context rightType (universeCodeCell rightLevel flag)) :
      HasTypeDescEitherIntro profile context
        (eitherInlCell leftValue) (eitherTypeCell leftType rightType)
  | eitherInrIntro {scope : Nat} (context : TypingContext profile scope)
      (rightValue leftType rightType : RawTerm scope) (leftLevel : LevelExpr) (flag : UniverseFlag)
      (rightTyped : HasTypeDescPi profile context rightValue rightType)
      (leftTypeFormed :
        HasTypeDescPi profile context leftType (universeCodeCell leftLevel flag)) :
      HasTypeDescEitherIntro profile context
        (eitherInrCell rightValue) (eitherTypeCell leftType rightType)

/-- **★ A left injection of a universe code is typed.**  `eitherInl(Type@0) : either(Type@1, Type@1)` — the
non-vacuous left smoke (the value typed `Type@0 : Type@1`, the free right component `Type@1` formed at
`Type@2`).  The first coproduct value the kernel types. -/
theorem HasTypeDescEitherIntro.eitherInlOfUniverseCodeTyped {profile : PolyProfile} (flag : UniverseFlag) :
    HasTypeDescEitherIntro profile (TypingContext.empty : TypingContext profile 0)
      (eitherInlCell (universeCodeCell LevelExpr.lzero flag))
      (eitherTypeCell (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)
        (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)) :=
  HasTypeDescEitherIntro.eitherInlIntro TypingContext.empty
    (universeCodeCell LevelExpr.lzero flag)
    (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)
    (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)
    (LevelExpr.lsucc (LevelExpr.lsucc LevelExpr.lzero)) flag
    (HasTypeDescPi.ofFormation (HasTypeDesc.universeFormation TypingContext.empty LevelExpr.lzero flag))
    (HasTypeDescPi.ofFormation
      (HasTypeDesc.universeFormation TypingContext.empty (LevelExpr.lsucc LevelExpr.lzero) flag))

/-- **★ A right injection of a universe code is typed.**  `eitherInr(Type@0) : either(Type@1, Type@1)` — the
`inr` mirror of `eitherInlOfUniverseCodeTyped` (the value typed `Type@0 : Type@1`, the free LEFT component
`Type@1` formed at `Type@2`). -/
theorem HasTypeDescEitherIntro.eitherInrOfUniverseCodeTyped {profile : PolyProfile} (flag : UniverseFlag) :
    HasTypeDescEitherIntro profile (TypingContext.empty : TypingContext profile 0)
      (eitherInrCell (universeCodeCell LevelExpr.lzero flag))
      (eitherTypeCell (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)
        (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)) :=
  HasTypeDescEitherIntro.eitherInrIntro TypingContext.empty
    (universeCodeCell LevelExpr.lzero flag)
    (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)
    (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)
    (LevelExpr.lsucc (LevelExpr.lsucc LevelExpr.lzero)) flag
    (HasTypeDescPi.ofFormation (HasTypeDesc.universeFormation TypingContext.empty LevelExpr.lzero flag))
    (HasTypeDescPi.ofFormation
      (HasTypeDesc.universeFormation TypingContext.empty (LevelExpr.lsucc LevelExpr.lzero) flag))

/-- **★ Closed forms (subject): an either-intro-typed subject is a left or right injection.**  Every term
typed by `HasTypeDescEitherIntro` is `eitherInl(a)` or `eitherInr(b)` — the coproduct analogue of
`HasTypeDescPairIntro.subjectIsPair`.  Two-arm free-index `cases`; the SR-free canonicity ingredient. -/
theorem HasTypeDescEitherIntro.subjectIsEitherInjection {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescEitherIntro profile context subject classifier) :
    (∃ value : RawTerm scope, subject = eitherInlCell value) ∨
    (∃ value : RawTerm scope, subject = eitherInrCell value) := by
  cases derivation with
  | eitherInlIntro leftValue _leftType _rightType _rightLevel _flag _leftTyped _rightTypeFormed =>
      exact Or.inl ⟨leftValue, rfl⟩
  | eitherInrIntro rightValue _leftType _rightType _leftLevel _flag _rightTyped _leftTypeFormed =>
      exact Or.inr ⟨rightValue, rfl⟩

/-- **★ Closed forms (classifier): an either-intro classifier is an `eitherTypeCell`.**  Every classifier a
`HasTypeDescEitherIntro` derivation reaches is `either(A, B)` for some component types — the classifier-side
companion of `subjectIsEitherInjection`.  Two-arm `cases`. -/
theorem HasTypeDescEitherIntro.classifierIsEither {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescEitherIntro profile context subject classifier) :
    ∃ (leftType rightType : RawTerm scope), classifier = eitherTypeCell leftType rightType := by
  cases derivation with
  | eitherInlIntro _leftValue leftType rightType _rightLevel _flag _leftTyped _rightTypeFormed =>
      exact ⟨leftType, rightType, rfl⟩
  | eitherInrIntro _rightValue leftType rightType _leftLevel _flag _rightTyped _leftTypeFormed =>
      exact ⟨leftType, rightType, rfl⟩

end FX1Poly.Typed
