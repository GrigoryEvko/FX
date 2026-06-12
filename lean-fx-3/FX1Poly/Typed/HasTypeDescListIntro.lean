import FX1Poly.Typed.HasTypeDescPi

/-! # FX1Poly/Typed/HasTypeDescListIntro — the standalone List introduction judgment
    (DI-2e, the list constructors: `nil : List(A)` and `cons(h, t) : List(A)` — the FIRST RECURSIVE intro).

The pair / coproduct / option / identity introductions typed NON-recursive data VALUES (every premise was a
value or a type at an ALREADY-existing classifier).  This is the LIST twin, and the first one whose constructor
is RECURSIVE: `cons(h, t) : List(A)` has a tail premise `t : List(A)` typed BY THE SAME judgment.  So
`HasTypeDescListIntro` is the first standalone data-intro inductive with a SELF-REFERENTIAL constructor arm
(strictly positive — the inductive appears positively in the `cons` tail premise).  Same cascade-free pattern (a
brand-new standalone judgment, NOT mutual with / NOT an arm of any existing engine), so it disturbs no recursor.
This is the scrutinee-typing prerequisite for the list ELIMINATOR (`listElim`, the first RECURSIVE eliminator,
a future brick).

## The two arms

  * `listNilIntro` — `nil : List(A)` is the NULLARY arm with a FREE element type (like `optionNone`): `nil`
    carries no element, so `A` is free and the rule carries a type-formedness premise (`A : Type@_`).
  * `listConsIntro` — `cons(h, t) : List(A)` is the RECURSIVE arm: a head `h : A` (which pins `A`) plus a tail
    `t : List(A)` typed by `HasTypeDescListIntro` itself.  The recursion is the genuinely-new structure.

  * `listNilCell` / `listConsCell` / `listTypeCell` — the value/type cells (`gen_listNil`, arity 0;
    `gen_listCons`, arity 2 `[0, 0]`; `gen_listCode`, arity 1 `[0]`), inline `mkGen`.
  * `HasTypeDescListIntro` — the judgment, two arms (one nullary-free, one recursive).
  * `HasTypeDescListIntro.{listNilOfUniverseCodeTyped, listConsOfUniverseCodesTyped}` (★) — the non-vacuous
    smokes: `nil : List(Type@0)` and the one-element list `cons(Type@0, nil) : List(Type@1)` (exercising the
    recursive arm — the tail `nil` typed by the same engine).
  * `HasTypeDescListIntro.subjectIsListConstructor` / `classifierIsList` — the closed-forms inversions (the
    subject IS a `nil` or `cons`; the classifier IS a `listTypeCell`).

## SR deferral (same as the other intros)

Judgment + smokes + inversions are SR-free.  The SR/SN quartet is GrownCtxConv-5-ENTANGLED (a `cons` steps when its
head/tail steps, re-typing only via the grown master subject-reduction dispatcher, `SN-055` / GrownCtxConv-5 #842) — the
deliberate deferral.

## Zero-axiom

A two-arm positive inductive (the recursive arm is strictly positive); the smokes are direct arm applications
(the cons smoke nests `listNilIntro` for the tail); the inversions are free-index `cases` with `rfl`.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The List introduction judgment.**  A standalone layer (NOT mutual with / NOT an arm of any existing
engine) typing the list value constructors at their list type code.  `nil` needs only a type-formedness witness
for the free element type `A`; `cons(h, t)` needs a head premise `h : A` (which pins `A`) and a RECURSIVE tail
premise `t : List(A)` (typed by this judgment itself — the first self-referential data-intro arm). -/
inductive HasTypeDescListIntro (profile : PolyProfile) :
    {scope : Nat} → TypingContext profile scope → RawTerm scope → RawTerm scope → Prop where
  | listNilIntro {scope : Nat} (context : TypingContext profile scope)
      (elementType : RawTerm scope) (elementLevel : LevelExpr) (flag : UniverseFlag)
      (elementTypeFormed :
        HasTypeDescPi profile context elementType (universeCodeCell elementLevel flag)) :
      HasTypeDescListIntro profile context listNilCell (listTypeCell elementType)
  | listConsIntro {scope : Nat} (context : TypingContext profile scope)
      (headValue tailList elementType : RawTerm scope)
      (headTyped : HasTypeDescPi profile context headValue elementType)
      (tailTyped : HasTypeDescListIntro profile context tailList (listTypeCell elementType)) :
      HasTypeDescListIntro profile context (listConsCell headValue tailList) (listTypeCell elementType)

/-- **★ The empty list of a universe code is typed.**  `nil : List(Type@0)` — the non-vacuous `nil` smoke (the
free element component `Type@0` formed at `Type@1`). -/
theorem HasTypeDescListIntro.listNilOfUniverseCodeTyped {profile : PolyProfile} (flag : UniverseFlag) :
    HasTypeDescListIntro profile (TypingContext.empty : TypingContext profile 0)
      listNilCell (listTypeCell (universeCodeCell LevelExpr.lzero flag)) :=
  HasTypeDescListIntro.listNilIntro TypingContext.empty
    (universeCodeCell LevelExpr.lzero flag) (LevelExpr.lsucc LevelExpr.lzero) flag
    (HasTypeDescPi.ofFormation (HasTypeDesc.universeFormation TypingContext.empty LevelExpr.lzero flag))

/-- **★ A one-element list of a universe code is typed.**  `cons(Type@0, nil) : List(Type@1)` — the non-vacuous
RECURSIVE smoke (head `Type@0 : Type@1` pins the element type `Type@1`, tail `nil : List(Type@1)` typed by the
SAME engine via `listNilIntro` with `Type@1` formed at `Type@2`).  The first list the kernel types whose
constructor exercises the recursive arm. -/
theorem HasTypeDescListIntro.listConsOfUniverseCodesTyped {profile : PolyProfile} (flag : UniverseFlag) :
    HasTypeDescListIntro profile (TypingContext.empty : TypingContext profile 0)
      (listConsCell (universeCodeCell LevelExpr.lzero flag) listNilCell)
      (listTypeCell (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)) :=
  HasTypeDescListIntro.listConsIntro TypingContext.empty
    (universeCodeCell LevelExpr.lzero flag) listNilCell
    (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)
    (HasTypeDescPi.ofFormation (HasTypeDesc.universeFormation TypingContext.empty LevelExpr.lzero flag))
    (HasTypeDescListIntro.listNilIntro TypingContext.empty
      (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)
      (LevelExpr.lsucc (LevelExpr.lsucc LevelExpr.lzero)) flag
      (HasTypeDescPi.ofFormation
        (HasTypeDesc.universeFormation TypingContext.empty (LevelExpr.lsucc LevelExpr.lzero) flag)))

/-- **★ Closed forms (subject): a list-intro-typed subject is `nil` or `cons`.**  Every term typed by
`HasTypeDescListIntro` is `nil` or `cons(h, t)` — the list analogue of
`HasTypeDescOptionIntro.subjectIsOptionConstructor`.  Two-arm free-index `cases`; the SR-free canonicity
ingredient. -/
theorem HasTypeDescListIntro.subjectIsListConstructor {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescListIntro profile context subject classifier) :
    subject = listNilCell ∨
    (∃ (headValue tailList : RawTerm scope), subject = listConsCell headValue tailList) := by
  cases derivation with
  | listNilIntro _elementType _elementLevel _flag _elementTypeFormed =>
      exact Or.inl rfl
  | listConsIntro headValue tailList _elementType _headTyped _tailTyped =>
      exact Or.inr ⟨headValue, tailList, rfl⟩

/-- **★ Closed forms (classifier): a list-intro classifier is a `listTypeCell`.**  Every classifier a
`HasTypeDescListIntro` derivation reaches is `List(A)` for some element type — the classifier-side companion of
`subjectIsListConstructor`.  Two-arm `cases`. -/
theorem HasTypeDescListIntro.classifierIsList {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescListIntro profile context subject classifier) :
    ∃ elementType : RawTerm scope, classifier = listTypeCell elementType := by
  cases derivation with
  | listNilIntro elementType _elementLevel _flag _elementTypeFormed =>
      exact ⟨elementType, rfl⟩
  | listConsIntro _headValue _tailList elementType _headTyped _tailTyped =>
      exact ⟨elementType, rfl⟩

end FX1Poly.Typed
