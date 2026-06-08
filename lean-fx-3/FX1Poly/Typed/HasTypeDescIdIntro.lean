import FX1Poly.Typed.HasTypeDescPi

/-! # FX1Poly/Typed/HasTypeDescIdIntro — the standalone identity-type introduction judgment
    (DI-2d, the reflexivity intro: `refl(x) : Id(A, x, x)`).

The pair / coproduct / option introductions typed Σ / coproduct / option VALUES; this is the IDENTITY twin,
typing the reflexivity constructor `refl` at the identity type code.  Same cascade-free pattern (a brand-new
standalone judgment, NOT mutual with / NOT an arm of any existing engine).  This is the scrutinee-typing
prerequisite for the identity ELIMINATOR (`HasTypeDescIdElim`, DI-5e) — `idJ`'s witness premise needs an engine
that types `refl`.

## The reflexive-endpoint structure

`refl(x) : Id(A, x, x)` is the PINNED intro (like `optionSome` / `pair`): the witness `x : A` pins both the type
`A` and BOTH endpoints (which are EQUAL — `x = x`).  So the rule has ONE premise (the witness typing) and the
classifier is `Id(A, x, x)` — the only identity types `refl` inhabits are the reflexive ones (both endpoints the
same term).

  * `reflCell` / `idTypeCell` — the value/type cells (`gen_refl`, arity 1 `[0]`; `gen_idCode`, arity 3
    `[0, 0, 0]` — `Id(typeCode, left, right)`), inline `mkGen`.
  * `HasTypeDescIdIntro` — the judgment, one arm (`reflIntro`): from `x : A`, conclude `refl(x) : Id(A, x, x)`.
  * `HasTypeDescIdIntro.reflOfUniverseCodeTyped` (★) — the non-vacuous smoke
    `refl(Type@0) : Id(Type@1, Type@0, Type@0)`.
  * `HasTypeDescIdIntro.subjectIsRefl` / `classifierIsReflexiveId` — the closed-forms inversions (the subject IS a
    `reflCell`; the classifier IS a REFLEXIVE `idTypeCell` — both endpoints the same term).

## SR deferral (same as the other intros)

Judgment + smoke + inversions are SR-free.  The SR/SN quartet is GCC-5-ENTANGLED (a `refl` steps when its witness
steps, re-typing only via the grown master subject-reduction dispatcher, `SN-055` / GCC-5 #842) — the deliberate
deferral.

## Zero-axiom

A single-arm positive inductive; the smoke is a direct arm application with an `ofFormation universeFormation`
sub-derivation; the inversions are single-arm `cases` with `rfl`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- The reflexivity value cell `refl(witness)` — `gen_refl` (arity 1, `binderShifts = [0]`). -/
def reflCell {scope : Nat} (witness : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_refl () (.childCons witness .childNil)

/-- The identity type code `Id(typeCode, left, right)` — `gen_idCode` (arity 3, `binderShifts = [0, 0, 0]`), the
heterogeneous three-child code (a type and two endpoint terms) that classifies the reflexivity cell. -/
def idTypeCell {scope : Nat} (typeCode left right : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_idCode () (.childCons typeCode (.childCons left (.childCons right .childNil)))

/-- **The identity-type introduction judgment.**  A standalone layer (NOT mutual with / NOT an arm of any
existing engine, mirroring `HasTypeDescOptionIntro`) typing the reflexivity constructor.  From a witness
`x : A`, `refl(x)` inhabits the REFLEXIVE identity type `Id(A, x, x)` (both endpoints the witness — the only
identity types `refl` populates). -/
inductive HasTypeDescIdIntro (profile : PolyProfile) :
    {scope : Nat} → TypingContext profile scope → RawTerm scope → RawTerm scope → Prop where
  | reflIntro {scope : Nat} (context : TypingContext profile scope)
      (witness typeCode : RawTerm scope)
      (witnessTyped : HasTypeDescPi profile context witness typeCode) :
      HasTypeDescIdIntro profile context (reflCell witness) (idTypeCell typeCode witness witness)

/-- **★ A reflexivity proof is typed.**  `refl(Type@0) : Id(Type@1, Type@0, Type@0)` — the non-vacuous smoke
(witness `Type@0 : Type@1`, so the identity type is at `Type@1` between `Type@0` and itself).  The first
identity proof the kernel types. -/
theorem HasTypeDescIdIntro.reflOfUniverseCodeTyped {profile : PolyProfile} (flag : UniverseFlag) :
    HasTypeDescIdIntro profile (TypingContext.empty : TypingContext profile 0)
      (reflCell (universeCodeCell LevelExpr.lzero flag))
      (idTypeCell (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)
        (universeCodeCell LevelExpr.lzero flag) (universeCodeCell LevelExpr.lzero flag)) :=
  HasTypeDescIdIntro.reflIntro TypingContext.empty
    (universeCodeCell LevelExpr.lzero flag)
    (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)
    (HasTypeDescPi.ofFormation (HasTypeDesc.universeFormation TypingContext.empty LevelExpr.lzero flag))

/-- **★ Closed forms (subject): an id-intro-typed subject is a `reflCell`.**  Every term typed by
`HasTypeDescIdIntro` is `refl(x)` — the identity analogue of `HasTypeDescOptionIntro.subjectIsOptionConstructor`.
Single-arm free-index `cases`; the SR-free canonicity ingredient. -/
theorem HasTypeDescIdIntro.subjectIsRefl {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescIdIntro profile context subject classifier) :
    ∃ witness : RawTerm scope, subject = reflCell witness := by
  cases derivation with
  | reflIntro witness _typeCode _witnessTyped =>
      exact ⟨witness, rfl⟩

/-- **★ Closed forms (classifier): an id-intro classifier is a REFLEXIVE `idTypeCell`.**  Every classifier a
`HasTypeDescIdIntro` derivation reaches is `Id(A, x, x)` for some type `A` and endpoint `x` — the two endpoints
are the SAME term (`refl` only inhabits reflexive identity types).  The classifier-side companion of
`subjectIsRefl`. -/
theorem HasTypeDescIdIntro.classifierIsReflexiveId {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescIdIntro profile context subject classifier) :
    ∃ (typeCode endpoint : RawTerm scope), classifier = idTypeCell typeCode endpoint endpoint := by
  cases derivation with
  | reflIntro witness typeCode _witnessTyped =>
      exact ⟨typeCode, witness, rfl⟩

end FX1Poly.Typed
