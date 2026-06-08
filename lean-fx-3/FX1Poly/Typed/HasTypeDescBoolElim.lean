import FX1Poly.Typed.HasTypeDescDataIntro

/-! # FX1Poly/Typed/HasTypeDescBoolElim — the standalone boolean ELIMINATOR judgment + typed ι-computation
    (DI-5 first brick: the kernel's data story extends from INTRODUCTION to ELIMINATION).

DI-1/DI-2 typed the data CONSTRUCTORS (`boolTrue`/`boolFalse`, `pair`, `eitherInl`/`eitherInr`); the
canonical-forms theorems showed every closed-normal data inhabitant IS one of those.  This file adds the
first ELIMINATOR — non-dependent `boolElim` — and the genuinely new content the eliminators carry: typed
ι-COMPUTATION.  `boolElim` is the textbook minimal eliminator (`gen_boolElim`, arity 3, `binderShifts =
[0, 0, 0]`, no motive binder): it selects a branch by the scrutinee's tag.

Following the established cascade-free pattern, this is a brand-new standalone judgment (NOT mutual with /
NOT an arm of any existing engine).

  * `boolElimCell` — the `gen_boolElim` cell `boolElim(scrutinee, thenBranch, elseBranch)`.
  * `HasTypeDescBoolElim` — the judgment: `boolElim(s, t, e) : C` from a scrutinee typed at `boolCode` (by
    the data-intro engine) and two branches typed at the common result `C` (by the grown engine).  The
    non-dependent eliminator (a constant motive `C`).
  * `HasTypeDescBoolElim.boolElimOfUniverseCodesTyped` (★) — the non-vacuous smoke `boolElim(boolTrue,
    Type@0, Type@0) : Type@1`.
  * `HasTypeDescBoolElim.subjectIsBoolElim` — the free-index closed-forms inversion (the subject IS a
    `boolElimCell`).
  * `boolElimTrueIotaComputesTyped` / `boolElimFalseIotaComputesTyped` (★) — the headline: a typed
    `boolElim` on a VALUE (`boolTrue` / `boolFalse`) ι-reduces to the corresponding branch, AND that branch
    is typed at the result `C`.  The eliminator COMPUTES (the `Step.iotaBoolTrue` / `iotaBoolFalse` rule) and
    the computation PRESERVES TYPING — the typed-ι subject-reduction for the value case.  Stated
    constructor-side (the elim is BUILT from the branch premises), so it is SR-FREE and propext-free: it does
    not extract from a derivation (no specific-index `cases`) and does not need the branch-congruence SR.

## The SR-free, propext-free framing

The FULL subject reduction of `boolElim` (any step preserves typing) is NOT SR-free: a step can be a
congruence on a branch (`thenBranch ↝ thenBranch'`), whose re-typing consumes the grown master SR (`SN-055`
/ GrownCtxConv-5 #842).  And extracting the branch premise from a derivation at the literal `boolElimCell boolTrue …`
subject is the cons-index propext trap.  The constructor-side ι-computation theorems sidestep BOTH: they take
the branch typings as hypotheses and exhibit the typed reduct directly.  That is the genuinely new, landable
content — typed eliminator computation — with the full SR deferred to the GrownCtxConv-5 endgame.

## Zero-axiom

A single-arm positive inductive; the smoke + ι-computation theorems are direct constructions
(`boolElimIntro` + `boolTrueTyped` / `ofFormation universeFormation` + `Step.iotaBoolTrue` / `iotaBoolFalse`);
the inversion is a free-index `cases` with `rfl`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- The boolean eliminator cell `boolElim(scrutinee, thenBranch, elseBranch)` — `gen_boolElim` (arity 3,
`binderShifts = [0, 0, 0]`, all three children at the ambient scope, no motive binder). -/
def boolElimCell {scope : Nat} (scrutinee thenBranch elseBranch : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_boolElim ()
    (.childCons scrutinee (.childCons thenBranch (.childCons elseBranch .childNil)))

/-- **The boolean eliminator judgment.**  A standalone layer (NOT mutual with / NOT an arm of any existing
engine) typing the non-dependent `boolElim`: `boolElim(s, t, e)` inhabits the common result type `C` when the
scrutinee is typed at `boolCode` (by the data-intro engine — so it is `boolTrue` or `boolFalse`) and both
branches are typed at `C` (by the grown engine).  Constant motive `C` (the non-dependent eliminator). -/
inductive HasTypeDescBoolElim (profile : PolyProfile) :
    {scope : Nat} → TypingContext profile scope → RawTerm scope → RawTerm scope → Prop where
  | boolElimIntro {scope : Nat} (context : TypingContext profile scope)
      (scrutinee thenBranch elseBranch resultType : RawTerm scope)
      (scrutineeTyped : HasTypeDescDataIntro profile context scrutinee boolTypeCell)
      (thenTyped : HasTypeDescPi profile context thenBranch resultType)
      (elseTyped : HasTypeDescPi profile context elseBranch resultType) :
      HasTypeDescBoolElim profile context
        (boolElimCell scrutinee thenBranch elseBranch) resultType

/-- **★ A boolean eliminator is typed.**  `boolElim(boolTrue, Type@0, Type@0) : Type@1` — the non-vacuous
smoke (scrutinee `boolTrue : boolCode` via the data-intro engine, both branches `Type@0 : Type@1` via
`ofFormation universeFormation`).  The first eliminator the kernel types. -/
theorem HasTypeDescBoolElim.boolElimOfUniverseCodesTyped {profile : PolyProfile} (flag : UniverseFlag) :
    HasTypeDescBoolElim profile (TypingContext.empty : TypingContext profile 0)
      (boolElimCell boolTrueCell (universeCodeCell LevelExpr.lzero flag)
        (universeCodeCell LevelExpr.lzero flag))
      (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag) :=
  HasTypeDescBoolElim.boolElimIntro TypingContext.empty boolTrueCell
    (universeCodeCell LevelExpr.lzero flag) (universeCodeCell LevelExpr.lzero flag)
    (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)
    (HasTypeDescDataIntro.boolTrueTyped TypingContext.empty)
    (HasTypeDescPi.ofFormation (HasTypeDesc.universeFormation TypingContext.empty LevelExpr.lzero flag))
    (HasTypeDescPi.ofFormation (HasTypeDesc.universeFormation TypingContext.empty LevelExpr.lzero flag))

/-- **★ Closed forms: a bool-elim-typed subject is a `boolElimCell`.**  Every term typed by
`HasTypeDescBoolElim` is `boolElim(s, t, e)` for some scrutinee and branches.  Free-index single-arm `cases`. -/
theorem HasTypeDescBoolElim.subjectIsBoolElim {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescBoolElim profile context subject classifier) :
    ∃ (scrutinee thenBranch elseBranch : RawTerm scope),
      subject = boolElimCell scrutinee thenBranch elseBranch := by
  cases derivation with
  | boolElimIntro scrutinee thenBranch elseBranch _resultType _scrutineeTyped _thenTyped _elseTyped =>
      exact ⟨scrutinee, thenBranch, elseBranch, rfl⟩

/-- **★ Typed ι-computation (true case).**  A `boolElim` on `boolTrue` (with both branches typed at `C`) is
typed at `C`, ι-reduces to the THEN branch (`Step.iotaBoolTrue`), and that branch is typed at `C`.  The typed
ι subject-reduction for the value case: the eliminator COMPUTES and the computation PRESERVES TYPING.
Constructor-side (the elim is built from the premises), so SR-free and propext-free. -/
theorem boolElimTrueIotaComputesTyped {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (thenBranch elseBranch resultType : RawTerm scope)
    (thenTyped : HasTypeDescPi profile context thenBranch resultType)
    (elseTyped : HasTypeDescPi profile context elseBranch resultType) :
    HasTypeDescBoolElim profile context
      (boolElimCell boolTrueCell thenBranch elseBranch) resultType ∧
    Step (boolElimCell boolTrueCell thenBranch elseBranch) thenBranch ∧
    HasTypeDescPi profile context thenBranch resultType :=
  ⟨HasTypeDescBoolElim.boolElimIntro context boolTrueCell thenBranch elseBranch resultType
      (HasTypeDescDataIntro.boolTrueTyped context) thenTyped elseTyped,
    Step.iotaBoolTrue,
    thenTyped⟩

/-- **★ Typed ι-computation (false case).**  The `boolFalse` mirror of `boolElimTrueIotaComputesTyped`: a
`boolElim` on `boolFalse` ι-reduces to the ELSE branch (`Step.iotaBoolFalse`), typed at `C`. -/
theorem boolElimFalseIotaComputesTyped {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (thenBranch elseBranch resultType : RawTerm scope)
    (thenTyped : HasTypeDescPi profile context thenBranch resultType)
    (elseTyped : HasTypeDescPi profile context elseBranch resultType) :
    HasTypeDescBoolElim profile context
      (boolElimCell boolFalseCell thenBranch elseBranch) resultType ∧
    Step (boolElimCell boolFalseCell thenBranch elseBranch) elseBranch ∧
    HasTypeDescPi profile context elseBranch resultType :=
  ⟨HasTypeDescBoolElim.boolElimIntro context boolFalseCell thenBranch elseBranch resultType
      (HasTypeDescDataIntro.boolFalseTyped context) thenTyped elseTyped,
    Step.iotaBoolFalse,
    elseTyped⟩

end FX1Poly.Typed
