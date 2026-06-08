import FX1Poly.Typed.HasTypeDescPairIntro

/-! # FX1Poly/Typed/HasTypeDescSigmaProjection — the Σ-projection ELIMINATOR + content-projection ι-computation
    (DI-5d: the Σ eliminator, completing the Σ/pair data story — intro DI-2a + canon DI-2-canon + this elim).

DI-5a/b/c shipped the bool / coproduct / option eliminators (branch-selection, app-chain, and the mixed shape).
`fst` / `snd` are the Σ eliminators and carry the THIRD distinct ι shape:

  * `fst(pair(a, b)) ↝ a`  (`Step.iotaFstPair`)
  * `snd(pair(a, b)) ↝ b`  (`Step.iotaSndPair`)

the CONTENT-PROJECTION shape: the reduct is a CHILD of the SCRUTINEE (`a`/`b` inside `pair(a, b)`), not a branch
of the eliminator (boolElim) and not a handler applied to a payload (eitherMatch).  It is the SIMPLEST typed ι:
the reduct's typing is one of the pair's component typings DIRECTLY — no branch typing, no `piElim`, no `subst0`.

Following the established cascade-free pattern (a brand-new standalone judgment), consuming `HasTypeDescPairIntro`
(DI-2a) for the scrutinee premise.

  * `fstCell` / `sndCell` — the `gen_fst` / `gen_snd` projection cells (arity 1, `[0]`).
  * `HasTypeDescSigmaProjection` — the judgment, two arms (`fstIntro` / `sndIntro`): from a scrutinee typed at
    `product(A, B)` (by the pair-intro engine — so it is a `pair`), `fst(p) : A` and `snd(p) : B` (the
    non-dependent first/second component projections).
  * `HasTypeDescSigmaProjection.fstOfUniverseCodesTyped` (★) — the non-vacuous smoke
    `fst(pair(Type@0, Type@0)) : Type@1`.
  * `HasTypeDescSigmaProjection.subjectIsSigmaProjection` — the free-index closed-forms inversion.
  * `fstProjectionIotaComputesTyped` / `sndProjectionIotaComputesTyped` (★) — the typed content-projection
    ι-computation: a typed projection of a `pair` ι-reduces to the corresponding component, typed at its
    component type.  The eliminator COMPUTES and the computation PRESERVES TYPING — and the reduct's typing is
    the component hypothesis verbatim.

## The SR-free, propext-free framing (as DI-5a/b/c)

Constructor-side: each projection is BUILT from the pair's component typings, the reduct's typing IS the matching
component typing.  No derivation casing (no cons-index propext trap), no scrutinee-congruence (the full SR
consumes the grown master SR / GrownCtxConv-5 #842).  The genuinely-new content is the third ι shape (content projection)
typed-and-computing.

## Zero-axiom

A two-arm positive inductive; the smoke + ι-computation theorems are direct constructions (`fstIntro` /
`sndIntro` + `HasTypeDescPairIntro.pairIntro` + `Step.iotaFstPair` / `iotaSndPair`); the inversion is a free-index
`cases` with `rfl`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- The first-projection cell `fst(pairTerm)` — `gen_fst` (arity 1, `binderShifts = [0]`). -/
def fstCell {scope : Nat} (pairTerm : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_fst () (.childCons pairTerm .childNil)

/-- The second-projection cell `snd(pairTerm)` — `gen_snd` (arity 1, `binderShifts = [0]`). -/
def sndCell {scope : Nat} (pairTerm : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_snd () (.childCons pairTerm .childNil)

/-- **The Σ-projection eliminator judgment.**  A standalone layer typing the non-dependent projections:
`fst(p) : A` and `snd(p) : B` when the scrutinee `p` is typed at `product(A, B)` (by the pair-intro engine — so
it is a `pair`).  The two component types `A`, `B` come straight from the product classifier. -/
inductive HasTypeDescSigmaProjection (profile : PolyProfile) :
    {scope : Nat} → TypingContext profile scope → RawTerm scope → RawTerm scope → Prop where
  | fstIntro {scope : Nat} (context : TypingContext profile scope)
      (pairTerm firstType secondType : RawTerm scope)
      (pairTyped :
        HasTypeDescPairIntro profile context pairTerm (productTypeCell firstType secondType)) :
      HasTypeDescSigmaProjection profile context (fstCell pairTerm) firstType
  | sndIntro {scope : Nat} (context : TypingContext profile scope)
      (pairTerm firstType secondType : RawTerm scope)
      (pairTyped :
        HasTypeDescPairIntro profile context pairTerm (productTypeCell firstType secondType)) :
      HasTypeDescSigmaProjection profile context (sndCell pairTerm) secondType

/-- **★ A first projection is typed.**  `fst(pair(Type@0, Type@0)) : Type@1` — the non-vacuous smoke (scrutinee
`pair(Type@0, Type@0) : product(Type@1, Type@1)` via `pairOfUniverseCodesTyped`, so the first component type is
`Type@1`).  The first projection the kernel types. -/
theorem HasTypeDescSigmaProjection.fstOfUniverseCodesTyped {profile : PolyProfile} (flag : UniverseFlag) :
    HasTypeDescSigmaProjection profile (TypingContext.empty : TypingContext profile 0)
      (fstCell (pairCell (universeCodeCell LevelExpr.lzero flag) (universeCodeCell LevelExpr.lzero flag)))
      (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag) :=
  HasTypeDescSigmaProjection.fstIntro TypingContext.empty
    (pairCell (universeCodeCell LevelExpr.lzero flag) (universeCodeCell LevelExpr.lzero flag))
    (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)
    (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)
    (HasTypeDescPairIntro.pairOfUniverseCodesTyped flag)

/-- **★ Closed forms: a Σ-projection-typed subject is `fst(p)` or `snd(p)`.**  Every term typed by
`HasTypeDescSigmaProjection` is `fst(p)` or `snd(p)`.  Two-arm free-index `cases`. -/
theorem HasTypeDescSigmaProjection.subjectIsSigmaProjection {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescSigmaProjection profile context subject classifier) :
    (∃ pairTerm : RawTerm scope, subject = fstCell pairTerm) ∨
    (∃ pairTerm : RawTerm scope, subject = sndCell pairTerm) := by
  cases derivation with
  | fstIntro pairTerm _firstType _secondType _pairTyped =>
      exact Or.inl ⟨pairTerm, rfl⟩
  | sndIntro pairTerm _firstType _secondType _pairTyped =>
      exact Or.inr ⟨pairTerm, rfl⟩

/-- **★ Typed content-projection ι-computation (first projection).**  A typed `fst` of a `pair` is typed at the
first component type `A`, ι-reduces to the FIRST component (`Step.iotaFstPair`), and that component is typed at
`A`.  The content-projection typed ι: the eliminator COMPUTES and the reduct's typing is the first-component
hypothesis verbatim.  Constructor-side: SR-free and propext-free. -/
theorem fstProjectionIotaComputesTyped {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (firstValue secondValue firstType secondType : RawTerm scope)
    (firstTyped : HasTypeDescPi profile context firstValue firstType)
    (secondTyped : HasTypeDescPi profile context secondValue secondType) :
    HasTypeDescSigmaProjection profile context
      (fstCell (pairCell firstValue secondValue)) firstType ∧
    Step (fstCell (pairCell firstValue secondValue)) firstValue ∧
    HasTypeDescPi profile context firstValue firstType := by
  refine ⟨?_, Step.iotaFstPair, firstTyped⟩
  exact HasTypeDescSigmaProjection.fstIntro context (pairCell firstValue secondValue)
    firstType secondType
    (HasTypeDescPairIntro.pairIntro context firstValue secondValue firstType secondType
      firstTyped secondTyped)

/-- **★ Typed content-projection ι-computation (second projection).**  The `snd` mirror of
`fstProjectionIotaComputesTyped`: a typed `snd` of a `pair` ι-reduces to the SECOND component
(`Step.iotaSndPair`), typed at the second component type `B`. -/
theorem sndProjectionIotaComputesTyped {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (firstValue secondValue firstType secondType : RawTerm scope)
    (firstTyped : HasTypeDescPi profile context firstValue firstType)
    (secondTyped : HasTypeDescPi profile context secondValue secondType) :
    HasTypeDescSigmaProjection profile context
      (sndCell (pairCell firstValue secondValue)) secondType ∧
    Step (sndCell (pairCell firstValue secondValue)) secondValue ∧
    HasTypeDescPi profile context secondValue secondType := by
  refine ⟨?_, Step.iotaSndPair, secondTyped⟩
  exact HasTypeDescSigmaProjection.sndIntro context (pairCell firstValue secondValue)
    firstType secondType
    (HasTypeDescPairIntro.pairIntro context firstValue secondValue firstType secondType
      firstTyped secondTyped)

end FX1Poly.Typed
