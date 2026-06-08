import FX1Poly.Typed.HasTypeDescEitherIntro
import FX1Poly.Core.RawTermSubst0Commute

/-! # FX1Poly/Typed/HasTypeDescEitherMatch — the coproduct ELIMINATOR judgment + typed app-chain ι-computation
    (DI-5, the coproduct eliminator: the SECOND ι shape after boolElim's branch-selection).

DI-5a typed `boolElim`, whose ι SELECTS a branch directly (`boolElim(boolTrue, t, e) ↝ t`).  `eitherMatch`
is the next eliminator and the first with the **app-chain** ι shape: it APPLIES the matching handler to the
wrapped payload (`eitherMatch(eitherInl(v), l, r) ↝ app(l, v)`, `Step.iotaEitherMatchInl`).  So the branches
are FUNCTIONS (`A → C`, `B → C`), and the typed ι-computation's reduct is an APPLICATION typed by `piElim`.

Following the established cascade-free pattern (a brand-new standalone judgment).

  * `eitherMatchCell` — the `gen_eitherMatch` cell (arity 3, `[0, 0, 0]`).
  * `HasTypeDescEitherMatch` — the judgment: `eitherMatch(s, l, r) : C` from a scrutinee typed at
    `either(A, B)` (by the either-intro engine — so it is `eitherInl`/`eitherInr`) and two function branches
    `l : A → C`, `r : B → C` (typed at `piTyCodeCell A (weaken C)` / `piTyCodeCell B (weaken C)` — the
    non-dependent arrows, codomain weakened past the binder, by the grown engine).
  * `HasTypeDescEitherMatch.subjectIsEitherMatch` — the free-index closed-forms inversion.
  * `eitherMatchInlIotaComputesTyped` / `eitherMatchInrIotaComputesTyped` (★) — the typed app-chain
    ι-computation: a typed `eitherMatch` on an injection ι-reduces to the handler APPLIED to the payload, and
    that application is typed at `C`.  The reduct `app(l, v) : C` is built by `piElim` (`l : A → C`,
    `v : A`); the non-dependent arrow makes the elimination type `subst0 (weaken C) v = C` collapse
    (`RawTerm.weaken_subst_singleton`).  The eliminator COMPUTES and the computation PRESERVES TYPING.

## The SR-free, propext-free framing (as DI-5a)

Constructor-side: the elim is BUILT from the branch typings, the reduct's typing is BUILT by `piElim` from
the same hypotheses.  No derivation casing (no cons-index propext trap), no branch-congruence (the full SR
consumes the grown master SR / GCC-5 #842).  The genuinely-new content here vs DI-5a is the app-chain ι shape
— the reduct is an application, not a directly-selected branch.

## Zero-axiom

A single-arm positive inductive; the ι-computation theorems are direct constructions (`eitherMatchIntro` +
`eitherInlIntro`/`eitherInrIntro` + `Step.iotaEitherMatchInl`/`Inr` + `HasTypeDescPi.piElim` +
`RawTerm.weaken_subst_singleton`); the inversion is a free-index `cases` with `rfl`.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- The coproduct eliminator cell `eitherMatch(scrutinee, leftBranch, rightBranch)` — `gen_eitherMatch`
(arity 3, `binderShifts = [0, 0, 0]`). -/
def eitherMatchCell {scope : Nat} (scrutinee leftBranch rightBranch : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_eitherMatch ()
    (.childCons scrutinee (.childCons leftBranch (.childCons rightBranch .childNil)))

/-- **The coproduct eliminator judgment.**  A standalone layer typing the non-dependent `eitherMatch`:
`eitherMatch(s, l, r) : C` when the scrutinee is typed at `either(A, B)` (by the either-intro engine) and the
two branches are FUNCTIONS `l : A → C` and `r : B → C` (the non-dependent arrows `piTyCodeCell A (weaken C)` /
`piTyCodeCell B (weaken C)`, by the grown engine). -/
inductive HasTypeDescEitherMatch (profile : PolyProfile) :
    {scope : Nat} → TypingContext profile scope → RawTerm scope → RawTerm scope → Prop where
  | eitherMatchIntro {scope : Nat} (context : TypingContext profile scope)
      (scrutinee leftBranch rightBranch leftType rightType resultType : RawTerm scope)
      (scrutineeTyped :
        HasTypeDescEitherIntro profile context scrutinee (eitherTypeCell leftType rightType))
      (leftBranchTyped :
        HasTypeDescPi profile context leftBranch (piTyCodeCell leftType (RawTerm.weaken resultType)))
      (rightBranchTyped :
        HasTypeDescPi profile context rightBranch (piTyCodeCell rightType (RawTerm.weaken resultType))) :
      HasTypeDescEitherMatch profile context
        (eitherMatchCell scrutinee leftBranch rightBranch) resultType

/-- **★ Closed forms: an either-match-typed subject is an `eitherMatchCell`.**  Every term typed by
`HasTypeDescEitherMatch` is `eitherMatch(s, l, r)`.  Free-index single-arm `cases`. -/
theorem HasTypeDescEitherMatch.subjectIsEitherMatch {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescEitherMatch profile context subject classifier) :
    ∃ (scrutinee leftBranch rightBranch : RawTerm scope),
      subject = eitherMatchCell scrutinee leftBranch rightBranch := by
  cases derivation with
  | eitherMatchIntro scrutinee leftBranch rightBranch _leftType _rightType _resultType
      _scrutineeTyped _leftBranchTyped _rightBranchTyped =>
      exact ⟨scrutinee, leftBranch, rightBranch, rfl⟩

/-- **★ Typed app-chain ι-computation (inl case).**  A typed `eitherMatch` on `eitherInl(value)` is typed at
`C`, ι-reduces to `app(leftBranch, value)` (`Step.iotaEitherMatchInl`), and that application is typed at `C`.
The reduct's typing is `piElim` (`leftBranch : A → C`, `value : A`), with the non-dependent codomain
`subst0 (weaken C) value` collapsing to `C` by `RawTerm.weaken_subst_singleton`.  The eliminator COMPUTES
(app-chain) and the computation PRESERVES TYPING.  Constructor-side: SR-free and propext-free. -/
theorem eitherMatchInlIotaComputesTyped {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (value leftBranch rightBranch leftType rightType resultType : RawTerm scope)
    (rightLevel : LevelExpr) (flag : UniverseFlag)
    (valueTyped : HasTypeDescPi profile context value leftType)
    (rightTypeFormed : HasTypeDescPi profile context rightType (universeCodeCell rightLevel flag))
    (leftBranchTyped :
      HasTypeDescPi profile context leftBranch (piTyCodeCell leftType (RawTerm.weaken resultType)))
    (rightBranchTyped :
      HasTypeDescPi profile context rightBranch (piTyCodeCell rightType (RawTerm.weaken resultType))) :
    HasTypeDescEitherMatch profile context
      (eitherMatchCell (eitherInlCell value) leftBranch rightBranch) resultType ∧
    Step (eitherMatchCell (eitherInlCell value) leftBranch rightBranch)
      (appCell leftBranch value) ∧
    HasTypeDescPi profile context (appCell leftBranch value) resultType := by
  refine ⟨?_, Step.iotaEitherMatchInl, ?_⟩
  · exact HasTypeDescEitherMatch.eitherMatchIntro context (eitherInlCell value) leftBranch rightBranch
      leftType rightType resultType
      (HasTypeDescEitherIntro.eitherInlIntro context value leftType rightType rightLevel flag
        valueTyped rightTypeFormed)
      leftBranchTyped rightBranchTyped
  · have appTyped := HasTypeDescPi.piElim leftBranchTyped valueTyped
    -- `piElim` types the reduct at `(weaken resultType).subst0 value`; the non-dependent codomain
    -- collapses to `resultType`.  `weaken_subst_singleton` is stated in `subst (singleton …)` form,
    -- defeq to the `subst0` form `piElim` produced — restate it in `subst0` form so `rw` matches.
    have codomainCollapses : (RawTerm.weaken resultType).subst0 value = resultType :=
      RawTerm.weaken_subst_singleton resultType value
    rw [codomainCollapses] at appTyped
    exact appTyped

/-- **★ Typed app-chain ι-computation (inr case).**  The `eitherInr` mirror of
`eitherMatchInlIotaComputesTyped`: a typed `eitherMatch` on `eitherInr(value)` ι-reduces to
`app(rightBranch, value)`, typed at `C`. -/
theorem eitherMatchInrIotaComputesTyped {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (value leftBranch rightBranch leftType rightType resultType : RawTerm scope)
    (leftLevel : LevelExpr) (flag : UniverseFlag)
    (valueTyped : HasTypeDescPi profile context value rightType)
    (leftTypeFormed : HasTypeDescPi profile context leftType (universeCodeCell leftLevel flag))
    (leftBranchTyped :
      HasTypeDescPi profile context leftBranch (piTyCodeCell leftType (RawTerm.weaken resultType)))
    (rightBranchTyped :
      HasTypeDescPi profile context rightBranch (piTyCodeCell rightType (RawTerm.weaken resultType))) :
    HasTypeDescEitherMatch profile context
      (eitherMatchCell (eitherInrCell value) leftBranch rightBranch) resultType ∧
    Step (eitherMatchCell (eitherInrCell value) leftBranch rightBranch)
      (appCell rightBranch value) ∧
    HasTypeDescPi profile context (appCell rightBranch value) resultType := by
  refine ⟨?_, Step.iotaEitherMatchInr, ?_⟩
  · exact HasTypeDescEitherMatch.eitherMatchIntro context (eitherInrCell value) leftBranch rightBranch
      leftType rightType resultType
      (HasTypeDescEitherIntro.eitherInrIntro context value leftType rightType leftLevel flag
        valueTyped leftTypeFormed)
      leftBranchTyped rightBranchTyped
  · have appTyped := HasTypeDescPi.piElim rightBranchTyped valueTyped
    have codomainCollapses : (RawTerm.weaken resultType).subst0 value = resultType :=
      RawTerm.weaken_subst_singleton resultType value
    rw [codomainCollapses] at appTyped
    exact appTyped

end FX1Poly.Typed
