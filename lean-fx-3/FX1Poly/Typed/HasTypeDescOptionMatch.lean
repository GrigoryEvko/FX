import FX1Poly.Typed.HasTypeDescOptionIntro
import FX1Poly.Core.RawTermSubst0Commute

/-! # FX1Poly/Typed/HasTypeDescOptionMatch — the Option ELIMINATOR + the first MIXED-ι typed computation
    (DI-5c: the option eliminator — the FIRST eliminator whose two ι rules have DIFFERENT shapes).

DI-5a (`boolElim`) had branch-SELECTION ι (`boolElim(boolTrue, t, e) ↝ t`).  DI-5b (`eitherMatch`) had APP-CHAIN
ι (`eitherMatch(eitherInl(v), l, r) ↝ app(l, v)`).  `optionMatch` is the first eliminator to use BOTH at once:

  * `optionMatch(optionNone, n, s) ↝ n` — branch-SELECTION (`Step.iotaOptionMatchNone`, the boolElim shape: the
    None branch `n` is a VALUE at the result type).
  * `optionMatch(optionSome(v), n, s) ↝ app(s, v)` — APP-CHAIN (`Step.iotaOptionMatchSome`, the eitherMatch
    shape: the Some branch `s` is a FUNCTION `A → C`, applied to the wrapped value).

So the judgment carries a value branch AND a function branch, and the two typed-ι theorems exercise the two
shapes respectively.  Following the established cascade-free pattern (a brand-new standalone judgment), consuming
`HasTypeDescOptionIntro` (DI-2c) for the scrutinee premise.

  * `optionMatchCell` — the `gen_optionMatch` cell (arity 3, `[0, 0, 0]`).
  * `HasTypeDescOptionMatch` — the judgment: `optionMatch(s, n, sm) : C` from a scrutinee typed at `option(A)`
    (by the option-intro engine — so it is `optionNone`/`optionSome`), a None branch `n : C` (value, by the grown
    engine) and a Some branch `sm : A → C` (the non-dependent arrow `piTyCodeCell A (weaken C)`, by the grown
    engine).
  * `HasTypeDescOptionMatch.subjectIsOptionMatch` — the free-index closed-forms inversion.
  * `optionMatchNoneIotaComputesTyped` (★, branch-selection) — a typed `optionMatch` on `optionNone` is typed at
    `C`, ι-reduces to the None branch, and that branch is typed at `C` (the boolElim-shape typed ι).
  * `optionMatchSomeIotaComputesTyped` (★, app-chain) — a typed `optionMatch` on `optionSome(v)` ι-reduces to
    `app(sm, v)`, typed at `C` via `piElim` with the non-dependent codomain `(weaken C).subst0 v` collapsing to
    `C` (`RawTerm.weaken_subst_singleton`) — the eitherMatch-shape typed ι.

## The SR-free, propext-free framing (as DI-5a/DI-5b)

Constructor-side: each elim is BUILT from the branch typings, the reduct's typing is the branch typing
(None case) or `piElim` from the same hypotheses (Some case).  No derivation casing (no cons-index propext
trap), no branch-congruence (the full SR consumes the grown master SR / GrownCtxConv-5 #842).  The genuinely-new content
is that ONE eliminator now demonstrates BOTH ι shapes typed-and-computing.

## Zero-axiom

A single-arm positive inductive; the ι-computation theorems are direct constructions (`optionMatchIntro` +
`optionNoneIntro`/`optionSomeIntro` + `Step.iotaOptionMatchNone`/`Some` + `HasTypeDescPi.piElim` +
`RawTerm.weaken_subst_singleton`); the inversion is a free-index `cases` with `rfl`.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- The option eliminator cell `optionMatch(scrutinee, noneBranch, someBranch)` — `gen_optionMatch` (arity 3,
`binderShifts = [0, 0, 0]`). -/
def optionMatchCell {scope : Nat} (scrutinee noneBranch someBranch : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_optionMatch ()
    (.childCons scrutinee (.childCons noneBranch (.childCons someBranch .childNil)))

/-- **The option eliminator judgment.**  A standalone layer typing the non-dependent `optionMatch`:
`optionMatch(s, n, sm) : C` when the scrutinee is typed at `option(A)` (by the option-intro engine), the None
branch is `n : C` (a value, by the grown engine) and the Some branch is `sm : A → C` (the non-dependent arrow
`piTyCodeCell A (weaken C)`, by the grown engine).  The value-branch/function-branch split is what lets the two
ι rules take their two shapes. -/
inductive HasTypeDescOptionMatch (profile : PolyProfile) :
    {scope : Nat} → TypingContext profile scope → RawTerm scope → RawTerm scope → Prop where
  | optionMatchIntro {scope : Nat} (context : TypingContext profile scope)
      (scrutinee noneBranch someBranch elementType resultType : RawTerm scope)
      (scrutineeTyped :
        HasTypeDescOptionIntro profile context scrutinee (optionTypeCell elementType))
      (noneBranchTyped : HasTypeDescPi profile context noneBranch resultType)
      (someBranchTyped :
        HasTypeDescPi profile context someBranch (piTyCodeCell elementType (RawTerm.weaken resultType))) :
      HasTypeDescOptionMatch profile context
        (optionMatchCell scrutinee noneBranch someBranch) resultType

/-- **★ Closed forms: an option-match-typed subject is an `optionMatchCell`.**  Every term typed by
`HasTypeDescOptionMatch` is `optionMatch(s, n, sm)`.  Free-index single-arm `cases`. -/
theorem HasTypeDescOptionMatch.subjectIsOptionMatch {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescOptionMatch profile context subject classifier) :
    ∃ (scrutinee noneBranch someBranch : RawTerm scope),
      subject = optionMatchCell scrutinee noneBranch someBranch := by
  cases derivation with
  | optionMatchIntro scrutinee noneBranch someBranch _elementType _resultType
      _scrutineeTyped _noneBranchTyped _someBranchTyped =>
      exact ⟨scrutinee, noneBranch, someBranch, rfl⟩

/-- **★ Typed branch-selection ι-computation (None case).**  A typed `optionMatch` on `optionNone` is typed at
`C`, ι-reduces to the None branch (`Step.iotaOptionMatchNone`), and that branch is typed at `C`.  The
boolElim-shape typed ι (the reduct IS the selected value branch).  Constructor-side: SR-free and propext-free.
The `optionNone` scrutinee typing needs the element-type-formedness witness (the `None` asymmetry). -/
theorem optionMatchNoneIotaComputesTyped {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (noneBranch someBranch elementType resultType : RawTerm scope)
    (elementLevel : LevelExpr) (flag : UniverseFlag)
    (elementTypeFormed :
      HasTypeDescPi profile context elementType (universeCodeCell elementLevel flag))
    (noneBranchTyped : HasTypeDescPi profile context noneBranch resultType)
    (someBranchTyped :
      HasTypeDescPi profile context someBranch (piTyCodeCell elementType (RawTerm.weaken resultType))) :
    HasTypeDescOptionMatch profile context
      (optionMatchCell optionNoneCell noneBranch someBranch) resultType ∧
    Step (optionMatchCell optionNoneCell noneBranch someBranch) noneBranch ∧
    HasTypeDescPi profile context noneBranch resultType := by
  refine ⟨?_, Step.iotaOptionMatchNone, noneBranchTyped⟩
  exact HasTypeDescOptionMatch.optionMatchIntro context optionNoneCell noneBranch someBranch
    elementType resultType
    (HasTypeDescOptionIntro.optionNoneIntro context elementType elementLevel flag elementTypeFormed)
    noneBranchTyped someBranchTyped

/-- **★ Typed app-chain ι-computation (Some case).**  A typed `optionMatch` on `optionSome(value)` is typed at
`C`, ι-reduces to `app(someBranch, value)` (`Step.iotaOptionMatchSome`), and that application is typed at `C`.
The eitherMatch-shape typed ι (the reduct is the Some FUNCTION applied to the payload), with the non-dependent
codomain `(weaken C).subst0 value` collapsing to `C` (`RawTerm.weaken_subst_singleton`, restated subst0-form so
the syntactic `rw` matches).  Constructor-side: SR-free and propext-free. -/
theorem optionMatchSomeIotaComputesTyped {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (value noneBranch someBranch elementType resultType : RawTerm scope)
    (valueTyped : HasTypeDescPi profile context value elementType)
    (noneBranchTyped : HasTypeDescPi profile context noneBranch resultType)
    (someBranchTyped :
      HasTypeDescPi profile context someBranch (piTyCodeCell elementType (RawTerm.weaken resultType))) :
    HasTypeDescOptionMatch profile context
      (optionMatchCell (optionSomeCell value) noneBranch someBranch) resultType ∧
    Step (optionMatchCell (optionSomeCell value) noneBranch someBranch)
      (appCell someBranch value) ∧
    HasTypeDescPi profile context (appCell someBranch value) resultType := by
  refine ⟨?_, Step.iotaOptionMatchSome, ?_⟩
  · exact HasTypeDescOptionMatch.optionMatchIntro context (optionSomeCell value) noneBranch someBranch
      elementType resultType
      (HasTypeDescOptionIntro.optionSomeIntro context value elementType valueTyped)
      noneBranchTyped someBranchTyped
  · have appTyped := HasTypeDescPi.piElim someBranchTyped valueTyped
    -- `piElim` types the reduct at `(weaken resultType).subst0 value`; the non-dependent codomain collapses to
    -- `resultType`.  `weaken_subst_singleton` is stated in `subst (singleton …)` form, defeq to the `subst0`
    -- form `piElim` produced — restate it in `subst0` form so `rw` matches (the DI-5b app-chain gotcha).
    have codomainCollapses : (RawTerm.weaken resultType).subst0 value = resultType :=
      RawTerm.weaken_subst_singleton resultType value
    rw [codomainCollapses] at appTyped
    exact appTyped

end FX1Poly.Typed
