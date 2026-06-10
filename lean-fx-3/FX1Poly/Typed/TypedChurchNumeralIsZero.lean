import FX1Poly.Typed.TypedChurchNumeralComputeGeneral
import FX1Poly.Typed.TypedChurchNegation

/-! # FX1Poly/Typed/TypedChurchNumeralIsZero — the term model COMPUTES the `isZero` predicate

`TypedChurchNumeralComputeGeneral` proved the general iteration computation
(`churchNumeralLambda n` applied to `(A, f, x) ↝* f^n x`); `TypedChurchNegation` proved the term model
computes Boolean negation.  This file combines the two threads to compute the first genuine PREDICATE on the
Church numerals — `isZero`, a `ChurchNat → ChurchBool` decision — closing the loop from "the encoding holds
numerals" to "the encoding RUNS algorithms that consume them".

The Church-encoded `isZero` feeds the numeral the constant-false step over the base `churchTrue`:

  `churchIsZero = λn. n placeholder (λ_. churchFalse) churchTrue`

A Church numeral `n` is the iterator `λA.λf.λx. f^n x`; applied to `(placeholder, const churchFalse,
churchTrue)` it computes `(const churchFalse)^n churchTrue`.  At `n = 0` the iterate is just the base
`churchTrue`; at `n = k+1` the OUTERMOST `const churchFalse` application ignores its argument and collapses the
whole iterate to `churchFalse` in a single β-step — so:

  * `churchIsZero_onZero`  (★) : `churchIsZero (numeral 0)     ↝* churchTrue`  — zero is zero;
  * `churchIsZero_onSucc`  (★) : `churchIsZero (numeral (k+1)) ↝* churchFalse` — a successor is not, for EVERY `k`;
  * `churchIsZero_discriminates`     : the two outputs are non-convertible, so the predicate genuinely separates
    zero from nonzero (reusing `churchTrue_notConvertible_churchFalse`).

The successor case uses the general iteration lemma at an ARBITRARY depth `k+1` — `isZero` decides the WHOLE
numeral family, not fixed fixtures.

## Why this is a COMPUTATIONAL result, not a typed one (the predicativity observation)

A typed `isZero : ChurchNat → ChurchBool` would instantiate the numeral's type binder `A : Type@0` at
`A := ChurchBool`.  But `ChurchBool = Π(A:Type@0).Π(t:A).Π(f:A).A` lives at `Type@1` (one universe above its
`A:Type@0` binder), so it is NOT a legal `Type@0` argument to the iterator — the predicative stratification
`Type@n : Type@(n+1)` (mechanized in `UNIV-PREDICATIVE`, the engine is non-cumulative) forbids the
instantiation.  This is exactly the impredicativity that System-F-style Church recursion silently relies on and
that FX rejects by design.  So `isZero`, like the negation in `TypedChurchNegation`, ships as a purely
OPERATIONAL `StepStar`/`Conv` fact: the type argument is the inert `branchMotivePlaceholder`, never inspected
by the reduction, and the computation is faithful regardless.  The predicate is genuinely COMPUTED; only its
predicatively-typed packaging is unavailable — a precise demonstration of where the predicative discipline
bites the untyped Church toolkit.

## Zero-axiom verification

Three β-reshapes — `constFalseStep_appReducesToFalse` (the const-false collapse via `weaken_subst_singleton`),
`churchIsZeroBody_substitutes` (the outer β-contractum, three weakened constants cancelled), and the shipped
`churchNumeral_appliedReducesToIterate_general` — chained by `StepStar.trans`/`trans_compose`.  The
discrimination reuses `Conv.fromStepStar` + `Conv.trans`/`Conv.sym` + `churchTrue_notConvertible_churchFalse`.
No `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, or `omega`.  Gated per-decl in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe StepStar

/-- The constant-false step `λ_. churchFalse` — a unary function ignoring its argument, returning `churchFalse`
(`churchFalse` is closed, so it is weakened under the binder it never references). -/
abbrev constFalseStep : RawTerm 0 :=
  lamCell (universeCodeCell LevelExpr.lzero UniverseFlag.standard) (RawTerm.weaken churchFalseLambda)

/-- Applying the constant-false step to ANY argument β-reduces straight to `churchFalse` — the weakened body
ignores the substituted argument (`weaken_subst_singleton`).  The single β-step that collapses each successor
numeral's iterate to `churchFalse`. -/
theorem constFalseStep_appReducesToFalse (argument : RawTerm 0) :
    Step (appCell constFalseStep argument) churchFalseLambda := by
  have reshape : RawTerm.subst0 (RawTerm.weaken churchFalseLambda) argument = churchFalseLambda := by
    unfold RawTerm.subst0
    exact RawTerm.weaken_subst_singleton churchFalseLambda argument
  rw [← reshape]
  exact Step.beta

/-- ★ The Church-encoded `isZero` combinator `λn. n placeholder (λ_. churchFalse) churchTrue`.  It feeds the
bound numeral `n` (de Bruijn `var 0`) the constant-false step over the base `churchTrue`; the three arguments
are weakened under the `λn.` binder.  The type argument is the inert `branchMotivePlaceholder` (never inspected
by the iteration — see the predicativity note in the file header). -/
abbrev churchIsZeroLambda : RawTerm 0 :=
  lamCell (universeCodeCell LevelExpr.lzero UniverseFlag.standard)
    (appCell (appCell (appCell RawTerm.newestVar (RawTerm.weaken branchMotivePlaceholder))
      (RawTerm.weaken constFalseStep)) (RawTerm.weaken churchTrueLambda))

/-- The β-contractum reshape: substituting a numeral for the bound `n` cancels the three weakened constants
(`weaken_subst_singleton`) and resolves the head `var 0` to the numeral — yielding the numeral applied to the
placeholder type, the constant-false step, and `churchTrue`.  The bridge from the outer β-step to the iteration
lemma. -/
theorem churchIsZeroBody_substitutes (numeralArg : RawTerm 0) :
    RawTerm.subst0 (appCell (appCell (appCell RawTerm.newestVar (RawTerm.weaken branchMotivePlaceholder))
      (RawTerm.weaken constFalseStep)) (RawTerm.weaken churchTrueLambda)) numeralArg
      = appCell (appCell (appCell numeralArg branchMotivePlaceholder) constFalseStep) churchTrueLambda := by
  unfold RawTerm.subst0
  show appCell (appCell (appCell (RawTerm.subst (RawTermSubst.singleton numeralArg) RawTerm.newestVar)
      (RawTerm.subst (RawTermSubst.singleton numeralArg) (RawTerm.weaken branchMotivePlaceholder)))
      (RawTerm.subst (RawTermSubst.singleton numeralArg) (RawTerm.weaken constFalseStep)))
      (RawTerm.subst (RawTermSubst.singleton numeralArg) (RawTerm.weaken churchTrueLambda))
    = appCell (appCell (appCell numeralArg branchMotivePlaceholder) constFalseStep) churchTrueLambda
  rw [RawTerm.weaken_subst_singleton branchMotivePlaceholder numeralArg,
      RawTerm.weaken_subst_singleton constFalseStep numeralArg,
      RawTerm.weaken_subst_singleton churchTrueLambda numeralArg,
      show RawTerm.subst (RawTermSubst.singleton numeralArg) RawTerm.newestVar = numeralArg from rfl]

/-- ★ `isZero` of ZERO computes to `churchTrue`: `churchIsZero (numeral 0) ↝* churchTrue`.  One outer β feeds
`churchNumeralLambda 0` into the selector; the iteration lemma at depth `0` returns the base `churchTrue`
directly (the empty iterate `iteratedApplication 0 _ churchTrue = churchTrue`). -/
theorem churchIsZero_onZero :
    StepStar (appCell churchIsZeroLambda (churchNumeralLambda 0)) churchTrueLambda :=
  StepStar.trans
    (by rw [← churchIsZeroBody_substitutes (churchNumeralLambda 0)]; exact Step.beta)
    (churchNumeral_appliedReducesToIterate_general 0 branchMotivePlaceholder constFalseStep churchTrueLambda)

/-- ★ `isZero` of a SUCCESSOR numeral computes to `churchFalse`: `churchIsZero (numeral (k+1)) ↝* churchFalse`,
for EVERY `k`.  One outer β feeds `churchNumeralLambda (k+1)` into the selector; the iteration lemma reduces it
to `(const churchFalse)^(k+1) churchTrue`, whose OUTERMOST `const churchFalse` application then collapses to
`churchFalse` in a single β-step (`constFalseStep_appReducesToFalse`) — the inner iterate is discarded
unevaluated. -/
theorem churchIsZero_onSucc (priorDepth : Nat) :
    StepStar (appCell churchIsZeroLambda (churchNumeralLambda (priorDepth + 1))) churchFalseLambda :=
  StepStar.trans
    (by rw [← churchIsZeroBody_substitutes (churchNumeralLambda (priorDepth + 1))]; exact Step.beta)
    (StepStar.trans_compose
      (churchNumeral_appliedReducesToIterate_general (priorDepth + 1) branchMotivePlaceholder
        constFalseStep churchTrueLambda)
      (StepStar.trans
        (constFalseStep_appReducesToFalse
          (iteratedApplication priorDepth constFalseStep churchTrueLambda))
        (StepStar.refl _)))

/-- ★ The predicate genuinely SEPARATES zero from nonzero: `churchIsZero (numeral 0)` and
`churchIsZero (numeral 1)` are non-convertible — they compute to `churchTrue` and `churchFalse` respectively,
which `churchTrue_notConvertible_churchFalse` proves distinct.  A hypothetical conversion of the two `isZero`
calls would, through their reductions, force `churchTrue =Conv churchFalse`. -/
theorem churchIsZero_discriminates :
    ¬ Conv (appCell churchIsZeroLambda (churchNumeralLambda 0))
        (appCell churchIsZeroLambda (churchNumeralLambda 1)) := by
  intro convertibility
  exact churchTrue_notConvertible_churchFalse
    (Conv.trans (Conv.sym (Conv.fromStepStar churchIsZero_onZero))
      (Conv.trans convertibility (Conv.fromStepStar (churchIsZero_onSucc 0))))

end FX1Poly.Typed
