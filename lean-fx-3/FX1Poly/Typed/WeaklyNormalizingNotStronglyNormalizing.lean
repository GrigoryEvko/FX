import FX1Poly.Typed.UntypedOmegaNotStronglyNormalizing

/-! # Foundation/PolyCell/Typed/WeaklyNormalizingNotStronglyNormalizing
    - weak normalization does NOT imply strong normalization in the raw calculus

A second raw-reduction pathology, sharper than the Ω witness in
`UntypedOmegaNotStronglyNormalizing.lean`.  Ω = `(λx. x x)(λx. x x)` has NO
normalizing reduction path at all — every reduction loops.  This file exhibits
the textbook separating example (Barendregt) of a closed raw term that DOES have
a terminating reduction yet is still NOT strongly normalizing:

  `(λx. Type@levelExpr) Ω`

The constant function `λx. Type@levelExpr` discards its argument.  So the term
has two kinds of reduction:

  * the **β path** fires the outer redex, discards the (divergent) argument, and
    lands on the normal form `Type@levelExpr` in a single step — a terminating
    reduction, so the term is WEAKLY normalizing;
  * the **argument path** reduces the discarded `Ω` in place (congruence into the
    second child of the application), looping back to the same term forever — so
    the term is NOT strongly normalizing.

Hence in the FX raw reduction, weak normalization (∃ a reduction to a normal
form) does NOT imply strong normalization (ALL reductions terminate).  This is
exactly why SN-043 (`HasTypeDescPi Γ t T → IsStronglyNormalizing t`) proves the
STRONG property: a merely weakly-normalizing system can still diverge under an
adversarial reduction strategy (here, "always reduce the discarded argument"),
so decidable conversion and the normalizer need the strong guarantee that typing
delivers — the weak one is not enough.

Everything is about the raw `Step` relation; no typing derivation is consulted.
The β path uses `Step.beta` (the discarded body is a nullary universe-code leaf,
so `subst0` is the identity on it by computation — no cancellation lemma needed);
the loop uses the uniform congruence rule `Step.cong` with `StepChildren.there`
to reach the argument position, fed the `Step Ω Ω` self-step from the Ω witness.
Zero-axiom.
-/

namespace FX1Poly.Typed

open FX1Poly.Core
open FX1Poly.Universe
open StepStar

/-- `λx. Type@levelExpr` — a constant function whose body ignores the bound
variable.  The body is a nullary universe-code leaf living at scope `1` (under
the binder), so the abstraction discards whatever it is applied to. -/
def discardingConstantLambda (levelExpr : LevelExpr) (flag : UniverseFlag) : RawTerm 0 :=
  lamCell (universeCodeCell levelExpr flag)

/-- `(λx. Type@levelExpr) Ω` — the constant function applied to the divergent Ω
combinator (from `UntypedOmegaNotStronglyNormalizing`). -/
def discardingApplicationOnOmega (levelExpr : LevelExpr) (flag : UniverseFlag) : RawTerm 0 :=
  appCell (discardingConstantLambda levelExpr flag) omegaCombinator

/-- **β path (terminating).**  The outer redex contracts, discarding the
argument, and lands on the body `Type@levelExpr` in one step.  The reduct equals
the body on the nose: `subst0` of a nullary leaf is the leaf by computation, so
no substitution-after-weakening cancellation lemma is required. -/
theorem discardingApplicationOnOmega_betaReachesBody
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    Step (discardingApplicationOnOmega levelExpr flag) (universeCodeCell levelExpr flag) :=
  Step.beta

/-- The β reduct `Type@levelExpr` is a normal form — it has no outgoing `Step`. -/
theorem discardedBody_isNormalForm (levelExpr : LevelExpr) (flag : UniverseFlag)
    (target : RawTerm 0) :
    Step (universeCodeCell levelExpr flag) target → False :=
  fun step => noStep_universeCode (levelExpr, flag) step

/-- **Argument path (non-terminating).**  Reducing the discarded `Ω` argument in
place (the uniform congruence rule stepping the second child of the application)
loops back to the same term: `(λx. Type@levelExpr) Ω ↝ (λx. Type@levelExpr) Ω`. -/
theorem discardingApplicationOnOmega_argumentSelfLoop
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    Step (discardingApplicationOnOmega levelExpr flag)
      (discardingApplicationOnOmega levelExpr flag) := by
  apply Step.cong .gen_app ()
  apply StepChildren.there
  apply StepChildren.here
  exact omegaCombinator_betaSelfStep

/-- The discarding application is NOT strongly normalizing: it self-loops, so it
cannot be accessible under the one-step-successor relation. -/
theorem discardingApplicationOnOmega_notStronglyNormalizing
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    ¬ IsStronglyNormalizing (discardingApplicationOnOmega levelExpr flag) :=
  fun stronglyNormalizing =>
    accessibleElementNotSelfRelated stronglyNormalizing
      (discardingApplicationOnOmega_argumentSelfLoop levelExpr flag)

/-- ★ Weak normalization does NOT imply strong normalization in the raw calculus.
There is a closed term with a one-step reduction to a normal form (so it IS
weakly normalizing) that is nonetheless NOT strongly normalizing — it also admits
an infinite reduction.  Witness: `(λx. Type@0) Ω`.  This is the exact reason
SN-043 proves the STRONG normalization property and not merely the weak one:
typing must rule out the adversarial "reduce the discarded argument forever"
strategy, which weak normalization alone permits. -/
theorem weaklyNormalizingDoesNotImplyStronglyNormalizing :
    ∃ subjectTerm normalFormReduct : RawTerm 0,
      Step subjectTerm normalFormReduct ∧
      (∀ furtherReduct, Step normalFormReduct furtherReduct → False) ∧
      ¬ IsStronglyNormalizing subjectTerm :=
  ⟨discardingApplicationOnOmega LevelExpr.lzero UniverseFlag.standard,
    universeCodeCell LevelExpr.lzero UniverseFlag.standard,
    discardingApplicationOnOmega_betaReachesBody LevelExpr.lzero UniverseFlag.standard,
    discardedBody_isNormalForm LevelExpr.lzero UniverseFlag.standard,
    discardingApplicationOnOmega_notStronglyNormalizing LevelExpr.lzero UniverseFlag.standard⟩

end FX1Poly.Typed
