import FX1Poly.Typed.SimplyTypedTermFundamentalLevelFree
import FX1Poly.Typed.SimplyTypedNormalForm
import FX1Poly.Typed.SimplyTypedTermSubjectReductionLevelFree
import FX1Poly.Core.RawTermNF
import FX1Poly.Core.Step
import FX1Poly.Core.ExistsStepOfNotNormal

/-! # FX1Poly/Typed/SimplyTypedTermCanonicityLevelFree
    — canonicity (progress) for the simply-typed fragment: closed normal forms are lambdas.

**OFF-PATH CROSSCHECK (supersession map, 2026-06-05): this is the LEVEL-FREE simply-typed canonicity — an
independent STLC crosscheck leg, NOT the kernel canonicity (SN-047..049 on `HasTypeDescPi`).  Off the kernel
critical path; retained, not deleted.**

The classic STLC capstone, the last piece of the simply-typed metatheory.  In `SimplyTypedTermLF` (var/app/
lam over universe-code/arrow types, no constants), the only closed normal forms are lambdas — every
would-be base-type value is a neutral application spine, and a closed spine's head variable is impossible.

* `LnNeutral` — a term is neutral if it is a variable or an application whose function is neutral.
* `lnNeutral_scopeZero_absurd` — at the empty scope there are no neutrals (the head variable inhabits
  `Fin 0`).
* `isStepNormalForm_appCell_function` — a normal application has a normal function (a function step would
  lift to a parent step via `cong`).
* `SimplyTypedTermLF.canonicalSplit` — a normal simply-typed term is neutral or a lambda (induct on typing;
  the app case recurses on the function: neutral function → neutral app; lambda function → β-redex, not
  normal).
* `SimplyTypedTermLF.closedNormalIsLambda` — **canonicity**: a closed simply-typed term in normal form is a
  lambda (the split's neutral branch is killed by `lnNeutral_scopeZero_absurd`).
* `SimplyTypedTermLF.normalFormIsLambda` — **the capstone**: every closed simply-typed term normalizes to a
  lambda (canonicity composed with type-preserving normalization, `normalForm_typed` +
  `normalForm_isStepNormalForm`).

With this the simply-typed fragment has the complete classic metatheory suite: strong normalization,
confluence, decidable conversion, a canonical normal form, subject reduction, type-preserving normalization,
and now canonicity — all zero-axiom.

## Zero-axiom verification

`canonicalSplit` inducts on the typing derivation, discharging the β-redex case via `Step.beta` +
`isStepNormalForm_blocks_step` and the child-normality side-condition via `exists_step_of_not_isStepNormalForm`
+ `Step.cong`/`StepChildren.here`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Gated per declaration in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- A neutral simply-typed term: a variable, or an application whose function is neutral.  At scope 0 there
are no neutrals (the head variable is impossible), so closed normal forms are lambdas. -/
inductive LnNeutral {scope : Nat} : RawTerm scope → Prop
  | var (index : Fin scope) : LnNeutral (variableCell index)
  | app {functionTerm argument : RawTerm scope} (functionNeutral : LnNeutral functionTerm) :
      LnNeutral (appCell functionTerm argument)

/-- A neutral term at the empty scope is impossible (its head variable would inhabit `Fin 0`). -/
theorem lnNeutral_scopeZero_absurd {term : RawTerm 0} (neutral : LnNeutral term) : False := by
  induction neutral with
  | var index => exact index.elim0
  | app _functionNeutral ih => exact ih

/-- Child normality: a normal application has a normal function.  A function step would lift to a parent step
through `cong`, contradicting the application's normality. -/
theorem isStepNormalForm_appCell_function {scope : Nat} {functionTerm argument : RawTerm scope}
    (normal : RawTerm.isStepNormalForm (appCell functionTerm argument)) :
    RawTerm.isStepNormalForm functionTerm := by
  by_cases hFunctionNormal : RawTerm.isStepNormalForm functionTerm
  · exact hFunctionNormal
  · exfalso
    obtain ⟨functionAfter, functionStep⟩ := exists_step_of_not_isStepNormalForm hFunctionNormal
    have parentStep : Step (appCell functionTerm argument) (appCell functionAfter argument) :=
      Step.cong .gen_app ()
        (StepChildren.here
          (RawTermChildren.childCons argument RawTermChildren.childNil : RawTermChildren [0] scope)
          functionStep)
    exact RawTerm.isStepNormalForm_blocks_step normal _ parentStep

/-- **Canonical split.**  A normal simply-typed term is neutral or a lambda.  Inducts on the typing
derivation: a variable is neutral; a lambda is a lambda; an application's function is normal (child
normality) so the IH applies — a neutral function makes the application neutral, while a lambda function
would make the application a β-redex, contradicting normality. -/
theorem SimplyTypedTermLF.canonicalSplit {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {term type : RawTerm scope}
    (typed : SimplyTypedTermLF context term type) :
    RawTerm.isStepNormalForm term → LnNeutral term ∨ ∃ body, term = lamCell body := by
  induction typed with
  | var index =>
      intro _normal
      exact Or.inl (LnNeutral.var index)
  | @app sourceScope sourceContext functionTerm argument domainCode codomainBase
      functionTyped argumentTyped ihFunction _ihArgument =>
      intro normalApp
      have normalFunction := isStepNormalForm_appCell_function normalApp
      rcases ihFunction normalFunction with functionNeutral | ⟨body, functionEq⟩
      · exact Or.inl (LnNeutral.app functionNeutral)
      · subst functionEq
        exact absurd Step.beta (RawTerm.isStepNormalForm_blocks_step normalApp _)
  | @lam sourceScope sourceContext body domainCode codomainBase _domainExpr _codomainExpr _bodyTyped _ih =>
      intro _normal
      exact Or.inr ⟨body, rfl⟩

/-- **Canonicity.**  A closed simply-typed term in normal form is a lambda — the canonical split's neutral
branch is impossible at the empty scope. -/
theorem SimplyTypedTermLF.closedNormalIsLambda {profile : PolyProfile}
    {term type : RawTerm 0}
    (typed : SimplyTypedTermLF (TypingContext.empty : TypingContext profile 0) term type)
    (normal : RawTerm.isStepNormalForm term) :
    ∃ body, term = lamCell body := by
  rcases typed.canonicalSplit normal with neutral | lambda
  · exact absurd neutral lnNeutral_scopeZero_absurd
  · exact lambda

/-- **Every closed simply-typed term normalizes to a lambda.**  Canonicity composed with type-preserving
normalization: the canonical normal form of a closed simply-typed term is a lambda (`normalForm_typed`
supplies its typing, `normalForm_isStepNormalForm` its normality, and canonicity concludes the shape). -/
theorem SimplyTypedTermLF.normalFormIsLambda {profile : PolyProfile}
    {term type : RawTerm 0}
    (typed : SimplyTypedTermLF (TypingContext.empty : TypingContext profile 0) term type) :
    ∃ body, typed.normalForm = lamCell body :=
  typed.normalForm_typed.closedNormalIsLambda typed.normalForm_isStepNormalForm

end FX1Poly.Typed
