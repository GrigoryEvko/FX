import FX1Poly.Typed.SimplyTypedTermFundamentalLevelFree
import FX1Poly.Typed.SimplyTypedTermInversionLevelFree
import FX1Poly.Typed.SimplyTypedTermSubstLevelFree
import FX1Poly.Typed.SimplyTypedNormalForm
import FX1Poly.Core.StepInversion
import FX1Poly.Core.RawTermSubst0Commute
import FX1Poly.Core.Normalize

/-! # FX1Poly/Typed/SimplyTypedTermSubjectReductionLevelFree
    — subject reduction for the simply-typed fragment, culminating in TYPE-PRESERVING NORMALIZATION.

The capstone of the subject-reduction arc.  Reduction preserves typing, and — composed with the
weak-normalization normalizer — the canonical normal form of a closed simply-typed term is itself
simply-typed at the same type.

* `SimplyTypedTermLF.subjectReduction` — single-step SR: `ln Γ t T → Step t t' → ln Γ t' T`.
* `SimplyTypedTermLF.subjectReductionStar` — multi-step SR along a `StepStar` chain.
* `SimplyTypedTermLF.normalForm_typed` — **the gold payoff**: a closed simply-typed term's canonical normal
  form (`SimplyTypedNormalForm.normalForm`) is simply-typed at the same type.

`SimplyTypedTermLF` is the syntax-directed STLC (var/app/lam, no eliminators), so a raw `Step` out of an `ln`
term is only β or congruence — the 16 ι-reductions are structurally impossible (no eliminator generator).
The proof inducts on the typing derivation and inverts the `Step` per shape via the `StepInversion` library:

* `var` — `Step.no_step_from_var` refutes any step from a variable.
* `app` — `Step.from_app` splits into β / cong-function / cong-argument.  The β case inverts the function's
  `lam`-typing (`inversionLambda`), aligns the domain/codomain by injecting the Π-type equality, runs the
  substitution β-engine (`substituteUnderBinding`), and cancels the codomain weakening
  (`weaken_subst_singleton`: `(weaken cod)[arg] = cod`).  The cong cases recurse via the IHs.
* `lam` — `Step.from_lam` gives the single congruence-through-body case; recurse via the body IH.

`normalForm_typed` then threads the normalizer's reduction chain (`RawTerm.normalize_reducesTo`) through
`subjectReductionStar`: since `normalForm = normalize term stronglyNormalizingBare` reduces FROM the term,
its typing is inherited.

## Zero-axiom verification

Composes `Step.from_app` / `Step.from_lam` / `Step.no_step_from_var` (inversions), `inversionLambda`,
`substituteUnderBinding` (the β-engine), `weaken_subst_singleton`, and `normalize_reducesTo` — all
zero-axiom.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Gated
per declaration in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe Foundation

/-- **Single-step subject reduction.**  A reduction out of a simply-typed term lands a simply-typed term of
the same type.  Inducts on the typing derivation, inverting the `Step` per term shape. -/
theorem SimplyTypedTermLF.subjectReduction {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (typed : SimplyTypedTermLF context subject classifier) :
    ∀ {target : RawTerm scope}, Step subject target → SimplyTypedTermLF context target classifier := by
  induction typed with
  | var index =>
      intro target step
      exact absurd step Step.no_step_from_var
  | @app sourceScope sourceContext functionTerm argument domainCode codomainBase
      functionTyped argumentTyped ihFunction ihArgument =>
      intro target step
      rcases Step.from_app step with
        ⟨body, functionEq, targetEq⟩ | ⟨functionAfter, targetEq, functionStep⟩
        | ⟨argumentAfter, targetEq, argumentStep⟩
      · -- β: functionTerm = `lam body`, target = `body[argument]`
        subst functionEq
        subst targetEq
        obtain ⟨invDomain, invCodomain, typeEq, _invDomainExpr, _invCodomainExpr, bodyTyped⟩ :=
          functionTyped.inversionLambda
        injection typeEq with _ _ _ spineEq
        injection spineEq with _ _ _ domainEq tailEq
        injection tailEq with _ _ _ codomainWeakEq _
        subst domainEq
        rw [← codomainWeakEq] at bodyTyped
        have result := bodyTyped.substituteUnderBinding argument argumentTyped
        have cancel : RawTerm.subst0 (RawTerm.weaken codomainBase) argument = codomainBase :=
          RawTerm.weaken_subst_singleton codomainBase argument
        rwa [cancel] at result
      · subst targetEq
        exact SimplyTypedTermLF.app (ihFunction functionStep) argumentTyped
      · subst targetEq
        exact SimplyTypedTermLF.app functionTyped (ihArgument argumentStep)
  | @lam sourceScope sourceContext body domainCode codomainBase
      domainExpr codomainExpr bodyTyped ihBody =>
      intro target step
      obtain ⟨bodyAfter, targetEq, bodyStep⟩ := Step.from_lam step
      subst targetEq
      exact SimplyTypedTermLF.lam domainExpr codomainExpr (ihBody bodyStep)

/-- **Multi-step subject reduction.**  Typing is preserved along any `StepStar` reduction chain (iterate
`subjectReduction` over the chain). -/
theorem SimplyTypedTermLF.subjectReductionStar {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (typed : SimplyTypedTermLF context subject classifier) :
    ∀ {target : RawTerm scope}, StepStar subject target → SimplyTypedTermLF context target classifier := by
  intro target chain
  revert typed
  induction chain with
  | refl => exact fun typed => typed
  | trans headStep _tailChain tailIH =>
      exact fun typed => tailIH (typed.subjectReduction headStep)

/-- **Type-preserving normalization (the SR-arc gold payoff).**  The canonical normal form of a closed
simply-typed term is itself simply-typed at the same type: the normalizer's reduction chain
(`normalize_reducesTo`) is threaded through multi-step subject reduction. -/
theorem SimplyTypedTermLF.normalForm_typed {profile : PolyProfile}
    {term type : RawTerm 0}
    (typed : SimplyTypedTermLF (TypingContext.empty : TypingContext profile 0) term type) :
    SimplyTypedTermLF (TypingContext.empty : TypingContext profile 0) typed.normalForm type :=
  typed.subjectReductionStar (RawTerm.normalize_reducesTo term typed.stronglyNormalizingBare)

end FX1Poly.Typed
