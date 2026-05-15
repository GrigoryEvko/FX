import LeanFX2.Reducibility.Basic

/-! # LeanFX2.Term.SN.Helpers — pure SN preservation lemmas

Pure strong-normalization preservation theorems shared by the Kripke
step-indexed candidate and Term-level SN endpoints.  Imports only the
bare SN foundation (`Reducibility.Basic`), so it stays disjoint from any
logical-relation predicate machinery.

## Contents

| Theorem                                           | Form                          |
| ------------------------------------------------- | ----------------------------- |
| `RawTerm.unit_isStronglyNormalizing`              | closed-leaf raw SN            |
| `RawTerm.boolTrue_isStronglyNormalizing`          | closed-leaf raw SN            |
| `RawTerm.boolFalse_isStronglyNormalizing`         | closed-leaf raw SN            |
| `RawTerm.natZero_isStronglyNormalizing`           | closed-leaf raw SN            |
| `RawTerm.lam_isStronglyNormalizing`               | unary intro (binder) SN       |
| `Term.lam_isStronglyNormalizing`                  | typed lam SN preservation     |
| `Term.lamPi_isStronglyNormalizing`                | typed lamPi SN preservation   |
| `RawTerm.isStronglyNormalizing.step_preserves`    | CR2 forward closure (raw)     |
| `RawTerm.isStronglyNormalizing_weaken`            | weakening preserves raw SN    |
| `Term.isStronglyNormalizing_weaken`               | typed weakening SN            |

All 10 theorems are zero-axiom (`#print axioms` clean) and lean only
on `RawStep.par.*_inv` inversion lemmas plus
`RawTerm.isStronglyNormalizing.intro`.
-/

namespace LeanFX2

/-- `RawTerm.unit` is strongly normalizing.  No β/ι rule has unit
as a source, so any parallel step is `refl`; `parProgress` rules
that out. -/
theorem RawTerm.unit_isStronglyNormalizing {scope : Nat} :
    RawTerm.isStronglyNormalizing (RawTerm.unit : RawTerm scope) :=
  RawTerm.isStronglyNormalizing.intro RawTerm.unit
    (fun _ parStep =>
      (parStep.2 (RawStep.par.unit_inv parStep.1).symm).elim)

/-- `RawTerm.boolTrue` is strongly normalizing. -/
theorem RawTerm.boolTrue_isStronglyNormalizing {scope : Nat} :
    RawTerm.isStronglyNormalizing (RawTerm.boolTrue : RawTerm scope) :=
  RawTerm.isStronglyNormalizing.intro RawTerm.boolTrue
    (fun _ parStep =>
      (parStep.2 (RawStep.par.boolTrue_inv parStep.1).symm).elim)

/-- `RawTerm.boolFalse` is strongly normalizing. -/
theorem RawTerm.boolFalse_isStronglyNormalizing {scope : Nat} :
    RawTerm.isStronglyNormalizing (RawTerm.boolFalse : RawTerm scope) :=
  RawTerm.isStronglyNormalizing.intro RawTerm.boolFalse
    (fun _ parStep =>
      (parStep.2 (RawStep.par.boolFalse_inv parStep.1).symm).elim)

/-- `RawTerm.natZero` is strongly normalizing. -/
theorem RawTerm.natZero_isStronglyNormalizing {scope : Nat} :
    RawTerm.isStronglyNormalizing (RawTerm.natZero : RawTerm scope) :=
  RawTerm.isStronglyNormalizing.intro RawTerm.natZero
    (fun _ parStep =>
      (parStep.2 (RawStep.par.natZero_inv parStep.1).symm).elim)

/-- `RawTerm.lam body` is strongly normalizing whenever `body` is.

Proof: every `RawStep.par` from `lam body` lands at `lam bodyTarget`
with `par body bodyTarget` (`RawStep.par.lam_inv`); the `parProgress`
disequality `lam body ≠ lam bodyTarget` forces `body ≠ bodyTarget`
(by `RawTerm.lam` injectivity), so the recursive IH on `body`'s SN
witness handles the bodyTarget case. -/
theorem RawTerm.lam_isStronglyNormalizing {scope : Nat}
    {body : RawTerm (scope + 1)}
    (bodyIsSN : RawTerm.isStronglyNormalizing body) :
    RawTerm.isStronglyNormalizing (RawTerm.lam body) := by
  induction bodyIsSN with
  | intro currentBody _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro (RawTerm.lam currentBody) ?_
    intro target progressStep
    obtain ⟨bodyTarget, targetEq, bodyStep⟩ :=
      RawStep.par.lam_inv progressStep.1
    subst targetEq
    have bodyDistinct : currentBody ≠ bodyTarget := fun bodyEq =>
      progressStep.2 (congrArg RawTerm.lam bodyEq)
    exact inductiveHypothesis bodyTarget ⟨bodyStep, bodyDistinct⟩

/-- Typed wrapper for non-dependent lambda SN preservation. -/
theorem Term.lam_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {bodyRaw : RawTerm (scope + 1)}
    {bodyTerm :
      Term (context.cons domainType) codomainType.weaken bodyRaw}
    (bodyIsSN : Term.isStronglyNormalizing bodyTerm) :
    Term.isStronglyNormalizing
      (Term.lam (codomainType := codomainType) bodyTerm) :=
  RawTerm.lam_isStronglyNormalizing bodyIsSN

/-- Typed wrapper for dependent lambda SN preservation.

`Term.lamPi` projects to the same raw lambda constructor as
`Term.lam`, so the direct M04 value-SN endpoint is the same raw
closure over the body. -/
theorem Term.lamPi_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType : Ty level scope}
    {codomainType : Ty level (scope + 1)}
    {bodyRaw : RawTerm (scope + 1)}
    {bodyTerm : Term (context.cons domainType) codomainType bodyRaw}
    (bodyIsSN : Term.isStronglyNormalizing bodyTerm) :
    Term.isStronglyNormalizing (Term.lamPi bodyTerm) :=
  RawTerm.lam_isStronglyNormalizing bodyIsSN

/-- **CR2 raw-level**: SN is preserved under parallel-progress
reduction.  Direct destructuring of the SN constructor's closure. -/
theorem RawTerm.isStronglyNormalizing.step_preserves {scope : Nat}
    {source target : RawTerm scope}
    (sourceIsSN : RawTerm.isStronglyNormalizing source)
    (progressStep : RawStep.parProgress source target) :
    RawTerm.isStronglyNormalizing target := by
  cases sourceIsSN with
  | intro _ closure => exact closure target progressStep

/-- **Raw weakening preserves SN**: weakening preserves raw SN.

Any progress step out of `source.weaken` lands in a weakened target by
`RawStep.par.weaken_inv`.  Substituting a dummy singleton back through
that weakened step reflects it to a progress step from `source`, so the
source SN induction supplies SN of the inner target and hence of its
weakened image. -/
theorem RawTerm.isStronglyNormalizing_weaken {scope : Nat}
    {source : RawTerm scope}
    (sourceIsSN : RawTerm.isStronglyNormalizing source) :
    RawTerm.isStronglyNormalizing source.weaken := by
  induction sourceIsSN with
  | intro currentSource _ sourceIH =>
      refine RawTerm.isStronglyNormalizing.intro
        currentSource.weaken ?_
      intro targetAfter progressStep
      obtain ⟨targetInner, targetEq⟩ :=
        RawStep.par.weaken_inv progressStep.1
      have singletonStep :
          RawStep.par
            (currentSource.weaken.subst
              (RawTermSubst.singleton RawTerm.unit))
            (targetAfter.subst
              (RawTermSubst.singleton RawTerm.unit)) :=
        RawStep.par.subst_par
          (fun _position => RawStep.par.refl _) progressStep.1
      have innerStep : RawStep.par currentSource targetInner := by
        rw [RawTerm.weaken_subst_singleton currentSource RawTerm.unit,
            targetEq,
            RawTerm.weaken_subst_singleton targetInner RawTerm.unit]
          at singletonStep
        exact singletonStep
      have innerDistinct : currentSource ≠ targetInner := by
        intro sourceEq
        apply progressStep.2
        rw [targetEq, sourceEq]
      rw [targetEq]
      exact sourceIH targetInner ⟨innerStep, innerDistinct⟩

/-- **Typed weakening preserves SN**: typed SN is stable under
one-binder weakening. -/
theorem Term.isStronglyNormalizing_weaken
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType sourceType : Ty level scope}
    {sourceRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    (sourceIsSN : Term.isStronglyNormalizing sourceTerm) :
    Term.isStronglyNormalizing (Term.weaken newType sourceTerm) :=
  RawTerm.isStronglyNormalizing_weaken sourceIsSN

/-- `RawTerm.cumulUpMarker inner` is strongly normalizing whenever
`inner` is.  Powers the cross-universe cumulUp Term-level helper.
Body uses `RawStep.par.cumulUpMarker_inv` inversion. -/
theorem RawTerm.cumulUpMarker_isStronglyNormalizing {scope : Nat}
    {innerCodeRaw : RawTerm scope}
    (innerIsSN : RawTerm.isStronglyNormalizing innerCodeRaw) :
    RawTerm.isStronglyNormalizing
      (RawTerm.cumulUpMarker innerCodeRaw) := by
  induction innerIsSN with
  | intro currentInner _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.cumulUpMarker currentInner) ?_
    intro target progressStep
    obtain ⟨innerTarget, targetEq, innerStep⟩ :=
      RawStep.par.cumulUpMarker_inv progressStep.1
    subst targetEq
    have innerDistinct :
        currentInner ≠ innerTarget := fun innerEq =>
      progressStep.2 (congrArg RawTerm.cumulUpMarker innerEq)
    exact inductiveHypothesis innerTarget
      ⟨innerStep, innerDistinct⟩

/-- Shape-specialized inversion for predecessor SN from successor SN. -/
theorem RawTerm.natSucc_predecessor_isStronglyNormalizing_aux {scope : Nat}
    {source : RawTerm scope}
    (sourceIsSN : RawTerm.isStronglyNormalizing source) :
    ∀ {predecessorRaw : RawTerm scope},
      source = RawTerm.natSucc predecessorRaw →
      RawTerm.isStronglyNormalizing predecessorRaw := by
  induction sourceIsSN with
  | intro currentSource _ inductiveHypothesis =>
    intro predecessorRaw sourceEq
    cases sourceEq
    refine RawTerm.isStronglyNormalizing.intro predecessorRaw ?_
    intro predecessorTarget predecessorProgress
    have succProgress :
        RawStep.parProgress
          (RawTerm.natSucc predecessorRaw)
          (RawTerm.natSucc predecessorTarget) := by
      refine ⟨RawStep.par.natSucc predecessorProgress.1, ?_⟩
      intro succEq
      apply predecessorProgress.2
      injection succEq
    exact inductiveHypothesis
      (RawTerm.natSucc predecessorTarget) succProgress rfl

/-- If a natural successor is strongly normalizing, its predecessor is
strongly normalizing.  Used by nat-eliminator successor ι expansions. -/
theorem RawTerm.natSucc_predecessor_isStronglyNormalizing {scope : Nat}
    {predecessorRaw : RawTerm scope}
    (successorIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.natSucc predecessorRaw)) :
    RawTerm.isStronglyNormalizing predecessorRaw :=
  RawTerm.natSucc_predecessor_isStronglyNormalizing_aux
    successorIsSN rfl

end LeanFX2
