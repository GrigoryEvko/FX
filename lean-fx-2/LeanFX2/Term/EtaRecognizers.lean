import LeanFX2.Term.TypedInversion
import LeanFX2.Term.StrengtheningImage.ImageUnweaken

/-! # Term/EtaRecognizers

Typed recognizers for eta-shaped term fragments.

This file starts with the lambda eta app-arm recognizer.  It is the
small T12 bridge between:

* `Term.app_inv`, which exposes a concrete `Term.app` arm,
* `Term.weakenInverse_atVarZero`, which recognizes the newest
  variable argument, and
* `Term.weaken_inv_arrow`, which turns a successful unweaken of the
  function side into the canonical weakened function.

The harder disjunctive `lam_inv` theorem can consume this theorem
after it has already selected the `Term.app` branch of the lambda body.
-/

namespace LeanFX2

namespace Term

/-- Recognize the concrete lambda eta app arm.

If an application under `context.cons domainType` has function side in
the weakening image of an arrow `domainType -> codomainType`, and its
argument side is the newest variable, then the app is heterogeneously
equal to the canonical `eta_lam_shape_construct` for the recovered
outer-scope function.

This is intentionally an app-arm recognizer, not the full
`lam_inv_disjunctive` theorem: callers still use `Term.app_inv` to
separate `Term.app` from `Term.appPi`, then use this lemma on the
`Term.app` branch. -/
theorem eta_lam_shape_recognize_app_of_unweaken
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {functionRaw : RawTerm scope}
    (functionTerm :
      Term (context.cons domainType)
        (Ty.arrow domainType codomainType).weaken
        functionRaw.weaken)
    (argumentTerm :
      Term (context.cons domainType)
        domainType.weaken
        (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩))
    {originalFunction :
      Term context (Ty.arrow domainType codomainType) functionRaw}
    (functionUnweaken :
      Term.unweaken? functionTerm = some originalFunction) :
    HEq (Term.app functionTerm argumentTerm)
        (Term.eta_lam_shape_construct originalFunction) := by
  have functionHEq :
      HEq functionTerm
        (Term.weaken (newType := domainType) originalFunction) :=
    Term.weaken_inv_arrow functionTerm functionUnweaken
  obtain ⟨_, argumentHEq⟩ :=
    Term.weakenInverse_atVarZero
      (context := context)
      (newType := domainType)
      (weakenedTerm := argumentTerm)
  unfold Term.eta_lam_shape_construct
  cases functionHEq
  cases argumentHEq
  rfl

end Term

end LeanFX2
