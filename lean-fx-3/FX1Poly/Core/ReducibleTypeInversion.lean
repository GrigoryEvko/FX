import FX1Poly.Core.ReducibleType

/-! # Foundation/PolyCell/Core/ReducibleTypeInversion
    — inversion lemmas for the dependent reducibility relation

Two characterizations of `ReducibleType` (`ReducibleType.lean`) by the shape of the type-code, both
needed by any conversion-invariance argument:

  * `reductReducibleThroughHeadStep` — if a type-code reducible at a candidate weak-head steps, the
    reduct is reducible at the SAME candidate (the only arm that derives a head-stepping code is
    `headExpand`; `neutral` forbids a head step and `piType` is `gen_piTyCode`-rooted, which never head
    steps).  This is exactly the `headExpand`-inversion the conv-invariance `headExpand` case consumes.
  * `neutralCandidateStronglyNormalizing` — a weak-head-normal non-Π reducible type's candidate is the
    strong-normalization candidate (up to pointwise iff): the only available arm is `neutral`.  This is
    the canonical-form characterization the conv-invariance `neutral` case consumes.

## Zero-axiom verification

`cases` on the `ReducibleType` derivation (the same propext-clean inversion `ReducibleType.deterministic`
already uses), discharging cross-arm impossibilities by `HeadStep.deterministic` /
`HeadStep.subjectRootIsApp` + `Generator.noConfusion`.  Pointwise-iff, no predicate equality, hence no
`funext`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Swept
per declaration by `#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation
open StepStar

/-- A redex-type's reducibility descends to its weak-head contractum: a type-code reducible at a
candidate that weak-head steps has the reduct reducible at the SAME candidate. -/
theorem ReducibleType.reductReducibleThroughHeadStep {scope : Nat}
    {typeCode reduct : RawTerm scope} {candidate : RawTerm scope → Prop}
    (reducible : ReducibleType typeCode candidate) (headStep : HeadStep typeCode reduct) :
    ReducibleType reduct candidate := by
  cases reducible with
  | headExpand headStepShipped reductReducible =>
      have reductEquation := HeadStep.deterministic headStepShipped headStep
      subst reductEquation
      exact reductReducible
  | neutral noHeadStep _notPiType => exact absurd headStep (noHeadStep _)
  | piType _codomainCandidate _domainReducible _codomainReducible =>
      exact Generator.noConfusion (HeadStep.subjectRootIsApp headStep)

/-- A weak-head-normal non-Π reducible type's candidate is the strong-normalization candidate (up to
pointwise iff): the only derivation arm available for such a code is `neutral`. -/
theorem ReducibleType.neutralCandidateStronglyNormalizing {scope : Nat}
    {typeCode : RawTerm scope} {candidate : RawTerm scope → Prop}
    (reducible : ReducibleType typeCode candidate)
    (noHeadStep : ∀ reduct : RawTerm scope, ¬ HeadStep typeCode reduct)
    (notPiType : typeCode.rootGenerator ≠ Generator.gen_piTyCode) :
    PointwiseIff candidate IsStronglyNormalizing := by
  cases reducible with
  | headExpand headStep _reductReducible => exact absurd headStep (noHeadStep _)
  | neutral _noHeadStep _notPiType => intro _term; exact Iff.rfl
  | piType _codomainCandidate _domainReducible _codomainReducible => exact absurd rfl notPiType

end FX1Poly.Core
