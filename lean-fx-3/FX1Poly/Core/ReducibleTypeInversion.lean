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

Both lemmas delegate to the upstream inversion helpers `ReducibleType.candidateAtWhnfReduct` and
`ReducibleType.candidateIffStronglyNormalizing`, which perform the derivation induction and absorb the
`ofPointwiseIff` congruence arm internally; this file re-exposes them under these conv-invariance-facing
names.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Swept
per declaration by `#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation
open StepStar

/-- A redex-type's reducibility descends to its weak-head contractum: a type-code reducible at a
candidate that weak-head steps has the reduct reducible at the SAME candidate. -/
theorem ReducibleType.reductReducibleThroughWeakHeadStep {scope : Nat}
    {typeCode reduct : RawTerm scope} {candidate : RawTerm scope → Prop}
    (reducible : ReducibleType typeCode candidate) (weakHeadStep : WeakHeadStep typeCode reduct) :
    ReducibleType reduct candidate :=
  reducible.candidateAtWhnfReduct weakHeadStep

/-- A weak-head-normal non-Π reducible type's candidate is the strong-normalization candidate (up to
pointwise iff): the only derivation arm available for such a code is `neutral`. -/
theorem ReducibleType.neutralCandidateStronglyNormalizing {scope : Nat}
    {typeCode : RawTerm scope} {candidate : RawTerm scope → Prop}
    (reducible : ReducibleType typeCode candidate)
    (noWeakHeadStep : ∀ reduct : RawTerm scope, ¬ WeakHeadStep typeCode reduct)
    (notPiType : typeCode.rootGenerator ≠ Generator.gen_piTyCode) :
    PointwiseIff candidate IsStronglyNormalizing :=
  reducible.candidateIffStronglyNormalizing noWeakHeadStep notPiType

end FX1Poly.Core
