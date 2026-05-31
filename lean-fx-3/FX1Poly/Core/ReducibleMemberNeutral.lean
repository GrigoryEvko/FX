import FX1Poly.Core.ReducibleMember

/-! # Foundation/PolyCell/Core/ReducibleMemberNeutral
    — membership at a neutral classifier is exactly strong normalization

The `neutral` arm of `ReducibleType` assigns the strong-normalization candidate to EVERY weak-head-normal
non-Π type (a variable, a stuck application/eliminator, a universe code, any non-Π former).  So semantic
membership at such a classifier collapses to a single, sharp statement:

  `IsReducibleMember classifier term ↔ IsStronglyNormalizing term`   (classifier neutral).

This is the semantic heart of why the reducibility model proves SN — every type whose code is a normal
leaf (in particular every universe code, the classifier of every well-formed TYPE) classifies EXACTLY
the strongly-normalizing terms.  The fundamental theorem's formation/universe arms read the `←` direction
(an SN formation subject is a member of its universe-code classifier); the `→` direction extracts SN from
membership (the candidate→SN bridge at a fixed neutral type, without the scope+1 of the general CR1).

## Zero-axiom verification

`ReducibleType.deterministic` against the `neutral` witness for the `→` direction; the explicit
`neutral`-candidate triple for the `←` direction.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Swept per declaration by `#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation
open StepStar

/-- **Membership at a neutral classifier is exactly strong normalization.**  A weak-head-normal non-Π
type denotes the strong-normalization candidate (`ReducibleType.neutral`), so a term is a reducible
member of it precisely when strongly normalizing.  `→`: the member's candidate coincides with the SN
candidate by `ReducibleType.deterministic`.  `←`: the SN candidate is itself a witnessing candidate. -/
theorem IsReducibleMember.atNeutralClassifier {scope : Nat} {classifier term : RawTerm scope}
    (noWeakHeadStep : ∀ reduct : RawTerm scope, ¬ WeakHeadStep classifier reduct)
    (notPiType : classifier.rootGenerator ≠ Generator.gen_piTyCode) :
    IsReducibleMember classifier term ↔ IsStronglyNormalizing term := by
  constructor
  · intro member
    obtain ⟨candidate, reducible, membership⟩ := member
    exact (ReducibleType.deterministic reducible
      (ReducibleType.neutral noWeakHeadStep notPiType) term).mp membership
  · intro stronglyNormalizing
    exact ⟨IsStronglyNormalizing, ReducibleType.neutral noWeakHeadStep notPiType, stronglyNormalizing⟩

end FX1Poly.Core
