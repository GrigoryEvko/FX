import FX1Poly.Modal.GradedFundamentalTheorem

namespace FX1Poly.Modal

/-! Confirm erasure does not collapse types and HasSimpleType types real lambdas. -/

-- eraseType of a graded arrow is a SimpleType arrow (NOT collapsed to base).
example : eraseType (.arrow UsageGrade.one GType.base GType.base) = .arrow .base .base := rfl
example : eraseType (.arrow UsageGrade.zero (.arrow UsageGrade.one .base .base) .base)
    = .arrow (.arrow .base .base) .base := rfl

-- HasSimpleType genuinely types a lambda at an arrow type (not leaf-only): the K combinator.
example : HasSimpleType [] (.lam (.lam (.var 1)))
    (.arrow .base (.arrow .base .base)) := kCombinator_typed.erase

-- And the erased K has the expected erased type (arrow grades gone):
example : eraseType (.arrow UsageGrade.one GType.base (.arrow UsageGrade.zero GType.base GType.base))
    = .arrow .base (.arrow .base .base) := rfl

-- The transfer: HasUsage.stronglyNormalizing reduces to HasSimpleType.stronglyNormalizing on the
-- SAME term (erase keeps the term).  Confirm definitionally the term is preserved by checking the
-- erase target's term slot is the input term (via the smoke witnesses already typed above).
#print axioms HasUsage.erase
#print eraseType

end FX1Poly.Modal
