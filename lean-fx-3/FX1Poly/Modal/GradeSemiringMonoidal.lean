import FX1Poly.Modal.GradeSemiringProduct
import FX1Poly.Modal.ComplexitySemiring

/-! # FX1Poly/Modal/GradeSemiringMonoidal
    — the grade-semiring product (DIM-PRODUCT) is SYMMETRIC MONOIDAL: commutative and associative up to
      strict grade-semiring isomorphism; plus a 3-dimension free-metatheory instance

`OrderedGradeSemiring.product` (`GradeSemiringProduct.lean`, DIM-PRODUCT/#1035) composes two grade dimensions.
For §6's "Product of all forms the grade vector every binding carries" to be well-defined when there are N ≥ 3
dimensions, the product must be COMMUTATIVE and ASSOCIATIVE — otherwise "the product of all dimensions" would
depend on how you order and group them.  This file supplies exactly that: the commutativity and associativity
isomorphisms, and shows they are STRICT grade-semiring isomorphisms (preserve every operation and the order),
so the grade vector is well-defined independent of dimension order/grouping.

  * **`OrderedGradeSemiring.swapGrade` (commutativity / braiding)** — `Prod.swap : product A B → product B A`,
    a grade-semiring ISOMORPHISM: preserves `zero`/`one`/`add`/`mul` (all definitional) and the order (`le`,
    via Bool-AND commutativity), and is its own inverse (`swapGrade_involutive`).  So `product A B ≅ product B A`
    strictly — the two dimensions can be listed in either order with no observable difference.

  * **`OrderedGradeSemiring.assocGrade` / `unassocGrade` (associator)** — the reshaping bijection `product
    (product A B) C ≅ product A (product B C)`, again a grade-semiring isomorphism (operations definitional,
    order via Bool-AND associativity; the two reshapings are mutually inverse, `assocGrade_unassocGrade` /
    `unassocGrade_assocGrade`).  So grouping `((A×B)×C)` and `(A×(B×C))` give isomorphic grade dimensions —
    "the product of all dimensions" is grouping-independent.

  * **`fxUsageTimesSecurityTimesComplexitySemiring` (+ `_isLawful`, `_metatheoryFree`)** — a concrete THREE-
    dimension grade semiring usage{0,1,ω} × security{unclass<class} × complexity (ℕ), lawful by NESTED
    `IsLawfulOrderedGradeSemiring.product`, with the full metatheory (SN + subject reduction) FOR FREE via
    `HasGradeOver.metatheoryBundle`.  This exhibits the DIM-PRODUCT free-metatheory pattern at N = 3 — the
    grade vector composes to arbitrarily many dimensions, each new factor adding zero metatheory cost.

Together: the grade-semiring product is a strict symmetric monoidal structure on grade dimensions, and the
N-fold grade vector inherits the entire metatheory by iterating the binary product — the precise content of
§6's "one parameterized checking algorithm; product of all forms the grade vector".

## Zero-axiom verification

The isomorphism laws are definitional (`rfl`) for every operation; the order laws route through the two
propext-free Bool helpers `boolAndComm` / `boolAndAssoc` (`cases <;> rfl`).  The 3-dimension instance threads
the shipped factor witnesses + `IsLawfulOrderedGradeSemiring.product` + `HasGradeOver.metatheoryBundle`.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration
audit-gated in `FX1PolyAudit/AuditModal.lean`.
-/

namespace FX1Poly.Modal

/-- Bool-AND commutativity, propext-free (`Bool.and_comm` in core may route through `decide`/`propext`). -/
private theorem boolAndComm (leftBit rightBit : Bool) :
    (leftBit && rightBit) = (rightBit && leftBit) := by
  cases leftBit <;> cases rightBit <;> rfl

/-- Bool-AND associativity, propext-free. -/
private theorem boolAndAssoc (firstBit secondBit thirdBit : Bool) :
    ((firstBit && secondBit) && thirdBit) = (firstBit && (secondBit && thirdBit)) := by
  cases firstBit <;> cases secondBit <;> cases thirdBit <;> rfl

/-! ## Commutativity: `product A B ≅ product B A` via `swapGrade` -/

/-- The commutativity (braiding) map of the grade-semiring product: `product A B → product B A`. -/
def OrderedGradeSemiring.swapGrade {factorA factorB : OrderedGradeSemiring}
    (grade : (OrderedGradeSemiring.product factorA factorB).Carrier) :
    (OrderedGradeSemiring.product factorB factorA).Carrier := Prod.swap grade

theorem OrderedGradeSemiring.swapGrade_zero {factorA factorB : OrderedGradeSemiring} :
    OrderedGradeSemiring.swapGrade (factorA := factorA) (factorB := factorB)
      (OrderedGradeSemiring.product factorA factorB).zero
      = (OrderedGradeSemiring.product factorB factorA).zero := rfl

theorem OrderedGradeSemiring.swapGrade_one {factorA factorB : OrderedGradeSemiring} :
    OrderedGradeSemiring.swapGrade (factorA := factorA) (factorB := factorB)
      (OrderedGradeSemiring.product factorA factorB).one
      = (OrderedGradeSemiring.product factorB factorA).one := rfl

theorem OrderedGradeSemiring.swapGrade_add {factorA factorB : OrderedGradeSemiring}
    (firstGrade secondGrade : (OrderedGradeSemiring.product factorA factorB).Carrier) :
    OrderedGradeSemiring.swapGrade ((OrderedGradeSemiring.product factorA factorB).add firstGrade secondGrade)
      = (OrderedGradeSemiring.product factorB factorA).add
          (OrderedGradeSemiring.swapGrade firstGrade) (OrderedGradeSemiring.swapGrade secondGrade) := rfl

theorem OrderedGradeSemiring.swapGrade_mul {factorA factorB : OrderedGradeSemiring}
    (firstGrade secondGrade : (OrderedGradeSemiring.product factorA factorB).Carrier) :
    OrderedGradeSemiring.swapGrade ((OrderedGradeSemiring.product factorA factorB).mul firstGrade secondGrade)
      = (OrderedGradeSemiring.product factorB factorA).mul
          (OrderedGradeSemiring.swapGrade firstGrade) (OrderedGradeSemiring.swapGrade secondGrade) := rfl

/-- `swapGrade` preserves (and reflects) the order: the swapped grades compare in `B × A` exactly as the
originals compare in `A × B` — via Bool-AND commutativity. -/
theorem OrderedGradeSemiring.swapGrade_le {factorA factorB : OrderedGradeSemiring}
    (firstGrade secondGrade : (OrderedGradeSemiring.product factorA factorB).Carrier) :
    (OrderedGradeSemiring.product factorB factorA).le
        (OrderedGradeSemiring.swapGrade firstGrade) (OrderedGradeSemiring.swapGrade secondGrade)
      = (OrderedGradeSemiring.product factorA factorB).le firstGrade secondGrade :=
  boolAndComm _ _

/-- `swapGrade` is its own inverse — the commutativity iso is involutive. -/
theorem OrderedGradeSemiring.swapGrade_involutive {factorA factorB : OrderedGradeSemiring}
    (grade : (OrderedGradeSemiring.product factorA factorB).Carrier) :
    OrderedGradeSemiring.swapGrade (OrderedGradeSemiring.swapGrade grade) = grade := rfl

/-! ## Associativity: `product (product A B) C ≅ product A (product B C)` via `assocGrade` / `unassocGrade` -/

/-- The associativity map of the grade-semiring product (right-reassociation). -/
def OrderedGradeSemiring.assocGrade {factorA factorB factorC : OrderedGradeSemiring}
    (grade : (OrderedGradeSemiring.product (OrderedGradeSemiring.product factorA factorB) factorC).Carrier) :
    (OrderedGradeSemiring.product factorA (OrderedGradeSemiring.product factorB factorC)).Carrier :=
  (grade.1.1, (grade.1.2, grade.2))

/-- The inverse associativity map (left-reassociation). -/
def OrderedGradeSemiring.unassocGrade {factorA factorB factorC : OrderedGradeSemiring}
    (grade : (OrderedGradeSemiring.product factorA (OrderedGradeSemiring.product factorB factorC)).Carrier) :
    (OrderedGradeSemiring.product (OrderedGradeSemiring.product factorA factorB) factorC).Carrier :=
  ((grade.1, grade.2.1), grade.2.2)

theorem OrderedGradeSemiring.assocGrade_zero {factorA factorB factorC : OrderedGradeSemiring} :
    OrderedGradeSemiring.assocGrade (factorA := factorA) (factorB := factorB) (factorC := factorC)
      (OrderedGradeSemiring.product (OrderedGradeSemiring.product factorA factorB) factorC).zero
      = (OrderedGradeSemiring.product factorA (OrderedGradeSemiring.product factorB factorC)).zero := rfl

theorem OrderedGradeSemiring.assocGrade_one {factorA factorB factorC : OrderedGradeSemiring} :
    OrderedGradeSemiring.assocGrade (factorA := factorA) (factorB := factorB) (factorC := factorC)
      (OrderedGradeSemiring.product (OrderedGradeSemiring.product factorA factorB) factorC).one
      = (OrderedGradeSemiring.product factorA (OrderedGradeSemiring.product factorB factorC)).one := rfl

theorem OrderedGradeSemiring.assocGrade_add {factorA factorB factorC : OrderedGradeSemiring}
    (firstGrade secondGrade :
      (OrderedGradeSemiring.product (OrderedGradeSemiring.product factorA factorB) factorC).Carrier) :
    OrderedGradeSemiring.assocGrade
        ((OrderedGradeSemiring.product (OrderedGradeSemiring.product factorA factorB) factorC).add
          firstGrade secondGrade)
      = (OrderedGradeSemiring.product factorA (OrderedGradeSemiring.product factorB factorC)).add
          (OrderedGradeSemiring.assocGrade firstGrade) (OrderedGradeSemiring.assocGrade secondGrade) := rfl

theorem OrderedGradeSemiring.assocGrade_mul {factorA factorB factorC : OrderedGradeSemiring}
    (firstGrade secondGrade :
      (OrderedGradeSemiring.product (OrderedGradeSemiring.product factorA factorB) factorC).Carrier) :
    OrderedGradeSemiring.assocGrade
        ((OrderedGradeSemiring.product (OrderedGradeSemiring.product factorA factorB) factorC).mul
          firstGrade secondGrade)
      = (OrderedGradeSemiring.product factorA (OrderedGradeSemiring.product factorB factorC)).mul
          (OrderedGradeSemiring.assocGrade firstGrade) (OrderedGradeSemiring.assocGrade secondGrade) := rfl

/-- `assocGrade` preserves (and reflects) the order — via Bool-AND associativity. -/
theorem OrderedGradeSemiring.assocGrade_le {factorA factorB factorC : OrderedGradeSemiring}
    (firstGrade secondGrade :
      (OrderedGradeSemiring.product (OrderedGradeSemiring.product factorA factorB) factorC).Carrier) :
    (OrderedGradeSemiring.product factorA (OrderedGradeSemiring.product factorB factorC)).le
        (OrderedGradeSemiring.assocGrade firstGrade) (OrderedGradeSemiring.assocGrade secondGrade)
      = (OrderedGradeSemiring.product (OrderedGradeSemiring.product factorA factorB) factorC).le
          firstGrade secondGrade :=
  (boolAndAssoc _ _ _).symm

/-- `assocGrade` then `unassocGrade` is the identity (left-inverse of the associator). -/
theorem OrderedGradeSemiring.assocGrade_unassocGrade {factorA factorB factorC : OrderedGradeSemiring}
    (grade : (OrderedGradeSemiring.product (OrderedGradeSemiring.product factorA factorB) factorC).Carrier) :
    OrderedGradeSemiring.unassocGrade (OrderedGradeSemiring.assocGrade grade) = grade := rfl

/-- `unassocGrade` then `assocGrade` is the identity (right-inverse of the associator). -/
theorem OrderedGradeSemiring.unassocGrade_assocGrade {factorA factorB factorC : OrderedGradeSemiring}
    (grade : (OrderedGradeSemiring.product factorA (OrderedGradeSemiring.product factorB factorC)).Carrier) :
    OrderedGradeSemiring.assocGrade (OrderedGradeSemiring.unassocGrade grade) = grade := rfl

/-! ## A concrete THREE-dimension grade semiring with free metatheory -/

/-- usage{0,1,ω} × security{unclass<class} × complexity(ℕ) — a 3-dimension grade semiring by nested product. -/
def fxUsageTimesSecurityTimesComplexitySemiring : OrderedGradeSemiring :=
  OrderedGradeSemiring.product
    (OrderedGradeSemiring.product fxUsageSemiring fxSecuritySemiring) fxComplexitySemiring

/-- The 3-dimension product is lawful, by NESTED `IsLawfulOrderedGradeSemiring.product` over the three factor
witnesses — no new law proof for the composite. -/
theorem fxUsageTimesSecurityTimesComplexitySemiring_isLawful :
    IsLawfulOrderedGradeSemiring fxUsageTimesSecurityTimesComplexitySemiring :=
  IsLawfulOrderedGradeSemiring.product
    (IsLawfulOrderedGradeSemiring.product fxUsageSemiring_isLawful fxSecuritySemiring_isLawful)
    fxComplexitySemiring_isLawful

/-- ★ The full metatheory of the 3-dimension usage×security×complexity system, FOR FREE — SN + subject
reduction, the lawfulness discharged by the nested product witness.  The grade vector composes to arbitrarily
many dimensions, each new factor adding zero metatheory cost (the DIM-PRODUCT pattern at N = 3). -/
theorem fxUsageTimesSecurityTimesComplexity_metatheoryFree
    {typeContext : List (GTypeOver fxUsageTimesSecurityTimesComplexitySemiring)}
    {grades : GradeVectorOver fxUsageTimesSecurityTimesComplexitySemiring} {term : GradedLambda}
    {resultType : GTypeOver fxUsageTimesSecurityTimesComplexitySemiring}
    (typed : HasGradeOver fxUsageTimesSecurityTimesComplexitySemiring typeContext grades term resultType) :
    GradedLambda.IsStronglyNormalizing term ∧
      ∀ reduct : GradedLambda, GradedLambda.Reduces term reduct →
        HasGradeOver fxUsageTimesSecurityTimesComplexitySemiring typeContext grades reduct resultType :=
  HasGradeOver.metatheoryBundle fxUsageTimesSecurityTimesComplexitySemiring_isLawful typed

end FX1Poly.Modal
