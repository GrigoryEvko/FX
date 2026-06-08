import FX1Poly.Modal.ResourceGraded
import FX1Poly.Modal.GradedCompositionGeneric

/-! # FX1Poly/Modal/GradeSemiringProduct
    — the PRODUCT of two ordered grade semirings is an ordered grade semiring, lawful from the factors;
      a 2-dimension graded typing inherits the full metatheory (SN + SR) FOR FREE

§6 of `fx_design.md` makes a central claim: the twenty-one graded dimensions "are instances of one
parameterized checking algorithm; each dimension provides a semiring … Product of all forms the grade
vector every binding carries."  The generic graded engine `HasGradeOver R` (`GradedTypingGeneric.lean`)
already realizes the "one algorithm, parameterized by a semiring `R`" half — and `DIM2-7`/`#880` showed a
SINGLE second dimension (usage) composes onto the type dimension without cascading the metatheory.  This
file mechanizes the "product of all forms the grade vector" half — composing TWO grade semirings into ONE,
and showing the composite inherits the whole metatheory with ZERO new proof.

  * **`OrderedGradeSemiring.product` (factorA factorB)** — the componentwise product semiring: carrier
    `factorA.Carrier × factorB.Carrier`, `zero`/`one`/`add`/`mul` pairwise, `le` the conjunction of the
    factor orders, `carrierDecEq` the product decidable equality.

  * **`IsLawfulOrderedGradeSemiring.product` (★, the metatheory core)** — the product is LAWFUL whenever
    both factors are: all sixteen ordered-semiring laws (§6.1) follow componentwise.  The eleven equational
    laws close term-mode by `Prod.ext` of the two factor proofs; the five order laws (`le` is a `Bool`
    conjunction) close through the propext-free Bool-AND helpers `andBothTrue` / `andLeftTrue` /
    `andRightTrue` (Lean core's `Bool.and_eq_true` leaks `propext` — these reprove its directions by
    `cases`+`Bool.noConfusion`, the discipline the security-dimension order laws already use).  This is the
    composition theorem: lawfulness is preserved under product, so the generic metatheory — which consumes
    exactly an `IsLawfulOrderedGradeSemiring` witness — transfers to the composite for free.

  * **`fxUsageTimesSecuritySemiring` (+ `_isLawful`)** — the concrete 2-dimension instance: FX's usage
    semiring `{0,1,ω}` (§6.1) PRODUCT its security semiring `{unclassified < classified}` (§6.3).  Its unit
    grade is literally the pair `(usage 1, security classified)` (`fxUsageTimesSecurity_one_isPair`).

  * **`fxUsageTimesSecurity_variableCarriesBothGrades`** — a single variable typed in the composite system
    carries BOTH a usage grade AND a security grade in ONE `HasGradeOver` judgment — the §6 "grade vector
    every binding carries", made concrete for two simultaneous dimensions.

  * **`fxUsageTimesSecurity_metatheoryFree` (★, the thesis payoff)** — ANY term typed in the usage×security
    system is strongly normalizing AND subject-reduction-stable, the lawfulness premise discharged by the
    product witness.  No SN re-proof, no SR re-proof: the generic `HasGradeOver.metatheoryBundle`
    specialized to the product.  `fxUsageTimesSecurity_appliedIdentity_metatheoryFree` exhibits it
    non-vacuously on the redex `(λx. x) z` carrying a 2-dimension grade.  This generalizes `DIM2-7` from a
    single added dimension to a product of two — the orthogonal-composition thesis at the grade-vector level.

## Zero-axiom verification

Every law of the product is proved componentwise from the factor laws — `Prod.ext` for the equational laws,
the three propext-free Bool-AND helpers for the order laws.  The concrete instance and the metatheory-free
corollary thread only the shipped `fxUsageSemiring_isLawful` / `fxSecuritySemiring_isLawful`,
`HasGradeOver.var` / `.metatheoryBundle`, and `appliedIdentityOver_typed`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditModal.lean`.
-/

namespace FX1Poly.Modal

/-- `(leftBit && rightBit) = true` from both components, propext-free (`Bool.and_eq_true` leaks `propext`). -/
private theorem andBothTrue {leftBit rightBit : Bool}
    (leftTrue : leftBit = true) (rightTrue : rightBit = true) : (leftBit && rightBit) = true := by
  rw [leftTrue]; exact rightTrue

/-- Left projection of `(leftBit && rightBit) = true`, propext-free via `cases` + `Bool.noConfusion`. -/
private theorem andLeftTrue {leftBit rightBit : Bool}
    (bothTrue : (leftBit && rightBit) = true) : leftBit = true := by
  cases caseBit : leftBit with
  | true => rfl
  | false => rw [caseBit, Bool.false_and] at bothTrue; exact Bool.noConfusion bothTrue

/-- Right projection of `(leftBit && rightBit) = true`, propext-free via `cases` + `Bool.noConfusion`. -/
private theorem andRightTrue {leftBit rightBit : Bool}
    (bothTrue : (leftBit && rightBit) = true) : rightBit = true := by
  cases caseBit : leftBit with
  | true => rw [caseBit, Bool.true_and] at bothTrue; exact bothTrue
  | false => rw [caseBit, Bool.false_and] at bothTrue; exact Bool.noConfusion bothTrue

/-- **The componentwise product of two ordered grade semirings.**  Carrier is the product of carriers;
`zero`/`one`/`add`/`mul` are pairwise; `le` is the conjunction of the factor orders; the carrier decidable
equality is the product decidable equality.  This is the algebra behind §6's "Product of all forms the grade
vector every binding carries". -/
def OrderedGradeSemiring.product (factorA factorB : OrderedGradeSemiring) : OrderedGradeSemiring where
  Carrier := factorA.Carrier × factorB.Carrier
  zero := (factorA.zero, factorB.zero)
  one := (factorA.one, factorB.one)
  add := fun firstGrade secondGrade =>
    (factorA.add firstGrade.1 secondGrade.1, factorB.add firstGrade.2 secondGrade.2)
  mul := fun firstGrade secondGrade =>
    (factorA.mul firstGrade.1 secondGrade.1, factorB.mul firstGrade.2 secondGrade.2)
  le := fun firstGrade secondGrade =>
    factorA.le firstGrade.1 secondGrade.1 && factorB.le firstGrade.2 secondGrade.2
  carrierDecEq := @instDecidableEqProd _ _ factorA.carrierDecEq factorB.carrierDecEq

/-- ★ **Lawfulness is preserved under product.**  When both factors satisfy the §6.1 ordered-semiring laws,
so does their product: the eleven equational laws by `Prod.ext` of the factor proofs, the five order laws
through the propext-free Bool-AND helpers.  This is the composition theorem — the generic metatheory consumes
exactly an `IsLawfulOrderedGradeSemiring` witness, so it transfers to any composite dimension for free. -/
theorem IsLawfulOrderedGradeSemiring.product {factorA factorB : OrderedGradeSemiring}
    (lawfulA : IsLawfulOrderedGradeSemiring factorA) (lawfulB : IsLawfulOrderedGradeSemiring factorB) :
    IsLawfulOrderedGradeSemiring (OrderedGradeSemiring.product factorA factorB) where
  add_comm := fun firstGrade secondGrade =>
    Prod.ext (lawfulA.add_comm firstGrade.1 secondGrade.1) (lawfulB.add_comm firstGrade.2 secondGrade.2)
  add_assoc := fun firstGrade secondGrade thirdGrade =>
    Prod.ext (lawfulA.add_assoc firstGrade.1 secondGrade.1 thirdGrade.1)
      (lawfulB.add_assoc firstGrade.2 secondGrade.2 thirdGrade.2)
  add_zero := fun someGrade =>
    Prod.ext (lawfulA.add_zero someGrade.1) (lawfulB.add_zero someGrade.2)
  zero_add := fun someGrade =>
    Prod.ext (lawfulA.zero_add someGrade.1) (lawfulB.zero_add someGrade.2)
  mul_assoc := fun firstGrade secondGrade thirdGrade =>
    Prod.ext (lawfulA.mul_assoc firstGrade.1 secondGrade.1 thirdGrade.1)
      (lawfulB.mul_assoc firstGrade.2 secondGrade.2 thirdGrade.2)
  mul_one := fun someGrade =>
    Prod.ext (lawfulA.mul_one someGrade.1) (lawfulB.mul_one someGrade.2)
  one_mul := fun someGrade =>
    Prod.ext (lawfulA.one_mul someGrade.1) (lawfulB.one_mul someGrade.2)
  mul_zero := fun someGrade =>
    Prod.ext (lawfulA.mul_zero someGrade.1) (lawfulB.mul_zero someGrade.2)
  zero_mul := fun someGrade =>
    Prod.ext (lawfulA.zero_mul someGrade.1) (lawfulB.zero_mul someGrade.2)
  left_distrib := fun firstGrade secondGrade thirdGrade =>
    Prod.ext (lawfulA.left_distrib firstGrade.1 secondGrade.1 thirdGrade.1)
      (lawfulB.left_distrib firstGrade.2 secondGrade.2 thirdGrade.2)
  right_distrib := fun firstGrade secondGrade thirdGrade =>
    Prod.ext (lawfulA.right_distrib firstGrade.1 secondGrade.1 thirdGrade.1)
      (lawfulB.right_distrib firstGrade.2 secondGrade.2 thirdGrade.2)
  le_refl := fun someGrade =>
    andBothTrue (lawfulA.le_refl someGrade.1) (lawfulB.le_refl someGrade.2)
  le_trans := fun _firstGrade _secondGrade _thirdGrade firstBelowSecond secondBelowThird =>
    andBothTrue
      (lawfulA.le_trans _ _ _ (andLeftTrue firstBelowSecond) (andLeftTrue secondBelowThird))
      (lawfulB.le_trans _ _ _ (andRightTrue firstBelowSecond) (andRightTrue secondBelowThird))
  le_antisymm := fun _firstGrade _secondGrade firstBelowSecond secondBelowFirst =>
    Prod.ext (lawfulA.le_antisymm _ _ (andLeftTrue firstBelowSecond) (andLeftTrue secondBelowFirst))
      (lawfulB.le_antisymm _ _ (andRightTrue firstBelowSecond) (andRightTrue secondBelowFirst))
  add_le_add_left := fun _scaleGrade _firstGrade _secondGrade firstBelowSecond =>
    andBothTrue (lawfulA.add_le_add_left _ _ _ (andLeftTrue firstBelowSecond))
      (lawfulB.add_le_add_left _ _ _ (andRightTrue firstBelowSecond))
  mul_le_mul_left := fun _scaleGrade _firstGrade _secondGrade firstBelowSecond =>
    andBothTrue (lawfulA.mul_le_mul_left _ _ _ (andLeftTrue firstBelowSecond))
      (lawfulB.mul_le_mul_left _ _ _ (andRightTrue firstBelowSecond))

/-- The concrete 2-dimension grade semiring: usage `{0,1,ω}` (§6.1) PRODUCT security
`{unclassified < classified}` (§6.3). -/
def fxUsageTimesSecuritySemiring : OrderedGradeSemiring :=
  OrderedGradeSemiring.product fxUsageSemiring fxSecuritySemiring

/-- The usage×security product is a lawful ordered semiring — directly from the two factor witnesses, no new
law proof. -/
theorem fxUsageTimesSecuritySemiring_isLawful :
    IsLawfulOrderedGradeSemiring fxUsageTimesSecuritySemiring :=
  IsLawfulOrderedGradeSemiring.product fxUsageSemiring_isLawful fxSecuritySemiring_isLawful

/-- The 2-dimension unit grade is literally the pair `(usage 1, security classified)`. -/
theorem fxUsageTimesSecurity_one_isPair :
    fxUsageTimesSecuritySemiring.one = (UsageGrade.one, SecurityGrade.classified) := rfl

/-- A single variable carries BOTH a usage grade AND a security grade in ONE `HasGradeOver` judgment — §6's
"grade vector every binding carries", concrete for two simultaneous dimensions. -/
theorem fxUsageTimesSecurity_variableCarriesBothGrades :
    HasGradeOver fxUsageTimesSecuritySemiring [GTypeOver.base]
      (GradeVectorOver.single fxUsageTimesSecuritySemiring 1 0 fxUsageTimesSecuritySemiring.one)
      (.var 0) GTypeOver.base :=
  HasGradeOver.var (R := fxUsageTimesSecuritySemiring) [GTypeOver.base] 0 GTypeOver.base rfl

/-- ★ **The full metatheory of the composed usage×security dimension, FOR FREE.**  Any term typed in the
2-dimension system is strongly normalizing AND subject-reduction-stable — the lawfulness premise discharged
by the product witness, the generic `HasGradeOver.metatheoryBundle` specialized to the product.  No new SN
or SR proof: composing two dimensions inherits both halves.  Generalizes `DIM2-7`/`#880` from a single added
dimension to a product of two. -/
theorem fxUsageTimesSecurity_metatheoryFree {typeContext : List (GTypeOver fxUsageTimesSecuritySemiring)}
    {grades : GradeVectorOver fxUsageTimesSecuritySemiring} {term : GradedLambda}
    {resultType : GTypeOver fxUsageTimesSecuritySemiring}
    (typed : HasGradeOver fxUsageTimesSecuritySemiring typeContext grades term resultType) :
    GradedLambda.IsStronglyNormalizing term ∧
      ∀ reduct : GradedLambda, GradedLambda.Reduces term reduct →
        HasGradeOver fxUsageTimesSecuritySemiring typeContext grades reduct resultType :=
  HasGradeOver.metatheoryBundle fxUsageTimesSecuritySemiring_isLawful typed

/-- Non-vacuity of the metatheory-free composition: the redex `(λx. x) z`, carrying a 2-dimension grade,
inherits both strong normalization and graded subject reduction. -/
theorem fxUsageTimesSecurity_appliedIdentity_metatheoryFree :
    GradedLambda.IsStronglyNormalizing (GradedLambda.app (.lam (.var 0)) (.var 0)) ∧
      ∀ reduct : GradedLambda,
        GradedLambda.Reduces (GradedLambda.app (.lam (.var 0)) (.var 0)) reduct →
        HasGradeOver fxUsageTimesSecuritySemiring [GTypeOver.base]
          (GradeVectorOver.add (GradeVectorOver.cons fxUsageTimesSecuritySemiring.zero GradeVectorOver.nil)
            (GradeVectorOver.scale fxUsageTimesSecuritySemiring.one
              (GradeVectorOver.single fxUsageTimesSecuritySemiring 1 0 fxUsageTimesSecuritySemiring.one)))
          reduct GTypeOver.base :=
  fxUsageTimesSecurity_metatheoryFree (appliedIdentityOver_typed fxUsageTimesSecuritySemiring)

end FX1Poly.Modal
