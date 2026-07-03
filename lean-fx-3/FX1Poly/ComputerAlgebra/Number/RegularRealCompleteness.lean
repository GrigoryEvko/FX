import FX1Poly.ComputerAlgebra.Number.RegularRealDistance
import FX1Poly.ComputerAlgebra.Number.RegularRealOrder

/-! # RegularReal completeness — the diagonal limit (NUM-R-6b)

A regular Cauchy sequence of reals — pairwise within
`1/(i+1) + 1/(j+1)` in the real-level distance — has a LIMIT built by
the diagonal: sample the `K n`-th real at its own `K n`-th approximant,
where `K n = 2·(2·n+1)+1` is the quarter-scaled depth.

The diagonal's regularity needs NO slack closure: chaining through the
`K i`-th approximant of the `K j`-th real, the Cauchy modulus is
evaluated AT the deep index `K i`, so its setoid tolerance lands on the
same denominator as the sequence moduli and the whole bound collapses
by same-denominator sums — four quarters at depth `K i` are EXACTLY
`1/(i+1)` (the quadruple split), and the two quarters at depth `K j`
relax to `1/(j+1)` by one antitone step.

Still ahead in R-6: the convergence theorem (`values n` sits within a
vanishing real-level bound of the limit) and limit uniqueness. -/

namespace FX1Poly.ComputerAlgebra

open RationalPair

/-- The diagonal sampling depth — the quarter-scaled index at which
`1/(n+1)` splits exactly into four reciprocals. -/
def diagonalSamplingIndex (index : Nat) : Nat :=
  2 * (2 * index + 1) + 1

/-- **A regular Cauchy sequence of reals** — pairwise within the sum
of the position reciprocals, in the real-level distance. -/
structure RegularRealSequence where
  values : Nat → RegularReal
  isCauchy : ∀ firstPosition secondPosition : Nat,
    IsWithinRealBound (values firstPosition) (values secondPosition)
      (addExact (reciprocalOfSucc firstPosition)
        (reciprocalOfSucc secondPosition))

/-- **The diagonal limit** — the `K n`-th real sampled at its own
`K n`-th approximant.  Regularity chains the Cauchy modulus (evaluated
at the deep index) with the deep real's own regularity; the
accumulated bound is three same-denominator pieces at depth `K i`
summing exactly to the quadruple split of `1/(i+1)`, plus two pieces
at depth `K j` halving to `1/(2j+2)` and relaxing to `1/(j+1)`. -/
def limitReal (sequence : RegularRealSequence) : RegularReal :=
  { approximation := fun index =>
      (sequence.values (diagonalSamplingIndex index)).approximation
        (diagonalSamplingIndex index)
    isRegular := fun firstIndex secondIndex =>
      have chainedThroughDeepSample :
          IsWithinBound
            ((sequence.values (diagonalSamplingIndex firstIndex)).approximation
              (diagonalSamplingIndex firstIndex))
            ((sequence.values (diagonalSamplingIndex secondIndex)).approximation
              (diagonalSamplingIndex secondIndex))
            (addExact
              (addExact
                (addExact
                  (reciprocalOfSucc (diagonalSamplingIndex firstIndex))
                  (reciprocalOfSucc (diagonalSamplingIndex secondIndex)))
                (ratioOfNatSucc 2 (diagonalSamplingIndex firstIndex)))
              (addExact
                (reciprocalOfSucc (diagonalSamplingIndex firstIndex))
                (reciprocalOfSucc (diagonalSamplingIndex secondIndex)))) :=
        isWithinBoundTriangle
          (sequence.isCauchy (diagonalSamplingIndex firstIndex)
            (diagonalSamplingIndex secondIndex)
            (diagonalSamplingIndex firstIndex))
          ((sequence.values (diagonalSamplingIndex secondIndex)).isRegular
            (diagonalSamplingIndex firstIndex)
            (diagonalSamplingIndex secondIndex))
      have boundGathers :
          DenotesSameAs
            (addExact
              (addExact
                (addExact
                  (reciprocalOfSucc (diagonalSamplingIndex firstIndex))
                  (reciprocalOfSucc (diagonalSamplingIndex secondIndex)))
                (ratioOfNatSucc 2 (diagonalSamplingIndex firstIndex)))
              (addExact
                (reciprocalOfSucc (diagonalSamplingIndex firstIndex))
                (reciprocalOfSucc (diagonalSamplingIndex secondIndex))))
            (addExact (reciprocalOfSucc firstIndex)
              (reciprocalOfSucc (2 * secondIndex + 1))) :=
        denotesSameAsTrans
          (addExactRespectsDenotesSameAs
            (addExactRespectsDenotesSameAs
              (addExactComm
                (reciprocalOfSucc (diagonalSamplingIndex firstIndex))
                (reciprocalOfSucc (diagonalSamplingIndex secondIndex)))
              (denotesSameAsRefl
                (ratioOfNatSucc 2 (diagonalSamplingIndex firstIndex))))
            (denotesSameAsRefl
              (addExact
                (reciprocalOfSucc (diagonalSamplingIndex firstIndex))
                (reciprocalOfSucc (diagonalSamplingIndex secondIndex)))))
          (denotesSameAsTrans
            (addExactRespectsDenotesSameAs
              (addExactAssoc
                (reciprocalOfSucc (diagonalSamplingIndex secondIndex))
                (reciprocalOfSucc (diagonalSamplingIndex firstIndex))
                (ratioOfNatSucc 2 (diagonalSamplingIndex firstIndex)))
              (denotesSameAsRefl
                (addExact
                  (reciprocalOfSucc (diagonalSamplingIndex firstIndex))
                  (reciprocalOfSucc (diagonalSamplingIndex secondIndex)))))
            (denotesSameAsTrans
              (addExactAssoc
                (reciprocalOfSucc (diagonalSamplingIndex secondIndex))
                (addExact
                  (reciprocalOfSucc (diagonalSamplingIndex firstIndex))
                  (ratioOfNatSucc 2 (diagonalSamplingIndex firstIndex)))
                (addExact
                  (reciprocalOfSucc (diagonalSamplingIndex firstIndex))
                  (reciprocalOfSucc (diagonalSamplingIndex secondIndex))))
              (denotesSameAsTrans
                (addExactRespectsDenotesSameAs
                  (denotesSameAsRefl
                    (reciprocalOfSucc (diagonalSamplingIndex secondIndex)))
                  (addExactRespectsDenotesSameAs
                    (ratioOfNatSuccSumDenotesSame 1 2
                      (diagonalSamplingIndex firstIndex))
                    (denotesSameAsRefl
                      (addExact
                        (reciprocalOfSucc (diagonalSamplingIndex firstIndex))
                        (reciprocalOfSucc
                          (diagonalSamplingIndex secondIndex))))))
                (denotesSameAsTrans
                  (addExactRespectsDenotesSameAs
                    (denotesSameAsRefl
                      (reciprocalOfSucc (diagonalSamplingIndex secondIndex)))
                    (denotesSameAsSymm
                      (addExactAssoc
                        (ratioOfNatSucc 3 (diagonalSamplingIndex firstIndex))
                        (reciprocalOfSucc (diagonalSamplingIndex firstIndex))
                        (reciprocalOfSucc
                          (diagonalSamplingIndex secondIndex)))))
                  (denotesSameAsTrans
                    (addExactRespectsDenotesSameAs
                      (denotesSameAsRefl
                        (reciprocalOfSucc
                          (diagonalSamplingIndex secondIndex)))
                      (addExactRespectsDenotesSameAs
                        (ratioOfNatSuccSumDenotesSame 3 1
                          (diagonalSamplingIndex firstIndex))
                        (denotesSameAsRefl
                          (reciprocalOfSucc
                            (diagonalSamplingIndex secondIndex)))))
                    (denotesSameAsTrans
                      (addExactRespectsDenotesSameAs
                        (denotesSameAsRefl
                          (reciprocalOfSucc
                            (diagonalSamplingIndex secondIndex)))
                        (addExactComm
                          (ratioOfNatSucc 4
                            (diagonalSamplingIndex firstIndex))
                          (reciprocalOfSucc
                            (diagonalSamplingIndex secondIndex))))
                      (denotesSameAsTrans
                        (denotesSameAsSymm
                          (addExactAssoc
                            (reciprocalOfSucc
                              (diagonalSamplingIndex secondIndex))
                            (reciprocalOfSucc
                              (diagonalSamplingIndex secondIndex))
                            (ratioOfNatSucc 4
                              (diagonalSamplingIndex firstIndex))))
                        (denotesSameAsTrans
                          (addExactRespectsDenotesSameAs
                            (ratioOfNatSuccSumDenotesSame 1 1
                              (diagonalSamplingIndex secondIndex))
                            (denotesSameAsSymm
                              (reciprocalQuadrupleSplitDenotesSame
                                firstIndex)))
                          (denotesSameAsTrans
                            (addExactRespectsDenotesSameAs
                              (denotesSameAsSymm
                                (reciprocalHalvesDenotesSame
                                  (2 * secondIndex + 1)))
                              (denotesSameAsRefl
                                (reciprocalOfSucc firstIndex)))
                            (addExactComm
                              (reciprocalOfSucc (2 * secondIndex + 1))
                              (reciprocalOfSucc firstIndex)))))))))))
      isWithinBoundOfBoundLessEqual
        (addExactMonotone (lessEqualAsRefl (reciprocalOfSucc firstIndex))
          (ratioOfNatSuccAntitoneDenominator 1
            (natSelfLeDoubleSelfSucc secondIndex)))
        (isWithinBoundCongrBound boundGathers chainedThroughDeepSample) }

end FX1Poly.ComputerAlgebra
