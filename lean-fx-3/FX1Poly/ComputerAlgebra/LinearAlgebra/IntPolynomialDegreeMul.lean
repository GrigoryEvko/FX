import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialPseudoDegreeDecrease
import FX1Poly.ComputerAlgebra.Number.IntNoZeroDivisors

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/IntPolynomialDegreeMul — the fundamental degree law
(the WP-ENDO #2255 degree law, the tenth brick of `invariantFactorSeparator`'s ℚ[x] arc)

The pieces built so far — the `polyCoeff` convolution substrate (`polyCoeffAdd`/`polyCoeffScale`), the
degree↔coefficient bridge (`polyLeadingCoeffEqCoeffDegree`), the vanishing bounds
(`polyCoeffZeroFromTrimLength`), the nonzero leading coefficient (`polyLeadingCoeffNonzeroWhenNonempty`),
the strict-degree-from-vanishing lever (`polyDegreeLtOfCoeffVanishingAbove`), and the arbitrary-sign ℤ
no-zero-divisor (`intMulNeZero`) — combine here into the *fundamental degree law of an integral-domain
polynomial ring*:

  `polyDegree (polyMul p q) = polyDegree p + polyDegree q`   (for `polyTrim p ≠ []`, `polyTrim q ≠ []`).

## Why it is true

Over ℤ (an integral domain) the top coefficient of a product is the product of the top coefficients, with
all higher coefficients vanishing:

  * `polyCoeffMulTop`: `polyCoeff (polyMul p q) (deg p + deg q) = polyLeadingCoeff p * polyLeadingCoeff q`
    — the two leading terms multiply, the lower terms of `p` contribute only below `deg p + deg q`;
  * `polyCoeffMulVanish`: every coefficient strictly above `deg p + deg q` is `0`;
  * `intMulNeZero`: the top coefficient is nonzero (both leading coefficients nonzero, ℤ has no zero
    divisors), pinning the degree from *below* (`polyDegreeGeOfCoeffNonzero`), while the vanishing pins it
    from *above* (`polyDegreeLtOfCoeffVanishingAbove`).

Antisymmetry of the two bounds gives equality.  `polyDegreeDvdMono` is the immediate divisibility
corollary: a nonzero multiple of `p` has degree at least `deg p`.

## Zero-axiom design

Structural induction on the left factor's coefficient list; every coefficient step routes through the
imported homomorphisms and the corpus `Int` ring lemmas, every Nat step through the constructive core
order lemmas (`Nat.le_of_succ_le_succ`, `Nat.lt_succ_of_le`, `Nat.le_add_right`, `Nat.le_antisymm`, …).
The product-position arithmetic is arranged so the peeled index sits *second* under `+`, making the
successor/predecessor reductions definitional (no subtraction-order lemma, which would leak `propext`).
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration
gated in `FX1PolyAudit/ComputerAlgebra/LinearAlgebra/IntPolynomialDegreeMul.lean`.
-/

namespace FX1Poly.ComputerAlgebra

/-! ## An all-zero left factor annihilates the product coefficientwise -/

/-- **A polynomial all of whose coefficients vanish multiplies to the zero polynomial.**  If
`polyCoeff leftPoly i = 0` for every `i`, then `polyCoeff (polyMul leftPoly rightPoly) position = 0` for
every position.  Induction on `leftPoly`: the head coefficient is `0` (kills the scaled summand) and the
tail is again all-zero (kills the shifted summand by the induction hypothesis). -/
theorem polyCoeffMulLeftZero :
    ∀ (leftPoly : List Int), (∀ i, polyCoeff leftPoly i = 0) →
      ∀ (rightPoly : List Int) (position : Nat),
        polyCoeff (polyMul leftPoly rightPoly) position = 0 := by
  intro leftPoly
  induction leftPoly with
  | nil => intro _ _ _; rfl
  | cons leftHead leftTail ih =>
      intro hzero rightPoly position
      have headZero : leftHead = 0 := hzero 0
      have tailZero : ∀ i, polyCoeff leftTail i = 0 := fun i => hzero (i + 1)
      show polyCoeff (polyAdd (polyScale leftHead rightPoly)
              (0 :: polyMul leftTail rightPoly)) position = 0
      rw [polyCoeffAdd, polyCoeffScale, headZero, intZeroMul, intZeroAdd]
      cases position with
      | zero => rfl
      | succ pos' =>
          show polyCoeff (polyMul leftTail rightPoly) pos' = 0
          exact ih tailZero rightPoly pos'

/-! ## Coefficients of a product vanish strictly above the sum of degrees -/

/-- **Product coefficients vanish above the sum of the degree bounds.**  If `leftPoly`'s coefficients
vanish at and above `leftBound` and `rightPoly`'s at and above `rightBound`, then every coefficient of the
product at a position with `rightBound + leftBound ≤ position + 1` is `0`.  Induction on `leftPoly`; the
`leftBound = 0` case (the left factor is entirely zero) defers to `polyCoeffMulLeftZero`, and the
successor case peels one coefficient — the scaled summand vanishes because `rightBound ≤ position`, the
shifted summand by the induction hypothesis on the strictly smaller position. -/
theorem polyCoeffMulVanish (rightPoly : List Int) :
    ∀ (leftPoly : List Int) (leftBound rightBound position : Nat),
      (∀ i, leftBound ≤ i → polyCoeff leftPoly i = 0) →
      (∀ j, rightBound ≤ j → polyCoeff rightPoly j = 0) →
      rightBound + leftBound ≤ position + 1 →
      polyCoeff (polyMul leftPoly rightPoly) position = 0 := by
  intro leftPoly
  induction leftPoly with
  | nil => intro _ _ _ _ _ _; rfl
  | cons leftHead leftTail ih =>
      intro leftBound rightBound position hp hq hbound
      cases leftBound with
      | zero =>
          exact polyCoeffMulLeftZero (leftHead :: leftTail)
            (fun i => hp i (Nat.zero_le i)) rightPoly position
      | succ m =>
          have hRmLePos : rightBound + m ≤ position := Nat.le_of_succ_le_succ hbound
          have hNqLePos : rightBound ≤ position :=
            Nat.le_trans (Nat.le_add_right rightBound m) hRmLePos
          show polyCoeff (polyAdd (polyScale leftHead rightPoly)
                  (0 :: polyMul leftTail rightPoly)) position = 0
          rw [polyCoeffAdd, polyCoeffScale, hq position hNqLePos, intMulZero, intZeroAdd]
          cases position with
          | zero => rfl
          | succ pos' =>
              show polyCoeff (polyMul leftTail rightPoly) pos' = 0
              have hp' : ∀ i, m ≤ i → polyCoeff leftTail i = 0 :=
                fun i hmi => hp (i + 1) (Nat.succ_le_succ hmi)
              have hbound' : rightBound + m ≤ pos' + 1 := Nat.le_of_succ_le_succ hbound
              exact ih m rightBound pos' hp' hq hbound'

/-! ## The top coefficient of a product is the product of the leading coefficients -/

/-- **The product's top coefficient factors.**  If `leftPoly`'s coefficients vanish strictly above
`leftDeg` and `rightPoly`'s strictly above `rightDeg`, then the product's coefficient at the top position
is `polyCoeff leftPoly leftDeg * polyCoeff rightPoly rightDeg`.  Induction on `leftPoly` with the peeled
index `leftDeg` placed second under `+` (so the position reductions `rightDeg + 0 ≡ rightDeg` and
`rightDeg + (m+1) ≡ (rightDeg + m).succ` are definitional): in the `leftDeg = 0` case the tail is all-zero
(shifted summand vanishes via `polyCoeffMulLeftZero`); in the successor case the scaled summand's index
`rightDeg + (m+1)` sits strictly above `rightDeg` so that summand vanishes, and the shifted summand is the
induction hypothesis. -/
theorem polyCoeffMulTop (rightPoly : List Int) :
    ∀ (leftPoly : List Int) (leftDeg rightDeg : Nat),
      (∀ i, leftDeg < i → polyCoeff leftPoly i = 0) →
      (∀ j, rightDeg < j → polyCoeff rightPoly j = 0) →
      polyCoeff (polyMul leftPoly rightPoly) (rightDeg + leftDeg)
        = polyCoeff leftPoly leftDeg * polyCoeff rightPoly rightDeg := by
  intro leftPoly
  induction leftPoly with
  | nil =>
      intro leftDeg rightDeg _ _
      show (0 : Int) = polyCoeff ([] : List Int) leftDeg * polyCoeff rightPoly rightDeg
      show (0 : Int) = (0 : Int) * polyCoeff rightPoly rightDeg
      exact (intZeroMul (polyCoeff rightPoly rightDeg)).symm
  | cons leftHead leftTail ih =>
      intro leftDeg rightDeg hp hq
      cases leftDeg with
      | zero =>
          have tailZero : ∀ j, polyCoeff leftTail j = 0 :=
            fun j => hp (j + 1) (Nat.succ_pos j)
          have secondZero : polyCoeff (0 :: polyMul leftTail rightPoly) rightDeg = 0 := by
            cases rightDeg with
            | zero => rfl
            | succ r => exact polyCoeffMulLeftZero leftTail tailZero rightPoly r
          show polyCoeff (polyAdd (polyScale leftHead rightPoly)
                  (0 :: polyMul leftTail rightPoly)) rightDeg
              = leftHead * polyCoeff rightPoly rightDeg
          rw [polyCoeffAdd, polyCoeffScale, secondZero, intAddZero]
      | succ m =>
          have hlt : rightDeg < rightDeg + (m + 1) :=
            Nat.lt_succ_of_le (Nat.le_add_right rightDeg m)
          have hp' : ∀ i, m < i → polyCoeff leftTail i = 0 :=
            fun i hmi => hp (i + 1) (Nat.succ_lt_succ hmi)
          have ihTail : polyCoeff (polyMul leftTail rightPoly) (rightDeg + m)
              = polyCoeff leftTail m * polyCoeff rightPoly rightDeg :=
            ih m rightDeg hp' hq
          show polyCoeff (polyAdd (polyScale leftHead rightPoly)
                  (0 :: polyMul leftTail rightPoly)) (rightDeg + (m + 1))
              = polyCoeff leftTail m * polyCoeff rightPoly rightDeg
          rw [polyCoeffAdd, polyCoeffScale, hq (rightDeg + (m + 1)) hlt, intMulZero, intZeroAdd]
          show polyCoeff (polyMul leftTail rightPoly) (rightDeg + m)
              = polyCoeff leftTail m * polyCoeff rightPoly rightDeg
          exact ihTail

/-! ## The lower degree bound (a nonzero coefficient forces the degree up)

The degree↔trim-length successor bridge `polyTrimLengthEqDegreeSucc`
(`(polyTrim coeffs).length = polyDegree coeffs + 1` for a nonzero polynomial) is reused from
`IntPolynomialPseudoDegreeDecrease`. -/

/-- `position < bound → position ≤ bound − 1`, by cases on `bound` (the successor case is
`Nat.le_of_lt_succ` and `(bound'+1) − 1` reduces to `bound'` definitionally — no subtraction-order lemma,
which would leak `propext`). -/
theorem natLePredOfLt : ∀ (position bound : Nat), position < bound → position ≤ bound - 1
  | position, 0, hLt => absurd hLt (Nat.not_lt_zero position)
  | _, _ + 1, hLt => Nat.le_of_lt_succ hLt

/-- **A nonzero coefficient at a position forces the degree at least that high.**  `polyCoeff coeffs
position ≠ 0 → position ≤ polyDegree coeffs` — the contrapositive of `polyCoeffZeroFromTrimLength`
(coefficients at/above the trimmed length vanish) turned into a lower bound on the degree. -/
theorem polyDegreeGeOfCoeffNonzero (coeffs : List Int) (position : Nat)
    (isCoeffNonzero : polyCoeff coeffs position ≠ 0) : position ≤ polyDegree coeffs := by
  have hLt : position < (polyTrim coeffs).length := by
    apply Nat.lt_of_not_le
    intro hLe
    exact isCoeffNonzero (polyCoeffZeroFromTrimLength coeffs position hLe)
  exact natLePredOfLt position (polyTrim coeffs).length hLt

/-! ## The fundamental degree law -/

/-- **The degree of a product is the sum of the degrees.**  For `polyTrim p ≠ []` and `polyTrim q ≠ []`,
`polyDegree (polyMul p q) = polyDegree p + polyDegree q`.  The product's coefficient at position
`deg p + deg q` is `polyLeadingCoeff p * polyLeadingCoeff q` (`polyCoeffMulTop` + the degree↔coefficient
bridge), nonzero because both leading coefficients are nonzero and ℤ has no zero divisors
(`intMulNeZero`) — pinning the degree from below (`polyDegreeGeOfCoeffNonzero`); the coefficients above
that position all vanish (`polyCoeffMulVanish`), pinning it from above
(`polyDegreeLtOfCoeffVanishingAbove`).  Antisymmetry closes it. -/
theorem polyDegreeMul (leftPoly rightPoly : List Int)
    (isLeftNonzero : polyTrim leftPoly ≠ []) (isRightNonzero : polyTrim rightPoly ≠ []) :
    polyDegree (polyMul leftPoly rightPoly) = polyDegree leftPoly + polyDegree rightPoly := by
  have topCoeff :
      polyCoeff (polyMul leftPoly rightPoly) (polyDegree leftPoly + polyDegree rightPoly)
        = polyLeadingCoeff leftPoly * polyLeadingCoeff rightPoly := by
    have hpVanish : ∀ i, polyDegree leftPoly < i → polyCoeff leftPoly i = 0 := by
      intro i hi
      apply polyCoeffZeroFromTrimLength
      rw [polyTrimLengthEqDegreeSucc leftPoly isLeftNonzero]
      exact hi
    have hqVanish : ∀ j, polyDegree rightPoly < j → polyCoeff rightPoly j = 0 := by
      intro j hj
      apply polyCoeffZeroFromTrimLength
      rw [polyTrimLengthEqDegreeSucc rightPoly isRightNonzero]
      exact hj
    have raw : polyCoeff (polyMul leftPoly rightPoly) (polyDegree rightPoly + polyDegree leftPoly)
        = polyCoeff leftPoly (polyDegree leftPoly) * polyCoeff rightPoly (polyDegree rightPoly) :=
      polyCoeffMulTop rightPoly leftPoly (polyDegree leftPoly) (polyDegree rightPoly) hpVanish hqVanish
    rw [polyLeadingCoeffEqCoeffDegree leftPoly, polyLeadingCoeffEqCoeffDegree rightPoly,
        Nat.add_comm (polyDegree leftPoly) (polyDegree rightPoly)]
    exact raw
  have topNe : polyLeadingCoeff leftPoly * polyLeadingCoeff rightPoly ≠ 0 :=
    intMulNeZero (polyLeadingCoeffNonzeroWhenNonempty leftPoly isLeftNonzero)
      (polyLeadingCoeffNonzeroWhenNonempty rightPoly isRightNonzero)
  have coeffNe :
      polyCoeff (polyMul leftPoly rightPoly) (polyDegree leftPoly + polyDegree rightPoly) ≠ 0 :=
    fun coeffIsZero => topNe (topCoeff ▸ coeffIsZero)
  have lower : polyDegree leftPoly + polyDegree rightPoly ≤ polyDegree (polyMul leftPoly rightPoly) :=
    polyDegreeGeOfCoeffNonzero (polyMul leftPoly rightPoly)
      (polyDegree leftPoly + polyDegree rightPoly) coeffNe
  have vanishAbove : ∀ position, polyDegree leftPoly + polyDegree rightPoly + 1 ≤ position →
      polyCoeff (polyMul leftPoly rightPoly) position = 0 := by
    intro position hpos
    apply polyCoeffMulVanish rightPoly leftPoly (polyDegree leftPoly + 1) (polyDegree rightPoly + 1)
      position
    · intro i hi
      apply polyCoeffZeroFromTrimLength
      rw [polyTrimLengthEqDegreeSucc leftPoly isLeftNonzero]
      exact hi
    · intro j hj
      apply polyCoeffZeroFromTrimLength
      rw [polyTrimLengthEqDegreeSucc rightPoly isRightNonzero]
      exact hj
    · exact Nat.succ_le_succ
        (Nat.le_trans
          (Nat.le_of_eq (Nat.add_comm (polyDegree rightPoly + 1) (polyDegree leftPoly)))
          hpos)
  have upper : polyDegree (polyMul leftPoly rightPoly)
      < polyDegree leftPoly + polyDegree rightPoly + 1 :=
    polyDegreeLtOfCoeffVanishingAbove (polyMul leftPoly rightPoly)
      (polyDegree leftPoly + polyDegree rightPoly + 1)
      (Nat.le_add_left 1 (polyDegree leftPoly + polyDegree rightPoly)) vanishAbove
  exact Nat.le_antisymm (Nat.le_of_lt_succ upper) lower

/-- **Degree monotonicity under (trim-equal) multiples.**  If `q` equals `p · r` up to trailing zeros
(`polyTrim q = polyTrim (polyMul p r)`) with `p`, `r` nonzero, then `polyDegree p ≤ polyDegree q` — a
nonzero multiple of `p` has degree at least `deg p`.  The divisibility-reasoning corollary of the degree
law. -/
theorem polyDegreeDvdMono (dividend multiplierLeft multiplierRight : List Int)
    (isLeftNonzero : polyTrim multiplierLeft ≠ []) (isRightNonzero : polyTrim multiplierRight ≠ [])
    (isTrimEqProduct : polyTrim dividend = polyTrim (polyMul multiplierLeft multiplierRight)) :
    polyDegree multiplierLeft ≤ polyDegree dividend := by
  have hDegEq : polyDegree dividend = polyDegree (polyMul multiplierLeft multiplierRight) := by
    show (polyTrim dividend).length - 1
        = (polyTrim (polyMul multiplierLeft multiplierRight)).length - 1
    rw [isTrimEqProduct]
  rw [hDegEq, polyDegreeMul multiplierLeft multiplierRight isLeftNonzero isRightNonzero]
  exact Nat.le_add_right (polyDegree multiplierLeft) (polyDegree multiplierRight)

/-! ## Groundings -/

/-- `(x + 1)² = x² + 2x + 1` has degree `2`: `polyDegree (polyMul [1, 1] [1, 1]) = 2`, a `decide`
cross-check of `polyDegreeMul` (both factors degree `1`). -/
theorem polyDegreeMulBinomialExample : polyDegree (polyMul [1, 1] [1, 1]) = 2 := by decide

/-- `(x − 2)(x − 5)` has degree `2`: `polyDegree (polyMul (polyLinearFactor 2) (polyLinearFactor 5)) = 2`,
the degree law exhibited on the linear-factor product `[10, -7, 1]`. -/
theorem polyDegreeMulLinearFactorsExample :
    polyDegree (polyMul (polyLinearFactor 2) (polyLinearFactor 5)) = 2 := by decide

/-- Marker: the ℤ[x] fundamental degree law ships — `polyDegree (polyMul p q) = polyDegree p +
polyDegree q` for nonzero `p`, `q` (the top coefficient is the product of the leading coefficients, hence
nonzero by ℤ's no-zero-divisor property, while higher coefficients vanish), together with the
divisibility corollary `polyDegreeDvdMono`.  The degree-decrease/termination content for the Euclidean
pseudo-division GCD. -/
def fxIntPoly_hasPolynomialDegreeMul : Bool := true

end FX1Poly.ComputerAlgebra
