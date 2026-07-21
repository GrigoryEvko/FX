import FX1Poly.ComputerAlgebra.LinearAlgebra.RationalPolynomialRing

/-! # RationalPolynomialBezout — trim-level `rpxMul` commutativity, the Bezout identity over ℚ[x], and the
Smith pivot-clear seed

The ℚ[x] ring layer (`RationalPolynomialRing`) shipped `rpxMul` two-sided distributivity, trim-level
associativity, the aggregate division reconstruction, and "gcd divides both", but left the Bezout identity
open, naming the missing prerequisite: `rpxMul` commutativity up to trim. This module supplies it and closes
the wall.

`rbzMulCommTrim` proves `rpxTrim (p × q) = rpxTrim (q × p)` as convolution symmetry through the coefficient
bridge — a right-cons coefficient decomposition (`rbzMulRightConsCoeff`, the mirror of `rpxMul`'s definitional
left-cons recursion) turns commutativity into a clean structural induction (`rbzMulCommCoeff`). This yields the
left-trim-congruence (`rbzMulRespectsTrimLeft`) and divisibility transitivity (`rbzDividesTrans`).

`rbzBezoutIdentity` gives `∃ u v, rpxTrim (u·p + v·q) = rpxTrim (rpxGcd fuel p q)` at every fuel via the
extended-Euclidean recursion (`rbzBezoutInvariant`, structural on fuel, no fuel-adequacy measure needed), whose
step swap `(u', v') ↦ (v', u' − v'·quotient)` is carried by `rbzComboRewrite` over the aggregate reconstruction
`primary ≡ quotient·secondary + remainder`.

The Smith pivot-clear seed lands the ℚ[x]-matrix carrier `rbzPolyMatrix` with accessors, the single-entry
clear (`rbzClearEntry`) and column clear (`rbzColumnClear`), the first pivot lemma (`rbzClearEntryReducesDegree`,
from `rpdDivModRemainderDegree`), and the reconstruction certifying the clear as an elementary operation
`entry ≡ quotient·pivot + cleared` (`rbzClearEntryReconstructs`). The full Smith normal form remains walled
(`rsiHasSmithNormalForm`).

Every convolution/negation law is structural on the coefficient list; every trim-level law routes through the
coefficient bridge and the shipped `qnf*` field laws; the Bezout recursion is structural on fuel. No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`, `funext`, or `WellFounded.fix`.
Per-declaration audit twin in the matching `FX1PolyAudit` path. -/

namespace FX1Poly.ComputerAlgebra

/-! ## Derived `QnfRat` and additive-rearrangement helpers -/

/-- **Multiplication pushes past negation on the left.**  `(-a) · b = -(a · b)` — commute, reuse the shipped
right-negation law (`qnfMulNegRight`), commute back. -/
theorem rbzQnfMulNegLeft (leftFactor rightFactor : QnfRat) :
    qnfMul (qnfNeg leftFactor) rightFactor = qnfNeg (qnfMul leftFactor rightFactor) :=
  (qnfMulComm (qnfNeg leftFactor) rightFactor).trans
    ((qnfMulNegRight rightFactor leftFactor).trans
      (congrArg qnfNeg (qnfMulComm rightFactor leftFactor)))

/-- **The three-summand swap** `X + (Y + Z) = Y + (X + Z)` — associativity, commutativity of the front pair,
associativity back.  The convolution-symmetry regrouping lever. -/
theorem rbzQnfAddSwap (valueX valueY valueZ : QnfRat) :
    qnfAdd valueX (qnfAdd valueY valueZ) = qnfAdd valueY (qnfAdd valueX valueZ) :=
  (qnfAddAssoc valueX valueY valueZ).symm.trans
    ((congrArg (qnfAdd · valueZ) (qnfAddComm valueX valueY)).trans
      (qnfAddAssoc valueY valueX valueZ))

/-- **The Bezout additive cancellation** `(a + b) + (c − a) = c + b` — the `a` and `−a` cancel through the
commutative-group laws.  The coefficientwise heart of `rbzCombineCancelTrim`. -/
theorem rbzQnfCombineCancel (valueA valueB valueC : QnfRat) :
    qnfAdd (qnfAdd valueA valueB) (qnfSub valueC valueA) = qnfAdd valueC valueB :=
  (congrArg (qnfAdd (qnfAdd valueA valueB)) (qnfSubEqAddNeg valueC valueA)).trans
    ((congrArg (qnfAdd (qnfAdd valueA valueB)) (qnfAddComm valueC (qnfNeg valueA))).trans
      ((qnfAddAssoc (qnfAdd valueA valueB) (qnfNeg valueA) valueC).symm.trans
        ((congrArg (fun folded => qnfAdd (qnfAdd folded (qnfNeg valueA)) valueC)
            (qnfAddComm valueA valueB)).trans
          ((congrArg (qnfAdd · valueC) (qnfAddAssoc valueB valueA (qnfNeg valueA))).trans
            ((congrArg (fun folded => qnfAdd (qnfAdd valueB folded) valueC) (qnfAddNegRight valueA)).trans
              ((congrArg (qnfAdd · valueC) (qnfAddZeroRight valueB)).trans
                (qnfAddComm valueB valueC)))))))

/-! ## T1a — the negation/multiplication interaction laws (plain `Eq`) -/

/-- **Negation commutes past scaling.**  `-(scalar · p) = (-scalar) · p` (coefficientwise
`rbzQnfMulNegLeft`). -/
theorem rbzNegScale (scalar : QnfRat) :
    ∀ coeffs : List QnfRat, rpxNeg (rpxScale scalar coeffs) = rpxScale (qnfNeg scalar) coeffs
  | [] => rfl
  | coeff :: restCoeffs =>
      (congrArg (· :: rpxNeg (rpxScale scalar restCoeffs)) (rbzQnfMulNegLeft scalar coeff).symm).trans
        (congrArg (qnfMul (qnfNeg scalar) coeff :: ·) (rbzNegScale scalar restCoeffs))

/-- **Negation distributes over a polynomial sum.**  `-(p + q) = (-p) + (-q)` (coefficientwise
`qnfNegAdd`). -/
theorem rbzNegAdd :
    ∀ leftPoly rightPoly : List QnfRat,
      rpxNeg (rpxAdd leftPoly rightPoly) = rpxAdd (rpxNeg leftPoly) (rpxNeg rightPoly)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | leftHead :: leftTail, rightHead :: rightTail =>
      (congrArg (· :: rpxNeg (rpxAdd leftTail rightTail)) (qnfNegAdd leftHead rightHead)).trans
        (congrArg (qnfAdd (qnfNeg leftHead) (qnfNeg rightHead) :: ·) (rbzNegAdd leftTail rightTail))

/-- **Negation commutes past multiplication on the left.**  `(-p) × q = -(p × q)` (plain `Eq`) — induction
on `p`, folding `rbzNegAdd`, `rbzNegScale`, and `qnfNegZero` through the `rpxMul` convolution step. -/
theorem rbzMulNegLeft :
    ∀ (leftPoly rightPoly : List QnfRat),
      rpxMul (rpxNeg leftPoly) rightPoly = rpxNeg (rpxMul leftPoly rightPoly)
  | [], _ => rfl
  | leftHead :: leftTail, rightPoly => by
      show rpxAdd (rpxScale (qnfNeg leftHead) rightPoly) (qnfZero :: rpxMul (rpxNeg leftTail) rightPoly)
         = rpxNeg (rpxAdd (rpxScale leftHead rightPoly) (qnfZero :: rpxMul leftTail rightPoly))
      rw [rbzNegAdd, rbzNegScale]
      show rpxAdd (rpxScale (qnfNeg leftHead) rightPoly) (qnfZero :: rpxMul (rpxNeg leftTail) rightPoly)
         = rpxAdd (rpxScale (qnfNeg leftHead) rightPoly)
             (qnfNeg qnfZero :: rpxNeg (rpxMul leftTail rightPoly))
      rw [qnfNegZero, rbzMulNegLeft leftTail rightPoly]

/-! ## T1b — the convolution coefficient laws -/

/-- **The right-nil product vanishes coefficientwise.**  `rpxCoeff (p × []) n = qnfZero` — the product by the
zero polynomial is a list of zeros; induction on `p` through the shifted convolution. -/
theorem rbzMulNilRightCoeff :
    ∀ (poly : List QnfRat) (position : Nat), rpxCoeff (rpxMul poly []) position = qnfZero
  | [], _ => rfl
  | leftHead :: leftTail, position => by
      show rpxCoeff (qnfZero :: rpxMul leftTail []) position = qnfZero
      cases position with
      | zero => rfl
      | succ priorPosition => exact rbzMulNilRightCoeff leftTail priorPosition

/-- **The RIGHT-cons coefficient decomposition.**  `rpxMul` recurses on its LEFT argument, so peeling the
right factor's head is a theorem, not a definition: `rpxCoeff (p × (rightHead :: rightTail)) n = p[n]·rightHead
+ rpxCoeff (0 :: (p × rightTail)) n`.  Induction on `p`, position-cased through the convolution shift; the
successor case regroups by `rbzQnfAddSwap`.  This is the mirror that makes commutativity a clean induction. -/
theorem rbzMulRightConsCoeff :
    ∀ (poly : List QnfRat) (rightHead : QnfRat) (rightTail : List QnfRat) (position : Nat),
      rpxCoeff (rpxMul poly (rightHead :: rightTail)) position
        = qnfAdd (qnfMul (rpxCoeff poly position) rightHead)
            (rpxCoeff (qnfZero :: rpxMul poly rightTail) position)
  | [], rightHead, _, position => by
      show qnfZero = qnfAdd (qnfMul qnfZero rightHead) (rpxCoeff [qnfZero] position)
      rw [rpdCoeffSingletonZero, qnfMulZeroLeft, qnfAddZeroLeft]
  | leftHead :: leftTail, rightHead, rightTail, position => by
      show rpxCoeff (rpxAdd (rpxScale leftHead (rightHead :: rightTail))
              (qnfZero :: rpxMul leftTail (rightHead :: rightTail))) position
         = qnfAdd (qnfMul (rpxCoeff (leftHead :: leftTail) position) rightHead)
             (rpxCoeff (qnfZero :: rpxMul (leftHead :: leftTail) rightTail) position)
      rw [rpxCoeffAdd, rpxCoeffScale]
      cases position with
      | zero => rfl
      | succ priorPosition =>
          show qnfAdd (qnfMul leftHead (rpxCoeff rightTail priorPosition))
                (rpxCoeff (rpxMul leftTail (rightHead :: rightTail)) priorPosition)
             = qnfAdd (qnfMul (rpxCoeff leftTail priorPosition) rightHead)
                 (rpxCoeff (rpxMul (leftHead :: leftTail) rightTail) priorPosition)
          have lhsSecond : rpxCoeff (rpxMul leftTail (rightHead :: rightTail)) priorPosition
              = qnfAdd (qnfMul (rpxCoeff leftTail priorPosition) rightHead)
                  (rpxCoeff (qnfZero :: rpxMul leftTail rightTail) priorPosition) :=
            rbzMulRightConsCoeff leftTail rightHead rightTail priorPosition
          have rhsSecond : rpxCoeff (rpxMul (leftHead :: leftTail) rightTail) priorPosition
              = qnfAdd (qnfMul leftHead (rpxCoeff rightTail priorPosition))
                  (rpxCoeff (qnfZero :: rpxMul leftTail rightTail) priorPosition) := by
            show rpxCoeff (rpxAdd (rpxScale leftHead rightTail)
                    (qnfZero :: rpxMul leftTail rightTail)) priorPosition
               = qnfAdd (qnfMul leftHead (rpxCoeff rightTail priorPosition))
                   (rpxCoeff (qnfZero :: rpxMul leftTail rightTail) priorPosition)
            rw [rpxCoeffAdd, rpxCoeffScale]
          rw [lhsSecond, rhsSecond]
          exact rbzQnfAddSwap (qnfMul leftHead (rpxCoeff rightTail priorPosition))
            (qnfMul (rpxCoeff leftTail priorPosition) rightHead)
            (rpxCoeff (qnfZero :: rpxMul leftTail rightTail) priorPosition)

/-- **Convolution symmetry, coefficientwise.**  `rpxCoeff (p × q) n = rpxCoeff (q × p) n` — induction on `p`:
the empty case is `rbzMulNilRightCoeff`; the cons case peels `q`'s convolution against `p`'s head with
`rbzMulRightConsCoeff`, commutes the leading product (`qnfMulComm`), and recurses on the shifted tail. -/
theorem rbzMulCommCoeff :
    ∀ (leftPoly rightPoly : List QnfRat) (position : Nat),
      rpxCoeff (rpxMul leftPoly rightPoly) position = rpxCoeff (rpxMul rightPoly leftPoly) position
  | [], rightPoly, position => (rbzMulNilRightCoeff rightPoly position).symm
  | leftHead :: leftTail, rightPoly, position => by
      show rpxCoeff (rpxAdd (rpxScale leftHead rightPoly) (qnfZero :: rpxMul leftTail rightPoly)) position
         = rpxCoeff (rpxMul rightPoly (leftHead :: leftTail)) position
      rw [rpxCoeffAdd, rpxCoeffScale, rbzMulRightConsCoeff rightPoly leftHead leftTail position]
      have secondEq : rpxCoeff (qnfZero :: rpxMul leftTail rightPoly) position
          = rpxCoeff (qnfZero :: rpxMul rightPoly leftTail) position := by
        cases position with
        | zero => rfl
        | succ priorPosition => exact rbzMulCommCoeff leftTail rightPoly priorPosition
      rw [qnfMulComm leftHead (rpxCoeff rightPoly position), secondEq]

/-- **T1 — `rpxMul` is commutative up to trim.**  `rpxTrim (p × q) = rpxTrim (q × p)`: convolution symmetry
(`rbzMulCommCoeff`) closed at the trim level by the committed coefficient bridge (`rpdTrimEqOfCoeffEq`).  The
named prerequisite the committed Bezout wall called out. -/
theorem rbzMulCommTrim (leftPoly rightPoly : List QnfRat) :
    rpxTrim (rpxMul leftPoly rightPoly) = rpxTrim (rpxMul rightPoly leftPoly) :=
  rpdTrimEqOfCoeffEq (rpxMul leftPoly rightPoly) (rpxMul rightPoly leftPoly)
    (fun position => rbzMulCommCoeff leftPoly rightPoly position)

/-- **`rpxMul` respects trim in the LEFT argument.**  `rpxTrim leftA = rpxTrim leftB → rpxTrim (leftA × r) =
rpxTrim (leftB × r)` — commute to the right, transport with the committed `rpeMulRespectsTrimRight`, commute
back. -/
theorem rbzMulRespectsTrimLeft (leftA leftB rightPoly : List QnfRat)
    (trimEq : rpxTrim leftA = rpxTrim leftB) :
    rpxTrim (rpxMul leftA rightPoly) = rpxTrim (rpxMul leftB rightPoly) :=
  (rbzMulCommTrim leftA rightPoly).trans
    ((rpeMulRespectsTrimRight rightPoly leftA leftB trimEq).trans
      (rbzMulCommTrim rightPoly leftB))

/-- **Divisibility is transitive.**  `divisor | middle → middle | dividend → divisor | dividend` — compose the
cofactors as `secondCofactor × firstCofactor`, associate up to trim (`rpeMulAssocTrim`), and transport the
inner witness with `rpeMulRespectsTrimRight`. -/
theorem rbzDividesTrans (divisorPoly middlePoly dividendPoly : List QnfRat)
    (dividesMiddle : rpeDivides divisorPoly middlePoly)
    (dividesDividend : rpeDivides middlePoly dividendPoly) :
    rpeDivides divisorPoly dividendPoly := by
  obtain ⟨firstCofactor, firstEq⟩ := dividesMiddle
  obtain ⟨secondCofactor, secondEq⟩ := dividesDividend
  refine ⟨rpxMul secondCofactor firstCofactor, ?_⟩
  exact (rpeMulAssocTrim secondCofactor firstCofactor divisorPoly).trans
    ((rpeMulRespectsTrimRight secondCofactor (rpxMul firstCofactor divisorPoly) middlePoly firstEq).trans
      secondEq)

/-! ## T2 — the Bezout identity -/

/-- **The additive cancellation, trim level.**  `rpxTrim ((A + B) + (C − A)) = rpxTrim (C + B)` — the `A` and
`−A` cancel; via the coefficient bridge and `rbzQnfCombineCancel`. -/
theorem rbzCombineCancelTrim (polyA polyB polyC : List QnfRat) :
    rpxTrim (rpxAdd (rpxAdd polyA polyB) (rpxSub polyC polyA)) = rpxTrim (rpxAdd polyC polyB) := by
  apply rpdTrimEqOfCoeffEq
  intro position
  rw [rpxCoeffAdd, rpxCoeffAdd, rpxCoeffSub, rpxCoeffAdd]
  exact rbzQnfCombineCancel (rpxCoeff polyA position) (rpxCoeff polyB position) (rpxCoeff polyC position)

/-- **THE EUCLIDEAN-STEP COFACTOR REWRITE.**  Given the reconstruction `quotient·secondary + remainder ≡
primary`, the combination for cofactors `(cofactorV, cofactorU − cofactorV·quotient)` against `(primary,
secondary)` trims equal to `cofactorU·secondary + cofactorV·remainder`.  This is the extended-Euclidean
swap: it turns a Bezout pair for `(secondary, remainder)` into one for `(primary, secondary)`.  Uses
RIGHT-distributivity + `rbzMulNegLeft` (to expand the subtraction cofactor), `rpeMulRespectsTrimRight` +
LEFT-distributivity + `rpeMulAssocTrim` (to rewrite `cofactorV·primary`), and `rbzCombineCancelTrim` (to
cancel the shared `cofactorV·quotient·secondary` term). -/
theorem rbzComboRewrite (primary secondary quotient remainder cofactorU cofactorV : List QnfRat)
    (recon : rpxTrim (rpxAdd (rpxMul quotient secondary) remainder) = rpxTrim primary) :
    rpxTrim (rpxAdd (rpxMul cofactorV primary)
        (rpxMul (rpxSub cofactorU (rpxMul cofactorV quotient)) secondary))
      = rpxTrim (rpxAdd (rpxMul cofactorU secondary) (rpxMul cofactorV remainder)) := by
  have expandSub : rpxMul (rpxSub cofactorU (rpxMul cofactorV quotient)) secondary
      = rpxSub (rpxMul cofactorU secondary) (rpxMul (rpxMul cofactorV quotient) secondary) := by
    show rpxMul (rpxAdd cofactorU (rpxNeg (rpxMul cofactorV quotient))) secondary
       = rpxAdd (rpxMul cofactorU secondary) (rpxNeg (rpxMul (rpxMul cofactorV quotient) secondary))
    rw [rpeMulRightDistrib, rbzMulNegLeft]
  have vPrimaryTrim : rpxTrim (rpxMul cofactorV primary)
      = rpxTrim (rpxAdd (rpxMul (rpxMul cofactorV quotient) secondary) (rpxMul cofactorV remainder)) := by
    have step1 : rpxTrim (rpxMul cofactorV primary)
        = rpxTrim (rpxMul cofactorV (rpxAdd (rpxMul quotient secondary) remainder)) :=
      rpeMulRespectsTrimRight cofactorV primary
        (rpxAdd (rpxMul quotient secondary) remainder) recon.symm
    have step2 : rpxTrim (rpxMul cofactorV (rpxAdd (rpxMul quotient secondary) remainder))
        = rpxTrim (rpxAdd (rpxMul cofactorV (rpxMul quotient secondary)) (rpxMul cofactorV remainder)) :=
      congrArg rpxTrim (rpeMulLeftDistrib cofactorV (rpxMul quotient secondary) remainder)
    have step3 : rpxTrim (rpxAdd (rpxMul cofactorV (rpxMul quotient secondary)) (rpxMul cofactorV remainder))
        = rpxTrim (rpxAdd (rpxMul (rpxMul cofactorV quotient) secondary) (rpxMul cofactorV remainder)) :=
      rpeAddRespectsTrim (rpeMulAssocTrim cofactorV quotient secondary).symm rfl
    exact step1.trans (step2.trans step3)
  rw [expandSub]
  calc rpxTrim (rpxAdd (rpxMul cofactorV primary)
          (rpxSub (rpxMul cofactorU secondary) (rpxMul (rpxMul cofactorV quotient) secondary)))
      = rpxTrim (rpxAdd
          (rpxAdd (rpxMul (rpxMul cofactorV quotient) secondary) (rpxMul cofactorV remainder))
          (rpxSub (rpxMul cofactorU secondary) (rpxMul (rpxMul cofactorV quotient) secondary))) :=
        rpeAddRespectsTrim vPrimaryTrim rfl
    _ = rpxTrim (rpxAdd (rpxMul cofactorU secondary) (rpxMul cofactorV remainder)) :=
        rbzCombineCancelTrim (rpxMul (rpxMul cofactorV quotient) secondary) (rpxMul cofactorV remainder)
          (rpxMul cofactorU secondary)

/-- **THE BEZOUT INVARIANT.**  At EVERY fuel there exist cofactors with `rpxTrim (cofactorLeft·primary +
cofactorRight·secondary) = rpxTrim (rpxGcd fuel primary secondary)`.  Structural fuel induction — no
fuel-adequacy measure is needed because the aggregate reconstruction (`rpeDivModReconstructsTrim`) holds at
every fuel.  Base / terminal (`secondary` trims to `[]`, gcd = primary): cofactors `([1], [])`.  Euclidean
step: transport the inductive pair for `(secondary, remainder)` through `rbzComboRewrite`. -/
theorem rbzBezoutInvariant :
    ∀ (fuel : Nat) (primary secondary : List QnfRat),
      ∃ cofactorLeft cofactorRight,
        rpxTrim (rpxAdd (rpxMul cofactorLeft primary) (rpxMul cofactorRight secondary))
          = rpxTrim (rpxGcd fuel primary secondary)
  | 0, primary, secondary =>
      ⟨[qnfOne], [], by
        show rpxTrim (rpxAdd (rpxMul [qnfOne] primary) []) = rpxTrim primary
        rw [rpeAddNilRight]
        exact rpeMulOneLeftTrim primary⟩
  | fuel + 1, primary, secondary => by
      dsimp only [rpxGcd]
      cases hSecondaryTrim : rpxTrim secondary with
      | nil =>
          exact ⟨[qnfOne], [], by
            show rpxTrim (rpxAdd (rpxMul [qnfOne] primary) []) = rpxTrim primary
            rw [rpeAddNilRight]
            exact rpeMulOneLeftTrim primary⟩
      | cons trimHead trimTail =>
          obtain ⟨cofactorU, cofactorV, ihEq⟩ :=
            rbzBezoutInvariant fuel secondary (rpxRemainder fuel secondary primary)
          refine ⟨cofactorV,
            rpxSub cofactorU (rpxMul cofactorV (rpxDivMod fuel secondary primary).1), ?_⟩
          have recon : rpxTrim (rpxAdd (rpxMul (rpxDivMod fuel secondary primary).1 secondary)
              (rpxRemainder fuel secondary primary)) = rpxTrim primary :=
            rpeDivModReconstructsTrim fuel secondary primary
          exact (rbzComboRewrite primary secondary (rpxDivMod fuel secondary primary).1
              (rpxRemainder fuel secondary primary) cofactorU cofactorV recon).trans ihEq

/-- **THE BEZOUT IDENTITY over ℚ[x]** at any fuel — packaged from `rbzBezoutInvariant`.  Supersedes the
committed owner-false `rpeHasBezoutIdentity`. -/
theorem rbzBezoutIdentity (fuel : Nat) (primary secondary : List QnfRat) :
    ∃ cofactorLeft cofactorRight,
      rpxTrim (rpxAdd (rpxMul cofactorLeft primary) (rpxMul cofactorRight secondary))
        = rpxTrim (rpxGcd fuel primary secondary) :=
  rbzBezoutInvariant fuel primary secondary

/-! ## T3 — the Smith normal form pivot-clear seed -/

/-- The ℚ[x]-matrix carrier: rows of entries, each entry an ascending `QnfRat` coefficient list. -/
def rbzPolyMatrix : Type := List (List (List QnfRat))

/-- Read row `rowIndex` (the empty row past the end). -/
def rbzRowGet : List (List (List QnfRat)) → Nat → List (List QnfRat)
  | [], _ => []
  | row :: _, 0 => row
  | _ :: restRows, position + 1 => rbzRowGet restRows position

/-- Read entry `colIndex` of a row (the zero polynomial `[]` past the end). -/
def rbzEntryGet : List (List QnfRat) → Nat → List QnfRat
  | [], _ => []
  | entry :: _, 0 => entry
  | _ :: restEntries, position + 1 => rbzEntryGet restEntries position

/-- Read entry `(rowIndex, colIndex)` of a ℚ[x]-matrix; out-of-range reads the zero polynomial. -/
def rbzMatrixEntry (matrix : List (List (List QnfRat))) (rowIndex colIndex : Nat) : List QnfRat :=
  rbzEntryGet (rbzRowGet matrix rowIndex) colIndex

/-- Clear one entry against a pivot: the Euclidean-division residue `entry mod pivot` (the second component
of `rpxDivMod`).  This is the elementary column/row operation `entry ↦ entry − quotient·pivot`. -/
def rbzClearEntry (fuel : Nat) (pivot entry : List QnfRat) : List QnfRat :=
  (rpxDivMod fuel pivot entry).2

/-- Clear a whole column against a pivot — the map of `rbzClearEntry` over the column's entries. -/
def rbzColumnClear (fuel : Nat) (pivot : List QnfRat) : List (List QnfRat) → List (List QnfRat)
  | [] => []
  | entry :: restEntries => rbzClearEntry fuel pivot entry :: rbzColumnClear fuel pivot restEntries

/-- **THE FIRST PIVOT LEMMA.**  Clearing `entry` against a nonzero `pivot` (at the adequate fuel
`entry.length`) yields a residue that either annihilates (`rpxTrim = []`) or has degree strictly below the
pivot's — the Euclidean degree drop that makes Smith reduction terminate.  Directly the committed
`rpdDivModRemainderDegree`. -/
theorem rbzClearEntryReducesDegree (pivot entry : List QnfRat) (pivotNonzero : rpxTrim pivot ≠ []) :
    rpxTrim (rbzClearEntry entry.length pivot entry) = []
      ∨ rpxDegree (rbzClearEntry entry.length pivot entry) < rpxDegree pivot :=
  rpdDivModRemainderDegree pivot entry pivotNonzero

/-- **The clear is a legitimate elementary operation.**  `rpxTrim (quotient·pivot + cleared) = rpxTrim entry`
— the cleared entry differs from the original by a `pivot`-multiple, so column/row-clearing preserves the
lattice generated by the matrix.  Directly the committed aggregate reconstruction. -/
theorem rbzClearEntryReconstructs (fuel : Nat) (pivot entry : List QnfRat) :
    rpxTrim (rpxAdd (rpxMul (rpxDivMod fuel pivot entry).1 pivot) (rbzClearEntry fuel pivot entry))
      = rpxTrim entry :=
  rpeDivModReconstructsTrim fuel pivot entry

/-! ## Groundings (fires)

Closed-value kernel pins; the convolution / division / gcd pipeline reduces to canonical `QnfRat` normal
forms, so commutativity, the explicit-cofactor Bezout, and the pivot-clear hold by `rfl` at small instances,
and the general theorems fire at the difference-of-squares pair. -/

set_option maxRecDepth 8192

/-- Fire (convolution symmetry, closed value): `(1 + 2x)·(3 + x)` trims equal to `(3 + x)·(1 + 2x)`. -/
theorem rbzFireMulCommTrimClosed :
    rpxTrim (rpxMul [qnfOfInt 1, qnfOfInt 2] [qnfOfInt 3, qnfOfInt 1])
      = rpxTrim (rpxMul [qnfOfInt 3, qnfOfInt 1] [qnfOfInt 1, qnfOfInt 2]) := rfl

/-- Fire (the general commutativity theorem, instantiated): `(2 + 3x)·(1 + x)` trims equal to
`(1 + x)·(2 + 3x)`. -/
theorem rbzFireMulCommTrimTheorem :
    rpxTrim (rpxMul [qnfOfInt 2, qnfOfInt 3] [qnfOfInt 1, qnfOfInt 1])
      = rpxTrim (rpxMul [qnfOfInt 1, qnfOfInt 1] [qnfOfInt 2, qnfOfInt 3]) :=
  rbzMulCommTrim [qnfOfInt 2, qnfOfInt 3] [qnfOfInt 1, qnfOfInt 1]

/-- Fire (Bezout with explicit cofactors, closed value): `0·(x² − 1) + 1·(x − 1)` trims to `x − 1`, the gcd
of `x² − 1` and `x − 1` — the cofactor pair `([], [1])` pinned by `rfl`. -/
theorem rbzFireBezoutExplicitCofactors :
    rpxTrim (rpxAdd (rpxMul ([] : List QnfRat) [qnfOfInt (-1), qnfOfInt 0, qnfOfInt 1])
        (rpxMul [qnfOne] [qnfOfInt (-1), qnfOfInt 1]))
      = rpxTrim (rpxGcd 5 [qnfOfInt (-1), qnfOfInt 0, qnfOfInt 1] [qnfOfInt (-1), qnfOfInt 1]) := rfl

/-- Fire (the general Bezout theorem, instantiated): the recursion produces a cofactor pair for `(x² − 1,
x − 1)` whose combination trims to their gcd. -/
theorem rbzFireBezoutIdentityDifferenceOfSquares :
    ∃ cofactorLeft cofactorRight,
      rpxTrim (rpxAdd (rpxMul cofactorLeft [qnfOfInt (-1), qnfOfInt 0, qnfOfInt 1])
          (rpxMul cofactorRight [qnfOfInt (-1), qnfOfInt 1]))
        = rpxTrim (rpxGcd 5 [qnfOfInt (-1), qnfOfInt 0, qnfOfInt 1] [qnfOfInt (-1), qnfOfInt 1]) :=
  rbzBezoutIdentity 5 [qnfOfInt (-1), qnfOfInt 0, qnfOfInt 1] [qnfOfInt (-1), qnfOfInt 1]

/-- Fire (divisibility transitivity, instantiated): `x − 1` divides `x² − 1` via the chain `(x − 1) | (x² − 1)`
(exact division) and `(x² − 1) | (x² − 1)` (reflexivity). -/
theorem rbzFireDividesTrans :
    rpeDivides [qnfOfInt (-1), qnfOfInt 1] [qnfOfInt (-1), qnfOfInt 0, qnfOfInt 1] :=
  rbzDividesTrans [qnfOfInt (-1), qnfOfInt 1] [qnfOfInt (-1), qnfOfInt 0, qnfOfInt 1]
    [qnfOfInt (-1), qnfOfInt 0, qnfOfInt 1]
    (rpeExactDivisionGivesDivides 3 [qnfOfInt (-1), qnfOfInt 1]
      [qnfOfInt (-1), qnfOfInt 0, qnfOfInt 1] rfl)
    (rpeDividesRefl [qnfOfInt (-1), qnfOfInt 0, qnfOfInt 1])

/-- Fire (first pivot lemma, instantiated): clearing `x² + 1` against the pivot `x − 1` reduces the degree or
annihilates — here the residue is the constant `2`, degree `0 < 1`. -/
theorem rbzFireClearEntryReducesDegree :
    rpxTrim (rbzClearEntry [qnfOfInt 1, qnfOfInt 0, qnfOfInt 1].length
        [qnfOfInt (-1), qnfOfInt 1] [qnfOfInt 1, qnfOfInt 0, qnfOfInt 1]) = []
      ∨ rpxDegree (rbzClearEntry [qnfOfInt 1, qnfOfInt 0, qnfOfInt 1].length
          [qnfOfInt (-1), qnfOfInt 1] [qnfOfInt 1, qnfOfInt 0, qnfOfInt 1])
          < rpxDegree [qnfOfInt (-1), qnfOfInt 1] :=
  rbzClearEntryReducesDegree [qnfOfInt (-1), qnfOfInt 1] [qnfOfInt 1, qnfOfInt 0, qnfOfInt 1]
    rpdFireLinearFactorNonzero

/-- Fire (column clear, closed value): clearing the column `[x² − 1, x² + 1]` against the pivot `x − 1`
annihilates the first entry (`x − 1` divides `x² − 1` exactly). -/
theorem rbzFireColumnClearAnnihilatesFirst :
    rpxTrim (rbzEntryGet (rbzColumnClear 3 [qnfOfInt (-1), qnfOfInt 1]
        [[qnfOfInt (-1), qnfOfInt 0, qnfOfInt 1], [qnfOfInt 1, qnfOfInt 0, qnfOfInt 1]]) 0) = [] := rfl

/-- Fire (matrix entry accessor, closed value): entry `(1, 0)` of the 2×1 matrix `[[x²], [3]]` is `3`. -/
theorem rbzFireMatrixEntry :
    rbzMatrixEntry [[[qnfOfInt 0, qnfOfInt 0, qnfOfInt 1]], [[qnfOfInt 3]]] 1 0 = [qnfOfInt 3] := rfl

/-- Fire (clear reconstruction, instantiated): clearing `x² − 1` against `x − 1` reconstructs `x² − 1` as
`quotient·(x − 1) + cleared`. -/
theorem rbzFireClearReconstructs :
    rpxTrim (rpxAdd (rpxMul (rpxDivMod 3 [qnfOfInt (-1), qnfOfInt 1]
          [qnfOfInt (-1), qnfOfInt 0, qnfOfInt 1]).1 [qnfOfInt (-1), qnfOfInt 1])
        (rbzClearEntry 3 [qnfOfInt (-1), qnfOfInt 1] [qnfOfInt (-1), qnfOfInt 0, qnfOfInt 1]))
      = rpxTrim [qnfOfInt (-1), qnfOfInt 0, qnfOfInt 1] :=
  rbzClearEntryReconstructs 3 [qnfOfInt (-1), qnfOfInt 1] [qnfOfInt (-1), qnfOfInt 0, qnfOfInt 1]

/-! ## Content marker -/

/-- The Bezout identity over ℚ[x] is decided. `rbzMulCommTrim` proves trim-level `rpxMul` commutativity
(convolution symmetry via the right-cons coefficient decomposition `rbzMulRightConsCoeff` and the coefficient
bridge), yielding left-trim-congruence (`rbzMulRespectsTrimLeft`) and divisibility transitivity
(`rbzDividesTrans`). `rbzBezoutIdentity` then gives `∃ u v, rpxTrim (u·p + v·q) = rpxTrim (rpxGcd fuel p q)` at
every fuel via the extended-Euclidean recursion `rbzBezoutInvariant` with the step rewrite `rbzComboRewrite`.
The Smith pivot-clear seed also ships: the ℚ[x]-matrix carrier `rbzPolyMatrix` with accessors,
`rbzClearEntry`/`rbzColumnClear`, the first pivot lemma `rbzClearEntryReducesDegree`, and the elementary-op
reconstruction `rbzClearEntryReconstructs`. The full Smith normal form remains walled (`rsiHasSmithNormalForm`). -/
def rbzHasBezoutIdentity : Bool := true

end FX1Poly.ComputerAlgebra
