import FX1Poly.ComputerAlgebra.Decision.GroebnerMembership

/-! # FX1Poly/ComputerAlgebra/Decision/RigTypeIsomorphism — the free-rig
    type-isomorphism word problem.

A `RigType` is a formal (+, ×, 0, 1)-expression over indexed base atoms.  Its
normal form is a multivariate polynomial with NATURAL-number coefficients over
the shared `GrbExp` sorted-monomial substrate: iso-classes of objects in the free
rig (bicartesian / commutative-semiring-free) category are exactly the elements of
`Nat[x_0, x_1, ...]` (Fiore–Leinster), so structural byte-equality of normal forms
IS the type-isomorphism decision for the finite (+, ×, 0, 1)-fragment.

The coefficient carrier is `Nat`, a SEMIRING (no negation), so the vanishing-sum
cancel branch of the rational `grqTermInsert` never fires — `natTermInsert` is a
strictly-simpler three-way canonical merge.

Reuses VERBATIM the coefficient-agnostic `GrbExp` monomial kit from
`GroebnerMembership` (`grbExpBeq`, `grbExpBeqEq`, `grbExpInsert`, `grbExpMul`,
`grbMonoLess` and its order laws).  Mirrors the QnfRat sorted-term-list idiom of
`GroebnerRationalMembership` over `Nat`.

The exponential / function-type `(+, ×, ^)` extension is the honest ceiling: the
equational theory of the high-school identities is not finitely axiomatisable
(Wilkie/Tarski), so no finite `RigIso^pow` presentation is complete — walled below
as `rtiHasExponentialTypeIsoCompleteness`.  The multiplicative-congruence soundness
(distributivity / ×-commutativity / ×-associativity through the normal form) is
walled as `rtiHasMultiplicativeSoundness` (obstruction: the substrate carries no
monomial-multiplication commutativity/associativity law and no scale-through-merge
coefficient-convolution lemma); the DECISION nonetheless computes multiplicative
isomorphisms correctly (see the ground fires). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FX1Poly.ComputerAlgebra

/-! ## Clean Nat scalar kit (propext-free; `Nat.mul_assoc` / `Nat.add_mul` leak) -/

/-- Right-distributivity of Nat multiplication over addition, propext-free
(the library `Nat.add_mul` leaks propext; derived here via the clean
`Nat.mul_add` and `Nat.mul_comm`). -/
theorem natAddMulClean (leftValue middleValue rightValue : Nat) :
    (leftValue + middleValue) * rightValue =
      leftValue * rightValue + middleValue * rightValue := by
  rw [Nat.mul_comm (leftValue + middleValue) rightValue, Nat.mul_add,
    Nat.mul_comm rightValue leftValue, Nat.mul_comm rightValue middleValue]

/-- Left-swap of a nested Nat sum: `a + (b + c) = b + (a + c)`. -/
theorem natAddSwapLeft (leftValue middleValue rightValue : Nat) :
    leftValue + (middleValue + rightValue) = middleValue + (leftValue + rightValue) := by
  rw [← Nat.add_assoc, Nat.add_comm leftValue middleValue, Nat.add_assoc]

/-- Adding a nonzero-left Nat sum stays nonzero (positivity through the merge). -/
theorem natAddPosLeftIsNonzero (coefficient other : Nat)
    (hNonzero : Nat.beq coefficient 0 = false) : Nat.beq (coefficient + other) 0 = false := by
  cases coefficient with
  | zero => exact Bool.noConfusion hNonzero
  | succ predecessor => cases other with
    | zero => rfl
    | succ otherPredecessor => rfl

/-- A conditional whose both arms are `0` is `0`. -/
theorem natCondZeroBothArms (flag : Bool) : cond flag 0 0 = 0 := by
  cases flag with
  | false => rfl
  | true => rfl

/-! ## Terms and polynomials over Nat: sorted coefficient-carrying lists -/

/-- One polynomial term: a natural-number coefficient on an exponent vector. -/
structure NatTerm where
  coefficient : Nat
  exponentVector : GrbExp

/-- Structural Boolean equality on terms. -/
def natTermBeq (leftTerm rightTerm : NatTerm) : Bool :=
  Nat.beq leftTerm.coefficient rightTerm.coefficient &&
    grbExpBeq leftTerm.exponentVector rightTerm.exponentVector

/-- Reflexivity of `natTermBeq`. -/
theorem natTermBeqRefl (term : NatTerm) : natTermBeq term term = true := by
  show (Nat.beq term.coefficient term.coefficient &&
    grbExpBeq term.exponentVector term.exponentVector) = true
  rw [grbNatBeqRefl term.coefficient, grbExpBeqRefl term.exponentVector]
  rfl

/-- `natTermBeq` sound: beq-true terms are equal. -/
theorem natTermBeqEq : (leftTerm rightTerm : NatTerm) →
    natTermBeq leftTerm rightTerm = true → leftTerm = rightTerm
  | NatTerm.mk leftCoefficient leftExponent, NatTerm.mk rightCoefficient rightExponent,
      hBeq => by
      have hSplit := grbBoolAndElim _ _ hBeq
      rw [grbNatBeqEq leftCoefficient rightCoefficient hSplit.left,
        grbExpBeqEq leftExponent rightExponent hSplit.right]

/-- A polynomial: terms sorted strictly descending under `grbMonoLess` with all
stored coefficients nonzero — maintained by `natTermInsert`, certified by
`NatPolyCanonical`. -/
abbrev NatPoly := List NatTerm

/-- Structural Boolean equality on polynomials. -/
def natPolyBeq : NatPoly → NatPoly → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | leftHead :: leftRest, rightHead :: rightRest =>
      natTermBeq leftHead rightHead && natPolyBeq leftRest rightRest

/-- Reflexivity of `natPolyBeq`. -/
theorem natPolyBeqRefl : (poly : NatPoly) → natPolyBeq poly poly = true
  | [] => rfl
  | head :: rest => by
      show (natTermBeq head head && natPolyBeq rest rest) = true
      rw [natTermBeqRefl head, natPolyBeqRefl rest]
      rfl

/-- `natPolyBeq` sound: beq-true polynomials are equal. -/
theorem natPolyBeqEq : (leftPoly rightPoly : NatPoly) →
    natPolyBeq leftPoly rightPoly = true → leftPoly = rightPoly
  | [], [], _ => rfl
  | [], _ :: _, hBeq => Bool.noConfusion hBeq
  | _ :: _, [], hBeq => Bool.noConfusion hBeq
  | leftHead :: leftRest, rightHead :: rightRest, hBeq => by
      have hSplit := grbBoolAndElim _ _ hBeq
      rw [natTermBeqEq leftHead rightHead hSplit.left,
        natPolyBeqEq leftRest rightRest hSplit.right]

/-- The zero polynomial. -/
def natZeroPoly : NatPoly := []

/-- The constant-one polynomial. -/
def natOnePoly : NatPoly := [{ coefficient := 1, exponentVector := [] }]

/-- The degree-one monic polynomial in a single variable. -/
def natVariablePoly (index : Nat) : NatPoly :=
  [{ coefficient := 1,
     exponentVector := [{ variableIndex := index, exponent := 1 }] }]

/-! ## Term insertion: the three-way canonical merge (no cancel arm over Nat) -/

/-- Insert a coefficient-carrying term: a zero coefficient is a no-op; a collision
ADDS coefficients (over Nat the sum of nonzeros never vanishes, so there is no
cancel branch); otherwise place by the descending monomial order. -/
def natTermInsert (coefficient : Nat) (exponent : GrbExp) : NatPoly → NatPoly
  | [] =>
      cond (Nat.beq coefficient 0) []
        [{ coefficient := coefficient, exponentVector := exponent }]
  | head :: rest =>
      cond (Nat.beq coefficient 0)
        (head :: rest)
        (cond (grbExpBeq exponent head.exponentVector)
          ({ coefficient := coefficient + head.coefficient,
             exponentVector := head.exponentVector } :: rest)
          (cond (grbMonoLess head.exponentVector exponent)
            ({ coefficient := coefficient, exponentVector := exponent } :: head :: rest)
            (head :: natTermInsert coefficient exponent rest)))

/-- `natTermInsert` branch: zero coefficient into nil — no-op. -/
theorem natTermInsertNilOnZero (coefficient : Nat) (exponent : GrbExp)
    (hZero : Nat.beq coefficient 0 = true) : natTermInsert coefficient exponent [] = [] := by
  show cond (Nat.beq coefficient 0) []
      ([{ coefficient := coefficient, exponentVector := exponent }] : NatPoly) = []
  rw [hZero]; rfl

/-- `natTermInsert` branch: nonzero coefficient into nil — singleton. -/
theorem natTermInsertNilOnNonzero (coefficient : Nat) (exponent : GrbExp)
    (hZero : Nat.beq coefficient 0 = false) :
    natTermInsert coefficient exponent [] =
      [{ coefficient := coefficient, exponentVector := exponent }] := by
  show cond (Nat.beq coefficient 0) []
      ([{ coefficient := coefficient, exponentVector := exponent }] : NatPoly) =
    [{ coefficient := coefficient, exponentVector := exponent }]
  rw [hZero]; rfl

/-- `natTermInsert` branch: zero coefficient into cons — no-op. -/
theorem natTermInsertOnZero (coefficient : Nat) (exponent : GrbExp)
    (head : NatTerm) (rest : NatPoly) (hZero : Nat.beq coefficient 0 = true) :
    natTermInsert coefficient exponent (head :: rest) = head :: rest := by
  show cond (Nat.beq coefficient 0) (head :: rest) _ = head :: rest
  rw [hZero]; rfl

/-- `natTermInsert` branch: collision on a shared monomial — coefficients merge. -/
theorem natTermInsertOnCollisionMerge (coefficient : Nat) (exponent : GrbExp)
    (head : NatTerm) (rest : NatPoly) (hZero : Nat.beq coefficient 0 = false)
    (hShared : grbExpBeq exponent head.exponentVector = true) :
    natTermInsert coefficient exponent (head :: rest) =
      { coefficient := coefficient + head.coefficient,
        exponentVector := head.exponentVector } :: rest := by
  show cond (Nat.beq coefficient 0) (head :: rest)
      (cond (grbExpBeq exponent head.exponentVector)
        ({ coefficient := coefficient + head.coefficient,
           exponentVector := head.exponentVector } :: rest) _) = _
  rw [hZero, hShared]; rfl

/-- `natTermInsert` branch: the head dominates — prepend the new term. -/
theorem natTermInsertOnGreater (coefficient : Nat) (exponent : GrbExp)
    (head : NatTerm) (rest : NatPoly) (hZero : Nat.beq coefficient 0 = false)
    (hShared : grbExpBeq exponent head.exponentVector = false)
    (hLess : grbMonoLess head.exponentVector exponent = true) :
    natTermInsert coefficient exponent (head :: rest) =
      { coefficient := coefficient, exponentVector := exponent } :: head :: rest := by
  show cond (Nat.beq coefficient 0) (head :: rest)
      (cond (grbExpBeq exponent head.exponentVector) _
        (cond (grbMonoLess head.exponentVector exponent)
          ({ coefficient := coefficient, exponentVector := exponent } :: head :: rest) _)) = _
  rw [hZero, hShared, hLess]; rfl

/-- `natTermInsert` branch: the new term dominates — descend. -/
theorem natTermInsertOnSmaller (coefficient : Nat) (exponent : GrbExp)
    (head : NatTerm) (rest : NatPoly) (hZero : Nat.beq coefficient 0 = false)
    (hShared : grbExpBeq exponent head.exponentVector = false)
    (hLess : grbMonoLess head.exponentVector exponent = false) :
    natTermInsert coefficient exponent (head :: rest) =
      head :: natTermInsert coefficient exponent rest := by
  show cond (Nat.beq coefficient 0) (head :: rest)
      (cond (grbExpBeq exponent head.exponentVector) _
        (cond (grbMonoLess head.exponentVector exponent) _
          (head :: natTermInsert coefficient exponent rest))) = _
  rw [hZero, hShared, hLess]; rfl

/-! ## Addition, single-term scaling, multiplication -/

/-- Polynomial addition: fold the left terms into the right through `natTermInsert`. -/
def natAdd : NatPoly → NatPoly → NatPoly
  | [], right => right
  | term :: rest, right =>
      natTermInsert term.coefficient term.exponentVector (natAdd rest right)

/-- Multiply every term by a fixed coefficient and monomial (no re-sorting;
consumers fold the result through `natAdd`). -/
def natScaleTerm (scalar : Nat) (monomial : GrbExp) : NatPoly → NatPoly
  | [] => []
  | term :: rest =>
      { coefficient := scalar * term.coefficient,
        exponentVector := grbExpMul monomial term.exponentVector } ::
        natScaleTerm scalar monomial rest

/-- Polynomial multiplication: distribute `natScaleTerm` over `natAdd`. -/
def natMul : NatPoly → NatPoly → NatPoly
  | [], [] => []
  | [], _ :: _ => []
  | term :: rest, right =>
      natAdd (natScaleTerm term.coefficient term.exponentVector right) (natMul rest right)

/-- `natMul [] right = []` for every right operand. -/
theorem natMulNilLeft : (right : NatPoly) → natMul [] right = []
  | [] => rfl
  | _ :: _ => rfl

/-- `natScaleTerm scalar monomial [] = []`. -/
theorem natScaleTermNil (scalar : Nat) (monomial : GrbExp) :
    natScaleTerm scalar monomial [] = [] := rfl

/-- `natMul left [] = []` for every left operand. -/
theorem natMulNilRight : (left : NatPoly) → natMul left [] = []
  | [] => rfl
  | term :: rest => by
      show natAdd (natScaleTerm term.coefficient term.exponentVector []) (natMul rest []) = []
      rw [natScaleTermNil term.coefficient term.exponentVector, natMulNilRight rest]
      rfl

/-! ## Canonicity: strict descent plus nonzero coefficients -/

/-- The canonical-form invariant: exponent vectors strictly descending under
`grbMonoLess` AND every stored coefficient nonzero. -/
inductive NatPolyCanonical : NatPoly → Prop where
  | nilIsCanonical : NatPolyCanonical []
  | singleIsCanonical (term : NatTerm)
      (isNonzero : Nat.beq term.coefficient 0 = false) :
      NatPolyCanonical [term]
  | consIsCanonical (first second : NatTerm) (rest : NatPoly)
      (isNonzero : Nat.beq first.coefficient 0 = false)
      (isDescending : grbMonoLess second.exponentVector first.exponentVector = true)
      (tailIsCanonical : NatPolyCanonical (second :: rest)) :
      NatPolyCanonical (first :: second :: rest)

/-- The head coefficient of a canonical list is nonzero. -/
theorem natCanonicalHeadNonzero (head : NatTerm) (rest : NatPoly)
    (hCanonical : NatPolyCanonical (head :: rest)) :
    Nat.beq head.coefficient 0 = false := by
  cases hCanonical with
  | singleIsCanonical _ isNonzero => exact isNonzero
  | consIsCanonical _ _ _ isNonzero _ _ => exact isNonzero

/-- The tail of a canonical list is canonical. -/
theorem natCanonicalTail (head : NatTerm) (rest : NatPoly)
    (hCanonical : NatPolyCanonical (head :: rest)) : NatPolyCanonical rest := by
  cases hCanonical with
  | singleIsCanonical _ _ => exact NatPolyCanonical.nilIsCanonical
  | consIsCanonical _ _ _ _ _ tailIsCanonical => exact tailIsCanonical

/-- Dropping the second element of a canonical list keeps it canonical. -/
theorem natCanonicalSkip (first second : NatTerm) (rest : NatPoly)
    (hCanonical : NatPolyCanonical (first :: second :: rest)) :
    NatPolyCanonical (first :: rest) := by
  cases hCanonical with
  | consIsCanonical _ _ _ isNonzero isDescending tailIsCanonical =>
      cases tailIsCanonical with
      | singleIsCanonical _ _ =>
          exact NatPolyCanonical.singleIsCanonical first isNonzero
      | consIsCanonical _ _ _ _ isDescendingTail tailTailIsCanonical =>
          exact NatPolyCanonical.consIsCanonical _ _ _ isNonzero
            (grbMonoLessTrans _ _ _ isDescendingTail isDescending) tailTailIsCanonical

/-- Replacing the head coefficient (same exponent vector) by any nonzero
coefficient keeps a canonical list canonical — the collision-merge shape. -/
theorem natCanonicalReplaceHeadCoefficient (newCoefficient : Nat)
    (head : NatTerm) (rest : NatPoly) (isNonzero : Nat.beq newCoefficient 0 = false)
    (hCanonical : NatPolyCanonical (head :: rest)) :
    NatPolyCanonical
      ({ coefficient := newCoefficient, exponentVector := head.exponentVector } :: rest) := by
  cases hCanonical with
  | singleIsCanonical _ _ =>
      exact NatPolyCanonical.singleIsCanonical _ isNonzero
  | consIsCanonical _ second tailRest _ isDescending tailIsCanonical =>
      exact NatPolyCanonical.consIsCanonical _ second tailRest isNonzero
        isDescending tailIsCanonical

/-- Inserting a term strictly below a dominating head keeps the list canonical. -/
theorem natTermInsertUnderHead : (rest : NatPoly) → (head : NatTerm) →
    (coefficient : Nat) → (exponent : GrbExp) →
    grbMonoLess exponent head.exponentVector = true →
    NatPolyCanonical (head :: rest) →
    NatPolyCanonical (head :: natTermInsert coefficient exponent rest)
  | [], head, coefficient, exponent, hUnderHead, hCanonical => by
      cases hZero : Nat.beq coefficient 0 with
      | true =>
          rw [natTermInsertNilOnZero coefficient exponent hZero]
          exact hCanonical
      | false =>
          rw [natTermInsertNilOnNonzero coefficient exponent hZero]
          exact NatPolyCanonical.consIsCanonical head _ []
            (natCanonicalHeadNonzero head [] hCanonical) hUnderHead
            (NatPolyCanonical.singleIsCanonical _ hZero)
  | second :: rest2, head, coefficient, exponent, hUnderHead, hCanonical => by
      cases hCanonical with
      | consIsCanonical _ _ _ hHeadNonzero hSecondLess hTailCanonical =>
          cases hZero : Nat.beq coefficient 0 with
          | true =>
              rw [natTermInsertOnZero coefficient exponent second rest2 hZero]
              exact NatPolyCanonical.consIsCanonical head second rest2 hHeadNonzero
                hSecondLess hTailCanonical
          | false =>
              cases hShared : grbExpBeq exponent second.exponentVector with
              | true =>
                  rw [natTermInsertOnCollisionMerge coefficient exponent second rest2
                    hZero hShared]
                  exact NatPolyCanonical.consIsCanonical head _ rest2 hHeadNonzero
                    hSecondLess
                    (natCanonicalReplaceHeadCoefficient _ second rest2
                      (natAddPosLeftIsNonzero coefficient second.coefficient hZero)
                      hTailCanonical)
              | false =>
                  cases hLess : grbMonoLess second.exponentVector exponent with
                  | true =>
                      rw [natTermInsertOnGreater coefficient exponent second rest2
                        hZero hShared hLess]
                      exact NatPolyCanonical.consIsCanonical head _ _ hHeadNonzero
                        hUnderHead
                        (NatPolyCanonical.consIsCanonical _ second rest2 hZero hLess
                          hTailCanonical)
                  | false =>
                      have hUnderSecond : grbMonoLess exponent second.exponentVector = true := by
                        cases grbMonoLessTotal exponent second.exponentVector hShared with
                        | inl hForward => exact hForward
                        | inr hBackward => exact Bool.noConfusion (hLess.symm.trans hBackward)
                      rw [natTermInsertOnSmaller coefficient exponent second rest2
                        hZero hShared hLess]
                      exact NatPolyCanonical.consIsCanonical head second _ hHeadNonzero
                        hSecondLess
                        (natTermInsertUnderHead rest2 second coefficient exponent
                          hUnderSecond hTailCanonical)

/-- `natTermInsert` preserves canonicity — for ANY inserted coefficient. -/
theorem natTermInsertKeepsCanonical (coefficient : Nat) (exponent : GrbExp) :
    (poly : NatPoly) → NatPolyCanonical poly →
    NatPolyCanonical (natTermInsert coefficient exponent poly)
  | [], _ => by
      cases hZero : Nat.beq coefficient 0 with
      | true =>
          rw [natTermInsertNilOnZero coefficient exponent hZero]
          exact NatPolyCanonical.nilIsCanonical
      | false =>
          rw [natTermInsertNilOnNonzero coefficient exponent hZero]
          exact NatPolyCanonical.singleIsCanonical _ hZero
  | head :: rest, hCanonical => by
      cases hZero : Nat.beq coefficient 0 with
      | true =>
          rw [natTermInsertOnZero coefficient exponent head rest hZero]
          exact hCanonical
      | false =>
          cases hShared : grbExpBeq exponent head.exponentVector with
          | true =>
              rw [natTermInsertOnCollisionMerge coefficient exponent head rest hZero hShared]
              exact natCanonicalReplaceHeadCoefficient _ head rest
                (natAddPosLeftIsNonzero coefficient head.coefficient hZero) hCanonical
          | false =>
              cases hLess : grbMonoLess head.exponentVector exponent with
              | true =>
                  rw [natTermInsertOnGreater coefficient exponent head rest hZero hShared hLess]
                  exact NatPolyCanonical.consIsCanonical _ head rest hZero hLess hCanonical
              | false =>
                  have hUnderHead : grbMonoLess exponent head.exponentVector = true := by
                    cases grbMonoLessTotal exponent head.exponentVector hShared with
                    | inl hForward => exact hForward
                    | inr hBackward => exact Bool.noConfusion (hLess.symm.trans hBackward)
                  rw [natTermInsertOnSmaller coefficient exponent head rest hZero hShared hLess]
                  exact natTermInsertUnderHead rest head coefficient exponent
                    hUnderHead hCanonical

/-- `natAdd left right` is canonical whenever `right` is — for ANY left operand. -/
theorem natAddKeepsCanonical : (leftPoly rightPoly : NatPoly) →
    NatPolyCanonical rightPoly → NatPolyCanonical (natAdd leftPoly rightPoly)
  | [], _, hRightCanonical => hRightCanonical
  | term :: rest, rightPoly, hRightCanonical =>
      natTermInsertKeepsCanonical term.coefficient term.exponentVector
        (natAdd rest rightPoly)
        (natAddKeepsCanonical rest rightPoly hRightCanonical)

/-- `natMul` output is unconditionally canonical. -/
theorem natMulIsCanonical : (leftPoly rightPoly : NatPoly) →
    NatPolyCanonical (natMul leftPoly rightPoly)
  | [], [] => NatPolyCanonical.nilIsCanonical
  | [], _ :: _ => NatPolyCanonical.nilIsCanonical
  | term :: rest, rightPoly =>
      natAddKeepsCanonical (natScaleTerm term.coefficient term.exponentVector rightPoly)
        (natMul rest rightPoly) (natMulIsCanonical rest rightPoly)

/-! ## The Nat coefficient scan and canonical-list extensionality -/

/-- The contribution of one term to the coefficient at a probe exponent. -/
def natTermCoeffAt (term : NatTerm) (probe : GrbExp) : Nat :=
  cond (grbExpBeq probe term.exponentVector) term.coefficient 0

/-- Nat coefficient of a probe exponent in a polynomial (additive scan). -/
def natCoeff : NatPoly → GrbExp → Nat
  | [], _ => 0
  | term :: rest, probe => natTermCoeffAt term probe + natCoeff rest probe

/-- Coefficient scan through a term insertion — on ARBITRARY lists. -/
theorem natCoeffTermInsert : (poly : NatPoly) → (coefficient : Nat) →
    (exponent probe : GrbExp) →
    natCoeff (natTermInsert coefficient exponent poly) probe =
      cond (grbExpBeq probe exponent) coefficient 0 + natCoeff poly probe
  | [], coefficient, exponent, probe => by
      cases hZero : Nat.beq coefficient 0 with
      | true =>
          rw [natTermInsertNilOnZero coefficient exponent hZero,
            grbNatBeqEq coefficient 0 hZero]
          show (0 : Nat) = cond (grbExpBeq probe exponent) 0 0 + 0
          rw [natCondZeroBothArms (grbExpBeq probe exponent)]
      | false =>
          rw [natTermInsertNilOnNonzero coefficient exponent hZero]
          show natTermCoeffAt { coefficient := coefficient, exponentVector := exponent } probe
              + 0 = cond (grbExpBeq probe exponent) coefficient 0 + 0
          rfl
  | head :: rest, coefficient, exponent, probe => by
      cases hZero : Nat.beq coefficient 0 with
      | true =>
          rw [natTermInsertOnZero coefficient exponent head rest hZero,
            grbNatBeqEq coefficient 0 hZero]
          show natCoeff (head :: rest) probe =
            cond (grbExpBeq probe exponent) 0 0 + natCoeff (head :: rest) probe
          rw [natCondZeroBothArms (grbExpBeq probe exponent), Nat.zero_add]
      | false =>
          cases hShared : grbExpBeq exponent head.exponentVector with
          | true =>
              have expEq := grbExpBeqEq exponent head.exponentVector hShared
              rw [natTermInsertOnCollisionMerge coefficient exponent head rest hZero hShared,
                expEq]
              show cond (grbExpBeq probe head.exponentVector)
                  (coefficient + head.coefficient) 0 + natCoeff rest probe =
                cond (grbExpBeq probe head.exponentVector) coefficient 0 +
                  (cond (grbExpBeq probe head.exponentVector) head.coefficient 0
                    + natCoeff rest probe)
              cases hProbe : grbExpBeq probe head.exponentVector with
              | true => exact Nat.add_assoc coefficient head.coefficient (natCoeff rest probe)
              | false =>
                  exact congrArg (fun value => 0 + value)
                    (Nat.zero_add (natCoeff rest probe)).symm
          | false =>
              cases hLess : grbMonoLess head.exponentVector exponent with
              | true =>
                  rw [natTermInsertOnGreater coefficient exponent head rest hZero hShared hLess]
                  rfl
              | false =>
                  rw [natTermInsertOnSmaller coefficient exponent head rest hZero hShared hLess]
                  show natTermCoeffAt head probe
                      + natCoeff (natTermInsert coefficient exponent rest) probe =
                    cond (grbExpBeq probe exponent) coefficient 0 +
                      (natTermCoeffAt head probe + natCoeff rest probe)
                  rw [natCoeffTermInsert rest coefficient exponent probe]
                  show natTermCoeffAt head probe
                      + (cond (grbExpBeq probe exponent) coefficient 0 + natCoeff rest probe) =
                    cond (grbExpBeq probe exponent) coefficient 0 +
                      (natTermCoeffAt head probe + natCoeff rest probe)
                  exact natAddSwapLeft (natTermCoeffAt head probe)
                    (cond (grbExpBeq probe exponent) coefficient 0) (natCoeff rest probe)

/-- The coefficient scan is a `Nat.add` homomorphism through `natAdd`. -/
theorem natCoeffAdd : (leftPoly rightPoly : NatPoly) → (probe : GrbExp) →
    natCoeff (natAdd leftPoly rightPoly) probe =
      natCoeff leftPoly probe + natCoeff rightPoly probe
  | [], rightPoly, probe => (Nat.zero_add (natCoeff rightPoly probe)).symm
  | term :: rest, rightPoly, probe => by
      show natCoeff (natTermInsert term.coefficient term.exponentVector
        (natAdd rest rightPoly)) probe = _
      rw [natCoeffTermInsert (natAdd rest rightPoly) term.coefficient
        term.exponentVector probe, natCoeffAdd rest rightPoly probe]
      show cond (grbExpBeq probe term.exponentVector) term.coefficient 0 +
          (natCoeff rest probe + natCoeff rightPoly probe) =
        natTermCoeffAt term probe + natCoeff rest probe + natCoeff rightPoly probe
      exact (Nat.add_assoc
        (cond (grbExpBeq probe term.exponentVector) term.coefficient 0)
        (natCoeff rest probe) (natCoeff rightPoly probe)).symm

/-- In a canonical list, the tail scans to zero at the head's own exponent. -/
theorem natCoeffZeroUnderHead : (tail : NatPoly) → (head : NatTerm) →
    NatPolyCanonical (head :: tail) → natCoeff tail head.exponentVector = 0
  | [], _, _ => rfl
  | second :: rest, head, hCanonical => by
      cases hCanonical with
      | consIsCanonical _ _ _ hHeadNonzero hSecondLess hTailCanonical =>
          have hBeqFalse : grbExpBeq head.exponentVector second.exponentVector = false := by
            cases hBeqCheck : grbExpBeq head.exponentVector second.exponentVector with
            | false => rfl
            | true =>
                have expEq := grbExpBeqEq head.exponentVector second.exponentVector hBeqCheck
                rw [← expEq] at hSecondLess
                rw [grbMonoLessIrrefl head.exponentVector] at hSecondLess
                exact Bool.noConfusion hSecondLess
          show natTermCoeffAt second head.exponentVector + natCoeff rest head.exponentVector = 0
          show cond (grbExpBeq head.exponentVector second.exponentVector)
              second.coefficient 0 + natCoeff rest head.exponentVector = 0
          rw [hBeqFalse,
            natCoeffZeroUnderHead rest head
              (natCanonicalSkip head second rest
                (NatPolyCanonical.consIsCanonical head second rest hHeadNonzero
                  hSecondLess hTailCanonical))]
          rfl

/-- The scan of a canonical list at its own head exponent IS the head coefficient. -/
theorem natCoeffHeadIsCoefficient (head : NatTerm) (tail : NatPoly)
    (hCanonical : NatPolyCanonical (head :: tail)) :
    natCoeff (head :: tail) head.exponentVector = head.coefficient := by
  show natTermCoeffAt head head.exponentVector + natCoeff tail head.exponentVector
      = head.coefficient
  show cond (grbExpBeq head.exponentVector head.exponentVector)
      head.coefficient 0 + natCoeff tail head.exponentVector = head.coefficient
  rw [grbExpBeqRefl head.exponentVector, natCoeffZeroUnderHead tail head hCanonical]
  rfl

/-- A probe with nonzero coefficient in a canonical tail sits strictly below the head. -/
theorem natCoeffNonzeroImpliesLessThanHead : (tail : NatPoly) → (head : NatTerm) →
    (probe : GrbExp) → NatPolyCanonical (head :: tail) →
    (natCoeff tail probe = 0 → False) →
    grbMonoLess probe head.exponentVector = true
  | [], _, _, _, isNonzero => False.elim (isNonzero rfl)
  | second :: rest, head, probe, hCanonical, isNonzero => by
      cases hCanonical with
      | consIsCanonical _ _ _ hHeadNonzero hSecondLess hTailCanonical =>
          cases hProbe : grbExpBeq probe second.exponentVector with
          | true =>
              rw [grbExpBeqEq probe second.exponentVector hProbe]
              exact hSecondLess
          | false =>
              have tailNonzero : natCoeff rest probe = 0 → False := by
                intro tailZero
                apply isNonzero
                show natTermCoeffAt second probe + natCoeff rest probe = 0
                show cond (grbExpBeq probe second.exponentVector) second.coefficient 0
                    + natCoeff rest probe = 0
                rw [hProbe, tailZero]
                rfl
              exact grbMonoLessTrans probe second.exponentVector head.exponentVector
                (natCoeffNonzeroImpliesLessThanHead rest second probe hTailCanonical
                  tailNonzero)
                hSecondLess

/-- **Canonical-list extensionality**: canonical polynomials with pointwise-equal
coefficient functions are byte-equal lists — the T1 keystone. -/
theorem natPolyExtensionality : (leftPoly rightPoly : NatPoly) →
    NatPolyCanonical leftPoly → NatPolyCanonical rightPoly →
    ((probe : GrbExp) → natCoeff leftPoly probe = natCoeff rightPoly probe) →
    leftPoly = rightPoly
  | [], [], _, _, _ => rfl
  | [], headRight :: restRight, _, hRightCanonical, hPointwise => by
      exfalso
      have hZeroCoeff : headRight.coefficient = 0 :=
        (natCoeffHeadIsCoefficient headRight restRight hRightCanonical).symm.trans
          (hPointwise headRight.exponentVector).symm
      have hNonzeroFlag := natCanonicalHeadNonzero headRight restRight hRightCanonical
      rw [hZeroCoeff] at hNonzeroFlag
      exact Bool.noConfusion ((grbNatBeqRefl 0).symm.trans hNonzeroFlag)
  | headLeft :: restLeft, [], hLeftCanonical, _, hPointwise => by
      exfalso
      have hZeroCoeff : headLeft.coefficient = 0 :=
        (natCoeffHeadIsCoefficient headLeft restLeft hLeftCanonical).symm.trans
          (hPointwise headLeft.exponentVector)
      have hNonzeroFlag := natCanonicalHeadNonzero headLeft restLeft hLeftCanonical
      rw [hZeroCoeff] at hNonzeroFlag
      exact Bool.noConfusion ((grbNatBeqRefl 0).symm.trans hNonzeroFlag)
  | headLeft :: restLeft, headRight :: restRight, hLeftCanonical, hRightCanonical,
      hPointwise => by
      cases hHeads : grbExpBeq headLeft.exponentVector headRight.exponentVector with
      | true =>
          have headExpEq :=
            grbExpBeqEq headLeft.exponentVector headRight.exponentVector hHeads
          have hRightAtLeftExp : natCoeff (headRight :: restRight)
              headLeft.exponentVector = headRight.coefficient := by
            rw [headExpEq]
            exact natCoeffHeadIsCoefficient headRight restRight hRightCanonical
          have coeffEq : headLeft.coefficient = headRight.coefficient :=
            (natCoeffHeadIsCoefficient headLeft restLeft hLeftCanonical).symm.trans
              ((hPointwise headLeft.exponentVector).trans hRightAtLeftExp)
          have headEq : headLeft = headRight :=
            (congrArg (fun value => NatTerm.mk value headLeft.exponentVector) coeffEq).trans
              (congrArg (NatTerm.mk headRight.coefficient) headExpEq)
          have tailsAgree : (probe : GrbExp) →
              natCoeff restLeft probe = natCoeff restRight probe := by
            intro probe
            cases hProbeHead : grbExpBeq probe headLeft.exponentVector with
            | true =>
                rw [grbExpBeqEq probe headLeft.exponentVector hProbeHead,
                  natCoeffZeroUnderHead restLeft headLeft hLeftCanonical]
                have rightUnder : natCoeff restRight headLeft.exponentVector = 0 := by
                  rw [headExpEq]
                  exact natCoeffZeroUnderHead restRight headRight hRightCanonical
                exact rightUnder.symm
            | false =>
                have hProbeRight : grbExpBeq probe headRight.exponentVector = false := by
                  rw [← headExpEq]
                  exact hProbeHead
                have hPointAtExpanded :
                    natTermCoeffAt headLeft probe + natCoeff restLeft probe =
                      natTermCoeffAt headRight probe + natCoeff restRight probe :=
                  hPointwise probe
                show natCoeff restLeft probe = natCoeff restRight probe
                have hExpand :
                    cond (grbExpBeq probe headLeft.exponentVector) headLeft.coefficient 0
                        + natCoeff restLeft probe =
                      cond (grbExpBeq probe headRight.exponentVector) headRight.coefficient 0
                        + natCoeff restRight probe := hPointAtExpanded
                rw [hProbeHead, hProbeRight] at hExpand
                exact (Nat.zero_add (natCoeff restLeft probe)).symm.trans
                  (hExpand.trans (Nat.zero_add (natCoeff restRight probe)))
          rw [headEq]
          exact congrArg (List.cons headRight)
            (natPolyExtensionality restLeft restRight
              (natCanonicalTail headLeft restLeft hLeftCanonical)
              (natCanonicalTail headRight restRight hRightCanonical) tailsAgree)
      | false =>
          exfalso
          have hLeftCoeffFlag := natCanonicalHeadNonzero headLeft restLeft hLeftCanonical
          have hRightCoeffFlag :=
            natCanonicalHeadNonzero headRight restRight hRightCanonical
          have hPointLeft :
              natTermCoeffAt headRight headLeft.exponentVector
                + natCoeff restRight headLeft.exponentVector = headLeft.coefficient :=
            (hPointwise headLeft.exponentVector).symm.trans
              (natCoeffHeadIsCoefficient headLeft restLeft hLeftCanonical)
          have hPointLeftExpanded :
              cond (grbExpBeq headLeft.exponentVector headRight.exponentVector)
                  headRight.coefficient 0
                + natCoeff restRight headLeft.exponentVector = headLeft.coefficient :=
            hPointLeft
          rw [hHeads] at hPointLeftExpanded
          have hRightTailNonzero :
              natCoeff restRight headLeft.exponentVector = 0 → False := by
            intro isZero
            rw [isZero] at hPointLeftExpanded
            have hCollapse : (0 : Nat) = headLeft.coefficient :=
              (Nat.zero_add 0).symm.trans hPointLeftExpanded
            rw [← hCollapse] at hLeftCoeffFlag
            exact Bool.noConfusion ((grbNatBeqRefl 0).symm.trans hLeftCoeffFlag)
          have hLeftLessRight :
              grbMonoLess headLeft.exponentVector headRight.exponentVector = true :=
            natCoeffNonzeroImpliesLessThanHead restRight headRight
              headLeft.exponentVector hRightCanonical hRightTailNonzero
          have hHeadsSym :
              grbExpBeq headRight.exponentVector headLeft.exponentVector = false := by
            cases hBackward : grbExpBeq headRight.exponentVector headLeft.exponentVector with
            | false => rfl
            | true =>
                have backwardEq := grbExpBeqEq headRight.exponentVector
                  headLeft.exponentVector hBackward
                rw [backwardEq] at hHeads
                rw [grbExpBeqRefl headLeft.exponentVector] at hHeads
                exact Bool.noConfusion hHeads
          have hPointRight :
              natTermCoeffAt headLeft headRight.exponentVector
                + natCoeff restLeft headRight.exponentVector = headRight.coefficient :=
            (hPointwise headRight.exponentVector).trans
              (natCoeffHeadIsCoefficient headRight restRight hRightCanonical)
          have hPointRightExpanded :
              cond (grbExpBeq headRight.exponentVector headLeft.exponentVector)
                  headLeft.coefficient 0
                + natCoeff restLeft headRight.exponentVector = headRight.coefficient :=
            hPointRight
          rw [hHeadsSym] at hPointRightExpanded
          have hLeftTailNonzero :
              natCoeff restLeft headRight.exponentVector = 0 → False := by
            intro isZero
            rw [isZero] at hPointRightExpanded
            have hCollapse : (0 : Nat) = headRight.coefficient :=
              (Nat.zero_add 0).symm.trans hPointRightExpanded
            rw [← hCollapse] at hRightCoeffFlag
            exact Bool.noConfusion ((grbNatBeqRefl 0).symm.trans hRightCoeffFlag)
          have hRightLessLeft :
              grbMonoLess headRight.exponentVector headLeft.exponentVector = true :=
            natCoeffNonzeroImpliesLessThanHead restLeft headLeft
              headRight.exponentVector hLeftCanonical hLeftTailNonzero
          exact Bool.noConfusion
            ((grbMonoLessAsym headLeft.exponentVector headRight.exponentVector
              hLeftLessRight).symm.trans hRightLessLeft)

/-! ## The AC family used by rig-axiom soundness -/

/-- `natAdd poly [] = poly` on canonical input. -/
theorem natAddNilRightIsIdentity (poly : NatPoly) (hCanonical : NatPolyCanonical poly) :
    natAdd poly [] = poly :=
  natPolyExtensionality (natAdd poly []) poly
    (natAddKeepsCanonical poly [] NatPolyCanonical.nilIsCanonical) hCanonical
    (fun probe => by
      rw [natCoeffAdd poly [] probe]
      exact Nat.add_zero (natCoeff poly probe))

/-- Commutativity of `natAdd` on canonical operands. -/
theorem natAddComm (leftPoly rightPoly : NatPoly)
    (hLeftCanonical : NatPolyCanonical leftPoly) (hRightCanonical : NatPolyCanonical rightPoly) :
    natAdd leftPoly rightPoly = natAdd rightPoly leftPoly :=
  natPolyExtensionality (natAdd leftPoly rightPoly) (natAdd rightPoly leftPoly)
    (natAddKeepsCanonical leftPoly rightPoly hRightCanonical)
    (natAddKeepsCanonical rightPoly leftPoly hLeftCanonical)
    (fun probe => by
      rw [natCoeffAdd leftPoly rightPoly probe, natCoeffAdd rightPoly leftPoly probe]
      exact Nat.add_comm (natCoeff leftPoly probe) (natCoeff rightPoly probe))

/-- Associativity of `natAdd` (third operand canonical suffices). -/
theorem natAddAssoc (firstPoly secondPoly thirdPoly : NatPoly)
    (hThirdCanonical : NatPolyCanonical thirdPoly) :
    natAdd (natAdd firstPoly secondPoly) thirdPoly =
      natAdd firstPoly (natAdd secondPoly thirdPoly) :=
  natPolyExtensionality (natAdd (natAdd firstPoly secondPoly) thirdPoly)
    (natAdd firstPoly (natAdd secondPoly thirdPoly))
    (natAddKeepsCanonical (natAdd firstPoly secondPoly) thirdPoly hThirdCanonical)
    (natAddKeepsCanonical firstPoly (natAdd secondPoly thirdPoly)
      (natAddKeepsCanonical secondPoly thirdPoly hThirdCanonical))
    (fun probe => by
      rw [natCoeffAdd (natAdd firstPoly secondPoly) thirdPoly probe,
        natCoeffAdd firstPoly secondPoly probe,
        natCoeffAdd firstPoly (natAdd secondPoly thirdPoly) probe,
        natCoeffAdd secondPoly thirdPoly probe]
      exact Nat.add_assoc (natCoeff firstPoly probe) (natCoeff secondPoly probe)
        (natCoeff thirdPoly probe))

/-! ## The RigType carrier, normal form, and decision -/

/-- A formal (+, ×, 0, 1)-expression over indexed base atoms — an object of the
free rig category. -/
inductive RigType where
  | baseAtom (index : Nat)
  | zero
  | one
  | add (left right : RigType)
  | mul (left right : RigType)

/-- Interpret a `RigType` as its multivariate Nat-coefficient polynomial normal
form.  Canonical by construction (`natAdd` / `natMul` preserve canonicity). -/
def normalize : RigType → NatPoly
  | .baseAtom index => natVariablePoly index
  | .zero => natZeroPoly
  | .one => natOnePoly
  | .add left right => natAdd (normalize left) (normalize right)
  | .mul left right => natMul (normalize left) (normalize right)

/-- The type-isomorphism decision: two rig types are isomorphic in the free
(+, ×, 0, 1)-fragment iff their polynomial normal forms are byte-equal. -/
def decideRigIso (leftType rightType : RigType) : Bool :=
  natPolyBeq (normalize leftType) (normalize rightType)

/-- A single variable normal form is canonical. -/
theorem natVariablePolyIsCanonical (index : Nat) :
    NatPolyCanonical (natVariablePoly index) :=
  NatPolyCanonical.singleIsCanonical _ rfl

/-- The one polynomial is canonical. -/
theorem natOnePolyIsCanonical : NatPolyCanonical natOnePoly :=
  NatPolyCanonical.singleIsCanonical _ rfl

/-- Every `RigType` normal form is canonical. -/
theorem normalizeIsCanonical : (rigType : RigType) → NatPolyCanonical (normalize rigType)
  | .baseAtom index => natVariablePolyIsCanonical index
  | .zero => NatPolyCanonical.nilIsCanonical
  | .one => natOnePolyIsCanonical
  | .add left right =>
      natAddKeepsCanonical (normalize left) (normalize right) (normalizeIsCanonical right)
  | .mul left right => natMulIsCanonical (normalize left) (normalize right)

/-! ## RigIso: the rig-axiom congruence, and its soundness

`RigIso` is generated by the rig axioms whose soundness through `normalize` LANDS
zero-axiom: the additive commutative monoid (associativity, commutativity, both
units), multiplicative annihilation on both sides, and additive congruence with
reflexivity / symmetry / transitivity.  The multiplicative-congruence axioms
(distributivity, ×-commutativity, ×-associativity, ×-unit, the symmetric-monoidal
swaps) are NOT generators here — their soundness is walled (see
`rtiHasMultiplicativeSoundness`) although the DECISION computes them correctly. -/

/-- The rig-axiom congruence (sound-through-`normalize` fragment). -/
inductive RigIso : RigType → RigType → Prop where
  | refl (rigType : RigType) : RigIso rigType rigType
  | symm {leftType rightType : RigType} : RigIso leftType rightType → RigIso rightType leftType
  | trans {firstType secondType thirdType : RigType} :
      RigIso firstType secondType → RigIso secondType thirdType → RigIso firstType thirdType
  | addCongr {leftType leftType' rightType rightType' : RigType} :
      RigIso leftType leftType' → RigIso rightType rightType' →
      RigIso (.add leftType rightType) (.add leftType' rightType')
  | addAssoc (leftType middleType rightType : RigType) :
      RigIso (.add (.add leftType middleType) rightType)
        (.add leftType (.add middleType rightType))
  | addComm (leftType rightType : RigType) :
      RigIso (.add leftType rightType) (.add rightType leftType)
  | addZeroRight (rigType : RigType) : RigIso (.add rigType .zero) rigType
  | addZeroLeft (rigType : RigType) : RigIso (.add .zero rigType) rigType
  | mulZeroRight (rigType : RigType) : RigIso (.mul rigType .zero) .zero
  | mulZeroLeft (rigType : RigType) : RigIso (.mul .zero rigType) .zero

/-- **Rig-axiom soundness**: every `RigIso`-related pair has EQUAL normal forms —
so `RigIso` is a refinement of type-isomorphism decided by `decideRigIso`. -/
theorem rigIsoSound : {leftType rightType : RigType} →
    RigIso leftType rightType → normalize leftType = normalize rightType
  | _, _, RigIso.refl _ => rfl
  | _, _, RigIso.symm hIso => (rigIsoSound hIso).symm
  | _, _, RigIso.trans hFirst hSecond => (rigIsoSound hFirst).trans (rigIsoSound hSecond)
  | _, _, RigIso.addCongr hLeft hRight => by
      show natAdd (normalize _) (normalize _) = natAdd (normalize _) (normalize _)
      rw [rigIsoSound hLeft, rigIsoSound hRight]
  | _, _, RigIso.addAssoc leftType middleType rightType =>
      natAddAssoc (normalize leftType) (normalize middleType) (normalize rightType)
        (normalizeIsCanonical rightType)
  | _, _, RigIso.addComm leftType rightType =>
      natAddComm (normalize leftType) (normalize rightType)
        (normalizeIsCanonical leftType) (normalizeIsCanonical rightType)
  | _, _, RigIso.addZeroRight rigType =>
      natAddNilRightIsIdentity (normalize rigType) (normalizeIsCanonical rigType)
  | _, _, RigIso.addZeroLeft _ => rfl
  | _, _, RigIso.mulZeroRight rigType => natMulNilRight (normalize rigType)
  | _, _, RigIso.mulZeroLeft rigType => natMulNilLeft (normalize rigType)

/-! ## T3: the decision correctness -/

/-- Soundness direction: `RigIso`-related types are decided isomorphic. -/
theorem rigIsoImpliesDecide {leftType rightType : RigType}
    (hIso : RigIso leftType rightType) : decideRigIso leftType rightType = true := by
  show natPolyBeq (normalize leftType) (normalize rightType) = true
  rw [rigIsoSound hIso]
  exact natPolyBeqRefl (normalize rightType)

/-- Refutation half: distinct normal forms (decision `false`) refute `RigIso`. -/
theorem decideFalseRefutesRigIso {leftType rightType : RigType}
    (hDecide : decideRigIso leftType rightType = false) : RigIso leftType rightType → False := by
  intro hIso
  have hTrue := rigIsoImpliesDecide hIso
  rw [hDecide] at hTrue
  exact Bool.noConfusion hTrue

/-- If the two normal forms are equal lists then the decision is `true` — the
NF-level completeness the decision procedure realises computationally. -/
theorem equalNormalFormsDecide {leftType rightType : RigType}
    (hEqual : normalize leftType = normalize rightType) :
    decideRigIso leftType rightType = true := by
  show natPolyBeq (normalize leftType) (normalize rightType) = true
  rw [hEqual]
  exact natPolyBeqRefl (normalize rightType)

/-! ## T4 + T2-multiplicative WALLS

`rtiHasMultiplicativeSoundness = false`: the multiplicative-congruence rig axioms
(distributivity `a·(b+c) ~ a·b + a·c`, ×-commutativity, ×-associativity, ×-unit,
the symmetric-monoidal swaps) are NOT proven sound through `normalize` in this
file.  Two burned attacks: (1) structural induction on `natMul` fails because
`natAdd` is a `natTermInsert`-fold, not a `List.append`, so there is no clean
induction reconciling `natMul (natAdd x y) z` with `natAdd (natMul x z) (natMul y z)`;
(2) coefficient-extensionality reduces distributivity to
`natCoeff (natScaleTerm s m (natAdd b c)) = natCoeff (natScaleTerm s m b) + natCoeff (natScaleTerm s m c)`,
which needs a scale-through-merge convolution lemma (the monomial-multiplication
commutativity/associativity laws for `grbExpMul` and a double-sum exchange) that the
Groebner substrate does not carry.  The DECISION is unaffected — `decideRigIso`
computes multiplicative isomorphisms correctly (see the ground fires below). -/
def rtiHasMultiplicativeSoundness : Bool := false

/-- `rtiHasExponentialTypeIsoCompleteness = false`: extending the carrier with an
exponential/function-type former `pow (base exponent)` (object exponentiation
`cod ^ dom`) interprets into integer exponentiation on the polynomial semiring.
The equational theory of `(+, ×, ^)` on the positive integers is Tarski's
high-school-identity problem, which is NOT finitely axiomatisable (Wilkie 1980):
there exist identities true in the positive naturals but underivable from the
eleven high-school axioms.  Hence NO finite `RigIso^pow` presentation is complete
for the exponential fragment — it cannot be closed by adding finitely many axioms.
(The (+, ×, 0, 1)-fragment stays fully decided by `decideRigIso`.) -/
def rtiHasExponentialTypeIsoCompleteness : Bool := false

/-! ## T5: ground fires -/

/-- A distributivity isomorphism `x·(y+1) ~ x·y + x` decides TRUE — the normal
form realises distributivity even though its `RigIso` soundness is walled. -/
theorem rtiFireDistributivity :
    decideRigIso
      (.mul (.baseAtom 0) (.add (.baseAtom 1) .one))
      (.add (.mul (.baseAtom 0) (.baseAtom 1)) (.baseAtom 0)) = true := rfl

/-- A NON-isomorphism `x + x` (i.e. `2x`) versus `x · x` (i.e. `x²`) decides FALSE. -/
theorem rtiFireNonIso :
    decideRigIso
      (.add (.baseAtom 0) (.baseAtom 0))
      (.mul (.baseAtom 0) (.baseAtom 0)) = false := rfl

/-- Left-distributivity over a bare sum `x·(y+z) ~ x·y + x·z` decides TRUE. -/
theorem rtiFireLeftDistributivity :
    decideRigIso
      (.mul (.baseAtom 0) (.add (.baseAtom 1) (.baseAtom 2)))
      (.add (.mul (.baseAtom 0) (.baseAtom 1)) (.mul (.baseAtom 0) (.baseAtom 2))) = true := rfl

/-- Multiplicative annihilation `x · 0 ~ 0` decides TRUE. -/
theorem rtiFireMulZero :
    decideRigIso (.mul (.baseAtom 0) .zero) .zero = true := rfl

/-- Control: the additive-commutativity iso `x + y ~ y + x` decides TRUE. -/
theorem rtiFireAddComm :
    decideRigIso
      (.add (.baseAtom 0) (.baseAtom 1))
      (.add (.baseAtom 1) (.baseAtom 0)) = true := rfl

/-- Control non-iso: `x + y` versus `x · y` decides FALSE (a sum is not a product). -/
theorem rtiFireControlNonIso :
    decideRigIso
      (.add (.baseAtom 0) (.baseAtom 1))
      (.mul (.baseAtom 0) (.baseAtom 1)) = false := rfl

end FX1Poly.ComputerAlgebra
