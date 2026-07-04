import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.AdjunctionAtomRigidity
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineBoundaryChain
import FX1Poly.Polygraph.Computad.PathSplit

/-! # DisjointWindowFactorization — the whisker decomposition behind the realized swap (ARC-2b brick ii-a)

The `SpineAtomSwap` constructor transposes two adjacent atoms whose generators act on DISJOINT wire
windows, and it demands the whisker factorization exhibiting the disjointness: the second atom's left
context must factor through the first atom's produced window plus an INERT middle zone, and the first
atom's right context must factor as that inert zone followed by the second generator's window.  This
brick proves the factorization EXISTS at the walking adjunction, for adjacent boundary-chained atoms
whose windows are separated by a gap:

  * the gap is taken in EXISTENTIAL form (`windowGap` + an addition equation) — no truncated
    subtraction anywhere;
  * the two context paths are split by `splitPathAt` at the window arithmetic's indices;
  * every endpoint and every path pin then falls to seed rigidity (`adjunctionPathTargets_eq_of_length_eq`
    / `adjunctionPath_eq_of_length_eq`) — at the adjunction, parallel paths of equal length are equal, so
    the factorization is DETERMINED by the boundary-length bookkeeping.

The output hands the swap-application brick (ii-b) exactly the three facts it needs: the second atom's
left-context decomposition, the first atom's right-context decomposition, and the inert zone's length pin.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- Left-cancellation for `Nat` addition, hand-rolled (core `Nat.add_left_cancel` is propext-tainted;
`Nat.zero_add` / `Nat.succ_add` / `Nat.succ.inj` are clean). -/
private theorem natAddLeftCancel (base : Nat) :
    ∀ {leftValue rightValue : Nat},
      base + leftValue = base + rightValue → leftValue = rightValue := by
  induction base with
  | zero =>
      intro leftValue rightValue sumsEqual
      rw [Nat.zero_add, Nat.zero_add] at sumsEqual
      exact sumsEqual
  | succ basePred inductionHypothesis =>
      intro leftValue rightValue sumsEqual
      rw [Nat.succ_add, Nat.succ_add] at sumsEqual
      exact inductionHypothesis (Nat.succ.inj sumsEqual)

/-- ★ **Disjoint-window whisker factorization at the seed.**  For two atoms at the walking adjunction
firing at chained boundaries (`atomSecond` fires at `atomFirst`'s target boundary) with the second
window a `windowGap` to the RIGHT of the first's produced window, there is an inert middle path such
that (i) the second atom's left context is the first's left context, the first's produced 1-cell, then
the inert zone; (ii) the first atom's right context is the inert zone, the second generator's source
1-cell, then the second atom's right context; (iii) the inert zone's length is exactly the gap.  The
splits are produced by `splitPathAt` at the window arithmetic's indices, and every pin falls to seed
rigidity — parallel adjunction paths of equal length are equal. -/
theorem adjunctionSpineAtom_contextsFactor_of_disjointWindows
    {overallSource overallTarget : adjunctionGraph.Mode}
    (atomFirst atomSecond : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (boundariesChain : atomSecond.domBoundaryLength = atomFirst.codBoundaryLength)
    (windowGap : Nat)
    (windowsDisjoint :
      atomFirst.leftContext.length + atomFirst.generatorCod.length + windowGap
        = atomSecond.leftContext.length) :
    ∃ inertPath : ModalityPath adjunctionGraph atomFirst.rightMidMode atomSecond.leftMidMode,
      atomSecond.leftContext
          = composePath (composePath atomFirst.leftContext atomFirst.generatorCod) inertPath
        ∧ atomFirst.rightContext
          = composePath inertPath (composePath atomSecond.generatorDom atomSecond.rightContext)
        ∧ inertPath.length = windowGap := by
  obtain ⟨leftMidA, rightMidA, leftContextA, generatorDomA, generatorCodA, generatorA,
    rightContextA⟩ := atomFirst
  obtain ⟨leftMidB, rightMidB, leftContextB, generatorDomB, generatorCodB, generatorB,
    rightContextB⟩ := atomSecond
  dsimp only [SpineAtom.domBoundaryLength, SpineAtom.codBoundaryLength] at boundariesChain
  dsimp only at windowsDisjoint ⊢
  rw [← windowsDisjoint] at boundariesChain
  rw [Nat.add_assoc (leftContextA.length + generatorCodA.length + windowGap)
        generatorDomB.length rightContextB.length,
      Nat.add_assoc (leftContextA.length + generatorCodA.length) windowGap
        (generatorDomB.length + rightContextB.length)] at boundariesChain
  have gapPlusWindow := natAddLeftCancel _ boundariesChain
  have gapInRange : windowGap ≤ rightContextA.length :=
    gapPlusWindow ▸ Nat.le_add_right windowGap
      (generatorDomB.length + rightContextB.length)
  obtain ⟨inertMiddle, inertPrefix, inertSuffix, inertComposes, inertLength⟩ :=
    splitPathAt rightContextA windowGap gapInRange
  have inertSuffixLength : inertSuffix.length
      = generatorDomB.length + rightContextB.length := by
    have composedLengths := congrArg ModalityPath.length inertComposes
    rw [ModalityPath.length_composePath, inertLength, ← gapPlusWindow] at composedLengths
    exact natAddLeftCancel windowGap composedLengths
  have domInRange : generatorDomB.length ≤ inertSuffix.length :=
    inertSuffixLength.symm ▸ Nat.le_add_right generatorDomB.length rightContextB.length
  obtain ⟨genMiddle, genPrefix, genSuffix, genComposes, genLength⟩ :=
    splitPathAt inertSuffix generatorDomB.length domInRange
  have leftCandidateLength :
      (composePath (composePath leftContextA generatorCodA) inertPrefix).length
        = leftContextB.length := by
    rw [ModalityPath.length_composePath, ModalityPath.length_composePath, inertLength]
    exact windowsDisjoint
  cases adjunctionPathTargets_eq_of_length_eq
    (composePath (composePath leftContextA generatorCodA) inertPrefix) leftContextB
    leftCandidateLength
  have leftContextEquation := adjunctionPath_eq_of_length_eq
    (composePath (composePath leftContextA generatorCodA) inertPrefix) leftContextB
    leftCandidateLength
  cases adjunctionPathTargets_eq_of_length_eq genPrefix generatorDomB genLength
  have genPrefixEquation := adjunctionPath_eq_of_length_eq genPrefix generatorDomB genLength
  have genSuffixLength : genSuffix.length = rightContextB.length := by
    have composedLengths := congrArg ModalityPath.length genComposes
    rw [ModalityPath.length_composePath, genLength, inertSuffixLength] at composedLengths
    exact natAddLeftCancel generatorDomB.length composedLengths
  have genSuffixEquation := adjunctionPath_eq_of_length_eq genSuffix rightContextB
    genSuffixLength
  refine ⟨inertPrefix, leftContextEquation.symm, ?_, inertLength⟩
  rw [← inertComposes, ← genComposes, genPrefixEquation, genSuffixEquation]
  exact rfl

/-- ★ **Mirrored (left-of) disjoint-window whisker factorization at the seed.**  Same setting as
the right-of factorization, but the SECOND atom's window lies entirely to the LEFT of the first
atom's zone: the second's source window ends a `windowGap` below the first's left context.  Then
the first atom's left context factors as the second's window (left context, then source 1-cell)
followed by an inert zone, and the second atom's right context factors as that inert zone, the
first's produced 1-cell, then the first's right context.  Only ONE `splitPathAt` is needed —
every other pin lands as a WHOLE-composite rigidity equation, because at the adjunction parallel
paths of equal length are equal. -/
theorem adjunctionSpineAtom_contextsFactorLeft_of_disjointWindows
    {overallSource overallTarget : adjunctionGraph.Mode}
    (atomFirst atomSecond : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (boundariesChain : atomSecond.domBoundaryLength = atomFirst.codBoundaryLength)
    (windowGap : Nat)
    (windowsDisjoint :
      atomSecond.leftContext.length + atomSecond.generatorDom.length + windowGap
        = atomFirst.leftContext.length) :
    ∃ inertPath : ModalityPath adjunctionModeSignature.graph
        atomSecond.rightMidMode atomFirst.leftMidMode,
      atomFirst.leftContext
          = composePath (composePath atomSecond.leftContext atomSecond.generatorDom) inertPath
        ∧ atomSecond.rightContext
          = composePath inertPath (composePath atomFirst.generatorCod atomFirst.rightContext)
        ∧ inertPath.length = windowGap := by
  obtain ⟨leftMidA, rightMidA, leftContextA, generatorDomA, generatorCodA, generatorA,
    rightContextA⟩ := atomFirst
  obtain ⟨leftMidB, rightMidB, leftContextB, generatorDomB, generatorCodB, generatorB,
    rightContextB⟩ := atomSecond
  dsimp only [SpineAtom.domBoundaryLength, SpineAtom.codBoundaryLength] at boundariesChain
  dsimp only at windowsDisjoint ⊢
  rw [← windowsDisjoint] at boundariesChain
  rw [Nat.add_assoc (leftContextB.length + generatorDomB.length + windowGap)
        generatorCodA.length rightContextA.length,
      Nat.add_assoc (leftContextB.length + generatorDomB.length) windowGap
        (generatorCodA.length + rightContextA.length)] at boundariesChain
  have windowPlusGap := natAddLeftCancel _ boundariesChain
  have splitInRange : leftContextB.length + generatorDomB.length ≤ leftContextA.length :=
    windowsDisjoint ▸ Nat.le_add_right (leftContextB.length + generatorDomB.length) windowGap
  obtain ⟨splitMiddle, windowPrefix, inertPath, splitComposes, prefixLengthMatches⟩ :=
    splitPathAt leftContextA (leftContextB.length + generatorDomB.length) splitInRange
  have composedLengths := congrArg ModalityPath.length splitComposes
  rw [ModalityPath.length_composePath, prefixLengthMatches, ← windowsDisjoint]
    at composedLengths
  have inertLength := natAddLeftCancel _ composedLengths
  have prefixCandidateLength :
      (composePath leftContextB generatorDomB).length = windowPrefix.length := by
    rw [ModalityPath.length_composePath, prefixLengthMatches]
  cases adjunctionPathTargets_eq_of_length_eq (composePath leftContextB generatorDomB)
    windowPrefix prefixCandidateLength
  have windowPrefixEquation := adjunctionPath_eq_of_length_eq
    (composePath leftContextB generatorDomB) windowPrefix prefixCandidateLength
  have rightCandidateLength :
      (composePath inertPath (composePath generatorCodA rightContextA)).length
        = rightContextB.length := by
    rw [ModalityPath.length_composePath, ModalityPath.length_composePath, inertLength]
    exact windowPlusGap.symm
  have rightContextEquation := adjunctionPath_eq_of_length_eq
    (composePath inertPath (composePath generatorCodA rightContextA)) rightContextB
    rightCandidateLength
  refine ⟨inertPath, ?_, rightContextEquation.symm, inertLength⟩
  rw [← splitComposes, ← windowPrefixEquation]
  exact rfl

/-! ## Honesty markers -/

/-- **Honesty marker — the disjoint-window whisker factorization is SHIPPED (ARC-2b brick ii-a).**
`adjunctionSpineAtom_contextsFactor_of_disjointWindows` exhibits, for boundary-chained adjacent seed
atoms with a right-of gap, the inert middle path with both context decompositions and the gap-length
pin — exactly the data the `SpineAtomSwap` constructor's whisker shape demands.  The swap application
(ii-b), its chain preservation (ii-c-1), and the mirrored factorization below have since shipped;
still open: the mirrored swap APPLICATION and the cup/cap peel (iii).  `= true`. -/
def fxMode_hasDisjointWindowFactorization : Bool := true

/-- **Honesty marker — the mirrored (left-of) whisker factorization is SHIPPED (ARC-2b brick
ii-c-2a).**  `adjunctionSpineAtom_contextsFactorLeft_of_disjointWindows` covers the peel's other
bubbling direction: the second atom's window entirely LEFT of the first's zone.  One split, three
rigidity pins, gap-length returned.  NOT yet shipped: the mirrored swap APPLICATION (the pair
matches the `SpineAtomSwap` constructor's RHS, so the realized bubble wraps with symmetry) and the
cup/cap peel (iii).  `= true`. -/
def fxMode_hasMirroredWindowFactorization : Bool := true

end FX1Poly.Polygraph
