import FX1Poly.Polygraph.TwoCategory.WalkingString.StringDisjointWordLeftMirror

/-! # WalkingString/StringCommuteWordFactorData — the Type-valued COMMUTE factorization data, both directions
(FC-3 r5, B2)

The COMMUTE producer's per-step move re-threads the two moved atoms through the inert zone; those moved atoms are
DATA (they define the transposed `next` cell), so the inert path they carry must be Type-valued, not the
existential witness of a `Prop` factorization.  The walking-adjunction COMMUTE producers
(`SpineValleyCommuteProducer` / `SpineValleyCommuteProducerLeft`) re-wrap their `Prop` factorizations into
Type-valued `DisjointWindowFactorData` / `DisjointWindowFactorDataLeft` for exactly this reason.  This file ships
the WORD analogues — the four COMMUTE sites (`leftFactor` + `rightFactor`, both directions):

  * `DisjointWordWindowFactorData` / `disjointWordWindowFactorData_of_disjointWordWindows` — ★ the RIGHT-of
    Type-valued factorization (C1/C2): the inert path as DATA, with the two context decompositions
    (`capAtom.leftContext = (cup.left · cup.cod) · inert`, `cup.rightContext = inert · (cap.dom · cap.right)`).
    Re-runs the r4 `spineAtom_contextsFactor_of_disjointWordWindows` split-pack derivation into the structure —
    the Prop factorization is already machine-checked, so this is the Type-valued re-wrap the recon named.
  * `DisjointWordWindowFactorDataLeft` / `disjointWordWindowFactorDataLeft_of_disjointWordWindows` — ★ the LEFT-of
    Type-valued factorization (C3/C4): rides the B3 LEFT word factorization
    (`spineAtom_contextsFactorLeft_of_disjointWordWindows`), re-run into the structure.

Both keyed on the shared BOUNDARY WORD (not seed length-rigidity), so both run at the walking adjoint triple.
Non-vacuity (`stringCommuteWordFactorData_equalLengthDistinctWord`) builds BOTH Type-valued factorizations on the
equal-length-DISTINCT-word `(η : F·G, ε' : H·G)` config.

What this file does NOT ship (honest, the recon's Piece-I assembly residual for a later round): the full
`CommutePairData` (moved atoms + three boundary-path coherences + the flat swap, all sharing one inert path) and
the oracle's COMMUTE dispatch (`commuteCellDescentStepRight`).  The realized swaps themselves are already shipped
(r4 `spineAtomSwap_of_disjointWordWindows` right, B3 `spineAtomSwapLeft_of_disjointWordWindows` left); this file
ships the Type-valued factorization DATA both dispatch halves consume.

Raw Lean 4 + Init; each builder re-runs the split-pack derivation into a `Type`-valued structure (the inert path
is `splitPathAt`'s prefix, kept as data; the context decompositions are the split-pack's injected equalities).
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration `#assert_no_axioms` gated
in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- Left-cancellation for `Nat` addition, hand-rolled propext-free (core `Nat.add_left_cancel` leaks propext). -/
private theorem natAddLeftCancelCommute (base : Nat) :
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

/-! ## The RIGHT-of Type-valued factorization data (C1/C2) -/

/-- The RIGHT-of disjoint-window factorization data — Type-valued so the inert middle path is DATA the moved
atoms depend on: the inert path plus the two context decompositions.  The WORD analogue of the adjunction's
`DisjointWindowFactorData`. -/
structure DisjointWordWindowFactorData {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    (atomFirst atomSecond : SpineAtom signature overallSource overallTarget) : Type where
  /-- The inert middle zone separating the two windows. -/
  inertPath : ModalityPath signature.graph atomFirst.rightMidMode atomSecond.leftMidMode
  /-- The second atom's left context factors through the first's produced window then the inert zone. -/
  leftFactor : atomSecond.leftContext
    = composePath (composePath atomFirst.leftContext atomFirst.generatorCod) inertPath
  /-- The first atom's right context factors as the inert zone then the second atom's consumed window. -/
  rightFactor : atomFirst.rightContext
    = composePath inertPath (composePath atomSecond.generatorDom atomSecond.rightContext)

/-- ★ **The RIGHT-of Type-valued word factorization (C1/C2).**  A constructive mirror of the r4 Prop factorization
`spineAtom_contextsFactor_of_disjointWordWindows`, keeping the inert path (the `splitPathAt` prefix of the first
atom's right context) as DATA so the moved atoms it defines are usable in `Type`.  Every pin lands by
`composePath_splitPackEqOfPrefixLengthEq` on the shared word — signature-GENERIC, so it runs at the walking
adjoint triple where length-rigidity is FALSE. -/
def disjointWordWindowFactorData_of_disjointWordWindows {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    (atomFirst atomSecond : SpineAtom signature overallSource overallTarget)
    (sharedWord :
      composePath atomFirst.leftContext (composePath atomFirst.generatorCod atomFirst.rightContext)
        = composePath atomSecond.leftContext
            (composePath atomSecond.generatorDom atomSecond.rightContext))
    (windowGap : Nat)
    (windowsDisjoint :
      atomFirst.leftContext.length + atomFirst.generatorCod.length + windowGap
        = atomSecond.leftContext.length) :
    DisjointWordWindowFactorData atomFirst atomSecond := by
  obtain ⟨leftMidA, rightMidA, leftContextA, generatorDomA, generatorCodA, generatorA,
    rightContextA⟩ := atomFirst
  obtain ⟨leftMidB, rightMidB, leftContextB, generatorDomB, generatorCodB, generatorB,
    rightContextB⟩ := atomSecond
  dsimp only at sharedWord windowsDisjoint
  have sharedLength :
      leftContextA.length + (generatorCodA.length + rightContextA.length)
        = leftContextB.length + (generatorDomB.length + rightContextB.length) := by
    have lengthsEqual := congrArg ModalityPath.length sharedWord
    rw [ModalityPath.length_composePath, ModalityPath.length_composePath,
        ModalityPath.length_composePath, ModalityPath.length_composePath] at lengthsEqual
    exact lengthsEqual
  rw [← windowsDisjoint] at sharedLength
  rw [← Nat.add_assoc leftContextA.length generatorCodA.length rightContextA.length,
      Nat.add_assoc (leftContextA.length + generatorCodA.length) windowGap
        (generatorDomB.length + rightContextB.length)] at sharedLength
  have gapPlusWindow :
      rightContextA.length = windowGap + (generatorDomB.length + rightContextB.length) :=
    natAddLeftCancelCommute _ sharedLength
  have gapInRange : windowGap ≤ rightContextA.length := by
    rw [gapPlusWindow]; exact Nat.le_add_right _ _
  obtain ⟨inertMiddle, inertPrefix, inertSuffix, inertComposes, inertLength⟩ :=
    splitPathAt rightContextA windowGap gapInRange
  have inertSuffixLength : inertSuffix.length = generatorDomB.length + rightContextB.length := by
    have composedLengths := congrArg ModalityPath.length inertComposes
    rw [ModalityPath.length_composePath, inertLength, gapPlusWindow] at composedLengths
    exact natAddLeftCancelCommute _ composedLengths
  have domInRange : generatorDomB.length ≤ inertSuffix.length := by
    rw [inertSuffixLength]; exact Nat.le_add_right _ _
  obtain ⟨genMiddle, genPrefix, genSuffix, genComposes, genLength⟩ :=
    splitPathAt inertSuffix generatorDomB.length domInRange
  have splitEquation :
      composePath (composePath (composePath leftContextA generatorCodA) inertPrefix)
          (composePath genPrefix genSuffix)
        = composePath leftContextB (composePath generatorDomB rightContextB) := by
    rw [composePath_assoc (composePath leftContextA generatorCodA) inertPrefix
          (composePath genPrefix genSuffix),
        composePath_assoc leftContextA generatorCodA
          (composePath inertPrefix (composePath genPrefix genSuffix)),
        genComposes, inertComposes]
    exact sharedWord
  have leftPrefixLength :
      (composePath (composePath leftContextA generatorCodA) inertPrefix).length
        = leftContextB.length := by
    rw [ModalityPath.length_composePath, ModalityPath.length_composePath, inertLength]
    exact windowsDisjoint
  have leftPack := composePath_splitPackEqOfPrefixLengthEq
    (composePath (composePath leftContextA generatorCodA) inertPrefix)
    (composePath genPrefix genSuffix) leftContextB (composePath generatorDomB rightContextB)
    splitEquation leftPrefixLength
  have leftMidEqual : inertMiddle = leftMidB := congrArg (fun pack => pack.fst) leftPack
  subst leftMidEqual
  injection leftPack with _outerFstEqual innerLeftPack
  injection innerLeftPack with leftContextEquation suffixesEqual
  have rightPack := composePath_splitPackEqOfPrefixLengthEq
    genPrefix genSuffix generatorDomB rightContextB suffixesEqual genLength
  have rightMidEqual : genMiddle = rightMidB := congrArg (fun pack => pack.fst) rightPack
  subst rightMidEqual
  injection rightPack with _rightFstEqual innerRightPack
  injection innerRightPack with genPrefixEquation genSuffixEquation
  refine ⟨inertPrefix, leftContextEquation.symm, ?_⟩
  rw [← inertComposes, ← genComposes, genPrefixEquation, genSuffixEquation]

/-! ## The LEFT-of Type-valued factorization data (C3/C4) -/

/-- The LEFT-of disjoint-window factorization data — Type-valued (the WORD analogue of the adjunction's
`DisjointWindowFactorDataLeft`): the second atom's SOURCE window lies to the LEFT of the first's zone. -/
structure DisjointWordWindowFactorDataLeft {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    (atomFirst atomSecond : SpineAtom signature overallSource overallTarget) : Type where
  /-- The inert middle zone separating the two windows. -/
  inertPath : ModalityPath signature.graph atomSecond.rightMidMode atomFirst.leftMidMode
  /-- The first atom's left context factors through the second's window then the inert zone. -/
  leftFactor : atomFirst.leftContext
    = composePath (composePath atomSecond.leftContext atomSecond.generatorDom) inertPath
  /-- The second atom's right context factors as the inert zone then the first atom's produced window. -/
  rightFactor : atomSecond.rightContext
    = composePath inertPath (composePath atomFirst.generatorCod atomFirst.rightContext)

/-- ★ **The LEFT-of Type-valued word factorization (C3/C4).**  Rides the B3 LEFT word factorization
`spineAtom_contextsFactorLeft_of_disjointWordWindows`, re-run into the Type-valued structure so the inert path is
DATA.  Signature-GENERIC, so it runs at the walking adjoint triple. -/
def disjointWordWindowFactorDataLeft_of_disjointWordWindows {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    (atomFirst atomSecond : SpineAtom signature overallSource overallTarget)
    (sharedWord :
      composePath atomFirst.leftContext (composePath atomFirst.generatorCod atomFirst.rightContext)
        = composePath atomSecond.leftContext
            (composePath atomSecond.generatorDom atomSecond.rightContext))
    (windowGap : Nat)
    (windowsDisjoint :
      atomSecond.leftContext.length + atomSecond.generatorDom.length + windowGap
        = atomFirst.leftContext.length) :
    DisjointWordWindowFactorDataLeft atomFirst atomSecond := by
  obtain ⟨leftMidA, rightMidA, leftContextA, generatorDomA, generatorCodA, generatorA,
    rightContextA⟩ := atomFirst
  obtain ⟨leftMidB, rightMidB, leftContextB, generatorDomB, generatorCodB, generatorB,
    rightContextB⟩ := atomSecond
  dsimp only at sharedWord windowsDisjoint
  have windowInRange : leftContextB.length + generatorDomB.length ≤ leftContextA.length :=
    windowsDisjoint ▸ Nat.le_add_right (leftContextB.length + generatorDomB.length) windowGap
  obtain ⟨splitMiddle, windowPrefix, inertPath, splitComposes, prefixLengthMatches⟩ :=
    splitPathAt leftContextA (leftContextB.length + generatorDomB.length) windowInRange
  have wordEq :
      composePath windowPrefix (composePath inertPath (composePath generatorCodA rightContextA))
        = composePath (composePath leftContextB generatorDomB) rightContextB := by
    rw [← composePath_assoc windowPrefix inertPath (composePath generatorCodA rightContextA),
        splitComposes, composePath_assoc leftContextB generatorDomB rightContextB]
    exact sharedWord
  have lengthEq : windowPrefix.length = (composePath leftContextB generatorDomB).length := by
    rw [prefixLengthMatches, ModalityPath.length_composePath]
  have windowPack := composePath_splitPackEqOfPrefixLengthEq
    windowPrefix (composePath inertPath (composePath generatorCodA rightContextA))
    (composePath leftContextB generatorDomB) rightContextB wordEq lengthEq
  have midEqual : splitMiddle = rightMidB := congrArg (fun pack => pack.fst) windowPack
  subst midEqual
  injection windowPack with _fstEqual innerPack
  injection innerPack with windowPrefixEqual rightContextEquation
  refine ⟨inertPath, ?_, rightContextEquation.symm⟩
  rw [← splitComposes, windowPrefixEqual]

/-! ## Non-vacuity — both Type-valued factorizations on the equal-length-DISTINCT-word class -/

/-- ★ **Both Type-valued COMMUTE factorizations fire on the equal-length-DISTINCT-word config.**  The RIGHT-of data
is built for the `(η : F·G, ε' : H·G)` window pair (adjacent, `windowGap = 0`), and the LEFT-of data for the
mirror pair — both at the walking adjoint triple, the class the length-rigid engine could not run. -/
theorem stringCommuteWordFactorData_equalLengthDistinctWord :
    (∃ atomFirst atomSecond :
        SpineAtom adjointTripleModeSignature AdjointTripleMode.base AdjointTripleMode.base,
      Nonempty (DisjointWordWindowFactorData atomFirst atomSecond))
    ∧ (∃ atomFirst atomSecond :
        SpineAtom adjointTripleModeSignature AdjointTripleMode.base AdjointTripleMode.base,
      Nonempty (DisjointWordWindowFactorDataLeft atomFirst atomSecond)) := by
  refine ⟨?_, ?_⟩
  · let cupAtom : SpineAtom adjointTripleModeSignature AdjointTripleMode.base AdjointTripleMode.base :=
      ⟨AdjointTripleMode.base, AdjointTripleMode.base,
        ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base,
        ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base, stringFG,
        StringTwoCell.unitLower, stringHG⟩
    let capAtom : SpineAtom adjointTripleModeSignature AdjointTripleMode.base AdjointTripleMode.base :=
      ⟨AdjointTripleMode.base, AdjointTripleMode.base, stringFG, stringHG,
        ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base,
        StringTwoCell.counitUpper,
        ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base⟩
    exact ⟨cupAtom, capAtom,
      ⟨disjointWordWindowFactorData_of_disjointWordWindows cupAtom capAtom rfl 0 rfl⟩⟩
  · let unitAtom : SpineAtom adjointTripleModeSignature AdjointTripleMode.base AdjointTripleMode.base :=
      ⟨AdjointTripleMode.base, AdjointTripleMode.base, stringHG,
        ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base, stringFG,
        StringTwoCell.unitLower,
        ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base⟩
    let counitAtom : SpineAtom adjointTripleModeSignature AdjointTripleMode.base AdjointTripleMode.base :=
      ⟨AdjointTripleMode.base, AdjointTripleMode.base,
        ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base, stringHG,
        ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base,
        StringTwoCell.counitUpper, stringFG⟩
    exact ⟨unitAtom, counitAtom,
      ⟨disjointWordWindowFactorDataLeft_of_disjointWordWindows unitAtom counitAtom rfl 0 rfl⟩⟩

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the Type-valued COMMUTE factorization data is machine-checked, BOTH directions (FC-3 r5,
B2).**  The four COMMUTE sites (`leftFactor` + `rightFactor`, right + left) are packaged Type-valued so the moved
atoms depend on the inert path as DATA: `DisjointWordWindowFactorData` /
`disjointWordWindowFactorData_of_disjointWordWindows` (C1/C2) re-run the r4 RIGHT-of split-pack derivation into a
structure; `DisjointWordWindowFactorDataLeft` / `disjointWordWindowFactorDataLeft_of_disjointWordWindows` (C3/C4)
ride the B3 LEFT word factorization.  Both keyed on the shared BOUNDARY WORD, so both run at the walking adjoint
triple where length-rigidity is FALSE.  Non-vacuity `stringCommuteWordFactorData_equalLengthDistinctWord` builds
both on the `(η : F·G, ε' : H·G)` config.

  What this marker does NOT close (gates stay `false`): the full `CommutePairData` (moved atoms + three
  boundary-path coherences + the flat swap sharing one inert path) and the oracle's COMMUTE dispatch
  (`commuteCellDescentStepRight`) — the Piece-I assembly of a later round.  The realized swaps are already shipped
  (r4 right, B3 left); this ships the Type-valued factorization DATA both halves consume.
  `fxString_hasAdjointTripleCompleteness` stays `false`.  `= true`. -/
def fxString_hasCommuteWordFactorData : Bool := true

end FX1Poly.Polygraph
