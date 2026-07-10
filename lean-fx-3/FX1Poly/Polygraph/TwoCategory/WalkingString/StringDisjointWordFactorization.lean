import FX1Poly.Polygraph.TwoCategory.WalkingString.StringSeed
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineBoundaryWordChain
import FX1Poly.Polygraph.Computad.PathSplit
import FX1Poly.Polygraph.Computad.PathFactorization

/-! # WalkingString/StringDisjointWordFactorization — the WORD-indexed disjoint-window whisker factorization (FC-3 r4, B1)

The walking-adjunction disjoint-window factorization
(`adjunctionSpineAtom_contextsFactor_of_disjointWindows`, `WalkingAdjunction/DisjointWindowFactorization`)
pins every split piece by SEED LENGTH-RIGIDITY (`adjunctionPath_eq_of_length_eq`: at the single-colour
adjunction, parallel paths of equal length are equal).  That rigidity is FALSE at the walking adjoint
triple — `stringFG ≠ stringHG` at equal length `2` — so the length-rigid engine cannot re-run there.

This file re-derives the SAME factorization keyed on the shared BOUNDARY WORD instead of length-rigidity.
The word chain (`SpineBoundaryWordChained`, r2) hands every adjacent pair of atoms the shared-word equation
`atomFirst.leftContext · atomFirst.generatorCod · atomFirst.rightContext =
   atomSecond.leftContext · atomSecond.generatorDom · atomSecond.rightContext`
(the first atom's TARGET boundary word is the second atom's SOURCE boundary word).  Every split piece is
then pinned by `composePath_splitPackEqOfPrefixLengthEq` — length-split determinacy of a factorization of
ONE fixed word — rather than by parallel-path length-rigidity.  This is signature-GENERIC (it consumes only
the shared word + the disjointness gap), so it runs at the adjoint triple where length-rigidity fails.

  * `spineBoundaryWordChained_pairSharedWord` — the shared-word extractor: cons-inverting the word chain
    twice hands the `(*)` equation to the engine;
  * `spineAtom_contextsFactor_of_disjointWordWindows` — ★ the word-indexed factorization: for a right-of gap,
    the inert middle path with both context decompositions and the gap-length pin, proved by splitting
    `atomFirst.rightContext` with `splitPathAt` and discharging every pin by
    `composePath_splitPackEqOfPrefixLengthEq` on the shared word (NO length-rigidity);
  * `stringDisjointWordFactorization_equalLengthDistinctWord` — non-vacuity: the equal-length-DISTINCT-word
    config (`atomFirst.generatorCod = F·G`, `atomSecond.generatorDom = H·G`, both length `2` yet distinct)
    handled CORRECTLY on a genuinely word-chained spine at `adjointTripleModeSignature` — precisely the
    class where length-rigidity would be UNSOUND.

Raw Lean 4 + Init; the length bookkeeping is hand-rolled cancellation (core `Nat.add_*_cancel` is
propext-tainted).  `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration
`#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- Left-cancellation for `Nat` addition, hand-rolled (core `Nat.add_left_cancel` is propext-tainted;
`Nat.zero_add` / `Nat.succ_add` / `Nat.succ.inj` are clean). -/
private theorem natAddLeftCancelWord (base : Nat) :
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

/-! ## The shared-word extractor — the word chain hands the `(*)` equation -/

/-- **The shared boundary word of an adjacent pair.**  Cons-inverting `SpineBoundaryWordChained` twice: the
head atom fires at the running boundary word and hands its TARGET boundary word to the tail, which the second
atom then fires at — so the first atom's cod word IS the second atom's dom word.  This is the `(*)` equation
the word-indexed factorization consumes, delivered directly by the r2 word-chain substrate (replacing the
length-only boundary chain the length-rigid engine used). -/
theorem spineBoundaryWordChained_pairSharedWord {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {boundaryWord : ModalityPath signature.graph sourceMode targetMode}
    {atomFirst atomSecond : SpineAtom signature sourceMode targetMode}
    {rest : List (SpineAtom signature sourceMode targetMode)}
    (chained : SpineBoundaryWordChained boundaryWord (atomFirst :: atomSecond :: rest)) :
    composePath atomFirst.leftContext (composePath atomFirst.generatorCod atomFirst.rightContext)
      = composePath atomSecond.leftContext
          (composePath atomSecond.generatorDom atomSecond.rightContext) :=
  (spineBoundaryWordChained_tail (spineBoundaryWordChained_tail chained).2).1

/-! ## The word-indexed disjoint-window factorization -/

/-- ★ **Word-indexed disjoint-window whisker factorization.**  For two atoms whose boundary words chain
(`sharedWord`: the first's cod word = the second's dom word) with the second window a `windowGap` to the RIGHT
of the first's produced window, there is an inert middle path such that (i) the second atom's left context is
the first's left context, the first's produced 1-cell, then the inert zone; (ii) the first atom's right
context is the inert zone, the second generator's source 1-cell, then the second atom's right context; (iii)
the inert zone's length is exactly the gap.  Signature-GENERIC: every pin falls to
`composePath_splitPackEqOfPrefixLengthEq` on `sharedWord` (length-split determinacy of a factorization of the
ONE fixed word), NOT to parallel-path length-rigidity — so it runs at the walking adjoint triple where
`stringFG ≠ stringHG` makes length-rigidity false. -/
theorem spineAtom_contextsFactor_of_disjointWordWindows {signature : ModeSignature}
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
    ∃ inertPath : ModalityPath signature.graph atomFirst.rightMidMode atomSecond.leftMidMode,
      atomSecond.leftContext
          = composePath (composePath atomFirst.leftContext atomFirst.generatorCod) inertPath
        ∧ atomFirst.rightContext
          = composePath inertPath (composePath atomSecond.generatorDom atomSecond.rightContext)
        ∧ inertPath.length = windowGap := by
  obtain ⟨leftMidA, rightMidA, leftContextA, generatorDomA, generatorCodA, generatorA,
    rightContextA⟩ := atomFirst
  obtain ⟨leftMidB, rightMidB, leftContextB, generatorDomB, generatorCodB, generatorB,
    rightContextB⟩ := atomSecond
  dsimp only at sharedWord windowsDisjoint ⊢
  -- length bookkeeping: the shared word's length gives the boundary-length chain, from which the gap
  -- decomposition of `rightContextA` follows.
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
    natAddLeftCancelWord _ sharedLength
  have gapInRange : windowGap ≤ rightContextA.length := by
    rw [gapPlusWindow]; exact Nat.le_add_right _ _
  obtain ⟨inertMiddle, inertPrefix, inertSuffix, inertComposes, inertLength⟩ :=
    splitPathAt rightContextA windowGap gapInRange
  have inertSuffixLength : inertSuffix.length = generatorDomB.length + rightContextB.length := by
    have composedLengths := congrArg ModalityPath.length inertComposes
    rw [ModalityPath.length_composePath, inertLength, gapPlusWindow] at composedLengths
    exact natAddLeftCancelWord _ composedLengths
  have domInRange : generatorDomB.length ≤ inertSuffix.length := by
    rw [inertSuffixLength]; exact Nat.le_add_right _ _
  obtain ⟨genMiddle, genPrefix, genSuffix, genComposes, genLength⟩ :=
    splitPathAt inertSuffix generatorDomB.length domInRange
  -- pin (i): the left context, via the split-pack on the shared word (prefix `lcA · codA · inert`).
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
  -- pin (ii): the dom / right context, via the split-pack on the residue.
  have rightPack := composePath_splitPackEqOfPrefixLengthEq
    genPrefix genSuffix generatorDomB rightContextB suffixesEqual genLength
  have rightMidEqual : genMiddle = rightMidB := congrArg (fun pack => pack.fst) rightPack
  subst rightMidEqual
  injection rightPack with _rightFstEqual innerRightPack
  injection innerRightPack with genPrefixEquation genSuffixEquation
  refine ⟨inertPrefix, leftContextEquation.symm, ?_, inertLength⟩
  rw [← inertComposes, ← genComposes, genPrefixEquation, genSuffixEquation]

/-! ## Non-vacuity — the equal-length-DISTINCT-word class, handled correctly on a chained spine -/

/-- ★ **The engine handles the equal-length-DISTINCT-word config on a word-chained spine.**  The lower cup
`η : id_base ⇒ F·G` (produced window `F·G`) directly followed by the upper counit `ε' : H·G ⇒ id_base`
(consumed window `H·G`), both at the mode `base` and both windows of length `2`, but `F·G ≠ H·G` (distinct
colours).  This pair is genuinely word-chained (its shared boundary word is `F·G·H·G`), and the word-indexed
factorization produces the empty inert path (`windowGap = 0`) with both context decompositions — the config
where length-rigidity (`adjunctionPath_eq_of_length_eq`) would UNSOUNDLY equate `F·G` with `H·G`.  The engine
never touches length-rigidity: it factors through the genuinely-holding shared word instead. -/
theorem stringDisjointWordFactorization_equalLengthDistinctWord :
    ∃ inertPath : ModalityPath adjointTripleGraph AdjointTripleMode.base AdjointTripleMode.base,
      (stringFG : ModalityPath adjointTripleGraph AdjointTripleMode.base AdjointTripleMode.base)
          = composePath (composePath
              (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base) stringFG) inertPath
        ∧ (stringHG : ModalityPath adjointTripleGraph AdjointTripleMode.base AdjointTripleMode.base)
          = composePath inertPath
              (composePath stringHG
                (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base))
        ∧ inertPath.length = 0 := by
  -- the two atoms: the lower cup then the upper counit, sharing the boundary word `F·G·H·G`.
  let cupAtom : SpineAtom adjointTripleModeSignature AdjointTripleMode.base AdjointTripleMode.base :=
    ⟨AdjointTripleMode.base, AdjointTripleMode.base,
      ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base,
      ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base, stringFG,
      StringTwoCell.unitLower, stringHG⟩
  let capAtom : SpineAtom adjointTripleModeSignature AdjointTripleMode.base AdjointTripleMode.base :=
    ⟨AdjointTripleMode.base, AdjointTripleMode.base, stringFG, stringHG,
      ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base,
      StringTwoCell.counitUpper,
      ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base⟩
  -- the pair is word-chained from the cup's source boundary word `H·G`.
  have chained : SpineBoundaryWordChained (signature := adjointTripleModeSignature) stringHG
      [cupAtom, capAtom] :=
    SpineBoundaryWordChained.cons cupAtom rfl
      (SpineBoundaryWordChained.cons capAtom rfl (SpineBoundaryWordChained.nil _))
  have sharedWord := spineBoundaryWordChained_pairSharedWord chained
  obtain ⟨inertPath, leftFactor, rightFactor, inertLength⟩ :=
    spineAtom_contextsFactor_of_disjointWordWindows cupAtom capAtom sharedWord 0 rfl
  exact ⟨inertPath, leftFactor, rightFactor, inertLength⟩

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the WORD-indexed disjoint-window whisker factorization is machine-checked (FC-3 r4, B1).**
`spineAtom_contextsFactor_of_disjointWordWindows` re-derives the walking-adjunction factorization keyed on the
shared boundary WORD (`spineBoundaryWordChained_pairSharedWord` extracts it from the r2 word chain) instead of
seed length-rigidity: every split piece is pinned by `composePath_splitPackEqOfPrefixLengthEq` on the one fixed
shared word.  Signature-GENERIC — it runs at the walking adjoint triple where `stringFG ≠ stringHG` makes
`adjunctionPath_eq_of_length_eq` FALSE.  Non-vacuity: `stringDisjointWordFactorization_equalLengthDistinctWord`
handles the equal-length-DISTINCT-word config `(η : F·G, ε' : H·G)` on a genuinely word-chained spine — the
exact class the length-rigid engine could not touch.  `= true`. -/
def fxString_hasDisjointWordFactorization : Bool := true

end FX1Poly.Polygraph
