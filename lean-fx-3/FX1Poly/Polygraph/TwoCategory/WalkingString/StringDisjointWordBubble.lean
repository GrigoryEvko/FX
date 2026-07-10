import FX1Poly.Polygraph.TwoCategory.WalkingString.StringDisjointWordSwap

/-! # WalkingString/StringDisjointWordBubble — the WORD-indexed bubble-to-front driver (FC-3 r4, B3)

The pure-block sort carries a selected target atom to the front through a prefix of atoms, one adjacent
transposition per passed atom.  This file ships that carrier at the WORD granularity, the word analogue of
`WalkingAdjunction/ArcBubbleToFront`, riding the B1/B2 engine:

  * `spineAtomSwap_of_wordFactorization` — ★ the CONSUMING swap producer: builds the `SpineAtomSwap` directly
    from a factorization (`inertPath` + `leftFactor` + `rightFactor`) already in hand, so the bubble driver
    never needs to IDENTIFY a produced inert path with a carried one.  This is the mitigation the recon named
    for the two adjunction-side bubble identifications (which used seed length-rigidity, false at the triple);
  * `WordBubblesToFront` — ★ the bubble witness (right-of direction): the target transposes leftward past each
    prefix atom, each step carrying the passed atom, the inert gap path, and the word factorization equations;
  * `atomicTraceEquiv_of_wordBubblesToFront` / `spineTraceEquiv_of_wordBubblesToFront` — ★ the witnessed bubble
    IS a trace equivalence (one consuming swap per step under the head-cons congruence);
  * `spineBoundaryWordChained_of_wordBubblesToFront` — ★ the bubbled list stays boundary-WORD-chained at the
    same running boundary word (one B2 preservation per step).

Signature-GENERIC (the B1/B2 engine is), so it runs at the walking adjoint triple.  Non-vacuity
(`stringWordBubble_equalLengthDistinctWord`) bubbles the upper counit `ε' : H·G` past the lower cup `η : F·G`
(the equal-length-DISTINCT-word class) as a genuine trace-equivalence step on a word-chained spine.

What this file does NOT ship (honest, the multi-round residual the recon names): the LEFT-of mirror direction
(needs the mirrored word factorization + preservation), the partner LOCATION that constructs the witness from
arc-structure equality, and the pure-block SORT assembly that iterates the bubble into
`StringCellValleyTraceEquiv`.  The completeness flag stays `false`.

Raw Lean 4 + Init; the bubble is one consuming swap + one B2 preservation per step, folded by induction on the
witness.  `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration
`#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The consuming swap producer -/

/-- ★ **The consuming word swap.**  Given a factorization already in hand (an `inertPath` with `leftFactor` and
`rightFactor`, the B1 output), the adjacent pair `atomFirst :: atomSecond :: rest` transposes by a genuine
`SpineAtomSwap` directly — no `windowGap`, no `sharedWord`, no existential inert path, hence NO identification
of a produced path with a carried one (the mitigation for the adjunction-side bubble identifications, which
used seed length-rigidity that is false at the triple).  Body is the tail of
`spineAtomSwap_of_disjointWordWindows` with the factorization taken as input. -/
theorem spineAtomSwap_of_wordFactorization {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    (atomFirst atomSecond : SpineAtom signature overallSource overallTarget)
    (rest : List (SpineAtom signature overallSource overallTarget))
    (inertPath : ModalityPath signature.graph atomFirst.rightMidMode atomSecond.leftMidMode)
    (leftFactor :
      atomSecond.leftContext
        = composePath (composePath atomFirst.leftContext atomFirst.generatorCod) inertPath)
    (rightFactor :
      atomFirst.rightContext
        = composePath inertPath (composePath atomSecond.generatorDom atomSecond.rightContext)) :
    SpineAtomSwap signature
      (atomFirst :: atomSecond :: rest)
      ({ atomSecond with
          leftContext :=
            composePath (composePath atomFirst.leftContext atomFirst.generatorDom) inertPath }
        :: { atomFirst with
              rightContext :=
                composePath (composePath inertPath atomSecond.generatorCod)
                  atomSecond.rightContext }
        :: rest) := by
  obtain ⟨leftMidA, rightMidA, leftContextA, generatorDomA, generatorCodA, generatorA,
    rightContextA⟩ := atomFirst
  obtain ⟨leftMidB, rightMidB, leftContextB, generatorDomB, generatorCodB, generatorB,
    rightContextB⟩ := atomSecond
  dsimp only at leftFactor rightFactor ⊢
  rw [leftFactor, rightFactor, ← composePath_assoc inertPath generatorDomB rightContextB]
  exact SpineAtomSwap.swap generatorA generatorB leftContextA inertPath rightContextB rest

/-! ## The bubble witness (right-of direction) -/

/-- ★ **The WORD bubble witness (right-of).**  `WordBubblesToFront target prefixAtoms movedTarget
movedPrefixAtoms` says the target atom transposes leftward past every atom of `prefixAtoms` (head-first),
arriving at the front as `movedTarget` and leaving the passed atoms re-threaded as `movedPrefixAtoms`.  Each
step carries the passed atom, the inert gap path, and the WORD factorization equations (`leftFactor` /
`rightFactor`, the B1 output) — the target's window sits a gap RIGHT of the passed atom's produced window, so
the moved target's left context re-threads through the passed atom's SOURCE 1-cell.  The moved atoms are the
exact record updates the consuming swap produces, so consuming the witness is one swap per step. -/
inductive WordBubblesToFront {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    (target : SpineAtom signature overallSource overallTarget) :
    List (SpineAtom signature overallSource overallTarget) →
    SpineAtom signature overallSource overallTarget →
    List (SpineAtom signature overallSource overallTarget) → Prop where
  /-- The empty prefix: the target is already at the front, untouched. -/
  | nil : WordBubblesToFront target [] target []
  /-- Pass one more atom whose produced window lies a gap LEFT of the bubbled target's window. -/
  | stepRightOf (passedAtom : SpineAtom signature overallSource overallTarget)
      {restPrefix : List (SpineAtom signature overallSource overallTarget)}
      {movedTargetOfRest : SpineAtom signature overallSource overallTarget}
      {movedRestPrefix : List (SpineAtom signature overallSource overallTarget)}
      (restWitness : WordBubblesToFront target restPrefix movedTargetOfRest movedRestPrefix)
      (inertPath : ModalityPath signature.graph
        passedAtom.rightMidMode movedTargetOfRest.leftMidMode)
      (leftFactor :
        movedTargetOfRest.leftContext
          = composePath (composePath passedAtom.leftContext passedAtom.generatorCod) inertPath)
      (rightFactor :
        passedAtom.rightContext
          = composePath inertPath
              (composePath movedTargetOfRest.generatorDom movedTargetOfRest.rightContext)) :
      WordBubblesToFront target (passedAtom :: restPrefix)
        { movedTargetOfRest with
            leftContext :=
              composePath (composePath passedAtom.leftContext passedAtom.generatorDom) inertPath }
        ({ passedAtom with
            rightContext :=
              composePath (composePath inertPath movedTargetOfRest.generatorCod)
                movedTargetOfRest.rightContext }
          :: movedRestPrefix)

/-! ## Consumption — the bubble is a trace equivalence -/

/-- ★ **The WORD bubble is an atomic trace equivalence.**  A witnessed bubble carries
`prefixAtoms ++ target :: suffixAtoms` to `movedTarget :: movedPrefixAtoms ++ suffixAtoms` inside
`AtomicTraceEquiv`: induction on the witness, each step lifting the inner bubble under the head-cons
congruence and firing ONE consuming swap (`spineAtomSwap_of_wordFactorization`) on the now-adjacent pair — no
factorization-path identification, since the swap consumes the carried inert path. -/
theorem atomicTraceEquiv_of_wordBubblesToFront {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {target movedTarget : SpineAtom signature overallSource overallTarget}
    {prefixAtoms movedPrefixAtoms : List (SpineAtom signature overallSource overallTarget)}
    (witness : WordBubblesToFront target prefixAtoms movedTarget movedPrefixAtoms)
    (suffixAtoms : List (SpineAtom signature overallSource overallTarget)) :
    AtomicTraceEquiv signature (prefixAtoms ++ target :: suffixAtoms)
      (movedTarget :: (movedPrefixAtoms ++ suffixAtoms)) := by
  induction witness with
  | nil => exact AtomicTraceEquiv.refl (target :: suffixAtoms)
  | @stepRightOf passedAtom restPrefix movedTargetOfRest movedRestPrefix restWitness inertPath
      leftFactor rightFactor restHypothesis =>
      have swapFires := spineAtomSwap_of_wordFactorization passedAtom movedTargetOfRest
        (movedRestPrefix ++ suffixAtoms) inertPath leftFactor rightFactor
      exact AtomicTraceEquiv.trans
        (AtomicTraceEquiv.consCongr passedAtom restHypothesis)
        (AtomicTraceEquiv.ofSwap swapFires)

/-- ★ **The WORD bubble is a spine trace equivalence** — the block-level closure the pure-block sort runs on,
by including the atomic bubble (`AtomicTraceEquiv.toSpineTraceEquiv`). -/
theorem spineTraceEquiv_of_wordBubblesToFront {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {target movedTarget : SpineAtom signature overallSource overallTarget}
    {prefixAtoms movedPrefixAtoms : List (SpineAtom signature overallSource overallTarget)}
    (witness : WordBubblesToFront target prefixAtoms movedTarget movedPrefixAtoms)
    (suffixAtoms : List (SpineAtom signature overallSource overallTarget)) :
    SpineTraceEquiv signature (prefixAtoms ++ target :: suffixAtoms)
      (movedTarget :: (movedPrefixAtoms ++ suffixAtoms)) :=
  (atomicTraceEquiv_of_wordBubblesToFront witness suffixAtoms).toSpineTraceEquiv

/-! ## Consumption — the bubble preserves the WORD chain -/

/-- ★ **The WORD bubble preserves the boundary-word chain.**  A witnessed bubble of a boundary-word-chained
list is boundary-word-chained at the SAME running boundary word: induction on the witness, each step
re-assembling the chain with the passed atom in front of the bubbled tail and handing the now-adjacent pair to
the B2 word-chain preservation (`spineBoundaryWordChained_swappedPair`). -/
theorem spineBoundaryWordChained_of_wordBubblesToFront {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {target movedTarget : SpineAtom signature overallSource overallTarget}
    {prefixAtoms movedPrefixAtoms : List (SpineAtom signature overallSource overallTarget)}
    (witness : WordBubblesToFront target prefixAtoms movedTarget movedPrefixAtoms)
    (suffixAtoms : List (SpineAtom signature overallSource overallTarget)) :
    ∀ {boundaryWord : ModalityPath signature.graph overallSource overallTarget},
      SpineBoundaryWordChained boundaryWord (prefixAtoms ++ target :: suffixAtoms) →
      SpineBoundaryWordChained boundaryWord (movedTarget :: (movedPrefixAtoms ++ suffixAtoms)) := by
  induction witness with
  | nil => intro boundaryWord listChained; exact listChained
  | @stepRightOf passedAtom restPrefix movedTargetOfRest movedRestPrefix restWitness inertPath
      leftFactor rightFactor restHypothesis =>
      intro boundaryWord listChained
      obtain ⟨headFires, tailChained⟩ := spineBoundaryWordChained_tail listChained
      exact spineBoundaryWordChained_swappedPair passedAtom movedTargetOfRest
        (SpineBoundaryWordChained.cons passedAtom headFires (restHypothesis tailChained))
        inertPath leftFactor rightFactor

/-! ## Non-vacuity — bubble the equal-length-DISTINCT-word pair -/

/-- ★ **The equal-length-DISTINCT-word pair bubbles as a genuine trace step.**  The upper counit
`ε' : H·G ⇒ id_base` bubbles past the lower cup `η : id_base ⇒ F·G` (windows length `2`, `F·G ≠ H·G`): a
one-step `WordBubblesToFront` whose consuming swap is a `SpineTraceEquiv`, and whose bubbled list stays
boundary-word-chained.  The factorization is the B1 output at `windowGap = 0`.  This is the composable atom the
pure-block sort iterates, discharged at the exact class the length-rigid engine could not run. -/
theorem stringWordBubble_equalLengthDistinctWord :
    ∃ (movedTarget :
          SpineAtom adjointTripleModeSignature AdjointTripleMode.base AdjointTripleMode.base)
      (movedPrefix :
          List (SpineAtom adjointTripleModeSignature AdjointTripleMode.base AdjointTripleMode.base)),
      SpineTraceEquiv adjointTripleModeSignature
          [(⟨AdjointTripleMode.base, AdjointTripleMode.base,
              ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base,
              ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base, stringFG,
              StringTwoCell.unitLower, stringHG⟩ : SpineAtom adjointTripleModeSignature
                AdjointTripleMode.base AdjointTripleMode.base),
            ⟨AdjointTripleMode.base, AdjointTripleMode.base, stringFG, stringHG,
              ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base,
              StringTwoCell.counitUpper,
              ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base⟩]
          (movedTarget :: movedPrefix)
        ∧ SpineBoundaryWordChained (signature := adjointTripleModeSignature) stringHG
            (movedTarget :: movedPrefix) := by
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
  have chained : SpineBoundaryWordChained (signature := adjointTripleModeSignature) stringHG
      [cupAtom, capAtom] :=
    SpineBoundaryWordChained.cons cupAtom rfl
      (SpineBoundaryWordChained.cons capAtom rfl (SpineBoundaryWordChained.nil _))
  have sharedWord := spineBoundaryWordChained_pairSharedWord chained
  obtain ⟨inertPath, leftFactor, rightFactor, _⟩ :=
    spineAtom_contextsFactor_of_disjointWordWindows cupAtom capAtom sharedWord 0 rfl
  -- capAtom bubbles to the front past the single-atom prefix [cupAtom].
  have witness : WordBubblesToFront (signature := adjointTripleModeSignature) capAtom [cupAtom]
      { capAtom with
          leftContext :=
            composePath (composePath cupAtom.leftContext cupAtom.generatorDom) inertPath }
      [{ cupAtom with
          rightContext :=
            composePath (composePath inertPath capAtom.generatorCod) capAtom.rightContext }] :=
    WordBubblesToFront.stepRightOf cupAtom WordBubblesToFront.nil inertPath leftFactor rightFactor
  exact ⟨_, _, spineTraceEquiv_of_wordBubblesToFront witness [],
    spineBoundaryWordChained_of_wordBubblesToFront witness [] chained⟩

/-! ## Honesty markers -/

/-- **★ ESTABLISHED — the WORD-indexed bubble-to-front driver is machine-checked (FC-3 r4, B3).**
`WordBubblesToFront` witnesses an iterated right-of disjoint-window transposition carrying a target atom to the
front; `atomicTraceEquiv_of_wordBubblesToFront` / `spineTraceEquiv_of_wordBubblesToFront` realize it inside the
trace equivalences (one CONSUMING swap `spineAtomSwap_of_wordFactorization` per step — no factorization-path
identification, the recon's mitigation for the adjunction-side length-rigidity), and
`spineBoundaryWordChained_of_wordBubblesToFront` keeps the bubbled list word-chained at the same boundary word
(one B2 preservation per step).  Signature-GENERIC, runs at the adjoint triple.  Non-vacuity
`stringWordBubble_equalLengthDistinctWord` bubbles the upper counit `ε' : H·G` past the lower cup `η : F·G` as
a genuine `SpineTraceEquiv` step on a word-chained spine.  `= true`. -/
def fxString_hasWordBubbleToFront : Bool := true

/-- **OPEN (honest) — the bubble is the CARRIER; the pure-block SORT and the LEFT-of mirror are NOT assembled;
NO completeness flip.**  On top of the right-of word bubble the sort still needs: the LEFT-of mirror direction
(the mirrored word factorization + preservation, both un-ported), the partner LOCATION that constructs the
`WordBubblesToFront` witness from arc-structure equality, and the pure-block sort assembly iterating the bubble
into `StringCellValleyTraceEquiv` (plus the valley-append `matchingOf`-split, open even at the walking
adjunction, #2186).  These are the multi-round residual the recon names; `fxString_hasAdjointTripleCompleteness`
stays `false`.  `= false`. -/
def fxString_hasWordBubbleSortAssembly : Bool := false

end FX1Poly.Polygraph
