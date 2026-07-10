import FX1Poly.Polygraph.TwoCategory.WalkingString.StringDisjointWordFactorization
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.AtomicSwap

/-! # WalkingString/StringDisjointWordLeftMirror — the LEFT-of WORD-indexed disjoint-window factorization + reversed
swap (FC-3 r5, B3)

The r4 word engine (`StringDisjointWordFactorization` / `StringDisjointWordSwap` / `StringDisjointWordBubble`)
ships only the RIGHT-of bubbling direction: `spineAtom_contextsFactor_of_disjointWordWindows` splits the FIRST
atom's RIGHT context (the second window a gap to the RIGHT).  The walking-adjunction engine has BOTH directions
(`ArcBubbleToFront` carries `stepRightOf` and `stepLeftOf`); the LEFT-of word substrate was un-ported.  This file
ships it, the word analogue of `WalkingAdjunction/DisjointWindowFactorization`'s
`adjunctionSpineAtom_contextsFactorLeft_of_disjointWindows` and `DisjointWindowSwap`'s
`adjunctionSpineAtomSwapLeft_of_disjointWindows`, riding the SAME handedness-agnostic shared word
(`spineBoundaryWordChained_pairSharedWord` — the chain threads both endpoints symmetrically, §2 of the recon).

  * `spineAtom_contextsFactorLeft_of_disjointWordWindows` — ★ the LEFT-of factorization: the second atom's SOURCE
    window lies a `windowGap` to the LEFT of the first atom's zone, so the first's LEFT context factors as the
    second's window then the inert zone (`lc1 = (lc2 · dom2) · inert`), and the second's RIGHT context as that
    inert zone then the first's produced window (`rc2 = inert · (cod1 · rc1)`).  Proved by ONE `splitPathAt` of
    the first's left context and ONE `composePath_splitPackEqOfPrefixLengthEq` on the shared word — subsuming both
    the parallel-path and mode-target rigidity the length-rigid adjunction original needed two lemmas for.
    Signature-GENERIC, so it runs at the walking adjoint triple where length-rigidity is FALSE.  This is the
    LEFT word factorization the COMMUTE producer's LEFT half (C3/C4) rides.
  * `spineAtomSwapLeft_of_disjointWordWindows` / `spineAtomSwapLeft_of_wordFactorization` — ★ the REVERSED swap:
    the moved pair is the swap's SOURCE and the original pair its TARGET (the spatially-left atom seats at
    slot 0), consumed via `AtomicTraceEquiv.symm`.  Mirror of `adjunctionSpineAtomSwapLeft_of_disjointWindows` and
    `CommutePairDataLeft.swapStep`; the reversed seating is the only subtlety, already solved on the adjunction
    side.  The consuming form takes the factorization directly (for the bubble driver — no path identification).

Non-vacuity (`stringDisjointWordLeftMirror_equalLengthDistinctWord`) fires the LEFT factorization on the
equal-length-DISTINCT-word `(η : F·G, ε' : H·G)` config on a word-chained spine — the class the length-rigid
engine could not run.

What this file does NOT ship (honest residual, the recon's node-1 remainder): the LEFT chain-preservation
(`spineBoundaryWordChained_swappedPairLeft`) and the LEFT bubble inductive (`WordBubblesToFront.stepLeftOf`) — the
Piece-II SORT-assembly material (a later round).  This file ships the round-critical LEFT factorization that
un-gates the COMMUTE-left producer, plus the reversed swap it seats.

Raw Lean 4 + Init; the factorization is one `splitPathAt` + one split-pack on the shared word, the swap is one
`composePath_assoc` bridge.  `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free;
per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- Left-cancellation for `Nat` addition, hand-rolled propext-free (core `Nat.add_left_cancel` leaks propext). -/
private theorem natAddLeftCancelLeftMirror (base : Nat) :
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

/-! ## The LEFT-of word-indexed disjoint-window factorization -/

/-- ★ **LEFT-of word-indexed disjoint-window whisker factorization.**  For two atoms whose boundary words chain
(`sharedWord`) with the second's SOURCE window a `windowGap` to the LEFT of the first's produced window, there is
an inert middle path such that (i) the first atom's LEFT context is the second atom's window (left context, then
source 1-cell), then the inert zone; (ii) the second atom's RIGHT context is the inert zone, the first
generator's target 1-cell, then the first atom's right context; (iii) the inert zone's length is exactly the gap.
Signature-GENERIC: every pin falls to `composePath_splitPackEqOfPrefixLengthEq` on `sharedWord` (length-split
determinacy of ONE fixed word), NOT parallel-path length-rigidity.  The LEFT mirror of the r4
`spineAtom_contextsFactor_of_disjointWordWindows`; ONE split-pack suffices (the left split aligns the window
prefix directly). -/
theorem spineAtom_contextsFactorLeft_of_disjointWordWindows {signature : ModeSignature}
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
    ∃ inertPath : ModalityPath signature.graph atomSecond.rightMidMode atomFirst.leftMidMode,
      atomFirst.leftContext
          = composePath (composePath atomSecond.leftContext atomSecond.generatorDom) inertPath
        ∧ atomSecond.rightContext
          = composePath inertPath (composePath atomFirst.generatorCod atomFirst.rightContext)
        ∧ inertPath.length = windowGap := by
  obtain ⟨leftMidA, rightMidA, leftContextA, generatorDomA, generatorCodA, generatorA,
    rightContextA⟩ := atomFirst
  obtain ⟨leftMidB, rightMidB, leftContextB, generatorDomB, generatorCodB, generatorB,
    rightContextB⟩ := atomSecond
  dsimp only at sharedWord windowsDisjoint ⊢
  have windowInRange : leftContextB.length + generatorDomB.length ≤ leftContextA.length :=
    windowsDisjoint ▸ Nat.le_add_right (leftContextB.length + generatorDomB.length) windowGap
  obtain ⟨splitMiddle, windowPrefix, inertPath, splitComposes, prefixLengthMatches⟩ :=
    splitPathAt leftContextA (leftContextB.length + generatorDomB.length) windowInRange
  have inertLength : inertPath.length = windowGap := by
    have composedLengths := congrArg ModalityPath.length splitComposes
    rw [ModalityPath.length_composePath, prefixLengthMatches, ← windowsDisjoint] at composedLengths
    exact natAddLeftCancelLeftMirror _ composedLengths
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
  refine ⟨inertPath, ?_, rightContextEquation.symm, inertLength⟩
  rw [← splitComposes, windowPrefixEqual]

/-! ## The reversed WORD-indexed swap -/

/-- ★ **The REVERSED word-indexed disjoint-window swap.**  Adjacent atoms whose boundary words chain
(`sharedWord`) with the second's window a `windowGap` to the LEFT of the first's transpose by a genuine
`SpineAtomSwap` whose SOURCE is the moved pair and whose TARGET is the original pair (the spatially-left atom
seats at slot 0).  The LEFT factorization exhibits the constructor's whisker shape (up to one
`composePath_assoc`); the moved atoms are explicit record updates — the second atom's right context re-threads
through the first generator's SOURCE 1-cell, the first atom's left context re-threads through the second
generator's TARGET 1-cell.  Consumed by the peel through `AtomicTraceEquiv.symm`. -/
theorem spineAtomSwapLeft_of_disjointWordWindows {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    (atomFirst atomSecond : SpineAtom signature overallSource overallTarget)
    (rest : List (SpineAtom signature overallSource overallTarget))
    (sharedWord :
      composePath atomFirst.leftContext (composePath atomFirst.generatorCod atomFirst.rightContext)
        = composePath atomSecond.leftContext
            (composePath atomSecond.generatorDom atomSecond.rightContext))
    (windowGap : Nat)
    (windowsDisjoint :
      atomSecond.leftContext.length + atomSecond.generatorDom.length + windowGap
        = atomFirst.leftContext.length) :
    ∃ inertPath : ModalityPath signature.graph atomSecond.rightMidMode atomFirst.leftMidMode,
      inertPath.length = windowGap
        ∧ SpineAtomSwap signature
            ({ atomSecond with
                rightContext :=
                  composePath (composePath inertPath atomFirst.generatorDom) atomFirst.rightContext }
              :: { atomFirst with
                    leftContext :=
                      composePath (composePath atomSecond.leftContext atomSecond.generatorCod)
                        inertPath }
              :: rest)
            (atomFirst :: atomSecond :: rest) := by
  obtain ⟨inertPath, leftFactor, rightFactor, inertLength⟩ :=
    spineAtom_contextsFactorLeft_of_disjointWordWindows atomFirst atomSecond sharedWord windowGap
      windowsDisjoint
  refine ⟨inertPath, inertLength, ?_⟩
  obtain ⟨leftMidA, rightMidA, leftContextA, generatorDomA, generatorCodA, generatorA,
    rightContextA⟩ := atomFirst
  obtain ⟨leftMidB, rightMidB, leftContextB, generatorDomB, generatorCodB, generatorB,
    rightContextB⟩ := atomSecond
  dsimp only at leftFactor rightFactor ⊢
  rw [leftFactor, rightFactor, ← composePath_assoc inertPath generatorCodA rightContextA]
  exact SpineAtomSwap.swap generatorB generatorA leftContextB inertPath rightContextA rest

/-- ★ **The consuming reversed word swap.**  Given a LEFT factorization already in hand (an `inertPath` with
`leftFactor` and `rightFactor`), the pair transposes by the reversed `SpineAtomSwap` directly — no `windowGap`,
no `sharedWord`, no existential path, hence no identification of a produced path with a carried one (the
mitigation for the adjunction-side bubble identifications).  The body is the tail of
`spineAtomSwapLeft_of_disjointWordWindows` with the factorization taken as input — the LEFT analogue of
`spineAtomSwap_of_wordFactorization`, for the LEFT bubble driver. -/
theorem spineAtomSwapLeft_of_wordFactorization {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    (atomFirst atomSecond : SpineAtom signature overallSource overallTarget)
    (rest : List (SpineAtom signature overallSource overallTarget))
    (inertPath : ModalityPath signature.graph atomSecond.rightMidMode atomFirst.leftMidMode)
    (leftFactor :
      atomFirst.leftContext
        = composePath (composePath atomSecond.leftContext atomSecond.generatorDom) inertPath)
    (rightFactor :
      atomSecond.rightContext
        = composePath inertPath (composePath atomFirst.generatorCod atomFirst.rightContext)) :
    SpineAtomSwap signature
      ({ atomSecond with
          rightContext :=
            composePath (composePath inertPath atomFirst.generatorDom) atomFirst.rightContext }
        :: { atomFirst with
              leftContext :=
                composePath (composePath atomSecond.leftContext atomSecond.generatorCod) inertPath }
        :: rest)
      (atomFirst :: atomSecond :: rest) := by
  obtain ⟨leftMidA, rightMidA, leftContextA, generatorDomA, generatorCodA, generatorA,
    rightContextA⟩ := atomFirst
  obtain ⟨leftMidB, rightMidB, leftContextB, generatorDomB, generatorCodB, generatorB,
    rightContextB⟩ := atomSecond
  dsimp only at leftFactor rightFactor ⊢
  rw [leftFactor, rightFactor, ← composePath_assoc inertPath generatorCodA rightContextA]
  exact SpineAtomSwap.swap generatorB generatorA leftContextB inertPath rightContextA rest

/-! ## Non-vacuity — the LEFT factorization on the equal-length-DISTINCT-word class -/

/-- ★ **The LEFT factorization handles the equal-length-DISTINCT-word config.**  The lower unit `η : id_base ⇒
F·G` (produced window `F·G`) firing at left context `H·G`, whose TARGET word `H·G·F·G` is the SOURCE word of the
upper counit `ε' : H·G ⇒ id_base` sitting at the FRONT (left context `id_base`, window `H·G`, right context
`F·G`) — the second window `H·G` lies entirely to the LEFT (a `windowGap = 0`) of the first's produced `F·G`.
The LEFT factorization produces the empty inert path with both context decompositions — the equal-length
DISTINCT-word class (`F·G ≠ H·G`) the length-rigid engine could not run. -/
theorem stringDisjointWordLeftMirror_equalLengthDistinctWord :
    ∃ inertPath : ModalityPath adjointTripleGraph AdjointTripleMode.base AdjointTripleMode.base,
      (stringHG : ModalityPath adjointTripleGraph AdjointTripleMode.base AdjointTripleMode.base)
          = composePath (composePath
              (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base) stringHG) inertPath
        ∧ (stringFG : ModalityPath adjointTripleGraph AdjointTripleMode.base AdjointTripleMode.base)
          = composePath inertPath
              (composePath stringFG
                (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base))
        ∧ inertPath.length = 0 := by
  let unitAtom : SpineAtom adjointTripleModeSignature AdjointTripleMode.base AdjointTripleMode.base :=
    ⟨AdjointTripleMode.base, AdjointTripleMode.base, stringHG,
      ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base, stringFG,
      StringTwoCell.unitLower,
      ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base⟩
  let counitAtom : SpineAtom adjointTripleModeSignature AdjointTripleMode.base AdjointTripleMode.base :=
    ⟨AdjointTripleMode.base, AdjointTripleMode.base,
      ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base, stringHG,
      ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base,
      StringTwoCell.counitUpper, stringFG⟩
  obtain ⟨inertPath, leftFactor, rightFactor, inertLength⟩ :=
    spineAtom_contextsFactorLeft_of_disjointWordWindows unitAtom counitAtom rfl 0 rfl
  exact ⟨inertPath, leftFactor, rightFactor, inertLength⟩

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the LEFT-of WORD-indexed disjoint-window factorization + reversed swap are machine-checked
(FC-3 r5, B3).**  `spineAtom_contextsFactorLeft_of_disjointWordWindows` re-derives the walking-adjunction LEFT
factorization keyed on the shared boundary WORD (the same handedness-agnostic `(*)` the right-of engine used):
ONE `splitPathAt` of the first atom's LEFT context plus ONE `composePath_splitPackEqOfPrefixLengthEq` on the
shared word pins `lc1 = (lc2 · dom2) · inert` and `rc2 = inert · (cod1 · rc1)`, subsuming both rigidity lemmas.
`spineAtomSwapLeft_of_disjointWordWindows` / `spineAtomSwapLeft_of_wordFactorization` seat the REVERSED swap (moved
pair as SOURCE, original as TARGET), consumed via `AtomicTraceEquiv.symm`.  Signature-GENERIC, so it runs at the
walking adjoint triple where length-rigidity is FALSE.  Non-vacuity
`stringDisjointWordLeftMirror_equalLengthDistinctWord` fires the LEFT factorization on the equal-length
DISTINCT-word `(η : F·G, ε' : H·G)` config.  This is the LEFT word factorization the COMMUTE-left producer (C3/C4)
rides.

  What this marker does NOT close (honest residual): the LEFT chain-preservation
  (`spineBoundaryWordChained_swappedPairLeft`) and the LEFT bubble inductive (`WordBubblesToFront.stepLeftOf`) —
  the Piece-II SORT-assembly material for a later round.  `fxString_hasAdjointTripleCompleteness` stays `false`.
  `= true`. -/
def fxString_hasDisjointWordLeftMirror : Bool := true

end FX1Poly.Polygraph
