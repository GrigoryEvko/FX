import FX1Poly.Polygraph.TwoCategory.WalkingString.StringPositiveMidChordShift
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringPositiveMidSnakeExclusion
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringEmptyMidSurvivorIdentity
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringDisjointWordSwap
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringDisjointWordBubble
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringWordChainSwapLeft
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringWordChainAppend
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringSpineTopWordSwapInvariant
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringLastCupSharedTopPin
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.MatchingSwapPeel

/-! # WalkingString/StringPositiveMidLocateAux — the positive-mid fueled partner-LOCATE (FC-3 r45, R3)

The width-`0` fueled partner-LOCATE `stringMatchingLocateAux` (`StringWidthZeroPureCupSort`, r17) bubbles the
cup whose short chord sits at `targetWindow` to the spine's tail, threading BOTH the length chain and the
boundary-WORD chain, over `matchingOfSpineList 0`.  The positive-mid pure-cup determinacy brick
`StringPositiveMidPureCupDeterminacy` (`StringPositiveMidCupSortResidual`) drives its SORT off
`matchingOfSpineList midWidth` (the through-strand survivor count), so it needs the SAME fueled locate at the
`midWidth` bottom boundary.  This file ships that positive-mid locate.

It is the width-`0` locate re-parameterized `0 ⤳ midWidth`, riding the positive-mid LOCATE bricks already
built:

  * the chord-shift descents `stringMatchingChordShift_below/above_mid` (R1) for the below/above trichotomy;
  * the last-cup short-chord readoff `stringMatchingLastCup_isShortChord_mid` (r44 P2b) — no `0 + · = ·`
    reconciliation, the read lands at the genuine offset `midWidth + w`;
  * the snake exclusion `stringMatchingForwardChordsNotAdjacent_mid` (r43 P2a) — the ONE place `0 < midWidth`
    genuinely enters the locate (via the positive-boundary involution) — and the cup-end split
    `stringMatchingOpenWiresCupEndSplit_mid`;
  * the BASE FLOOR: the empty-mid matching survivor identity `emptyMidMatching_noForwardChord` (r44 P2c) —
    the empty spine's survivor top ports point BELOW `midWidth`, never forward, so the locate terminates
    honestly (no phantom forward chord to peel).  Where the width-`0` empty partner list is literally `[]`,
    the empty-mid partner is the survivor identity `[midWidth..2·midWidth]`; the refutation handles both the
    in-range survivor read (P2c) and the out-of-range fallback read.

The matching-invariance peel `extractDiagram_eq_of_atomicPureCupTraceEquiv` is `{signature}`-generic (fired at
`⟨List.range midWidth, …⟩ midWidth midWidth`, the seed's `nextFresh = midWidth` giving `Nat.le_refl`).  The
WORD-chain threading (swaps, shared-cod pin, `spineBoundaryWordChained_swappedPair{,Left}`, `_append`,
`spineListTopWord_atomicTraceEquiv`) is seed-INDEPENDENT — copied verbatim, the word chain never reads the
seed width.  Colour-blind throughout.

Raw Lean 4 + Init; structural / fuel recursion (fuel `Nat` per the list-length source recursion, the r17
template), no `omega` / `simp`-AC / `WellFounded.fix`.  `propext`/`Quot.sound`/`Classical`/`sorry`/
`native_decide`/`omega`-free; per-declaration `#assert_no_axioms` gated in the audit twin, `#print axioms` in
the independent witness. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private plumbing (per-file copies, following the codebase pattern) -/

private theorem listNilOrSnoc {carrier : Type _} :
    (list : List carrier) → list = [] ∨ ∃ prefixAtoms lastAtom, list = prefixAtoms ++ [lastAtom]
  | [] => Or.inl rfl
  | headAtom :: restAtoms =>
      match listNilOrSnoc restAtoms with
      | Or.inl restNil => Or.inr ⟨[], headAtom, by subst restNil; rfl⟩
      | Or.inr ⟨prefixAtoms, lastAtom, restSnoc⟩ =>
          Or.inr ⟨headAtom :: prefixAtoms, lastAtom, by subst restSnoc; rfl⟩

private theorem lengthSnoc {carrier : Type _} :
    (prefixAtoms : List carrier) → (lastAtom : carrier) →
    (prefixAtoms ++ [lastAtom]).length = prefixAtoms.length + 1
  | [], _ => rfl
  | _ :: restAtoms, lastAtom => congrArg Nat.succ (lengthSnoc restAtoms lastAtom)

private theorem snocSnocRegroup {carrier : Type _} :
    (xs : List carrier) → (firstAtom secondAtom : carrier) →
    (xs ++ [firstAtom]) ++ [secondAtom] = xs ++ [firstAtom, secondAtom]
  | [], _, _ => rfl
  | headAtom :: restAtoms, firstAtom, secondAtom =>
      congrArg (headAtom :: ·) (snocSnocRegroup restAtoms firstAtom secondAtom)

private theorem natAddSubCancel (baseValue : Nat) : (subtracted : Nat) →
    baseValue + subtracted - subtracted = baseValue
  | 0 => rfl
  | subtracted + 1 => by
      rw [Nat.add_succ, Nat.succ_sub_succ]
      exact natAddSubCancel baseValue subtracted

private theorem rangeLoopLength : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      have inner := rangeLoopLength count (count :: accumulated)
      show (List.range.loop count (count :: accumulated)).length = count + 1 + accumulated.length
      rw [inner]
      show count + (accumulated.length + 1) = count + 1 + accumulated.length
      rw [← Nat.add_assoc count accumulated.length 1, Nat.add_right_comm count accumulated.length 1]

private theorem rangeLength (count : Nat) : (List.range count).length = count := by
  show (List.range.loop count []).length = count
  rw [rangeLoopLength count []]; exact Nat.add_zero count

private theorem natListGetAt_zeroOfGe :
    (list : List Nat) → (index : Nat) → list.length ≤ index → natListGetAt list index = 0
  | [], _, _ => rfl
  | _ :: _, 0, atLeast => absurd atLeast (Nat.not_succ_le_zero _)
  | _ :: rest, index + 1, atLeast =>
      natListGetAt_zeroOfGe rest index (Nat.le_of_succ_le_succ atLeast)

/-- The partner list has length `midWidth + openWires` (per-file copy at the positive-mid seed). -/
private theorem extractDiagram_partner_length_mid (midWidth : Nat) (state : WireState) :
    (extractDiagram midWidth state).partner.length = midWidth + state.openWires.length := by
  show ((List.range (midWidth + state.openWires.length)).map
      (partnerIndexOf state.links (List.range midWidth ++ state.openWires)
        (midWidth + state.openWires.length))).length = midWidth + state.openWires.length
  rw [mapLength, rangeLength]

/-- A non-empty spine's top word is its LAST atom's cod boundary word (generic, seed-independent). -/
private theorem spineListTopWord_snoc {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (bottomWord : ModalityPath signature.graph sourceMode targetMode)
    (prefixAtoms : List (SpineAtom signature sourceMode targetMode))
    (lastAtom : SpineAtom signature sourceMode targetMode) :
    spineListTopWord bottomWord (prefixAtoms ++ [lastAtom])
      = composePath lastAtom.leftContext (composePath lastAtom.generatorCod lastAtom.rightContext) := by
  rw [spineListTopWord_append bottomWord prefixAtoms [lastAtom]]
  dsimp only [spineListTopWord]

/-- The empty pure-cup string spine over a POSITIVE mid-width bottom boundary has NO forward chord on the
survivor region: the survivor top port `midWidth + targetWindow` points strictly BELOW `midWidth`
(`emptyMidMatching_noForwardChord`, r44 P2c) when `targetWindow < midWidth`, and out of range the read is the
`0` fallback — so no forward chord can hold.  The positive-mid base-floor refutation the fueled locate
terminates on (the survivor-identity analogue of the width-`0` `emptyMatchingNoForwardChordCopy`). -/
private theorem stringEmptyMidNoForwardChordCopy
    {overallSource overallTarget : adjointTripleGraph.Mode} (midWidth targetWindow : Nat)
    (chordAt : natListGetAt
        (matchingOfSpineList midWidth
          ([] : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))).partner
        (midWidth + targetWindow)
      = midWidth + targetWindow + 1) : False := by
  rcases Nat.lt_or_ge targetWindow midWidth with below | atLeast
  · exact emptyMidMatching_noForwardChord below chordAt
  · have lenEq : (matchingOfSpineList midWidth
        ([] : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))).partner.length
        = midWidth + midWidth := by
      show (extractDiagram midWidth ⟨List.range midWidth, [], midWidth, 0⟩).partner.length = midWidth + midWidth
      rw [extractDiagram_partner_length_mid midWidth ⟨List.range midWidth, [], midWidth, 0⟩]
      show midWidth + (List.range midWidth).length = midWidth + midWidth
      rw [rangeLength]
    have outRange : (matchingOfSpineList midWidth
        ([] : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))).partner.length
        ≤ midWidth + targetWindow := by
      rw [lenEq]; exact Nat.add_le_add_left atLeast midWidth
    rw [natListGetAt_zeroOfGe _ _ outRange] at chordAt
    exact Nat.noConfusion chordAt

/-! ### `stringMatchingLocateAuxMid` — bubble the target cup to the spine's tail, threading BOTH the length
chain and the WORD chain, at the positive-mid seed -/

private theorem stringMatchingLocateAuxFueledMid
    {overallSource overallTarget : adjointTripleGraph.Mode} :
    (midWidth : Nat) →
    (midPos : 0 < midWidth) →
    (fuel : Nat) →
    (bottomWord : ModalityPath adjointTripleGraph overallSource overallTarget) →
    (spine : List (SpineAtom adjointTripleModeSignature overallSource overallTarget)) →
    spine.length ≤ fuel →
    SpineBoundaryChained midWidth spine →
    SpineBoundaryWordChained bottomWord spine →
    AllCupArity spine →
    (targetWindow : Nat) →
    natListGetAt (matchingOfSpineList midWidth spine).partner (midWidth + targetWindow)
      = midWidth + targetWindow + 1 →
    ∃ movedPrefix backCup,
      AtomicTraceEquiv adjointTripleModeSignature spine (movedPrefix ++ [backCup])
        ∧ matchingOfSpineList midWidth spine = matchingOfSpineList midWidth (movedPrefix ++ [backCup])
        ∧ AllCupArity (movedPrefix ++ [backCup])
        ∧ SpineBoundaryChained midWidth (movedPrefix ++ [backCup])
        ∧ SpineBoundaryWordChained bottomWord (movedPrefix ++ [backCup])
        ∧ backCup.leftContext.length = targetWindow
  | midWidth, _, 0, _, spine, lengthBound, _, _, _, targetWindow, chordAt => by
      cases listNilOrSnoc spine with
      | inl spineNil => subst spineNil
                        exact (stringEmptyMidNoForwardChordCopy midWidth targetWindow chordAt).elim
      | inr snocWit =>
          obtain ⟨t, Clast, spineSnoc⟩ := snocWit
          subst spineSnoc
          rw [lengthSnoc] at lengthBound
          exact absurd lengthBound (Nat.not_succ_le_zero _)
  | midWidth, midPos, fuel + 1, bottomWord, spine, lengthBound, chained, wordChained, pureCup, targetWindow, chordAt => by
      cases listNilOrSnoc spine with
      | inl spineNil => subst spineNil
                        exact (stringEmptyMidNoForwardChordCopy midWidth targetWindow chordAt).elim
      | inr snocWit =>
      obtain ⟨t, Clast, spineSnoc⟩ := snocWit
      subst spineSnoc
      have tLenBound : t.length ≤ fuel := by
        rw [lengthSnoc] at lengthBound; exact Nat.le_of_succ_le_succ lengthBound
      have prefixChained : SpineBoundaryChained midWidth t :=
        spineBoundaryChained_prefix_ofAppend t [Clast] midWidth chained
      have tPure : AllCupArity t := allCupArity_prefix_ofAppend t [Clast] pureCup
      have prefixWordChained : SpineBoundaryWordChained bottomWord t :=
        spineBoundaryWordChained_prefix_ofAppend bottomWord t [Clast] wordChained
      have clastChord := stringMatchingLastCup_isShortChord_mid midWidth t Clast chained pureCup
      obtain ⟨clastDom, clastCod⟩ := allCupArity_lastCup_arity t Clast pureCup
      have owSplit := stringMatchingOpenWiresCupEndSplit_mid midWidth t Clast pureCup
      have windowFits : Clast.leftContext.length
          ≤ (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ t).openWires.length := by
        rw [stringProcessSpine_prefix_openWires_eq_lastDomBoundary midWidth t Clast chained]
        show Clast.leftContext.length
          ≤ Clast.leftContext.length + Clast.generatorDom.length + Clast.rightContext.length
        exact Nat.le_trans (Nat.le_add_right Clast.leftContext.length Clast.generatorDom.length)
          (Nat.le_add_right (Clast.leftContext.length + Clast.generatorDom.length)
            Clast.rightContext.length)
      rcases Nat.lt_trichotomy targetWindow Clast.leftContext.length with below | middle | aboveW
      · -- (ii) targetWindow < wlast : the target sits below the last cup's window
        have wlastGe : targetWindow + 2 ≤ Clast.leftContext.length := by
          rcases Nat.lt_or_ge (targetWindow + 1) Clast.leftContext.length with hlt | hge
          · exact hlt
          · exfalso
            have snakeEq : targetWindow + 1 = Clast.leftContext.length := Nat.le_antisymm below hge
            have lowInRange : midWidth + targetWindow
                < midWidth + (matchingOfSpineList midWidth (t ++ [Clast])).topCount := by
              show midWidth + targetWindow
                < midWidth + (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ (t ++ [Clast])).openWires.length
              rw [owSplit]
              exact Nat.add_lt_add_left
                (Nat.lt_of_lt_of_le below (Nat.le_trans windowFits (Nat.le_add_right _ 2))) midWidth
            have chordHigh : natListGetAt
                (matchingOfSpineList midWidth (t ++ [Clast])).partner (midWidth + (targetWindow + 1))
              = midWidth + (targetWindow + 1) + 1 := by rw [snakeEq]; exact clastChord
            exact stringMatchingForwardChordsNotAdjacent_mid midWidth midPos (t ++ [Clast]) chained pureCup
              targetWindow lowInRange chordAt chordHigh
        have chordInT := stringMatchingChordShift_below_mid midWidth t Clast chained pureCup targetWindow below chordAt
        obtain ⟨pre', Csigma, atomicEquivT, _matchEqT, pureT', _chainedT', wordChainedT', sigWindow⟩ :=
          stringMatchingLocateAuxFueledMid midWidth midPos fuel bottomWord t tLenBound prefixChained
            prefixWordChained tPure targetWindow chordInT
        obtain ⟨_sigDom, sigCod⟩ := allCupArity_lastCup_arity pre' Csigma pureT'
        obtain ⟨windowGap, gapSpec⟩ := Nat.le.dest wlastGe
        have clastDomIsTop : spineListTopWord bottomWord t
            = composePath Clast.leftContext (composePath Clast.generatorDom Clast.rightContext) :=
          spineListTopWord_prefix_eq_lastDomWord bottomWord t Clast wordChained
        have sigmaCodIsTop : spineListTopWord bottomWord (pre' ++ [Csigma])
            = composePath Csigma.leftContext (composePath Csigma.generatorCod Csigma.rightContext) :=
          spineListTopWord_snoc bottomWord pre' Csigma
        have topInvariance : spineListTopWord bottomWord t
            = spineListTopWord bottomWord (pre' ++ [Csigma]) :=
          spineListTopWord_atomicTraceEquiv atomicEquivT bottomWord
        have sharedWord :
            composePath Csigma.leftContext (composePath Csigma.generatorCod Csigma.rightContext)
              = composePath Clast.leftContext (composePath Clast.generatorDom Clast.rightContext) :=
          sigmaCodIsTop.symm.trans (topInvariance.symm.trans clastDomIsTop)
        have preWordChained : SpineBoundaryWordChained bottomWord pre' :=
          spineBoundaryWordChained_prefix_ofAppend bottomWord pre' [Csigma] wordChainedT'
        have sigmaFiresAtPreTop : spineListTopWord bottomWord pre'
            = composePath Csigma.leftContext (composePath Csigma.generatorDom Csigma.rightContext) :=
          spineListTopWord_prefix_eq_lastDomWord bottomWord pre' Csigma wordChainedT'
        have pairChained : SpineBoundaryWordChained (spineListTopWord bottomWord pre') [Csigma, Clast] :=
          SpineBoundaryWordChained.cons Csigma sigmaFiresAtPreTop
            (SpineBoundaryWordChained.cons Clast sharedWord (SpineBoundaryWordChained.nil _))
        have windowsDisjoint :
            Csigma.leftContext.length + Csigma.generatorCod.length + windowGap
              = Clast.leftContext.length := by rw [sigWindow, sigCod]; exact gapSpec
        obtain ⟨inertPath, leftFactor, rightFactor, _inertLen⟩ :=
          spineAtom_contextsFactor_of_disjointWordWindows Csigma Clast sharedWord windowGap
            windowsDisjoint
        have swapStep := spineAtomSwap_of_wordFactorization Csigma Clast [] inertPath leftFactor rightFactor
        have swapEquiv := AtomicTraceEquiv.ofSwap swapStep
        have movedPairChained :=
          spineBoundaryWordChained_swappedPair Csigma Clast pairChained inertPath leftFactor rightFactor
        have e1' : AtomicTraceEquiv adjointTripleModeSignature (t ++ [Clast]) (pre' ++ [Csigma, Clast]) :=
          AtomicTraceEquiv.castList rfl (snocSnocRegroup pre' Csigma Clast)
            (atomicTraceEquiv_backAppendCongr atomicEquivT Clast)
        have fullEquiv := e1'.trans (atomicTraceEquiv_prefixCongr swapEquiv pre')
        have fullEquivCasted :
            AtomicTraceEquiv adjointTripleModeSignature (t ++ [Clast])
              ((pre' ++ [{ Clast with
                    leftContext :=
                      composePath (composePath Csigma.leftContext Csigma.generatorDom) inertPath }])
                ++ [{ Csigma with
                      rightContext :=
                        composePath (composePath inertPath Clast.generatorCod) Clast.rightContext }]) :=
          AtomicTraceEquiv.castList rfl (snocSnocRegroup pre' _ _).symm fullEquiv
        refine ⟨_, _, fullEquivCasted, ?_, ?_, ?_, ?_, sigWindow⟩
        · exact extractDiagram_eq_of_atomicPureCupTraceEquiv fullEquivCasted
            ⟨List.range midWidth, [], midWidth, 0⟩ midWidth midWidth (wireStateFresh_initial midWidth)
            isUnionFindForest_nil (Nat.le_refl midWidth) (rangeLength midWidth) chained pureCup
        · exact allCupArity_preservedOfAtomicTraceEquiv fullEquivCasted pureCup
        · exact (spineBoundaryChained_iff_of_atomicTraceEquiv fullEquivCasted midWidth).mp chained
        · rw [snocSnocRegroup pre']
          exact spineBoundaryWordChained_append bottomWord pre' _ preWordChained movedPairChained
      · -- (i) targetWindow = wlast : Clast IS the target
        exact ⟨t, Clast, AtomicTraceEquiv.refl (t ++ [Clast]), rfl, pureCup, chained, wordChained,
          middle.symm⟩
      · -- (iii) targetWindow > wlast : the target sits above the last cup's window
        have targetGe : Clast.leftContext.length + 2 ≤ targetWindow := by
          rcases Nat.lt_or_ge (Clast.leftContext.length + 1) targetWindow with hlt | hge
          · exact hlt
          · exfalso
            have snakeEq : Clast.leftContext.length + 1 = targetWindow := Nat.le_antisymm aboveW hge
            have lowInRange : midWidth + Clast.leftContext.length
                < midWidth + (matchingOfSpineList midWidth (t ++ [Clast])).topCount := by
              show midWidth + Clast.leftContext.length
                < midWidth + (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ (t ++ [Clast])).openWires.length
              rw [owSplit]
              exact Nat.add_lt_add_left
                (Nat.lt_of_le_of_lt windowFits (Nat.lt_add_of_pos_right (by decide : 0 < 2))) midWidth
            have chordHigh : natListGetAt
                (matchingOfSpineList midWidth (t ++ [Clast])).partner (midWidth + (Clast.leftContext.length + 1))
              = midWidth + (Clast.leftContext.length + 1) + 1 := by rw [snakeEq]; exact chordAt
            exact stringMatchingForwardChordsNotAdjacent_mid midWidth midPos (t ++ [Clast]) chained pureCup
              Clast.leftContext.length lowInRange clastChord chordHigh
        have chordInT := stringMatchingChordShift_above_mid midWidth t Clast chained pureCup targetWindow aboveW chordAt
        obtain ⟨pre', Csigma, atomicEquivT, _matchEqT, pureT', _chainedT', wordChainedT', sigWindow⟩ :=
          stringMatchingLocateAuxFueledMid midWidth midPos fuel bottomWord t tLenBound prefixChained
            prefixWordChained tPure (targetWindow - 2) chordInT
        obtain ⟨windowGap, gapSpec⟩ := Nat.le.dest targetGe
        have clastDomIsTop : spineListTopWord bottomWord t
            = composePath Clast.leftContext (composePath Clast.generatorDom Clast.rightContext) :=
          spineListTopWord_prefix_eq_lastDomWord bottomWord t Clast wordChained
        have sigmaCodIsTop : spineListTopWord bottomWord (pre' ++ [Csigma])
            = composePath Csigma.leftContext (composePath Csigma.generatorCod Csigma.rightContext) :=
          spineListTopWord_snoc bottomWord pre' Csigma
        have topInvariance : spineListTopWord bottomWord t
            = spineListTopWord bottomWord (pre' ++ [Csigma]) :=
          spineListTopWord_atomicTraceEquiv atomicEquivT bottomWord
        have sharedWord :
            composePath Csigma.leftContext (composePath Csigma.generatorCod Csigma.rightContext)
              = composePath Clast.leftContext (composePath Clast.generatorDom Clast.rightContext) :=
          sigmaCodIsTop.symm.trans (topInvariance.symm.trans clastDomIsTop)
        have preWordChained : SpineBoundaryWordChained bottomWord pre' :=
          spineBoundaryWordChained_prefix_ofAppend bottomWord pre' [Csigma] wordChainedT'
        have sigmaFiresAtPreTop : spineListTopWord bottomWord pre'
            = composePath Csigma.leftContext (composePath Csigma.generatorDom Csigma.rightContext) :=
          spineListTopWord_prefix_eq_lastDomWord bottomWord pre' Csigma wordChainedT'
        have pairChained : SpineBoundaryWordChained (spineListTopWord bottomWord pre') [Csigma, Clast] :=
          SpineBoundaryWordChained.cons Csigma sigmaFiresAtPreTop
            (SpineBoundaryWordChained.cons Clast sharedWord (SpineBoundaryWordChained.nil _))
        have windowsDisjoint :
            Clast.leftContext.length + Clast.generatorDom.length + windowGap
              = Csigma.leftContext.length := by
          rw [clastDom, Nat.add_zero, sigWindow, ← gapSpec,
            Nat.add_right_comm Clast.leftContext.length 2 windowGap]
          exact (natAddSubCancel (Clast.leftContext.length + windowGap) 2).symm
        obtain ⟨inertPath, leftFactor, rightFactor, inertLen⟩ :=
          spineAtom_contextsFactorLeft_of_disjointWordWindows Csigma Clast sharedWord windowGap
            windowsDisjoint
        have swapStep :=
          spineAtomSwapLeft_of_wordFactorization Csigma Clast [] inertPath leftFactor rightFactor
        have swapEquiv := (AtomicTraceEquiv.ofSwap swapStep).symm
        have movedPairChained :=
          spineBoundaryWordChained_swappedPairLeft Csigma Clast pairChained inertPath leftFactor rightFactor
        have e1' : AtomicTraceEquiv adjointTripleModeSignature (t ++ [Clast]) (pre' ++ [Csigma, Clast]) :=
          AtomicTraceEquiv.castList rfl (snocSnocRegroup pre' Csigma Clast)
            (atomicTraceEquiv_backAppendCongr atomicEquivT Clast)
        have fullEquiv := e1'.trans (atomicTraceEquiv_prefixCongr swapEquiv pre')
        have fullEquivCasted :
            AtomicTraceEquiv adjointTripleModeSignature (t ++ [Clast])
              ((pre' ++ [{ Clast with
                    rightContext :=
                      composePath (composePath inertPath Csigma.generatorDom) Csigma.rightContext }])
                ++ [{ Csigma with
                      leftContext :=
                        composePath (composePath Clast.leftContext Clast.generatorCod) inertPath }]) :=
          AtomicTraceEquiv.castList rfl (snocSnocRegroup pre' _ _).symm fullEquiv
        refine ⟨_, _, fullEquivCasted, ?_, ?_, ?_, ?_, ?_⟩
        · exact extractDiagram_eq_of_atomicPureCupTraceEquiv fullEquivCasted
            ⟨List.range midWidth, [], midWidth, 0⟩ midWidth midWidth (wireStateFresh_initial midWidth)
            isUnionFindForest_nil (Nat.le_refl midWidth) (rangeLength midWidth) chained pureCup
        · exact allCupArity_preservedOfAtomicTraceEquiv fullEquivCasted pureCup
        · exact (spineBoundaryChained_iff_of_atomicTraceEquiv fullEquivCasted midWidth).mp chained
        · rw [snocSnocRegroup pre']
          exact spineBoundaryWordChained_append bottomWord pre' _ preWordChained movedPairChained
        · show (composePath (composePath Clast.leftContext Clast.generatorCod) inertPath).length
            = targetWindow
          rw [ModalityPath.length_composePath, ModalityPath.length_composePath, inertLen, clastCod]
          exact gapSpec

/-- ★ **The positive-mid location step at the adjoint-triple seed.**  In a boundary-chained AND
boundary-word-chained pure-cup spine over the `midWidth` bottom boundary (`0 < midWidth`), the cup whose short
chord sits at `targetWindow` bubbles to the tail, keeping BOTH chains and the `matchingOfSpineList midWidth`.
The positive-mid analogue of `stringMatchingLocateAux`; the `0 < midWidth` enters through the snake exclusion
`stringMatchingForwardChordsNotAdjacent_mid`. -/
theorem stringMatchingLocateAuxMid
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (midWidth : Nat) (midPos : 0 < midWidth)
    (bottomWord : ModalityPath adjointTripleGraph overallSource overallTarget)
    (spine : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained midWidth spine)
    (wordChained : SpineBoundaryWordChained bottomWord spine)
    (pureCup : AllCupArity spine)
    (targetWindow : Nat)
    (chordAt : natListGetAt (matchingOfSpineList midWidth spine).partner (midWidth + targetWindow)
      = midWidth + targetWindow + 1) :
    ∃ movedPrefix backCup,
      AtomicTraceEquiv adjointTripleModeSignature spine (movedPrefix ++ [backCup])
        ∧ matchingOfSpineList midWidth spine = matchingOfSpineList midWidth (movedPrefix ++ [backCup])
        ∧ AllCupArity (movedPrefix ++ [backCup])
        ∧ SpineBoundaryChained midWidth (movedPrefix ++ [backCup])
        ∧ SpineBoundaryWordChained bottomWord (movedPrefix ++ [backCup])
        ∧ backCup.leftContext.length = targetWindow :=
  stringMatchingLocateAuxFueledMid midWidth midPos spine.length bottomWord spine (Nat.le_refl spine.length)
    chained wordChained pureCup targetWindow chordAt

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the positive-mid fueled partner-LOCATE is built (FC-3 r45, R3).**
`stringMatchingLocateAuxMid` bubbles the target cup (by chord window) to the spine's tail over
`matchingOfSpineList midWidth`, threading BOTH the length chain and the WORD chain, riding the positive-mid
LOCATE bricks: the chord-shift descents `stringMatchingChordShift_below/above_mid` (R1), the last-cup readoff
`stringMatchingLastCup_isShortChord_mid` (P2b), the snake exclusion `stringMatchingForwardChordsNotAdjacent_mid`
(P2a, the one place `0 < midWidth` enters), the cup-end split `stringMatchingOpenWiresCupEndSplit_mid`, and
the empty-mid survivor-identity base floor `emptyMidMatching_noForwardChord` (P2c).  The matching-invariance
peel `extractDiagram_eq_of_atomicPureCupTraceEquiv` fires at `⟨List.range midWidth, …⟩ midWidth midWidth`; the
WORD-chain threading is seed-independent (verbatim).  Structural fuel recursion.

  What this marker does NOT close (no gate flag flips): the positive-mid pure-cup SORT inhabiting the brick
  `StringPositiveMidPureCupDeterminacy`.  On top of this locate the sort still needs the fueled word-threaded
  sort assembly (R4) consuming the drop-injectivity (R2).  So `fxString_hasAdjointTripleCompleteness`
  (`StringMatchingCompleteness`) / `fxString_hasConvOfMapEqPortFlip` (`StringConvOfMapEqPort`) STAY `false`,
  and the brick STAYS `def`-open.  `= true`. -/
def fxString_hasPositiveMidLocateAux : Bool := true

end FX1Poly.Polygraph
