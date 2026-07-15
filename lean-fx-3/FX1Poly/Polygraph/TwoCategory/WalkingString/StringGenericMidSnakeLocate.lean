import FX1Poly.Polygraph.TwoCategory.WalkingString.StringGenericArcCensusInvolution
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringEmptyMidSurvivorIdentity
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringDisjointWordSwap
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringDisjointWordBubble
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringDisjointWordLeftMirror
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringWordChainSwapLeft
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringWordChainAppend
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringSpineTopWordSwapInvariant
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringLastCupSharedTopPin
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringPositiveMidLocateAux
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.MatchingSwapPeel

/-! # WalkingString — the GENERIC SNAKE EXCLUSION + the ANY-WIDTH fueled partner-LOCATE
(FC-4 r7, the locate tranche of the generic cup-sort driver)

The r6 tranche markers named two of the four remaining sort-chain nodes here: the SNAKE EXCLUSION (the one node
that consumed `0 < midWidth` at `k = 2`) and the fueled LOCATE.  Both land generically over
`AdjointStringConnectivity × midWidth`, and — riding the r7 ANY-WIDTH involution
(`genericMatchingPartner_isInvolution_anyWidth`, `StringGenericArcCensusInvolution`) — the positivity premise is
GONE: one snake exclusion and ONE fueled locate cover `midWidth = 0` and `0 < midWidth` alike, subsuming both
shipped `k = 2` lanes (`matchingForwardChordsNotAdjacent` / `stringMatchingLocateAux` at width-`0`,
`stringMatchingForwardChordsNotAdjacent_mid` / `stringMatchingLocateAuxMid` at positive mid).

  * ★ `genericMatchingForwardChordsNotAdjacent_mid` — two forward chords cannot sit at adjacent windows, at ANY
    `midWidth`, over the class: they would share the endpoint `midWidth + windowLow + 1`, impossible in the
    involutive boundary matching.  The FROZEN FC-3 r43 proof with the positive involution swapped for the
    any-width dispatch.
  * ★★ `genericMatchingLocateAuxMid` — the fueled partner-LOCATE at ANY `midWidth`, over the class: the cup whose
    short chord sits at `targetWindow` bubbles to the spine's tail, keeping the length chain, the boundary-WORD
    chain, and `matchingOfSpineList midWidth` (fuel = spine length, the VFA selection-sort `select` shape:
    STRUCTURAL recursion on a `Nat` fuel, one cup peeled per step).  The FROZEN FC-3 r45 proof, verbatim modulo
    the generic hooks: the r6 short-chord readoff + chord-shift descents, the r5 B3 tracking, the generic snake
    exclusion above, and the `{signature}`-generic empty-mid base floor (`emptyMidMatching_noForwardChord` at
    `targetWindow < midWidth`, the fallback read out of range — at `midWidth = 0` the fallback covers every
    window, which is why the width-`0` locate is the same theorem).

## The HONESTY LAW — fired at `k = 2` AND `k = 3`

  * ★ `k = 2` recovery — the generic locate at `adjointStringConnectivityAtTwo` re-derives the NAMED shipped
    `stringMatchingLocateAuxMid` (`stringLocateAuxMid_shippedInhabitant` / `..._viaGenericClassAtTwo` — the
    generic form needs no `0 < midWidth`, so it inhabits the shipped statement by discarding the premise).
  * ★ `k = 3` fires — the generic locate runs on genuine adjoint-quadruple spines through BOTH regimes: the
    width-`0` two-cup spine `[η1@0, η1@2]` with target window `0` (the BELOW branch: chord-shift descent +
    recursion + the disjoint-word swap bubble the locate's moving arm exercises) and the mid-`1` single-survivor
    cup with target window `0` (the MIDDLE branch at positive width).

## What this file does NOT do (the FLIP LAW, honest round boundary)

The census marker `fxString_hasNColourAtomPinReroute` (`StringKParameterizationCensus`) STAYS `false` here: this
is the locate tranche only.  The fueled SORT DRIVER + the generic determinacy + the `k = 3` decision are the
sibling tranche (`StringGenericMidPureCupSortDriver`); the closure adjudication lives in
`StringNColourAtomPinRerouteClosure`.

ADDITIVE ONLY: no shipped WalkingString file is touched.  Raw Lean 4 + Init; structural / fuel recursion (fuel
`Nat` per the list-length source recursion, the r17 template), no `omega` / `simp`-AC / `WellFounded.fix`;
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free.  Per-declaration `#assert_no_axioms`
gated in the audit twin plus an INDEPENDENT `#print axioms` witness. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private plumbing (per-file copies with a distinct `GSL` suffix, keeping the umbrella build's global table
duplicate-free) -/

private theorem listNilOrSnocGSL {carrier : Type _} :
    (list : List carrier) → list = [] ∨ ∃ prefixAtoms lastAtom, list = prefixAtoms ++ [lastAtom]
  | [] => Or.inl rfl
  | headAtom :: restAtoms =>
      match listNilOrSnocGSL restAtoms with
      | Or.inl restNil => Or.inr ⟨[], headAtom, by subst restNil; rfl⟩
      | Or.inr ⟨prefixAtoms, lastAtom, restSnoc⟩ =>
          Or.inr ⟨headAtom :: prefixAtoms, lastAtom, by subst restSnoc; rfl⟩

private theorem lengthSnocGSL {carrier : Type _} :
    (prefixAtoms : List carrier) → (lastAtom : carrier) →
    (prefixAtoms ++ [lastAtom]).length = prefixAtoms.length + 1
  | [], _ => rfl
  | _ :: restAtoms, lastAtom => congrArg Nat.succ (lengthSnocGSL restAtoms lastAtom)

private theorem snocSnocRegroupGSL {carrier : Type _} :
    (xs : List carrier) → (firstAtom secondAtom : carrier) →
    (xs ++ [firstAtom]) ++ [secondAtom] = xs ++ [firstAtom, secondAtom]
  | [], _, _ => rfl
  | headAtom :: restAtoms, firstAtom, secondAtom =>
      congrArg (headAtom :: ·) (snocSnocRegroupGSL restAtoms firstAtom secondAtom)

private theorem natAddSubCancelGSL (baseValue : Nat) : (subtracted : Nat) →
    baseValue + subtracted - subtracted = baseValue
  | 0 => rfl
  | subtracted + 1 => by
      rw [Nat.add_succ, Nat.succ_sub_succ]
      exact natAddSubCancelGSL baseValue subtracted

private theorem rangeLoopLengthGSL : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      have inner := rangeLoopLengthGSL count (count :: accumulated)
      show (List.range.loop count (count :: accumulated)).length = count + 1 + accumulated.length
      rw [inner]
      show count + (accumulated.length + 1) = count + 1 + accumulated.length
      rw [← Nat.add_assoc count accumulated.length 1, Nat.add_right_comm count accumulated.length 1]

private theorem rangeLengthGSL (count : Nat) : (List.range count).length = count := by
  show (List.range.loop count []).length = count
  rw [rangeLoopLengthGSL count []]; exact Nat.add_zero count

private theorem natListGetAtZeroOfGeGSL :
    (list : List Nat) → (index : Nat) → list.length ≤ index → natListGetAt list index = 0
  | [], _, _ => rfl
  | _ :: _, 0, atLeast => absurd atLeast (Nat.not_succ_le_zero _)
  | _ :: rest, index + 1, atLeast =>
      natListGetAtZeroOfGeGSL rest index (Nat.le_of_succ_le_succ atLeast)

/-- The partner list has length `midWidth + openWires` (per-file copy at the `midWidth` seed). -/
private theorem extractDiagramPartnerLengthGSL (midWidth : Nat) (state : WireState) :
    (extractDiagram midWidth state).partner.length = midWidth + state.openWires.length := by
  show ((List.range (midWidth + state.openWires.length)).map
      (partnerIndexOf state.links (List.range midWidth ++ state.openWires)
        (midWidth + state.openWires.length))).length = midWidth + state.openWires.length
  rw [mapLength, rangeLengthGSL]

/-- A non-empty spine's top word is its LAST atom's cod boundary word (generic, seed-independent). -/
private theorem spineListTopWordSnocGSL {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (bottomWord : ModalityPath signature.graph sourceMode targetMode)
    (prefixAtoms : List (SpineAtom signature sourceMode targetMode))
    (lastAtom : SpineAtom signature sourceMode targetMode) :
    spineListTopWord bottomWord (prefixAtoms ++ [lastAtom])
      = composePath lastAtom.leftContext (composePath lastAtom.generatorCod lastAtom.rightContext) := by
  rw [spineListTopWord_append bottomWord prefixAtoms [lastAtom]]
  dsimp only [spineListTopWord]

/-! ## The generic snake exclusion at ANY mid-width (rides the any-width involution) -/

/-- ★ **Two forward chords cannot be adjacent, at ANY `midWidth`, over the class.**  A forward chord
`(midWidth + windowLow, +1)` and another at the NEXT window `(midWidth + windowLow + 1, +1)` share the endpoint
`midWidth + windowLow + 1`, impossible in the involutive matching: the involution sends
`midWidth + windowLow + 1` back to `midWidth + windowLow`, not forward to `midWidth + windowLow + 2`.  Rules out
the degenerate snake position in both descent directions of the location induction.  Rides the r7 ANY-WIDTH
involution `genericMatchingPartner_isInvolution_anyWidth` — the `0 < midWidth` premise of the shipped `k = 2`
positive-mid sibling is DISPATCHED AWAY (width-`0` routes through the positivity-free width-`0` involution). -/
theorem genericMatchingForwardChordsNotAdjacent_mid (cls : AdjointStringConnectivity)
    {overallSource overallTarget : cls.signature.graph.Mode}
    (midWidth : Nat)
    (spine : List (SpineAtom cls.signature overallSource overallTarget))
    (chained : SpineBoundaryChained midWidth spine)
    (pureCup : AllCupArity spine)
    (windowLow : Nat)
    (lowInRange : midWidth + windowLow < midWidth + (matchingOfSpineList midWidth spine).topCount)
    (chordLow : natListGetAt (matchingOfSpineList midWidth spine).partner (midWidth + windowLow)
      = midWidth + windowLow + 1)
    (chordHigh : natListGetAt (matchingOfSpineList midWidth spine).partner (midWidth + (windowLow + 1))
      = midWidth + (windowLow + 1) + 1) : False := by
  have notFixed : natListGetAt (matchingOfSpineList midWidth spine).partner (midWidth + windowLow)
      ≠ midWidth + windowLow := by
    rw [chordLow]; exact Nat.ne_of_gt (Nat.lt_succ_self (midWidth + windowLow))
  have inv := genericMatchingPartner_isInvolution_anyWidth cls midWidth spine chained pureCup
    (midWidth + windowLow) lowInRange notFixed
  rw [chordLow, Nat.add_assoc midWidth windowLow 1, chordHigh] at inv
  have twoZero : midWidth + windowLow + 2 = midWidth + windowLow := inv
  exact absurd twoZero (Nat.ne_of_gt (Nat.lt_add_of_pos_right (by decide : 0 < 2)))

/-! ## The empty-mid base floor (`{signature}`-generic, private per-file copy) -/

/-- The empty pure-cup spine over ANY mid-width bottom boundary has NO forward chord: for
`targetWindow < midWidth` the survivor top port points strictly BELOW `midWidth`
(`emptyMidMatching_noForwardChord`), and out of range the read is the `0` fallback.  At `midWidth = 0` the
fallback covers every window — which is why the SAME base floor serves the width-`0` locate. -/
private theorem genericEmptyMidNoForwardChordGSL {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode} (midWidth targetWindow : Nat)
    (chordAt : natListGetAt
        (matchingOfSpineList midWidth
          ([] : List (SpineAtom signature overallSource overallTarget))).partner
        (midWidth + targetWindow)
      = midWidth + targetWindow + 1) : False := by
  rcases Nat.lt_or_ge targetWindow midWidth with below | atLeast
  · exact emptyMidMatching_noForwardChord below chordAt
  · have lenEq : (matchingOfSpineList midWidth
        ([] : List (SpineAtom signature overallSource overallTarget))).partner.length
        = midWidth + midWidth := by
      show (extractDiagram midWidth ⟨List.range midWidth, [], midWidth, 0⟩).partner.length
        = midWidth + midWidth
      rw [extractDiagramPartnerLengthGSL midWidth ⟨List.range midWidth, [], midWidth, 0⟩]
      show midWidth + (List.range midWidth).length = midWidth + midWidth
      rw [rangeLengthGSL]
    have outRange : (matchingOfSpineList midWidth
        ([] : List (SpineAtom signature overallSource overallTarget))).partner.length
        ≤ midWidth + targetWindow := by
      rw [lenEq]; exact Nat.add_le_add_left atLeast midWidth
    rw [natListGetAtZeroOfGeGSL _ _ outRange] at chordAt
    exact Nat.noConfusion chordAt

/-! ## The ANY-WIDTH fueled partner-LOCATE over the class -/

private theorem genericMatchingLocateAuxFueledMid (cls : AdjointStringConnectivity)
    {overallSource overallTarget : cls.signature.graph.Mode} :
    (midWidth : Nat) →
    (fuel : Nat) →
    (bottomWord : ModalityPath cls.signature.graph overallSource overallTarget) →
    (spine : List (SpineAtom cls.signature overallSource overallTarget)) →
    spine.length ≤ fuel →
    SpineBoundaryChained midWidth spine →
    SpineBoundaryWordChained bottomWord spine →
    AllCupArity spine →
    (targetWindow : Nat) →
    natListGetAt (matchingOfSpineList midWidth spine).partner (midWidth + targetWindow)
      = midWidth + targetWindow + 1 →
    ∃ movedPrefix backCup,
      AtomicTraceEquiv cls.signature spine (movedPrefix ++ [backCup])
        ∧ matchingOfSpineList midWidth spine = matchingOfSpineList midWidth (movedPrefix ++ [backCup])
        ∧ AllCupArity (movedPrefix ++ [backCup])
        ∧ SpineBoundaryChained midWidth (movedPrefix ++ [backCup])
        ∧ SpineBoundaryWordChained bottomWord (movedPrefix ++ [backCup])
        ∧ backCup.leftContext.length = targetWindow
  | midWidth, 0, _, spine, lengthBound, _, _, _, targetWindow, chordAt => by
      cases listNilOrSnocGSL spine with
      | inl spineNil => subst spineNil
                        exact (genericEmptyMidNoForwardChordGSL midWidth targetWindow chordAt).elim
      | inr snocWit =>
          obtain ⟨t, Clast, spineSnoc⟩ := snocWit
          subst spineSnoc
          rw [lengthSnocGSL] at lengthBound
          exact absurd lengthBound (Nat.not_succ_le_zero _)
  | midWidth, fuel + 1, bottomWord, spine, lengthBound, chained, wordChained, pureCup, targetWindow, chordAt => by
      cases listNilOrSnocGSL spine with
      | inl spineNil => subst spineNil
                        exact (genericEmptyMidNoForwardChordGSL midWidth targetWindow chordAt).elim
      | inr snocWit =>
      obtain ⟨t, Clast, spineSnoc⟩ := snocWit
      subst spineSnoc
      have tLenBound : t.length ≤ fuel := by
        rw [lengthSnocGSL] at lengthBound; exact Nat.le_of_succ_le_succ lengthBound
      have prefixChained : SpineBoundaryChained midWidth t :=
        spineBoundaryChained_prefix_ofAppend t [Clast] midWidth chained
      have tPure : AllCupArity t := allCupArity_prefix_ofAppend t [Clast] pureCup
      have prefixWordChained : SpineBoundaryWordChained bottomWord t :=
        spineBoundaryWordChained_prefix_ofAppend bottomWord t [Clast] wordChained
      have clastChord := genericMatchingLastCup_isShortChord_mid cls midWidth t Clast chained pureCup
      obtain ⟨clastDom, clastCod⟩ := allCupArity_lastCup_arity t Clast pureCup
      have owSplit := genericMatchingOpenWiresCupEndSplit_mid midWidth t Clast pureCup
      have windowFits : Clast.leftContext.length
          ≤ (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ t).openWires.length := by
        rw [genericProcessSpine_prefix_openWires_eq_lastDomBoundary cls midWidth t Clast chained]
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
            exact genericMatchingForwardChordsNotAdjacent_mid cls midWidth (t ++ [Clast]) chained pureCup
              targetWindow lowInRange chordAt chordHigh
        have chordInT := genericMatchingChordShift_below_mid cls midWidth t Clast chained pureCup
          targetWindow below chordAt
        obtain ⟨pre', Csigma, atomicEquivT, _matchEqT, pureT', _chainedT', wordChainedT', sigWindow⟩ :=
          genericMatchingLocateAuxFueledMid cls midWidth fuel bottomWord t tLenBound prefixChained
            prefixWordChained tPure targetWindow chordInT
        obtain ⟨_sigDom, sigCod⟩ := allCupArity_lastCup_arity pre' Csigma pureT'
        obtain ⟨windowGap, gapSpec⟩ := Nat.le.dest wlastGe
        have clastDomIsTop : spineListTopWord bottomWord t
            = composePath Clast.leftContext (composePath Clast.generatorDom Clast.rightContext) :=
          spineListTopWord_prefix_eq_lastDomWord bottomWord t Clast wordChained
        have sigmaCodIsTop : spineListTopWord bottomWord (pre' ++ [Csigma])
            = composePath Csigma.leftContext (composePath Csigma.generatorCod Csigma.rightContext) :=
          spineListTopWordSnocGSL bottomWord pre' Csigma
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
        have e1' : AtomicTraceEquiv cls.signature (t ++ [Clast]) (pre' ++ [Csigma, Clast]) :=
          AtomicTraceEquiv.castList rfl (snocSnocRegroupGSL pre' Csigma Clast)
            (atomicTraceEquiv_backAppendCongr atomicEquivT Clast)
        have fullEquiv := e1'.trans (atomicTraceEquiv_prefixCongr swapEquiv pre')
        have fullEquivCasted :
            AtomicTraceEquiv cls.signature (t ++ [Clast])
              ((pre' ++ [{ Clast with
                    leftContext :=
                      composePath (composePath Csigma.leftContext Csigma.generatorDom) inertPath }])
                ++ [{ Csigma with
                      rightContext :=
                        composePath (composePath inertPath Clast.generatorCod) Clast.rightContext }]) :=
          AtomicTraceEquiv.castList rfl (snocSnocRegroupGSL pre' _ _).symm fullEquiv
        refine ⟨_, _, fullEquivCasted, ?_, ?_, ?_, ?_, sigWindow⟩
        · exact extractDiagram_eq_of_atomicPureCupTraceEquiv fullEquivCasted
            ⟨List.range midWidth, [], midWidth, 0⟩ midWidth midWidth (wireStateFresh_initial midWidth)
            isUnionFindForest_nil (Nat.le_refl midWidth) (rangeLengthGSL midWidth) chained pureCup
        · exact allCupArity_preservedOfAtomicTraceEquiv fullEquivCasted pureCup
        · exact (spineBoundaryChained_iff_of_atomicTraceEquiv fullEquivCasted midWidth).mp chained
        · rw [snocSnocRegroupGSL pre']
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
            exact genericMatchingForwardChordsNotAdjacent_mid cls midWidth (t ++ [Clast]) chained pureCup
              Clast.leftContext.length lowInRange clastChord chordHigh
        have chordInT := genericMatchingChordShift_above_mid cls midWidth t Clast chained pureCup
          targetWindow aboveW chordAt
        obtain ⟨pre', Csigma, atomicEquivT, _matchEqT, pureT', _chainedT', wordChainedT', sigWindow⟩ :=
          genericMatchingLocateAuxFueledMid cls midWidth fuel bottomWord t tLenBound prefixChained
            prefixWordChained tPure (targetWindow - 2) chordInT
        obtain ⟨windowGap, gapSpec⟩ := Nat.le.dest targetGe
        have clastDomIsTop : spineListTopWord bottomWord t
            = composePath Clast.leftContext (composePath Clast.generatorDom Clast.rightContext) :=
          spineListTopWord_prefix_eq_lastDomWord bottomWord t Clast wordChained
        have sigmaCodIsTop : spineListTopWord bottomWord (pre' ++ [Csigma])
            = composePath Csigma.leftContext (composePath Csigma.generatorCod Csigma.rightContext) :=
          spineListTopWordSnocGSL bottomWord pre' Csigma
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
          exact (natAddSubCancelGSL (Clast.leftContext.length + windowGap) 2).symm
        obtain ⟨inertPath, leftFactor, rightFactor, inertLen⟩ :=
          spineAtom_contextsFactorLeft_of_disjointWordWindows Csigma Clast sharedWord windowGap
            windowsDisjoint
        have swapStep :=
          spineAtomSwapLeft_of_wordFactorization Csigma Clast [] inertPath leftFactor rightFactor
        have swapEquiv := (AtomicTraceEquiv.ofSwap swapStep).symm
        have movedPairChained :=
          spineBoundaryWordChained_swappedPairLeft Csigma Clast pairChained inertPath leftFactor rightFactor
        have e1' : AtomicTraceEquiv cls.signature (t ++ [Clast]) (pre' ++ [Csigma, Clast]) :=
          AtomicTraceEquiv.castList rfl (snocSnocRegroupGSL pre' Csigma Clast)
            (atomicTraceEquiv_backAppendCongr atomicEquivT Clast)
        have fullEquiv := e1'.trans (atomicTraceEquiv_prefixCongr swapEquiv pre')
        have fullEquivCasted :
            AtomicTraceEquiv cls.signature (t ++ [Clast])
              ((pre' ++ [{ Clast with
                    rightContext :=
                      composePath (composePath inertPath Csigma.generatorDom) Csigma.rightContext }])
                ++ [{ Csigma with
                      leftContext :=
                        composePath (composePath Clast.leftContext Clast.generatorCod) inertPath }]) :=
          AtomicTraceEquiv.castList rfl (snocSnocRegroupGSL pre' _ _).symm fullEquiv
        refine ⟨_, _, fullEquivCasted, ?_, ?_, ?_, ?_, ?_⟩
        · exact extractDiagram_eq_of_atomicPureCupTraceEquiv fullEquivCasted
            ⟨List.range midWidth, [], midWidth, 0⟩ midWidth midWidth (wireStateFresh_initial midWidth)
            isUnionFindForest_nil (Nat.le_refl midWidth) (rangeLengthGSL midWidth) chained pureCup
        · exact allCupArity_preservedOfAtomicTraceEquiv fullEquivCasted pureCup
        · exact (spineBoundaryChained_iff_of_atomicTraceEquiv fullEquivCasted midWidth).mp chained
        · rw [snocSnocRegroupGSL pre']
          exact spineBoundaryWordChained_append bottomWord pre' _ preWordChained movedPairChained
        · show (composePath (composePath Clast.leftContext Clast.generatorCod) inertPath).length
            = targetWindow
          rw [ModalityPath.length_composePath, ModalityPath.length_composePath, inertLen, clastCod]
          exact gapSpec

/-- ★★ **The ANY-WIDTH location step over the class.**  In a boundary-chained AND boundary-word-chained pure-cup
spine over ANY `midWidth` bottom boundary, the cup whose short chord sits at `targetWindow` bubbles to the tail,
keeping BOTH chains and the `matchingOfSpineList midWidth`.  Fuel seeded at the spine length (the VFA
selection-sort `select` shape).  The shipped `k = 2` positive-mid `stringMatchingLocateAuxMid` and width-`0`
`stringMatchingLocateAux` are BOTH instances — the `0 < midWidth` premise is gone (the snake exclusion
dispatches any-width). -/
theorem genericMatchingLocateAuxMid (cls : AdjointStringConnectivity)
    {overallSource overallTarget : cls.signature.graph.Mode}
    (midWidth : Nat)
    (bottomWord : ModalityPath cls.signature.graph overallSource overallTarget)
    (spine : List (SpineAtom cls.signature overallSource overallTarget))
    (chained : SpineBoundaryChained midWidth spine)
    (wordChained : SpineBoundaryWordChained bottomWord spine)
    (pureCup : AllCupArity spine)
    (targetWindow : Nat)
    (chordAt : natListGetAt (matchingOfSpineList midWidth spine).partner (midWidth + targetWindow)
      = midWidth + targetWindow + 1) :
    ∃ movedPrefix backCup,
      AtomicTraceEquiv cls.signature spine (movedPrefix ++ [backCup])
        ∧ matchingOfSpineList midWidth spine = matchingOfSpineList midWidth (movedPrefix ++ [backCup])
        ∧ AllCupArity (movedPrefix ++ [backCup])
        ∧ SpineBoundaryChained midWidth (movedPrefix ++ [backCup])
        ∧ SpineBoundaryWordChained bottomWord (movedPrefix ++ [backCup])
        ∧ backCup.leftContext.length = targetWindow :=
  genericMatchingLocateAuxFueledMid cls midWidth spine.length bottomWord spine
    (Nat.le_refl spine.length) chained wordChained pureCup targetWindow chordAt

/-! ## `k = 2` RECOVERY — the generic locate re-derives the NAMED shipped positive-mid locate -/

/-- The statement of the shipped `k = 2` positive-mid fueled locate, named as the recovery TARGET. -/
abbrev StringLocateAuxMidStatement : Prop :=
  ∀ {overallSource overallTarget : adjointTripleGraph.Mode} (midWidth : Nat),
    0 < midWidth →
    ∀ (bottomWord : ModalityPath adjointTripleGraph overallSource overallTarget)
      (spine : List (SpineAtom adjointTripleModeSignature overallSource overallTarget)),
    SpineBoundaryChained midWidth spine →
    SpineBoundaryWordChained bottomWord spine →
    AllCupArity spine →
    ∀ (targetWindow : Nat),
    natListGetAt (matchingOfSpineList midWidth spine).partner (midWidth + targetWindow)
      = midWidth + targetWindow + 1 →
    ∃ (movedPrefix : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
      (backCup : SpineAtom adjointTripleModeSignature overallSource overallTarget),
      AtomicTraceEquiv adjointTripleModeSignature spine (movedPrefix ++ [backCup])
        ∧ matchingOfSpineList midWidth spine = matchingOfSpineList midWidth (movedPrefix ++ [backCup])
        ∧ AllCupArity (movedPrefix ++ [backCup])
        ∧ SpineBoundaryChained midWidth (movedPrefix ++ [backCup])
        ∧ SpineBoundaryWordChained bottomWord (movedPrefix ++ [backCup])
        ∧ backCup.leftContext.length = targetWindow

/-- ★ **The shipped `k = 2` locate inhabits the named statement** — `stringMatchingLocateAuxMid` IS the recovery
target. -/
theorem stringLocateAuxMid_shippedInhabitant : StringLocateAuxMidStatement :=
  fun midWidth midPos bottomWord spine chained wordChained pureCup targetWindow chordAt =>
    stringMatchingLocateAuxMid midWidth midPos bottomWord spine chained wordChained pureCup
      targetWindow chordAt

/-- ★★ **The generic locate, at `k = 2`, RE-DERIVES the shipped locate** — the generic form carries NO
positivity premise, so it inhabits the shipped statement by discarding `0 < midWidth`. -/
theorem stringLocateAuxMid_viaGenericClassAtTwo : StringLocateAuxMidStatement :=
  fun midWidth _midPos bottomWord spine chained wordChained pureCup targetWindow chordAt =>
    genericMatchingLocateAuxMid adjointStringConnectivityAtTwo midWidth bottomWord spine chained
      wordChained pureCup targetWindow chordAt

/-! ## `k = 3` FIRES — the generic locate runs on genuine adjoint-quadruple spines, both regimes -/

/-- The width-`0` quad bottom word (the empty `base` endo-word the width-`0` word chain threads from). -/
def quadLocateBottomWordW0 : ModalityPath adjointQuadrupleGraph AdjointQuadrupleMode.base AdjointQuadrupleMode.base :=
  ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.base

/-- The width-`0` quad two-cup spine `[η1@0, η1@2]` computes partner `[1, 0, 3, 2]` — two disjoint short
chords, the target chord at window `0`. -/
theorem quadLocateTwoCup_matchingComputes :
    (matchingOfSpineList 0 [quadDropUnitOneW0, quadDropLastCupW2]).partner = [1, 0, 3, 2] := by decide

/-- ★ **The generic locate FIRES at `k = 3`, width-`0`, through the BELOW branch.**  On the quad two-cup spine
`[η1@0, η1@2]` with target window `0` (a genuine forward chord `partner[0] = 1`), the target sits BELOW the last
cup's window `2`, so the locate exercises the chord-shift descent, the recursion, and the disjoint-word swap
bubble — producing a moved spine whose BACK cup carries the target window `0`. -/
theorem genericLocateMid_firesAtThreeWidthZero :
    ∃ movedPrefix backCup,
      AtomicTraceEquiv adjointQuadrupleModeSignature [quadDropUnitOneW0, quadDropLastCupW2]
          (movedPrefix ++ [backCup])
        ∧ matchingOfSpineList 0 [quadDropUnitOneW0, quadDropLastCupW2]
            = matchingOfSpineList 0 (movedPrefix ++ [backCup])
        ∧ AllCupArity (movedPrefix ++ [backCup])
        ∧ SpineBoundaryChained 0 (movedPrefix ++ [backCup])
        ∧ SpineBoundaryWordChained quadLocateBottomWordW0 (movedPrefix ++ [backCup])
        ∧ backCup.leftContext.length = 0 :=
  genericMatchingLocateAuxMid adjointStringConnectivityAtThree 0 quadLocateBottomWordW0
    [quadDropUnitOneW0, quadDropLastCupW2]
    (SpineBoundaryChained.cons _ rfl (SpineBoundaryChained.cons _ rfl (SpineBoundaryChained.nil _)))
    (SpineBoundaryWordChained.cons _ rfl
      (SpineBoundaryWordChained.cons _ rfl (SpineBoundaryWordChained.nil _)))
    (AllCupArity.cons rfl rfl (AllCupArity.cons rfl rfl AllCupArity.nil))
    0 (by decide)

/-- The mid-`1` quad bottom word: the single survivor letter `L1 : base ⟶ tip`. -/
def quadLocateBottomWordMidOne : ModalityPath adjointQuadrupleGraph AdjointQuadrupleMode.base AdjointQuadrupleMode.tip :=
  ModalityPath.cons AdjointQuadrupleModality.letterOne
    (ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.tip)

/-- ★ **The generic locate FIRES at `k = 3`, mid-`1`, through the MIDDLE branch (positive width).**  On the
single-survivor quad cup `[quadMidOneCupOverL1]` with target window `0` (the chord `partner[1] = 2` at the
OFFSET index `midWidth + 0 = 1`), the last cup IS the target — the locate returns it at the tail with the
survivor through-strand re-ranking active (`midWidth = 1 > 0`). -/
theorem genericLocateMid_firesAtThreeMidOne :
    ∃ movedPrefix backCup,
      AtomicTraceEquiv adjointQuadrupleModeSignature [quadMidOneCupOverL1] (movedPrefix ++ [backCup])
        ∧ matchingOfSpineList 1 [quadMidOneCupOverL1] = matchingOfSpineList 1 (movedPrefix ++ [backCup])
        ∧ AllCupArity (movedPrefix ++ [backCup])
        ∧ SpineBoundaryChained 1 (movedPrefix ++ [backCup])
        ∧ SpineBoundaryWordChained quadLocateBottomWordMidOne (movedPrefix ++ [backCup])
        ∧ backCup.leftContext.length = 0 :=
  genericMatchingLocateAuxMid adjointStringConnectivityAtThree 1 quadLocateBottomWordMidOne
    [quadMidOneCupOverL1]
    (SpineBoundaryChained.cons _ rfl (SpineBoundaryChained.nil _))
    (SpineBoundaryWordChained.cons _ rfl (SpineBoundaryWordChained.nil _))
    (AllCupArity.cons rfl rfl AllCupArity.nil)
    0 (by decide)

/-! ## Road marker -/

/-- **★ ESTABLISHED — the generic snake exclusion + the ANY-WIDTH fueled partner-LOCATE are machine-checked
(FC-4 r7, the locate tranche of the generic cup-sort driver).**
`genericMatchingForwardChordsNotAdjacent_mid` rules out adjacent forward chords at EVERY `midWidth` over
`AdjointStringConnectivity` — the `0 < midWidth` premise of the shipped `k = 2` sibling is DISPATCHED AWAY by
the r7 any-width involution.  `genericMatchingLocateAuxMid` is the fueled partner-LOCATE at every `midWidth`
over the class (fuel = spine length, the VFA selection-sort `select` shape), riding the r6 short-chord readoff
+ chord-shift descents, the r5 B3 tracking, the generic snake exclusion, and the `{signature}`-generic
empty-mid base floor — subsuming BOTH shipped `k = 2` locates (width-`0` r17 and positive-mid r45) as
instances.  The HONESTY LAW discharged: the generic locate recovers the NAMED shipped
`stringMatchingLocateAuxMid` at `k = 2` (`stringLocateAuxMid_shippedInhabitant` /
`..._viaGenericClassAtTwo`) AND fires at `k = 3` through BOTH regimes — the width-`0` two-cup BELOW-branch
bubble (`genericLocateMid_firesAtThreeWidthZero`, cross-checked partner `[1,0,3,2]`) and the mid-`1`
positive-width MIDDLE branch (`genericLocateMid_firesAtThreeMidOne`).

  What this marker does NOT close (THE FLIP LAW): the census marker `fxString_hasNColourAtomPinReroute`
  (`StringKParameterizationCensus`) STAYS `false` here — the fueled SORT DRIVER + the generic determinacy +
  the `k = 3` decision are the sibling tranche (`StringGenericMidPureCupSortDriver`); the closure adjudication
  lives in `StringNColourAtomPinRerouteClosure`.  `= true`. -/
def fxString_hasGenericMidSnakeLocate : Bool := true

end FX1Poly.Polygraph
