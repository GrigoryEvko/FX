import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.MatchingWidthZeroSnake
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.MatchingWidthZeroChordShift
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.MatchingSwapPeel
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.MatchingDropLastCup
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.MatchingLastCupShortChord
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupSortComplete

/-! # MatchingWidthZeroSort — the width-0 pure-cup determinacy, POSITIVITY-FREE (Track B b#5 + c)

The location induction (`matchingLocateAux`) and the direct-Catalan sort assembly, ported to the plain
`matchingOf` carrier at the width-`0` seed, closing `WidthZeroPureCupDeterminacy`.  Everything runs
positivity-free: the swap fold rides piece (a) `extractDiagram_eq_of_atomicPureCupTraceEquiv`, the last-cup
readoff rides brick 1 `matchingLastCup_isShortChord`, the chord-shift descents ride b#3/b#4, the snake
exclusion rides b#5 (`matchingForwardChordsNotAdjacent`, the b#1 involution's consumer), and the cup drop
rides brick 3 `dropLastCup_matching_injective`.  NO arc census, NO `arcDiagram_eq_matching`, NO
`0 < bottomCount`.

  * ★ `matchingLocateAux` (b#5) — the location step: the cup whose short chord sits at `targetWindow` bubbles
    to the tail (fuel-driven `propext`-free unsnoc).

  * ★ `widthZeroPureCupDeterminacy_proof` (c) — the crux: two boundary-chained pure-cup spines over the
    width-`0` bottom boundary with equal `matchingOfSpineList 0` are `SpineTraceEquiv`.  This IS the
    `WidthZeroPureCupDeterminacy` (`SpineValleyCellDegenerate`) — GENERAL, no positivity hypothesis.

Raw Lean 4 + Init; structural / fuel recursion, no `omega` / `simp`-AC / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private plumbing (per-file copies) -/

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

private theorem natAddRightCancel :
    (added : Nat) → {leftSide rightSide : Nat} →
    leftSide + added = rightSide + added → leftSide = rightSide
  | 0, _, _, sumsEqual => sumsEqual
  | added + 1, _, _, sumsEqual => natAddRightCancel added (Nat.succ.inj sumsEqual)

private theorem natAddLeftCancel :
    (base : Nat) → {leftSide rightSide : Nat} →
    base + leftSide = base + rightSide → leftSide = rightSide
  | 0, _, _, sumsEqual => by rw [Nat.zero_add, Nat.zero_add] at sumsEqual; exact sumsEqual
  | base + 1, _, _, sumsEqual =>
      natAddLeftCancel base (Nat.succ.inj (by rw [Nat.succ_add, Nat.succ_add] at sumsEqual; exact sumsEqual))

private theorem natAddSubCancel (baseValue : Nat) : (subtracted : Nat) →
    baseValue + subtracted - subtracted = baseValue
  | 0 => rfl
  | subtracted + 1 => by
      rw [Nat.add_succ, Nat.succ_sub_succ]
      exact natAddSubCancel baseValue subtracted

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

private theorem addLeftVanish : {leftSummand rightSummand : Nat} →
    leftSummand + rightSummand = 0 → leftSummand = 0
  | _, 0, sumZero => sumZero
  | _, _ + 1, sumZero => by rw [Nat.add_succ] at sumZero; exact Nat.noConfusion sumZero

private theorem addRightVanish : {leftSummand rightSummand : Nat} →
    leftSummand + rightSummand = 0 → rightSummand = 0
  | _, 0, _ => rfl
  | _, _ + 1, sumZero => by rw [Nat.add_succ] at sumZero; exact Nat.noConfusion sumZero

private theorem singletonCupArity {overallSource overallTarget : adjunctionGraph.Mode}
    (atom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (capZero : capAtomCount [atom] = 0) :
    atom.generatorDom.length = 0 ∧ atom.generatorCod.length = 2 := by
  cases adjunctionSpineAtom_isCupOrCap atom with
  | inl cupArity => exact cupArity
  | inr capArity =>
      exfalso
      have guardTrue : (atom.generatorDom.length == 2 && atom.generatorCod.length == 0) = true := by
        rw [capArity.1, capArity.2]; rfl
      dsimp only [capAtomCount] at capZero
      rw [if_pos guardTrue] at capZero
      exact Nat.noConfusion capZero

private theorem lastCupArity
    {overallSource overallTarget : adjunctionGraph.Mode}
    (prefixAtoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (lastCup : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (pureCup : AllCupArity (prefixAtoms ++ [lastCup])) :
    lastCup.generatorDom.length = 0 ∧ lastCup.generatorCod.length = 2 := by
  have capZero : capAtomCount (prefixAtoms ++ [lastCup]) = 0 :=
    capAtomCount_ofAllCupArity (prefixAtoms ++ [lastCup]) pureCup
  have splitZero : capAtomCount prefixAtoms + capAtomCount [lastCup] = 0 :=
    (capAtomCount_append prefixAtoms [lastCup]).symm.trans capZero
  exact singletonCupArity lastCup (addRightVanish splitZero)

/-- The partner list has length `0 + openWires` (matching-carrier length reflect). -/
private theorem matchingPartnerLengthReflect
    {overallSource overallTarget : adjunctionGraph.Mode}
    (spine : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) :
    (matchingOfSpineList 0 spine).partner.length
      = 0 + (processSpine ⟨List.range 0, [], 0, 0⟩ spine).openWires.length := by
  show ((List.range (0 + (processSpine ⟨List.range 0, [], 0, 0⟩ spine).openWires.length)).map
      (partnerIndexOf (processSpine ⟨List.range 0, [], 0, 0⟩ spine).links
        (List.range 0 ++ (processSpine ⟨List.range 0, [], 0, 0⟩ spine).openWires)
        (0 + (processSpine ⟨List.range 0, [], 0, 0⟩ spine).openWires.length))).length
    = 0 + (processSpine ⟨List.range 0, [], 0, 0⟩ spine).openWires.length
  rw [mapLength, rangeLength]

/-- The last cup's short chord at index `0 + w` (reconciling brick 1's bare-`w` readoff). -/
private theorem matchingLastCup_isShortChord_zeroForm
    {overallSource overallTarget : adjunctionGraph.Mode}
    (prefixAtoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (lastCup : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (chained : SpineBoundaryChained 0 (prefixAtoms ++ [lastCup]))
    (pureCup : AllCupArity (prefixAtoms ++ [lastCup])) :
    natListGetAt (matchingOfSpineList 0 (prefixAtoms ++ [lastCup])).partner
        (0 + lastCup.leftContext.length)
      = 0 + lastCup.leftContext.length + 1 := by
  rw [Nat.zero_add]
  exact matchingLastCup_isShortChord prefixAtoms lastCup chained pureCup

/-- The empty width-0 spine has no forward chord (partner list is empty). -/
private theorem emptyMatchingNoForwardChord
    {overallSource overallTarget : adjunctionGraph.Mode} (targetWindow : Nat)
    (chordAt : natListGetAt
        (matchingOfSpineList 0
          ([] : List (SpineAtom adjunctionModeSignature overallSource overallTarget))).partner
        (0 + targetWindow)
      = 0 + targetWindow + 1) : False := by
  have partnerNil : (matchingOfSpineList 0
      ([] : List (SpineAtom adjunctionModeSignature overallSource overallTarget))).partner = [] := rfl
  rw [partnerNil] at chordAt
  have readZero : natListGetAt ([] : List Nat) (0 + targetWindow) = 0 := rfl
  rw [readZero] at chordAt
  exact Nat.noConfusion chordAt

/-! ### `matchingLocateAux` — bubble the target cup (by chord window) to the spine's tail -/

private theorem matchingLocateAuxFueled
    {overallSource overallTarget : adjunctionGraph.Mode} :
    (fuel : Nat) →
    (spine : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) →
    spine.length ≤ fuel →
    SpineBoundaryChained 0 spine →
    AllCupArity spine →
    (targetWindow : Nat) →
    natListGetAt (matchingOfSpineList 0 spine).partner (0 + targetWindow)
      = 0 + targetWindow + 1 →
    ∃ movedPrefix backCup,
      AtomicTraceEquiv adjunctionModeSignature spine (movedPrefix ++ [backCup])
        ∧ matchingOfSpineList 0 spine = matchingOfSpineList 0 (movedPrefix ++ [backCup])
        ∧ AllCupArity (movedPrefix ++ [backCup])
        ∧ SpineBoundaryChained 0 (movedPrefix ++ [backCup])
        ∧ backCup.leftContext.length = targetWindow
  | 0, spine, lengthBound, _, _, targetWindow, chordAt => by
      cases listNilOrSnoc spine with
      | inl spineNil => subst spineNil
                        exact (emptyMatchingNoForwardChord targetWindow chordAt).elim
      | inr snocWit =>
          obtain ⟨t, Clast, spineSnoc⟩ := snocWit
          subst spineSnoc
          rw [lengthSnoc] at lengthBound
          exact absurd lengthBound (Nat.not_succ_le_zero _)
  | fuel + 1, spine, lengthBound, chained, pureCup, targetWindow, chordAt => by
      cases listNilOrSnoc spine with
      | inl spineNil => subst spineNil
                        exact (emptyMatchingNoForwardChord targetWindow chordAt).elim
      | inr snocWit =>
      obtain ⟨t, Clast, spineSnoc⟩ := snocWit
      subst spineSnoc
      have tLenBound : t.length ≤ fuel := by
        rw [lengthSnoc] at lengthBound; exact Nat.le_of_succ_le_succ lengthBound
      have prefixChained : SpineBoundaryChained 0 t :=
        spineBoundaryChained_prefix_ofAppend t [Clast] 0 chained
      have tPure : AllCupArity t := allCupArity_prefix_ofAppend t [Clast] pureCup
      have clastChord := matchingLastCup_isShortChord_zeroForm t Clast chained pureCup
      obtain ⟨clastDom, clastCod⟩ := lastCupArity t Clast pureCup
      have owSplit := matchingOpenWiresCupEndSplit t Clast pureCup
      have windowFits : Clast.leftContext.length
          ≤ (processSpine ⟨List.range 0, [], 0, 0⟩ t).openWires.length := by
        rw [processSpine_prefix_openWires_eq_lastDomBoundary 0 t Clast chained]
        show Clast.leftContext.length
          ≤ Clast.leftContext.length + Clast.generatorDom.length + Clast.rightContext.length
        exact Nat.le_trans (Nat.le_add_right Clast.leftContext.length Clast.generatorDom.length)
          (Nat.le_add_right (Clast.leftContext.length + Clast.generatorDom.length)
            Clast.rightContext.length)
      rcases Nat.lt_trichotomy targetWindow Clast.leftContext.length with below | middle | aboveW
      · -- (ii) targetWindow < wlast
        have wlastGe : targetWindow + 2 ≤ Clast.leftContext.length := by
          rcases Nat.lt_or_ge (targetWindow + 1) Clast.leftContext.length with hlt | hge
          · exact hlt
          · exfalso
            have snakeEq : targetWindow + 1 = Clast.leftContext.length := Nat.le_antisymm below hge
            have lowInRange : 0 + targetWindow
                < 0 + (matchingOfSpineList 0 (t ++ [Clast])).topCount := by
              show 0 + targetWindow
                < 0 + (processSpine ⟨List.range 0, [], 0, 0⟩ (t ++ [Clast])).openWires.length
              rw [owSplit]
              exact Nat.add_lt_add_left
                (Nat.lt_of_lt_of_le below (Nat.le_trans windowFits (Nat.le_add_right _ 2))) 0
            have chordHigh : natListGetAt
                (matchingOfSpineList 0 (t ++ [Clast])).partner (0 + (targetWindow + 1))
              = 0 + (targetWindow + 1) + 1 := by rw [snakeEq]; exact clastChord
            exact matchingForwardChordsNotAdjacent (t ++ [Clast]) pureCup targetWindow
              lowInRange chordAt chordHigh
        have chordInT := matchingChordShift_below t Clast chained pureCup targetWindow below chordAt
        obtain ⟨pre', Csigma, atomicEquivT, _matchEqT, pureT', _chainedT', sigWindow⟩ :=
          matchingLocateAuxFueled fuel t tLenBound prefixChained tPure targetWindow chordInT
        obtain ⟨_sigDom, sigCod⟩ := lastCupArity pre' Csigma pureT'
        obtain ⟨windowGap, gapSpec⟩ := Nat.le.dest wlastGe
        have e1' : AtomicTraceEquiv adjunctionModeSignature (t ++ [Clast]) (pre' ++ [Csigma, Clast]) :=
          AtomicTraceEquiv.castList rfl (snocSnocRegroup pre' Csigma Clast)
            (atomicTraceEquiv_backAppendCongr atomicEquivT Clast)
        have chainedFull := (spineBoundaryChained_iff_of_atomicTraceEquiv e1' 0).mp chained
        obtain ⟨_, _, suffixChained⟩ := processSpine_openWires_length_ofChainedAppend pre'
          [Csigma, Clast] ⟨List.range 0, [], 0, 0⟩ 0 rfl chainedFull
        obtain ⟨_, clastTail⟩ := spineBoundaryChained_tail suffixChained
        have boundariesChain : Clast.domBoundaryLength = Csigma.codBoundaryLength :=
          (spineBoundaryChained_tail clastTail).1
        have windowsDisjoint :
            Csigma.leftContext.length + Csigma.generatorCod.length + windowGap
              = Clast.leftContext.length := by rw [sigWindow, sigCod]; exact gapSpec
        obtain ⟨inertPath, _inertLen, swapStep⟩ :=
          adjunctionSpineAtomSwap_of_disjointWindows Csigma Clast [] boundariesChain windowGap
            windowsDisjoint
        have swapEquiv : AtomicTraceEquiv adjunctionModeSignature [Csigma, Clast]
            [{ Clast with
                leftContext :=
                  composePath (composePath Csigma.leftContext Csigma.generatorDom) inertPath },
             { Csigma with
                rightContext :=
                  composePath (composePath inertPath Clast.generatorCod) Clast.rightContext }] :=
          AtomicTraceEquiv.ofSwap swapStep
        have fullEquiv := e1'.trans (atomicTraceEquiv_prefixCongr swapEquiv pre')
        have fullEquivCasted :
            AtomicTraceEquiv adjunctionModeSignature (t ++ [Clast])
              ((pre' ++ [{ Clast with
                    leftContext :=
                      composePath (composePath Csigma.leftContext Csigma.generatorDom) inertPath }])
                ++ [{ Csigma with
                      rightContext :=
                        composePath (composePath inertPath Clast.generatorCod) Clast.rightContext }]) :=
          AtomicTraceEquiv.castList rfl (snocSnocRegroup pre' _ _).symm fullEquiv
        refine ⟨_, _, fullEquivCasted, ?_, ?_, ?_, sigWindow⟩
        · exact extractDiagram_eq_of_atomicPureCupTraceEquiv fullEquivCasted
            ⟨List.range 0, [], 0, 0⟩ 0 0 (wireStateFresh_initial 0) isUnionFindForest_nil
            (Nat.zero_le 0) rfl chained pureCup
        · exact allCupArity_preservedOfAtomicTraceEquiv fullEquivCasted pureCup
        · exact (spineBoundaryChained_iff_of_atomicTraceEquiv fullEquivCasted 0).mp chained
      · -- (i) targetWindow = wlast : Clast IS the target
        exact ⟨t, Clast, AtomicTraceEquiv.refl (t ++ [Clast]), rfl, pureCup, chained, middle.symm⟩
      · -- (iii) targetWindow > wlast
        have targetGe : Clast.leftContext.length + 2 ≤ targetWindow := by
          rcases Nat.lt_or_ge (Clast.leftContext.length + 1) targetWindow with hlt | hge
          · exact hlt
          · exfalso
            have snakeEq : Clast.leftContext.length + 1 = targetWindow := Nat.le_antisymm aboveW hge
            have lowInRange : 0 + Clast.leftContext.length
                < 0 + (matchingOfSpineList 0 (t ++ [Clast])).topCount := by
              show 0 + Clast.leftContext.length
                < 0 + (processSpine ⟨List.range 0, [], 0, 0⟩ (t ++ [Clast])).openWires.length
              rw [owSplit]
              exact Nat.add_lt_add_left
                (Nat.lt_of_le_of_lt windowFits (Nat.lt_add_of_pos_right (by decide : 0 < 2))) 0
            have chordHigh : natListGetAt
                (matchingOfSpineList 0 (t ++ [Clast])).partner (0 + (Clast.leftContext.length + 1))
              = 0 + (Clast.leftContext.length + 1) + 1 := by rw [snakeEq]; exact chordAt
            exact matchingForwardChordsNotAdjacent (t ++ [Clast]) pureCup Clast.leftContext.length
              lowInRange clastChord chordHigh
        have chordInT := matchingChordShift_above t Clast chained pureCup targetWindow aboveW chordAt
        obtain ⟨pre', Csigma, atomicEquivT, _matchEqT, pureT', _chainedT', sigWindow⟩ :=
          matchingLocateAuxFueled fuel t tLenBound prefixChained tPure (targetWindow - 2) chordInT
        obtain ⟨windowGap, gapSpec⟩ := Nat.le.dest targetGe
        have e1' : AtomicTraceEquiv adjunctionModeSignature (t ++ [Clast]) (pre' ++ [Csigma, Clast]) :=
          AtomicTraceEquiv.castList rfl (snocSnocRegroup pre' Csigma Clast)
            (atomicTraceEquiv_backAppendCongr atomicEquivT Clast)
        have chainedFull := (spineBoundaryChained_iff_of_atomicTraceEquiv e1' 0).mp chained
        obtain ⟨_, _, suffixChained⟩ := processSpine_openWires_length_ofChainedAppend pre'
          [Csigma, Clast] ⟨List.range 0, [], 0, 0⟩ 0 rfl chainedFull
        obtain ⟨_, clastTail⟩ := spineBoundaryChained_tail suffixChained
        have boundariesChain : Clast.domBoundaryLength = Csigma.codBoundaryLength :=
          (spineBoundaryChained_tail clastTail).1
        have windowsDisjoint :
            Clast.leftContext.length + Clast.generatorDom.length + windowGap
              = Csigma.leftContext.length := by
          rw [clastDom, Nat.add_zero, sigWindow, ← gapSpec,
            Nat.add_right_comm Clast.leftContext.length 2 windowGap]
          exact (natAddSubCancel (Clast.leftContext.length + windowGap) 2).symm
        obtain ⟨inertPath, inertLen, swapLeft⟩ :=
          adjunctionSpineAtomSwapLeft_of_disjointWindows Csigma Clast [] boundariesChain windowGap
            windowsDisjoint
        have swapEquiv : AtomicTraceEquiv adjunctionModeSignature [Csigma, Clast]
            [{ Clast with
                rightContext :=
                  composePath (composePath inertPath Csigma.generatorDom) Csigma.rightContext },
             { Csigma with
                leftContext :=
                  composePath (composePath Clast.leftContext Clast.generatorCod) inertPath }] :=
          (AtomicTraceEquiv.ofSwap swapLeft).symm
        have fullEquiv := e1'.trans (atomicTraceEquiv_prefixCongr swapEquiv pre')
        have fullEquivCasted :
            AtomicTraceEquiv adjunctionModeSignature (t ++ [Clast])
              ((pre' ++ [{ Clast with
                    rightContext :=
                      composePath (composePath inertPath Csigma.generatorDom) Csigma.rightContext }])
                ++ [{ Csigma with
                      leftContext :=
                        composePath (composePath Clast.leftContext Clast.generatorCod) inertPath }]) :=
          AtomicTraceEquiv.castList rfl (snocSnocRegroup pre' _ _).symm fullEquiv
        refine ⟨_, _, fullEquivCasted, ?_, ?_, ?_, ?_⟩
        · exact extractDiagram_eq_of_atomicPureCupTraceEquiv fullEquivCasted
            ⟨List.range 0, [], 0, 0⟩ 0 0 (wireStateFresh_initial 0) isUnionFindForest_nil
            (Nat.zero_le 0) rfl chained pureCup
        · exact allCupArity_preservedOfAtomicTraceEquiv fullEquivCasted pureCup
        · exact (spineBoundaryChained_iff_of_atomicTraceEquiv fullEquivCasted 0).mp chained
        · show (composePath (composePath Clast.leftContext Clast.generatorCod) inertPath).length
            = targetWindow
          rw [ModalityPath.length_composePath, ModalityPath.length_composePath, inertLen, clastCod]
          exact gapSpec

/-- ★ **The width-0 location step.**  In a boundary-chained pure-cup spine, the cup whose short chord sits at
`targetWindow` bubbles to the tail. -/
theorem matchingLocateAux
    {overallSource overallTarget : adjunctionGraph.Mode}
    (spine : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained 0 spine)
    (pureCup : AllCupArity spine)
    (targetWindow : Nat)
    (chordAt : natListGetAt (matchingOfSpineList 0 spine).partner (0 + targetWindow)
      = 0 + targetWindow + 1) :
    ∃ movedPrefix backCup,
      AtomicTraceEquiv adjunctionModeSignature spine (movedPrefix ++ [backCup])
        ∧ matchingOfSpineList 0 spine = matchingOfSpineList 0 (movedPrefix ++ [backCup])
        ∧ AllCupArity (movedPrefix ++ [backCup])
        ∧ SpineBoundaryChained 0 (movedPrefix ++ [backCup])
        ∧ backCup.leftContext.length = targetWindow :=
  matchingLocateAuxFueled spine.length spine (Nat.le_refl spine.length) chained pureCup
    targetWindow chordAt

/-! ### The base case + the sort assembly -/

/-- A pure-cup width-0 spine whose processed open-wire count is `0` is empty. -/
private theorem pureCupSpine_nil_ofOpenWiresZero
    {overallSource overallTarget : adjunctionGraph.Mode}
    (spine : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (pureCup : AllCupArity spine)
    (owZero : (processSpine ⟨List.range 0, [], 0, 0⟩ spine).openWires.length = 0) :
    spine = [] := by
  cases listNilOrSnoc spine with
  | inl spineNil => exact spineNil
  | inr snocWit =>
      obtain ⟨t, Clast, spineSnoc⟩ := snocWit
      subst spineSnoc
      exfalso
      rw [matchingOpenWiresCupEndSplit t Clast pureCup] at owZero
      exact Nat.noConfusion owZero

/-- The base case: an empty first spine with equal width-0 matching forces the second spine empty. -/
private theorem matchingPureCupSpine_sort_nil
    {overallSource overallTarget : adjunctionGraph.Mode}
    (secondList : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (secondPureCup : AllCupArity secondList)
    (matchEqual : matchingOfSpineList 0
        ([] : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
      = matchingOfSpineList 0 secondList) :
    SpineTraceEquiv adjunctionModeSignature [] secondList := by
  have topEq : (matchingOfSpineList 0
      ([] : List (SpineAtom adjunctionModeSignature overallSource overallTarget))).topCount
      = (matchingOfSpineList 0 secondList).topCount := congrArg DiagramType.topCount matchEqual
  have owZero : (processSpine ⟨List.range 0, [], 0, 0⟩ secondList).openWires.length = 0 :=
    topEq.symm
  have secondNil : secondList = [] := pureCupSpine_nil_ofOpenWiresZero secondList secondPureCup owZero
  rw [secondNil]
  exact SpineTraceEquiv.refl []

private theorem matchingPureCupSpineSortFueled
    {overallSource overallTarget : adjunctionGraph.Mode} :
    (fuel : Nat) →
    (firstList secondList :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget)) →
    firstList.length ≤ fuel →
    SpineBoundaryChained 0 firstList →
    SpineBoundaryChained 0 secondList →
    AllCupArity firstList →
    AllCupArity secondList →
    matchingOfSpineList 0 firstList = matchingOfSpineList 0 secondList →
    SpineTraceEquiv adjunctionModeSignature firstList secondList
  | 0, firstList, secondList, lengthBound, _, _, _, secondPureCup, matchEqual => by
      cases listNilOrSnoc firstList with
      | inl firstNil => subst firstNil
                        exact matchingPureCupSpine_sort_nil secondList secondPureCup matchEqual
      | inr snocWit =>
          obtain ⟨t1, C1, firstSnoc⟩ := snocWit
          subst firstSnoc
          rw [lengthSnoc] at lengthBound
          exact absurd lengthBound (Nat.not_succ_le_zero _)
  | fuel + 1, firstList, secondList, lengthBound, chainedFirst, chainedSecond, firstPureCup,
      secondPureCup, matchEqual => by
      cases listNilOrSnoc firstList with
      | inl firstNil => subst firstNil
                        exact matchingPureCupSpine_sort_nil secondList secondPureCup matchEqual
      | inr snocWit =>
      obtain ⟨t1, C1, firstSnoc⟩ := snocWit
      subst firstSnoc
      have t1LenBound : t1.length ≤ fuel := by
        rw [lengthSnoc] at lengthBound; exact Nat.le_of_succ_le_succ lengthBound
      have prefixChainedFirst : SpineBoundaryChained 0 t1 :=
        spineBoundaryChained_prefix_ofAppend t1 [C1] 0 chainedFirst
      have t1Pure : AllCupArity t1 := allCupArity_prefix_ofAppend t1 [C1] firstPureCup
      obtain ⟨c1Dom, c1Cod⟩ := lastCupArity t1 C1 firstPureCup
      have c1Chord := matchingLastCup_isShortChord_zeroForm t1 C1 chainedFirst firstPureCup
      have chordSecond : natListGetAt
          (matchingOfSpineList 0 secondList).partner (0 + C1.leftContext.length)
        = 0 + C1.leftContext.length + 1 := by rw [← matchEqual]; exact c1Chord
      obtain ⟨pre2, backCup, locEquiv, locMatch, locPure, locChained, backWindow⟩ :=
        matchingLocateAux secondList chainedSecond secondPureCup C1.leftContext.length chordSecond
      obtain ⟨backDom, backCod⟩ := lastCupArity pre2 backCup locPure
      have appendedEqual := matchEqual.trans locMatch
      have owEqual :
          (processSpine ⟨List.range 0, [], 0, 0⟩ t1).openWires.length
            = (processSpine ⟨List.range 0, [], 0, 0⟩ pre2).openWires.length := by
        have partnerLenEq : (matchingOfSpineList 0 (t1 ++ [C1])).partner.length
            = (matchingOfSpineList 0 (pre2 ++ [backCup])).partner.length :=
          congrArg (fun matchData => matchData.partner.length) appendedEqual
        rw [matchingPartnerLengthReflect, matchingPartnerLengthReflect] at partnerLenEq
        have owFullEq :
            (processSpine ⟨List.range 0, [], 0, 0⟩ (t1 ++ [C1])).openWires.length
              = (processSpine ⟨List.range 0, [], 0, 0⟩ (pre2 ++ [backCup])).openWires.length :=
          natAddLeftCancel 0 partnerLenEq
        rw [matchingOpenWiresCupEndSplit t1 C1 firstPureCup,
          matchingOpenWiresCupEndSplit pre2 backCup locPure] at owFullEq
        exact natAddRightCancel 2 owFullEq
      have boundaryEqual : backCup.domBoundaryLength = C1.domBoundaryLength := by
        have domBackEq : backCup.domBoundaryLength
            = (processSpine ⟨List.range 0, [], 0, 0⟩ pre2).openWires.length :=
          (processSpine_prefix_openWires_eq_lastDomBoundary 0 pre2 backCup locChained).symm
        have domC1Eq : C1.domBoundaryLength
            = (processSpine ⟨List.range 0, [], 0, 0⟩ t1).openWires.length :=
          (processSpine_prefix_openWires_eq_lastDomBoundary 0 t1 C1 chainedFirst).symm
        exact domBackEq.trans (owEqual.symm.trans domC1Eq.symm)
      have backEqC1 : backCup = C1 :=
        adjunctionSpineAtom_eq_of_readOffs_at_equalBoundaryLengths backCup C1 boundaryEqual backWindow
          (backDom.trans c1Dom.symm) (backCod.trans c1Cod.symm)
      subst backCup
      have matchPrefixEqual : matchingOfSpineList 0 t1 = matchingOfSpineList 0 pre2 :=
        dropLastCup_matching_injective t1 pre2 C1 chainedFirst locChained firstPureCup locPure
          appendedEqual
      have prefixTrace : SpineTraceEquiv adjunctionModeSignature t1 pre2 :=
        matchingPureCupSpineSortFueled fuel t1 pre2 t1LenBound prefixChainedFirst
          (spineBoundaryChained_prefix_ofAppend pre2 [C1] 0 locChained) t1Pure
          (allCupArity_prefix_ofAppend pre2 [C1] locPure) matchPrefixEqual
      exact (spineTraceEquiv_backAppendCongr prefixTrace C1).trans locEquiv.toSpineTraceEquiv.symm

/-- ★ **The width-0 pure-cup determinacy — GENERAL, POSITIVITY-FREE (Track B, c).**  Two boundary-chained
pure-cup spines over the width-`0` bottom boundary with EQUAL `matchingOfSpineList 0` are `SpineTraceEquiv`.
This is exactly `WidthZeroPureCupDeterminacy`: peel the last cup of the first spine (brick 1
`matchingLastCup_isShortChord`), read its short chord in the second, bubble the partner cup to the tail
(`matchingLocateAux`, b#5), pin it by boundary-length rigidity, drop both by matching-injectivity (brick 3
`dropLastCup_matching_injective`), recurse, and re-append.  NO arc census, NO `arcDiagram_eq_matching`, NO
`0 < bottomCount`. -/
theorem widthZeroPureCupDeterminacy_proof
    {overallSource overallTarget : adjunctionGraph.Mode}
    (firstList secondList :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (firstPureCup : AllCupArity firstList)
    (secondPureCup : AllCupArity secondList)
    (chainedFirst : SpineBoundaryChained 0 firstList)
    (chainedSecond : SpineBoundaryChained 0 secondList)
    (matchEqual : matchingOfSpineList 0 firstList = matchingOfSpineList 0 secondList) :
    SpineTraceEquiv adjunctionModeSignature firstList secondList :=
  matchingPureCupSpineSortFueled firstList.length firstList secondList (Nat.le_refl firstList.length)
    chainedFirst chainedSecond firstPureCup secondPureCup matchEqual

/-! ## Honesty marker -/

/-- **★ CLOSED — the width-0 pure-cup determinacy is landed, GENERAL and POSITIVITY-FREE (Track B b#5 + c).**
`widthZeroPureCupDeterminacy_proof`: two boundary-chained pure-cup spines over the width-`0` bottom boundary
with equal `matchingOfSpineList 0` are `SpineTraceEquiv` — with NO `0 < bottomCount` hypothesis.  This IS
the `WidthZeroPureCupDeterminacy` (`SpineValleyCellDegenerate`), discharged via the location induction
`matchingLocateAux` (b#5, riding the b#1 partner involution through the snake exclusion + the b#3/b#4
chord-shift descents + piece (a)'s positivity-free swap fold) and the sort assembly (c, riding brick 1 /
brick 3).  NO arc census, NO `arcDiagram_eq_matching`.

  This closes the crux Tier-D residual the FULL `CellValleyTraceEquiv` lift's case (a) consumes
  (`degenerateEmptySource_of_widthZero`).  It does NOT flip the fib-3 gate (that additionally needs case
  (b) `MidZeroValleyTraceEquiv`).  `convOfMapEq` and the fib-3 gate flags stay `false`.  `= true`. -/
def fxMode_hasMatchingWidthZeroSort : Bool := true

end FX1Poly.Polygraph
