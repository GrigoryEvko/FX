import FX1Poly.Polygraph.TwoCategory.WalkingString.StringMatchingWidthZeroChordShift
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringMatchingDropLastCup
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringDisjointWordSwap
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringDisjointWordBubble
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringWordChainSwapLeft
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringWordChainAppend
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringSpineTopWordSwapInvariant
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringLastCupSharedTopPin
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringValleyDegenerateSplit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringScrambledThreeCupPortProbe
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.MatchingSwapPeel
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.MatchingWidthZeroSnake
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupDropAndAppend
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupSortComplete
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupLastCupReadoff

/-! # WalkingString/StringWidthZeroPureCupSort — the width-0 pure-cup determinacy INHABITED at the
adjoint-triple seed (FC-3 r17, THE NOVEL ASSEMBLY)

The walking adjunction closes `WidthZeroPureCupDeterminacy` (`MatchingWidthZeroSort`) with a fueled
partner-LOCATE recursion (`matchingLocateAux`) feeding a Catalan sort assembly.  Its last-cup pin
(`adjunctionSpineAtom_eq_of_readOffs_at_equalBoundaryLengths`) is LENGTH-rigid — it upgrades a
domain-boundary LENGTH equality to a WORD equality via `adjunctionPath_eq_of_length_eq` (parallel 1-cells
of equal length are equal), which is FALSE at the walking adjoint triple (`string_left_ne_coLeft`: `F`, `H`
both length-1, distinct).  This file re-plumbs the whole recursion onto the shipped WORD machinery, thereby
INHABITING `StringWidthZeroPureCupDeterminacyShared` (`StringValleyDegenerateSplit`).

The one novel derivation: thread a SECOND parallel chain — the boundary-WORD chain
`SpineBoundaryWordChained bottomWord` — through the fueled locate/sort alongside the length chain, and swap
the length-rigid last-cup pin for the shipped SHARED-COD pin `stringSpineAtom_eq_of_sharedCod_sameWindow`
(`StringLastCupSharedTopPin`).  Everything else transports from the mirror verbatim modulo the signature
tokens: the matching-invariance peel `extractDiagram_eq_of_atomicPureCupTraceEquiv` is `{signature}`-generic,
the readoff / chord-shift / drop bricks are the shipped r16 PORTS, and the swap producers are the shipped
WORD swaps.

  * ★ `stringMatchingLocateAux` (NOVEL-B) — the width-0 location step at the adjoint-triple seed: the cup
    whose short chord sits at `targetWindow` bubbles to the tail, keeping BOTH the length chain and the WORD
    chain.  The `sharedWord` the WORD swaps consume is delivered by the shared TOP word (top-word invariance
    across the recursion's returned equiv, `spineListTopWord_atomicTraceEquiv`), NOT length rigidity; the
    moved list's WORD chain is threaded by `spineBoundaryWordChained_swappedPair` (case ii) /
    `spineBoundaryWordChained_swappedPairLeft` (case iii) re-glued through W2 `spineBoundaryWordChained_append`.

  * ★ `stringWidthZeroPureCupDeterminacyShared_proof` (NOVEL-C/D) — the crux: `StringWidthZeroPureCupDeterminacyShared`
    is INHABITED.  The fueled sort peels the shared last cup, reads its short chord in the second spine,
    bubbles the partner to the tail (`stringMatchingLocateAux`), pins it by the SHARED-COD word pin, drops both
    by matching-injectivity (PORT 3 `stringDropLastCup_matching_injective`), recurses handing the SHORTER shared
    top word, and re-appends.  The base floor is NIL (`stringMatchingPureCupSpine_sort_nil`).

  * ★ `stringDegenerateEmptySource_of_widthZero_proved` (the case-(a) consumer) — the empty-source Tier-D
    dispatcher, now UNCONDITIONAL: `stringDegenerateEmptySource_of_widthZero` fed the inhabited determinacy.

Raw Lean 4 + Init; structural / fuel recursion (fuel `Nat` per the list-length source recursion), no `omega`
/ `simp`-AC / `WellFounded.fix`.  `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free;
per-declaration `#assert_no_axioms` gated in the audit twin.

What this does NOT flip: `fxString_hasWordBubbleSortAssembly` stays `false` (its docstring demands the pure-block
sort assembly INTO `StringCellValleyTraceEquiv` plus the valley-append `matchingOf`-split #2186 — strictly more
than this ONE sub-producer delivers), and `fxString_hasAdjointTripleCompleteness` stays `false` (needs all THREE
sub-producers).  This round flips the NEW `fxString_hasWidthZeroPureCupSort`. -/

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

/-- The empty width-0 string spine has no forward chord (partner list is empty).  Per-file copy of the
private `stringEmptyMatchingNoForwardChord` (a `noConfusion` on the fallback zero, census-free). -/
private theorem emptyMatchingNoForwardChordCopy
    {overallSource overallTarget : adjointTripleGraph.Mode} (targetWindow : Nat)
    (chordAt : natListGetAt
        (matchingOfSpineList 0
          ([] : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))).partner
        (0 + targetWindow)
      = 0 + targetWindow + 1) : False := by
  have partnerNil : (matchingOfSpineList 0
      ([] : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))).partner = [] := rfl
  rw [partnerNil] at chordAt
  have readZero : natListGetAt ([] : List Nat) (0 + targetWindow) = 0 := rfl
  rw [readZero] at chordAt
  exact Nat.noConfusion chordAt

/-- The last cup's short chord at index `0 + w` (reconciling PORT 1's bare-`w` readoff to the `0 +` form the
locate reads). -/
private theorem stringMatchingLastCup_isShortChord_zeroForm
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (prefixAtoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (lastCup : SpineAtom adjointTripleModeSignature overallSource overallTarget)
    (chained : SpineBoundaryChained 0 (prefixAtoms ++ [lastCup]))
    (pureCup : AllCupArity (prefixAtoms ++ [lastCup])) :
    natListGetAt (matchingOfSpineList 0 (prefixAtoms ++ [lastCup])).partner
        (0 + lastCup.leftContext.length)
      = 0 + lastCup.leftContext.length + 1 := by
  rw [Nat.zero_add]
  exact stringMatchingLastCup_isShortChord prefixAtoms lastCup chained pureCup

/-- A non-empty spine's top word is its LAST atom's cod boundary word.  `spineListTopWord` discards the
running word at the singleton suffix, so `spineListTopWord bw (prefixAtoms ++ [lastAtom])` reduces to
`lastAtom.leftContext · lastAtom.generatorCod · lastAtom.rightContext`. -/
private theorem spineListTopWord_snoc {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (bottomWord : ModalityPath signature.graph sourceMode targetMode)
    (prefixAtoms : List (SpineAtom signature sourceMode targetMode))
    (lastAtom : SpineAtom signature sourceMode targetMode) :
    spineListTopWord bottomWord (prefixAtoms ++ [lastAtom])
      = composePath lastAtom.leftContext (composePath lastAtom.generatorCod lastAtom.rightContext) := by
  rw [spineListTopWord_append bottomWord prefixAtoms [lastAtom]]
  dsimp only [spineListTopWord]

/-! ### `stringMatchingLocateAux` — bubble the target cup (by chord window) to the spine's tail, threading
BOTH the length chain and the WORD chain -/

private theorem stringMatchingLocateAuxFueled
    {overallSource overallTarget : adjointTripleGraph.Mode} :
    (fuel : Nat) →
    (bottomWord : ModalityPath adjointTripleGraph overallSource overallTarget) →
    (spine : List (SpineAtom adjointTripleModeSignature overallSource overallTarget)) →
    spine.length ≤ fuel →
    SpineBoundaryChained 0 spine →
    SpineBoundaryWordChained bottomWord spine →
    AllCupArity spine →
    (targetWindow : Nat) →
    natListGetAt (matchingOfSpineList 0 spine).partner (0 + targetWindow)
      = 0 + targetWindow + 1 →
    ∃ movedPrefix backCup,
      AtomicTraceEquiv adjointTripleModeSignature spine (movedPrefix ++ [backCup])
        ∧ matchingOfSpineList 0 spine = matchingOfSpineList 0 (movedPrefix ++ [backCup])
        ∧ AllCupArity (movedPrefix ++ [backCup])
        ∧ SpineBoundaryChained 0 (movedPrefix ++ [backCup])
        ∧ SpineBoundaryWordChained bottomWord (movedPrefix ++ [backCup])
        ∧ backCup.leftContext.length = targetWindow
  | 0, _, spine, lengthBound, _, _, _, targetWindow, chordAt => by
      cases listNilOrSnoc spine with
      | inl spineNil => subst spineNil
                        exact (emptyMatchingNoForwardChordCopy targetWindow chordAt).elim
      | inr snocWit =>
          obtain ⟨t, Clast, spineSnoc⟩ := snocWit
          subst spineSnoc
          rw [lengthSnoc] at lengthBound
          exact absurd lengthBound (Nat.not_succ_le_zero _)
  | fuel + 1, bottomWord, spine, lengthBound, chained, wordChained, pureCup, targetWindow, chordAt => by
      cases listNilOrSnoc spine with
      | inl spineNil => subst spineNil
                        exact (emptyMatchingNoForwardChordCopy targetWindow chordAt).elim
      | inr snocWit =>
      obtain ⟨t, Clast, spineSnoc⟩ := snocWit
      subst spineSnoc
      have tLenBound : t.length ≤ fuel := by
        rw [lengthSnoc] at lengthBound; exact Nat.le_of_succ_le_succ lengthBound
      have prefixChained : SpineBoundaryChained 0 t :=
        spineBoundaryChained_prefix_ofAppend t [Clast] 0 chained
      have tPure : AllCupArity t := allCupArity_prefix_ofAppend t [Clast] pureCup
      have prefixWordChained : SpineBoundaryWordChained bottomWord t :=
        spineBoundaryWordChained_prefix_ofAppend bottomWord t [Clast] wordChained
      have clastChord := stringMatchingLastCup_isShortChord_zeroForm t Clast chained pureCup
      obtain ⟨clastDom, clastCod⟩ := allCupArity_lastCup_arity t Clast pureCup
      have owSplit := matchingOpenWiresCupEndSplit t Clast pureCup
      have windowFits : Clast.leftContext.length
          ≤ (processSpine ⟨List.range 0, [], 0, 0⟩ t).openWires.length := by
        rw [stringProcessSpine_prefix_openWires_eq_lastDomBoundary 0 t Clast chained]
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
        have chordInT := stringMatchingChordShift_below t Clast chained pureCup targetWindow below chordAt
        obtain ⟨pre', Csigma, atomicEquivT, _matchEqT, pureT', _chainedT', wordChainedT', sigWindow⟩ :=
          stringMatchingLocateAuxFueled fuel bottomWord t tLenBound prefixChained prefixWordChained
            tPure targetWindow chordInT
        obtain ⟨_sigDom, sigCod⟩ := allCupArity_lastCup_arity pre' Csigma pureT'
        obtain ⟨windowGap, gapSpec⟩ := Nat.le.dest wlastGe
        -- the shared word: Csigma's cod word = Clast's dom word, from the shared TOP word (top-word
        -- invariance across the recursion's returned equiv), NOT length rigidity.
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
            ⟨List.range 0, [], 0, 0⟩ 0 0 (wireStateFresh_initial 0) isUnionFindForest_nil
            (Nat.zero_le 0) rfl chained pureCup
        · exact allCupArity_preservedOfAtomicTraceEquiv fullEquivCasted pureCup
        · exact (spineBoundaryChained_iff_of_atomicTraceEquiv fullEquivCasted 0).mp chained
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
        have chordInT := stringMatchingChordShift_above t Clast chained pureCup targetWindow aboveW chordAt
        obtain ⟨pre', Csigma, atomicEquivT, _matchEqT, pureT', _chainedT', wordChainedT', sigWindow⟩ :=
          stringMatchingLocateAuxFueled fuel bottomWord t tLenBound prefixChained prefixWordChained
            tPure (targetWindow - 2) chordInT
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
            ⟨List.range 0, [], 0, 0⟩ 0 0 (wireStateFresh_initial 0) isUnionFindForest_nil
            (Nat.zero_le 0) rfl chained pureCup
        · exact allCupArity_preservedOfAtomicTraceEquiv fullEquivCasted pureCup
        · exact (spineBoundaryChained_iff_of_atomicTraceEquiv fullEquivCasted 0).mp chained
        · rw [snocSnocRegroup pre']
          exact spineBoundaryWordChained_append bottomWord pre' _ preWordChained movedPairChained
        · show (composePath (composePath Clast.leftContext Clast.generatorCod) inertPath).length
            = targetWindow
          rw [ModalityPath.length_composePath, ModalityPath.length_composePath, inertLen, clastCod]
          exact gapSpec

/-- ★ **The width-0 location step at the adjoint-triple seed.**  In a boundary-chained AND
boundary-word-chained pure-cup spine, the cup whose short chord sits at `targetWindow` bubbles to the tail,
keeping BOTH chains and the `matchingOfSpineList 0`.  The `sharedWord` the WORD swap consumes is delivered by
the shared TOP word (`spineListTopWord_atomicTraceEquiv`), NOT length rigidity. -/
theorem stringMatchingLocateAux
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (bottomWord : ModalityPath adjointTripleGraph overallSource overallTarget)
    (spine : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained 0 spine)
    (wordChained : SpineBoundaryWordChained bottomWord spine)
    (pureCup : AllCupArity spine)
    (targetWindow : Nat)
    (chordAt : natListGetAt (matchingOfSpineList 0 spine).partner (0 + targetWindow)
      = 0 + targetWindow + 1) :
    ∃ movedPrefix backCup,
      AtomicTraceEquiv adjointTripleModeSignature spine (movedPrefix ++ [backCup])
        ∧ matchingOfSpineList 0 spine = matchingOfSpineList 0 (movedPrefix ++ [backCup])
        ∧ AllCupArity (movedPrefix ++ [backCup])
        ∧ SpineBoundaryChained 0 (movedPrefix ++ [backCup])
        ∧ SpineBoundaryWordChained bottomWord (movedPrefix ++ [backCup])
        ∧ backCup.leftContext.length = targetWindow :=
  stringMatchingLocateAuxFueled spine.length bottomWord spine (Nat.le_refl spine.length) chained
    wordChained pureCup targetWindow chordAt

/-! ### The base case + the WORD-threaded sort assembly -/

/-- A pure-cup width-0 string spine whose processed open-wire count is `0` is empty.  Re-copy of the
adjunction's `pureCupSpine_nil_ofOpenWiresZero` (generic `matchingOpenWiresCupEndSplit`). -/
private theorem stringPureCupSpine_nil_ofOpenWiresZero
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (spine : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
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

/-- The base floor: an empty first spine with equal width-0 matching forces the second spine empty. -/
private theorem stringMatchingPureCupSpine_sort_nil
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (secondList : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (secondPureCup : AllCupArity secondList)
    (matchEqual : matchingOfSpineList 0
        ([] : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
      = matchingOfSpineList 0 secondList) :
    SpineTraceEquiv adjointTripleModeSignature [] secondList := by
  have topEq : (matchingOfSpineList 0
      ([] : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))).topCount
      = (matchingOfSpineList 0 secondList).topCount := congrArg DiagramType.topCount matchEqual
  have owZero : (processSpine ⟨List.range 0, [], 0, 0⟩ secondList).openWires.length = 0 :=
    topEq.symm
  have secondNil : secondList = [] := stringPureCupSpine_nil_ofOpenWiresZero secondList secondPureCup owZero
  rw [secondNil]
  exact SpineTraceEquiv.refl []

/-- Back-append congruence for the string block-level trace equivalence: appending a fixed trailing atom to
both sides of a `SpineTraceEquiv` preserves it.  Routed through the ATOM granularity (both maps generic):
`spineTraceEquiv_iff_atomicTraceEquiv` + `atomicTraceEquiv_backAppendCongr`.  The three-generator analogue of
the adjunction-locked `spineTraceEquiv_backAppendCongr`. -/
theorem stringSpineTraceEquiv_backAppendCongr
    {overallSource overallTarget : adjointTripleGraph.Mode}
    {firstList secondList :
      List (SpineAtom adjointTripleModeSignature overallSource overallTarget)}
    (equiv : SpineTraceEquiv adjointTripleModeSignature firstList secondList)
    (tailAtom : SpineAtom adjointTripleModeSignature overallSource overallTarget) :
    SpineTraceEquiv adjointTripleModeSignature (firstList ++ [tailAtom]) (secondList ++ [tailAtom]) :=
  spineTraceEquiv_iff_atomicTraceEquiv.mpr
    (atomicTraceEquiv_backAppendCongr
      (spineTraceEquiv_iff_atomicTraceEquiv.mp equiv) tailAtom)

private theorem stringMatchingPureCupSpineSortFueled
    {overallSource overallTarget : adjointTripleGraph.Mode} :
    (fuel : Nat) →
    (bottomWord : ModalityPath adjointTripleGraph overallSource overallTarget) →
    (firstList secondList :
      List (SpineAtom adjointTripleModeSignature overallSource overallTarget)) →
    firstList.length ≤ fuel →
    SpineBoundaryChained 0 firstList →
    SpineBoundaryChained 0 secondList →
    SpineBoundaryWordChained bottomWord firstList →
    SpineBoundaryWordChained bottomWord secondList →
    spineListTopWord bottomWord firstList = spineListTopWord bottomWord secondList →
    AllCupArity firstList →
    AllCupArity secondList →
    matchingOfSpineList 0 firstList = matchingOfSpineList 0 secondList →
    SpineTraceEquiv adjointTripleModeSignature firstList secondList
  | 0, _, firstList, secondList, lengthBound, _, _, _, _, _, _, secondPureCup, matchEqual => by
      cases listNilOrSnoc firstList with
      | inl firstNil => subst firstNil
                        exact stringMatchingPureCupSpine_sort_nil secondList secondPureCup matchEqual
      | inr snocWit =>
          obtain ⟨t1, C1, firstSnoc⟩ := snocWit
          subst firstSnoc
          rw [lengthSnoc] at lengthBound
          exact absurd lengthBound (Nat.not_succ_le_zero _)
  | fuel + 1, bottomWord, firstList, secondList, lengthBound, chainedFirst, chainedSecond,
      firstWordChained, secondWordChained, topWordEq, firstPureCup, secondPureCup, matchEqual => by
      cases listNilOrSnoc firstList with
      | inl firstNil => subst firstNil
                        exact stringMatchingPureCupSpine_sort_nil secondList secondPureCup matchEqual
      | inr snocWit =>
      obtain ⟨t1, C1, firstSnoc⟩ := snocWit
      subst firstSnoc
      have t1LenBound : t1.length ≤ fuel := by
        rw [lengthSnoc] at lengthBound; exact Nat.le_of_succ_le_succ lengthBound
      have prefixChainedFirst : SpineBoundaryChained 0 t1 :=
        spineBoundaryChained_prefix_ofAppend t1 [C1] 0 chainedFirst
      have t1Pure : AllCupArity t1 := allCupArity_prefix_ofAppend t1 [C1] firstPureCup
      have prefixWordChainedFirst : SpineBoundaryWordChained bottomWord t1 :=
        spineBoundaryWordChained_prefix_ofAppend bottomWord t1 [C1] firstWordChained
      obtain ⟨c1Dom, c1Cod⟩ := allCupArity_lastCup_arity t1 C1 firstPureCup
      have c1Chord := stringMatchingLastCup_isShortChord_zeroForm t1 C1 chainedFirst firstPureCup
      have chordSecond : natListGetAt
          (matchingOfSpineList 0 secondList).partner (0 + C1.leftContext.length)
        = 0 + C1.leftContext.length + 1 := by rw [← matchEqual]; exact c1Chord
      obtain ⟨pre2, backCup, locEquiv, locMatch, locPure, locChained, locWordChained, backWindow⟩ :=
        stringMatchingLocateAux bottomWord secondList chainedSecond secondWordChained secondPureCup
          C1.leftContext.length chordSecond
      obtain ⟨backDom, backCod⟩ := allCupArity_lastCup_arity pre2 backCup locPure
      have appendedEqual := matchEqual.trans locMatch
      -- the shared-cod word for the pin: backCup's cod word = C1's cod word, via the shared TOP word.
      have c1CodIsTop : spineListTopWord bottomWord (t1 ++ [C1])
          = composePath C1.leftContext (composePath C1.generatorCod C1.rightContext) :=
        spineListTopWord_snoc bottomWord t1 C1
      have backCupCodIsTop : spineListTopWord bottomWord (pre2 ++ [backCup])
          = composePath backCup.leftContext (composePath backCup.generatorCod backCup.rightContext) :=
        spineListTopWord_snoc bottomWord pre2 backCup
      have secondTopEqBackCod : spineListTopWord bottomWord secondList
          = composePath backCup.leftContext (composePath backCup.generatorCod backCup.rightContext) :=
        (spineListTopWord_atomicTraceEquiv locEquiv bottomWord).trans backCupCodIsTop
      have codBoundaryWordsEqual :
          composePath backCup.leftContext (composePath backCup.generatorCod backCup.rightContext)
            = composePath C1.leftContext (composePath C1.generatorCod C1.rightContext) :=
        secondTopEqBackCod.symm.trans (topWordEq.symm.trans c1CodIsTop)
      have backEqC1 : backCup = C1 :=
        stringSpineAtom_eq_of_sharedCod_sameWindow backCup C1 codBoundaryWordsEqual backWindow
          (backCod.trans c1Cod.symm) backDom c1Dom
      subst backCup
      have matchPrefixEqual : matchingOfSpineList 0 t1 = matchingOfSpineList 0 pre2 :=
        stringDropLastCup_matching_injective t1 pre2 C1 chainedFirst locChained firstPureCup locPure
          appendedEqual
      -- the shorter shared top word for the recursion: both prefixes top out at C1's dom word.
      have shorterTopWordEq : spineListTopWord bottomWord t1 = spineListTopWord bottomWord pre2 :=
        (spineListTopWord_prefix_eq_lastDomWord bottomWord t1 C1 firstWordChained).trans
          (spineListTopWord_prefix_eq_lastDomWord bottomWord pre2 C1 locWordChained).symm
      have prefixTrace : SpineTraceEquiv adjointTripleModeSignature t1 pre2 :=
        stringMatchingPureCupSpineSortFueled fuel bottomWord t1 pre2 t1LenBound prefixChainedFirst
          (spineBoundaryChained_prefix_ofAppend pre2 [C1] 0 locChained)
          prefixWordChainedFirst
          (spineBoundaryWordChained_prefix_ofAppend bottomWord pre2 [C1] locWordChained)
          shorterTopWordEq t1Pure
          (allCupArity_prefix_ofAppend pre2 [C1] locPure) matchPrefixEqual
      exact (stringSpineTraceEquiv_backAppendCongr prefixTrace C1).trans locEquiv.toSpineTraceEquiv.symm

/-- ★★ **The width-0 pure-cup determinacy — INHABITED at the adjoint-triple seed (FC-3 r17, NOVEL-C/D).**
`StringWidthZeroPureCupDeterminacyShared`: two boundary-chained AND boundary-word-chained pure-cup string
spines over the width-`0` bottom boundary that share their `spineListTopWord` and have EQUAL
`matchingOfSpineList 0` are `SpineTraceEquiv`.  Peel the last cup of the first spine (PORT 1
`stringMatchingLastCup_isShortChord`), read its short chord in the second, bubble the partner cup to the tail
(`stringMatchingLocateAux`), pin it by the SHARED-COD word pin `stringSpineAtom_eq_of_sharedCod_sameWindow`
(NOT length rigidity), drop both by matching-injectivity (PORT 3 `stringDropLastCup_matching_injective`),
recurse handing the SHORTER shared top word, and re-append.  Seeds the fuel at `cupFirst.length`. -/
theorem stringWidthZeroPureCupDeterminacyShared_proof : StringWidthZeroPureCupDeterminacyShared := by
  intro overallSource overallTarget bottomWord cupFirst cupSecond pureA pureB chained0A chained0B
    wordA wordB topWordEq matchEq
  exact stringMatchingPureCupSpineSortFueled cupFirst.length bottomWord cupFirst cupSecond
    (Nat.le_refl cupFirst.length) chained0A chained0B wordA wordB topWordEq pureA pureB matchEq

/-! ## The unconditional case-(a) consumer -/

/-- ★ **Tier-D case (a), now UNCONDITIONAL.**  The empty-source dispatcher
`stringDegenerateEmptySource_of_widthZero` (`StringValleyDegenerateSplit`) fed the now-inhabited
`stringWidthZeroPureCupDeterminacyShared_proof`: when `sourcePath.length = 0`, two whole valleys with equal
boundary `matchingOf` have `SpineTraceEquiv` spines — with NO hypothesis on the determinacy Prop. -/
theorem stringDegenerateEmptySource_of_widthZero_proved
    {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    (valleyA valleyB : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath)
    (isValleyA : isCapThenCupValley SpineAtom.isCupAtom valleyA.spine = true)
    (isValleyB : isCapThenCupValley SpineAtom.isCupAtom valleyB.spine = true)
    (matchingEq : matchingOf valleyA = matchingOf valleyB)
    (sourceZero : sourcePath.length = 0) :
    SpineTraceEquiv adjointTripleModeSignature valleyA.spine valleyB.spine :=
  stringDegenerateEmptySource_of_widthZero stringWidthZeroPureCupDeterminacyShared_proof
    valleyA valleyB isValleyA isValleyB matchingEq sourceZero

/-! ## Concrete truth-probes (anti-vacuity) -/

/-- ★ **The locate fires on the r16 three-cup rainbow.**  Locating window `0` in the concrete three-cup
width-0 spine (its outer cup fires at window `0`, chord `0 ↦ 1`) returns a back cup at window `0` — a
machine-checked non-vacuity witness that `stringMatchingLocateAux` runs the whole locate machinery on a
genuinely `SpineBoundaryChained 0` + `SpineBoundaryWordChained` pure-cup spine. -/
theorem stringLocateThreeCupProbe_partnerWindowZero :
    ∃ movedPrefix backCup,
      AtomicTraceEquiv adjointTripleModeSignature stringProbeThreeCupSpine (movedPrefix ++ [backCup])
        ∧ matchingOfSpineList 0 stringProbeThreeCupSpine
            = matchingOfSpineList 0 (movedPrefix ++ [backCup])
        ∧ AllCupArity (movedPrefix ++ [backCup])
        ∧ SpineBoundaryChained 0 (movedPrefix ++ [backCup])
        ∧ SpineBoundaryWordChained
            (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base)
            (movedPrefix ++ [backCup])
        ∧ backCup.leftContext.length = 0 :=
  stringMatchingLocateAux (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base)
    stringProbeThreeCupSpine stringProbeThreeCup_chained stringScrambledThreeCup_wordChainThreads
    stringProbeThreeCup_pureCup 0 stringScrambledThreeCup_lastCupShortChord

/-- ★ **The whole width-0 sort fires end-to-end on the r16 three-cup rainbow.**  Applying the inhabited
determinacy to the concrete three-cup width-0 rainbow (as both arguments — equal matching, shared top word)
runs the FULL machinery — peel, locate, shared-cod pin, matching-injective drop, recurse — producing a
`SpineTraceEquiv`.  A machine-checked end-to-end firing (the case-(i) locate path at each descent). -/
theorem stringWidthZeroPureCupSort_firesOnThreeCupRainbow :
    SpineTraceEquiv adjointTripleModeSignature stringProbeThreeCupSpine stringProbeThreeCupSpine :=
  stringWidthZeroPureCupDeterminacyShared_proof
    (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base)
    stringProbeThreeCupSpine stringProbeThreeCupSpine
    stringProbeThreeCup_pureCup stringProbeThreeCup_pureCup
    stringProbeThreeCup_chained stringProbeThreeCup_chained
    stringScrambledThreeCup_wordChainThreads stringScrambledThreeCup_wordChainThreads
    rfl rfl

/-! ## Honesty marker -/

/-- **★ CLOSED — the width-0 pure-cup determinacy is INHABITED at the adjoint-triple seed (FC-3 r17, THE
NOVEL ASSEMBLY).**  `stringWidthZeroPureCupDeterminacyShared_proof` inhabits
`StringWidthZeroPureCupDeterminacyShared` (`StringValleyDegenerateSplit`) — two width-0 pure-cup string spines
sharing their `spineListTopWord` with equal `matchingOfSpineList 0` are `SpineTraceEquiv` — via the fueled
partner-LOCATE `stringMatchingLocateAux` and the WORD-threaded sort assembly.  The single novel derivation
threads a boundary-WORD chain alongside the length chain and swaps the walking-adjunction's length-rigid
last-cup pin (`adjunctionSpineAtom_eq_of_readOffs_at_equalBoundaryLengths`, whose `adjunctionPath_eq_of_length_eq`
upgrade is FALSE at the string) for the shipped SHARED-COD word pin `stringSpineAtom_eq_of_sharedCod_sameWindow`,
delivering the `sharedWord` the WORD swaps consume from the shared TOP word (`spineListTopWord_atomicTraceEquiv`).
Everything else transports verbatim: the matching-invariance peel `extractDiagram_eq_of_atomicPureCupTraceEquiv`
is `{signature}`-generic, the readoff / chord-shift / drop bricks are the r16 PORTS, the swaps are the shipped
WORD swaps (`spineAtomSwap_of_wordFactorization`, `spineAtomSwapLeft_of_wordFactorization`), and the moved-list
WORD chain is threaded by `spineBoundaryWordChained_swappedPair{,Left}` re-glued through W2
`spineBoundaryWordChained_append`.  `stringDegenerateEmptySource_of_widthZero_proved` is the now-unconditional
Tier-D case-(a) consumer.  Truth-probes `stringLocateThreeCupProbe_partnerWindowZero` and
`stringWidthZeroPureCupSort_firesOnThreeCupRainbow` fire the locate and the whole sort concretely.

  What this marker does NOT close (no gate flag flips beyond this one): `fxString_hasWordBubbleSortAssembly`
  (`StringDisjointWordBubble`) stays `false` — its docstring demands the pure-block sort assembly INTO
  `StringCellValleyTraceEquiv` PLUS the valley-append `matchingOf`-split (#2186), strictly more than this ONE
  sub-producer delivers; and `fxString_hasAdjointTripleCompleteness` (`StringMatchingCompleteness`) stays
  `false` — it needs all THREE sub-producers (`StringMidZeroValleyTraceEquiv`,
  `StringCellValleyTraceEquivPositive` remain colour-keyed residuals).  This round inhabits ONE of the three:
  the width-0 pure-cup determinacy sub-producer.  `= true`. -/
def fxString_hasWidthZeroPureCupSort : Bool := true

end FX1Poly.Polygraph
