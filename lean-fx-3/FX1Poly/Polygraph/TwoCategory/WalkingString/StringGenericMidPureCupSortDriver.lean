import FX1Poly.Polygraph.TwoCategory.WalkingString.StringGenericMidSnakeLocate
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringPositiveMidPureCupSort

/-! # WalkingString — the GENERIC FUELED CUP-SORT DRIVER + the ANY-WIDTH determinacy
(FC-4 r7, the driver tranche of the generic cup-sort chain)

THE SORT DRIVER: ONE fueled fold, generic over `AdjointStringConnectivity × midWidth`, NO positivity premise —
the selection-sort shape (fuel = first spine's length, one cup peeled per step, completeness keyed on the fuel
bound per the VFA "Selection" template): peel the shared last cup of the first spine (the r6 short-chord
readoff), read its chord in the second, bubble the partner cup to the tail (the r7 any-width fueled LOCATE),
pin it by the SHARED-COD word pin (the r5 B2 generic cup pin — the census bill's rerouted atom pin, consumed at
the exact node the refuted dom→cod pin used to occupy), drop both by matching-injectivity (the r6 generic drop),
recurse handing the SHORTER shared top word, and re-append.  The base floor forces the second spine empty from
the survivor open-wire count — at EVERY `midWidth` (the `topCount = midWidth` read needs no positivity).

  * ★★ `genericMatchingPureCupSpineSortFueledMid` — the fueled word-threaded sort over the class, at ANY
    `midWidth` (private; the fuel-keyed completeness form).
  * ★★ `GenericMidPureCupDeterminacy cls` / `genericMidPureCupDeterminacy_proof` — the ANY-WIDTH determinacy:
    two boundary-chained AND boundary-word-chained pure-cup spines over the SAME `midWidth` bottom boundary
    sharing their `spineListTopWord` with EQUAL `matchingOfSpineList midWidth` are `SpineTraceEquiv`.  STRONGER
    than both shipped `k = 2` bricks: no `0 < midWidth` premise, one statement covering the width-`0` AND
    positive-mid lanes.

## The HONESTY LAW — fired at `k = 2` AND `k = 3`

  * ★ `k = 2` recovery, BOTH shipped bricks: at `adjointStringConnectivityAtTwo` the generic determinacy
    re-derives the NAMED shipped `stringPositiveMidPureCupDeterminacy_proof` (dropping its positivity premise)
    AND — at `midWidth := 0` — the NAMED shipped `stringWidthZeroPureCupDeterminacyShared_proof`, each via the
    `shippedInhabitant` / `viaGenericClassAtTwo` pair on the LITERAL shipped statement.
  * ★ `k = 2` fire: the generic driver runs on the shipped distinct double-cup pair at `midWidth = 2`
    (`stringPositiveMidDistinctDoubleCup{LeftFirst,RightFirst}`, genuinely distinct spines with equal matching).
  * ★ `k = 3` fires (the FRESH `k = 3` SORT FIXTURES the census bill names): the quadruple decision runs on
      - the width-`0` DISTINCT-GENERATOR two-order pair `[η1@0, η3@2]` vs `[η3@0, η1@0]` — distinct generator
        sequences the boundary matching cannot separate (equal matchings `[1,0,3,2]`, `by decide`-pinned), the
        exact "fresh `k = 3` sort fixtures running end-to-end" clause;
      - the mid-`2` DISTINCT pair over the `L3·L4` survivor strands (equal matchings `[4,5,3,2,0,1,7,6]`,
        `by decide`-pinned) — the positive-width regime with through-strand re-ranking;
      - the NESTED-cup rainbow `[η1@0, η2@1]` (nested matching `[3,2,1,0]`, `by decide`-pinned) — the driver
        peels through a nested chord configuration.
    (A CROSSING-heavy pure-cup pair does not exist: cup insertions only produce planar nested/disjoint chords —
    the matching of a pure-cup spine is non-crossing, so "crossing-heavy" inputs are structurally impossible in
    the cup-sort's domain; recorded honestly here rather than faked.)
  * Negative controls: the two `k = 3` width-`0` orders carry DISTINCT generator sequences (window projections
    `[0, 2] ≠ [0, 0]`, `by decide`) and distinct head cods (`quadIndexWord`-separated) — `SpineTraceEquiv.refl`
    cannot inhabit the fired conclusions.

## What this file does NOT do (the FLIP LAW, honest round boundary)

The census marker `fxString_hasNColourAtomPinReroute` (`StringKParameterizationCensus`) STAYS `false` in THIS
file: the closure adjudication of its bill — clause by clause against the delivered vehicles — lives in the
sibling `StringNColourAtomPinRerouteClosure`, which supersedes the frozen owner by content marker.

ADDITIVE ONLY: no shipped WalkingString file is touched.  Raw Lean 4 + Init; structural / fuel recursion (fuel
`Nat` per the list-length source recursion), no `omega` / `simp`-AC / `WellFounded.fix`;
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free.  Per-declaration `#assert_no_axioms`
gated in the audit twin plus an INDEPENDENT `#print axioms` witness. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private plumbing (per-file copies with a distinct `GCS` suffix) -/

private theorem listNilOrSnocGCS {carrier : Type _} :
    (list : List carrier) → list = [] ∨ ∃ prefixAtoms lastAtom, list = prefixAtoms ++ [lastAtom]
  | [] => Or.inl rfl
  | headAtom :: restAtoms =>
      match listNilOrSnocGCS restAtoms with
      | Or.inl restNil => Or.inr ⟨[], headAtom, by subst restNil; rfl⟩
      | Or.inr ⟨prefixAtoms, lastAtom, restSnoc⟩ =>
          Or.inr ⟨headAtom :: prefixAtoms, lastAtom, by subst restSnoc; rfl⟩

private theorem lengthSnocGCS {carrier : Type _} :
    (prefixAtoms : List carrier) → (lastAtom : carrier) →
    (prefixAtoms ++ [lastAtom]).length = prefixAtoms.length + 1
  | [], _ => rfl
  | _ :: restAtoms, lastAtom => congrArg Nat.succ (lengthSnocGCS restAtoms lastAtom)

private theorem rangeLoopLengthGCS : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      have inner := rangeLoopLengthGCS count (count :: accumulated)
      show (List.range.loop count (count :: accumulated)).length = count + 1 + accumulated.length
      rw [inner]
      show count + (accumulated.length + 1) = count + 1 + accumulated.length
      rw [← Nat.add_assoc count accumulated.length 1, Nat.add_right_comm count accumulated.length 1]

private theorem rangeLengthGCS (count : Nat) : (List.range count).length = count := by
  show (List.range.loop count []).length = count
  rw [rangeLoopLengthGCS count []]; exact Nat.add_zero count

/-- A non-empty spine's top word is its LAST atom's cod boundary word (generic, seed-independent). -/
private theorem spineListTopWordSnocGCS {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (bottomWord : ModalityPath signature.graph sourceMode targetMode)
    (prefixAtoms : List (SpineAtom signature sourceMode targetMode))
    (lastAtom : SpineAtom signature sourceMode targetMode) :
    spineListTopWord bottomWord (prefixAtoms ++ [lastAtom])
      = composePath lastAtom.leftContext (composePath lastAtom.generatorCod lastAtom.rightContext) := by
  rw [spineListTopWord_append bottomWord prefixAtoms [lastAtom]]
  dsimp only [spineListTopWord]

/-! ## The back-append congruence for the block-level trace equivalence (`{signature}`-generic) -/

/-- Back-append congruence for the block-level trace equivalence, over ANY signature: appending a fixed
trailing atom to both sides of a `SpineTraceEquiv` preserves it.  Routed through the ATOM granularity (both
maps `{signature}`-generic): `spineTraceEquiv_iff_atomicTraceEquiv` + `atomicTraceEquiv_backAppendCongr`.  The
generic replacement for the shipped adjoint-triple-locked `stringSpineTraceEquiv_backAppendCongr`. -/
theorem genericSpineTraceEquiv_backAppendCongr {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (equiv : SpineTraceEquiv signature firstList secondList)
    (tailAtom : SpineAtom signature overallSource overallTarget) :
    SpineTraceEquiv signature (firstList ++ [tailAtom]) (secondList ++ [tailAtom]) :=
  spineTraceEquiv_iff_atomicTraceEquiv.mpr
    (atomicTraceEquiv_backAppendCongr
      (spineTraceEquiv_iff_atomicTraceEquiv.mp equiv) tailAtom)

/-! ## The base-floor apparatus (`{signature}`-generic): a pure-cup spine at survivor open-wire count is empty -/

/-- The processed open-wire count of a pure-cup spine is monotone in the fold: every cup step ADDS two wires. -/
private theorem genericPureCupOpenWiresMonotoneGCS {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode} :
    (spine : List (SpineAtom signature overallSource overallTarget)) →
    AllCupArity spine → (state : WireState) →
    state.openWires.length ≤ (processSpine state spine).openWires.length
  | [], _, _ => Nat.le_refl _
  | atom :: rest, pureCup, state => by
      cases pureCup with
      | cons hdom hcod restPure =>
          have stepEq : stepAtom state atom = stepCup state atom.leftContext.length :=
            stepAtom_ofCupArity state atom hdom hcod
          have grow : state.openWires.length ≤ (stepAtom state atom).openWires.length := by
            rw [stepEq]
            have stepLen : (stepCup state atom.leftContext.length).openWires.length
                = state.openWires.length + 2 :=
              natListInsertAt_length state.openWires atom.leftContext.length
                [state.nextFresh, state.nextFresh + 1]
            rw [stepLen]
            exact Nat.le_add_right _ 2
          have ih := genericPureCupOpenWiresMonotoneGCS rest restPure (stepAtom state atom)
          show state.openWires.length ≤ (processSpine (stepAtom state atom) rest).openWires.length
          exact Nat.le_trans grow ih

/-- The processed open-wire count of a pure-cup spine at the `midWidth` seed is at least `midWidth`. -/
private theorem genericPureCupOpenWiresGeMidGCS {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    (midWidth : Nat)
    (spine : List (SpineAtom signature overallSource overallTarget))
    (pureCup : AllCupArity spine) :
    midWidth ≤ (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ spine).openWires.length := by
  have mono := genericPureCupOpenWiresMonotoneGCS spine pureCup ⟨List.range midWidth, [], midWidth, 0⟩
  have seedLen : (⟨List.range midWidth, [], midWidth, 0⟩ : WireState).openWires.length = midWidth := by
    show (List.range midWidth).length = midWidth
    exact rangeLengthGCS midWidth
  rw [seedLen] at mono
  exact mono

/-- A pure-cup spine whose processed open-wire count is exactly the survivor count `midWidth` is empty. -/
private theorem genericPureCupSpineNilOfOpenWiresMidGCS {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    (midWidth : Nat)
    (spine : List (SpineAtom signature overallSource overallTarget))
    (pureCup : AllCupArity spine)
    (owMid : (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ spine).openWires.length = midWidth) :
    spine = [] := by
  cases listNilOrSnocGCS spine with
  | inl spineNil => exact spineNil
  | inr snocWit =>
      obtain ⟨t2, Clast2, spineSnoc⟩ := snocWit
      subst spineSnoc
      exfalso
      rw [genericMatchingOpenWiresCupEndSplit_mid midWidth t2 Clast2 pureCup] at owMid
      have ge := genericPureCupOpenWiresGeMidGCS midWidth t2
        (allCupArity_prefix_ofAppend t2 [Clast2] pureCup)
      have contra : (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ t2).openWires.length + 2
          ≤ (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ t2).openWires.length := by
        rw [owMid]; exact ge
      exact absurd (Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide : 0 < 2)) contra)
        (Nat.lt_irrefl _)

/-- The base floor: an empty first spine with equal `matchingOfSpineList midWidth` forces the second spine
empty — at EVERY `midWidth` (the empty spine's `topCount` is the survivor count `midWidth`). -/
private theorem genericMatchingPureCupSpineSortNilMidGCS {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    (midWidth : Nat)
    (secondList : List (SpineAtom signature overallSource overallTarget))
    (secondPureCup : AllCupArity secondList)
    (matchEqual : matchingOfSpineList midWidth
        ([] : List (SpineAtom signature overallSource overallTarget))
      = matchingOfSpineList midWidth secondList) :
    SpineTraceEquiv signature [] secondList := by
  have topEq : (matchingOfSpineList midWidth
      ([] : List (SpineAtom signature overallSource overallTarget))).topCount
      = (matchingOfSpineList midWidth secondList).topCount := congrArg DiagramType.topCount matchEqual
  have lhsTop : (matchingOfSpineList midWidth
      ([] : List (SpineAtom signature overallSource overallTarget))).topCount = midWidth := by
    show (List.range midWidth).length = midWidth
    exact rangeLengthGCS midWidth
  have owMid : (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ secondList).openWires.length
      = midWidth := by
    rw [lhsTop] at topEq
    exact topEq.symm
  have secondNil : secondList = [] :=
    genericPureCupSpineNilOfOpenWiresMidGCS midWidth secondList secondPureCup owMid
  rw [secondNil]
  exact SpineTraceEquiv.refl []

/-! ## ★★ THE FUELED SORT DRIVER — one word-threaded fold over the class, at ANY mid-width -/

private theorem genericMatchingPureCupSpineSortFueledMid (cls : AdjointStringConnectivity)
    {overallSource overallTarget : cls.signature.graph.Mode} :
    (midWidth : Nat) →
    (fuel : Nat) →
    (bottomWord : ModalityPath cls.signature.graph overallSource overallTarget) →
    (firstList secondList : List (SpineAtom cls.signature overallSource overallTarget)) →
    firstList.length ≤ fuel →
    SpineBoundaryChained midWidth firstList →
    SpineBoundaryChained midWidth secondList →
    SpineBoundaryWordChained bottomWord firstList →
    SpineBoundaryWordChained bottomWord secondList →
    spineListTopWord bottomWord firstList = spineListTopWord bottomWord secondList →
    AllCupArity firstList →
    AllCupArity secondList →
    matchingOfSpineList midWidth firstList = matchingOfSpineList midWidth secondList →
    SpineTraceEquiv cls.signature firstList secondList
  | midWidth, 0, _, firstList, secondList, lengthBound, _, _, _, _, _, _, secondPureCup, matchEqual => by
      cases listNilOrSnocGCS firstList with
      | inl firstNil =>
          subst firstNil
          exact genericMatchingPureCupSpineSortNilMidGCS midWidth secondList secondPureCup matchEqual
      | inr snocWit =>
          obtain ⟨t1, C1, firstSnoc⟩ := snocWit
          subst firstSnoc
          rw [lengthSnocGCS] at lengthBound
          exact absurd lengthBound (Nat.not_succ_le_zero _)
  | midWidth, fuel + 1, bottomWord, firstList, secondList, lengthBound, chainedFirst, chainedSecond,
      firstWordChained, secondWordChained, topWordEq, firstPureCup, secondPureCup, matchEqual => by
      cases listNilOrSnocGCS firstList with
      | inl firstNil =>
          subst firstNil
          exact genericMatchingPureCupSpineSortNilMidGCS midWidth secondList secondPureCup matchEqual
      | inr snocWit =>
      obtain ⟨t1, C1, firstSnoc⟩ := snocWit
      subst firstSnoc
      have t1LenBound : t1.length ≤ fuel := by
        rw [lengthSnocGCS] at lengthBound; exact Nat.le_of_succ_le_succ lengthBound
      have prefixChainedFirst : SpineBoundaryChained midWidth t1 :=
        spineBoundaryChained_prefix_ofAppend t1 [C1] midWidth chainedFirst
      have t1Pure : AllCupArity t1 := allCupArity_prefix_ofAppend t1 [C1] firstPureCup
      have prefixWordChainedFirst : SpineBoundaryWordChained bottomWord t1 :=
        spineBoundaryWordChained_prefix_ofAppend bottomWord t1 [C1] firstWordChained
      obtain ⟨c1Dom, c1Cod⟩ := allCupArity_lastCup_arity t1 C1 firstPureCup
      have c1Chord := genericMatchingLastCup_isShortChord_mid cls midWidth t1 C1 chainedFirst firstPureCup
      have chordSecond : natListGetAt
          (matchingOfSpineList midWidth secondList).partner (midWidth + C1.leftContext.length)
        = midWidth + C1.leftContext.length + 1 := by rw [← matchEqual]; exact c1Chord
      obtain ⟨pre2, backCup, locEquiv, locMatch, locPure, locChained, locWordChained, backWindow⟩ :=
        genericMatchingLocateAuxMid cls midWidth bottomWord secondList chainedSecond secondWordChained
          secondPureCup C1.leftContext.length chordSecond
      obtain ⟨backDom, backCod⟩ := allCupArity_lastCup_arity pre2 backCup locPure
      have appendedEqual := matchEqual.trans locMatch
      have c1CodIsTop : spineListTopWord bottomWord (t1 ++ [C1])
          = composePath C1.leftContext (composePath C1.generatorCod C1.rightContext) :=
        spineListTopWordSnocGCS bottomWord t1 C1
      have backCupCodIsTop : spineListTopWord bottomWord (pre2 ++ [backCup])
          = composePath backCup.leftContext (composePath backCup.generatorCod backCup.rightContext) :=
        spineListTopWordSnocGCS bottomWord pre2 backCup
      have secondTopEqBackCod : spineListTopWord bottomWord secondList
          = composePath backCup.leftContext (composePath backCup.generatorCod backCup.rightContext) :=
        (spineListTopWord_atomicTraceEquiv locEquiv bottomWord).trans backCupCodIsTop
      have codBoundaryWordsEqual :
          composePath backCup.leftContext (composePath backCup.generatorCod backCup.rightContext)
            = composePath C1.leftContext (composePath C1.generatorCod C1.rightContext) :=
        secondTopEqBackCod.symm.trans (topWordEq.symm.trans c1CodIsTop)
      have backEqC1 : backCup = C1 :=
        genericStringCupAtom_eq_of_sharedCod_sameWindow cls.toAdjointStringSignature backCup C1
          codBoundaryWordsEqual backWindow (backCod.trans c1Cod.symm) backDom c1Dom
      subst backCup
      have matchPrefixEqual : matchingOfSpineList midWidth t1 = matchingOfSpineList midWidth pre2 :=
        genericDropLastCup_matching_injective_mid cls midWidth t1 pre2 C1 chainedFirst locChained
          firstPureCup locPure appendedEqual
      have shorterTopWordEq : spineListTopWord bottomWord t1 = spineListTopWord bottomWord pre2 :=
        (spineListTopWord_prefix_eq_lastDomWord bottomWord t1 C1 firstWordChained).trans
          (spineListTopWord_prefix_eq_lastDomWord bottomWord pre2 C1 locWordChained).symm
      have prefixTrace : SpineTraceEquiv cls.signature t1 pre2 :=
        genericMatchingPureCupSpineSortFueledMid cls midWidth fuel bottomWord t1 pre2 t1LenBound
          prefixChainedFirst
          (spineBoundaryChained_prefix_ofAppend pre2 [C1] midWidth locChained)
          prefixWordChainedFirst
          (spineBoundaryWordChained_prefix_ofAppend bottomWord pre2 [C1] locWordChained)
          shorterTopWordEq t1Pure
          (allCupArity_prefix_ofAppend pre2 [C1] locPure) matchPrefixEqual
      exact (genericSpineTraceEquiv_backAppendCongr prefixTrace C1).trans locEquiv.toSpineTraceEquiv.symm

/-! ## ★★ THE ANY-WIDTH DETERMINACY — the generic brick, stronger than both shipped `k = 2` bricks -/

/-- ★★ **The ANY-WIDTH pure-cup determinacy over an adjoint-string connectivity class.**  Two boundary-chained
AND boundary-word-chained pure-cup spines over the SAME `midWidth` bottom boundary (ANY `midWidth` — no
positivity premise) that share their `spineListTopWord` and have EQUAL `matchingOfSpineList midWidth` are
`SpineTraceEquiv`.  At `midWidth = 0` this is the width-`0` determinacy; at `0 < midWidth` the positive-mid
determinacy — ONE statement, the generic form of the census bill's "full width-`0` quad sort" target. -/
def GenericMidPureCupDeterminacy (cls : AdjointStringConnectivity) : Prop :=
  ∀ {overallSource overallTarget : cls.signature.graph.Mode}
    (midWidth : Nat)
    (bottomWord : ModalityPath cls.signature.graph overallSource overallTarget)
    (cupFirst cupSecond : List (SpineAtom cls.signature overallSource overallTarget)),
    AllCupArity cupFirst → AllCupArity cupSecond →
    SpineBoundaryChained midWidth cupFirst → SpineBoundaryChained midWidth cupSecond →
    SpineBoundaryWordChained bottomWord cupFirst → SpineBoundaryWordChained bottomWord cupSecond →
    spineListTopWord bottomWord cupFirst = spineListTopWord bottomWord cupSecond →
    matchingOfSpineList midWidth cupFirst = matchingOfSpineList midWidth cupSecond →
    SpineTraceEquiv cls.signature cupFirst cupSecond

/-- ★★ **The ANY-WIDTH determinacy is INHABITED for every class** — the fueled sort driver with fuel seeded at
`cupFirst.length` (the VFA completeness hinge: the fuel bound `cupFirst.length ≤ cupFirst.length` is
`Nat.le_refl`, so fuel exhaustion never truncates). -/
theorem genericMidPureCupDeterminacy_proof (cls : AdjointStringConnectivity) :
    GenericMidPureCupDeterminacy cls := by
  intro overallSource overallTarget midWidth bottomWord cupFirst cupSecond pureA pureB chainedA chainedB
    wordA wordB topWordEq matchEq
  exact genericMatchingPureCupSpineSortFueledMid cls midWidth cupFirst.length bottomWord cupFirst
    cupSecond (Nat.le_refl cupFirst.length) chainedA chainedB wordA wordB topWordEq pureA pureB matchEq

/-! ## `k = 2` RECOVERY — the generic determinacy re-derives BOTH named shipped `k = 2` bricks -/

/-- ★ **The shipped positive-mid brick inhabits its literal statement** —
`stringPositiveMidPureCupDeterminacy_proof` IS the recovery target. -/
theorem stringPositiveMidDeterminacy_shippedInhabitant : StringPositiveMidPureCupDeterminacy :=
  stringPositiveMidPureCupDeterminacy_proof

/-- ★★ **The generic determinacy, at `k = 2`, RE-DERIVES the shipped positive-mid brick** — the generic form
needs no positivity, so it inhabits the LITERAL shipped `StringPositiveMidPureCupDeterminacy` by discarding the
`0 < midWidth` premise. -/
theorem stringPositiveMidDeterminacy_viaGenericClassAtTwo : StringPositiveMidPureCupDeterminacy :=
  fun midWidth bottomWord cupFirst cupSecond pureA pureB chainedA chainedB wordA wordB topWordEq
      _midPos matchEq =>
    genericMidPureCupDeterminacy_proof adjointStringConnectivityAtTwo midWidth bottomWord cupFirst
      cupSecond pureA pureB chainedA chainedB wordA wordB topWordEq matchEq

/-- ★ **The shipped width-`0` brick inhabits its literal statement** —
`stringWidthZeroPureCupDeterminacyShared_proof` IS the recovery target. -/
theorem stringWidthZeroDeterminacy_shippedInhabitant : StringWidthZeroPureCupDeterminacyShared :=
  stringWidthZeroPureCupDeterminacyShared_proof

/-- ★★ **The generic determinacy, at `k = 2` and `midWidth := 0`, RE-DERIVES the shipped width-`0` brick** —
the LITERAL shipped `StringWidthZeroPureCupDeterminacyShared`, through the SAME generic driver that covers the
positive-mid lane (the width-`0` and positive-mid `k = 2` sorts are two instances of ONE fueled fold). -/
theorem stringWidthZeroDeterminacy_viaGenericClassAtTwo : StringWidthZeroPureCupDeterminacyShared :=
  fun bottomWord cupFirst cupSecond pureA pureB chainedA chainedB wordA wordB topWordEq matchEq =>
    genericMidPureCupDeterminacy_proof adjointStringConnectivityAtTwo 0 bottomWord cupFirst cupSecond
      pureA pureB chainedA chainedB wordA wordB topWordEq matchEq

/-! ## `k = 2` FIRE — the generic driver runs on the shipped distinct double-cup pair -/

/-- ★ **The generic driver FIRES at `k = 2` on the shipped distinct double-cup pair** (`midWidth = 2`,
genuinely distinct spines with equal matching, the shipped anti-vacuity pair) — through the generic class
instance instead of the shipped `k = 2` proof. -/
theorem genericSortDriver_firesAtTwoOnDistinctDoubleCup :
    SpineTraceEquiv adjointTripleModeSignature
      stringPositiveMidDistinctDoubleCupLeftFirst stringPositiveMidDistinctDoubleCupRightFirst :=
  genericMidPureCupDeterminacy_proof adjointStringConnectivityAtTwo
    2 stringGH
    stringPositiveMidDistinctDoubleCupLeftFirst stringPositiveMidDistinctDoubleCupRightFirst
    (AllCupArity.cons rfl rfl (AllCupArity.cons rfl rfl AllCupArity.nil))
    (AllCupArity.cons rfl rfl (AllCupArity.cons rfl rfl AllCupArity.nil))
    (SpineBoundaryChained.cons _ rfl (SpineBoundaryChained.cons _ rfl (SpineBoundaryChained.nil _)))
    (SpineBoundaryChained.cons _ rfl (SpineBoundaryChained.cons _ rfl (SpineBoundaryChained.nil _)))
    (SpineBoundaryWordChained.cons _ rfl (SpineBoundaryWordChained.cons _ rfl (SpineBoundaryWordChained.nil _)))
    (SpineBoundaryWordChained.cons _ rfl (SpineBoundaryWordChained.cons _ rfl (SpineBoundaryWordChained.nil _)))
    rfl
    stringPositiveMidDistinctDoubleCup_matchingsAgree

/-! ## `k = 3` FIXTURES — the fresh adjoint-quadruple sort inputs -/

/-- `k = 3`, width-`0`, order A second atom: the unit `η3` at window `2` (leftContext `L1·L2`). -/
def quadSortCupThreeAtTwoW0 :
    SpineAtom adjointQuadrupleModeSignature AdjointQuadrupleMode.base AdjointQuadrupleMode.base where
  leftMidMode := AdjointQuadrupleMode.base
  rightMidMode := AdjointQuadrupleMode.base
  leftContext := quadL1L2
  generatorDom := ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.base
  generatorCod := quadL3L4
  generator := StringQuadTwoCell.unitThree
  rightContext := ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.base

/-- `k = 3`, width-`0`, order B first atom: the unit `η3` at window `0` (empty contexts). -/
def quadSortCupThreeAtZeroW0 :
    SpineAtom adjointQuadrupleModeSignature AdjointQuadrupleMode.base AdjointQuadrupleMode.base where
  leftMidMode := AdjointQuadrupleMode.base
  rightMidMode := AdjointQuadrupleMode.base
  leftContext := ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.base
  generatorDom := ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.base
  generatorCod := quadL3L4
  generator := StringQuadTwoCell.unitThree
  rightContext := ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.base

/-- `k = 3`, width-`0`, order B second atom: the unit `η1` at window `0` with the `L3·L4` block on the RIGHT. -/
def quadSortCupOneAtZeroOverL3L4 :
    SpineAtom adjointQuadrupleModeSignature AdjointQuadrupleMode.base AdjointQuadrupleMode.base where
  leftMidMode := AdjointQuadrupleMode.base
  rightMidMode := AdjointQuadrupleMode.base
  leftContext := ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.base
  generatorDom := ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.base
  generatorCod := quadL1L2
  generator := StringQuadTwoCell.unitOne
  rightContext := quadL3L4

/-- The `k = 3` width-`0` DISTINCT-GENERATOR pair, order A: `η1` first (window `0`), then `η3` (window `2`). -/
def quadSortOrderA :
    List (SpineAtom adjointQuadrupleModeSignature AdjointQuadrupleMode.base AdjointQuadrupleMode.base) :=
  [quadDropUnitOneW0, quadSortCupThreeAtTwoW0]

/-- The `k = 3` width-`0` DISTINCT-GENERATOR pair, order B: `η3` first (window `0`), then `η1` (window `0`). -/
def quadSortOrderB :
    List (SpineAtom adjointQuadrupleModeSignature AdjointQuadrupleMode.base AdjointQuadrupleMode.base) :=
  [quadSortCupThreeAtZeroW0, quadSortCupOneAtZeroOverL3L4]

/-- ★ decide pin: BOTH `k = 3` width-`0` orders compute the SAME matching `[1, 0, 3, 2]` — the boundary
matching cannot separate the two generator orders. -/
theorem quadSortOrders_matchingsAgree :
    matchingOfSpineList 0 quadSortOrderA = matchingOfSpineList 0 quadSortOrderB := by decide

/-- ★ decide pin: order A's partner list is `[1, 0, 3, 2]` (two disjoint short chords). -/
theorem quadSortOrderA_matchingComputes :
    (matchingOfSpineList 0 quadSortOrderA).partner = [1, 0, 3, 2] := by decide

/-- ★ Negative control (decide pin): the two orders are genuinely DISTINCT spines — their window projections
differ (`[0, 2] ≠ [0, 0]`), so `SpineTraceEquiv.refl` cannot inhabit the fired conclusion. -/
theorem quadSortOrders_windowsDiffer :
    quadSortOrderA.map (fun spineAtom => spineAtom.leftContext.length)
      ≠ quadSortOrderB.map (fun spineAtom => spineAtom.leftContext.length) := by decide

/-- ★ Negative control: the two orders carry DISTINCT head generators (`η1` vs `η3`, cods separated by
`quadIndexWord`) — the pair is a genuine generator-order transposition, not a relabelling. -/
theorem quadSortOrders_headGeneratorsDiffer :
    quadIndexWord quadDropUnitOneW0.generatorCod
      ≠ quadIndexWord quadSortCupThreeAtZeroW0.generatorCod := by decide

/-- ★★ **THE `k = 3` WIDTH-`0` SORT DECISION FIRES** — the census bill's "fresh `k = 3` sort fixtures" clause:
the quadruple determinacy (the generic driver at `adjointStringConnectivityAtThree`, `midWidth = 0`) runs
end-to-end on the two DISTINCT-GENERATOR orders of the `{η1, η3}` double-cup (equal matchings `[1,0,3,2]`,
distinct spines) and produces their `SpineTraceEquiv` — the full peel / locate / shared-cod-pin / drop /
recurse loop at three colours, on the fresh letter `L4`. -/
theorem quadSortDecision_firesAtThreeWidthZero :
    SpineTraceEquiv adjointQuadrupleModeSignature quadSortOrderA quadSortOrderB :=
  genericMidPureCupDeterminacy_proof adjointStringConnectivityAtThree
    0 quadLocateBottomWordW0 quadSortOrderA quadSortOrderB
    (AllCupArity.cons rfl rfl (AllCupArity.cons rfl rfl AllCupArity.nil))
    (AllCupArity.cons rfl rfl (AllCupArity.cons rfl rfl AllCupArity.nil))
    (SpineBoundaryChained.cons _ rfl (SpineBoundaryChained.cons _ rfl (SpineBoundaryChained.nil _)))
    (SpineBoundaryChained.cons _ rfl (SpineBoundaryChained.cons _ rfl (SpineBoundaryChained.nil _)))
    (SpineBoundaryWordChained.cons _ rfl (SpineBoundaryWordChained.cons _ rfl (SpineBoundaryWordChained.nil _)))
    (SpineBoundaryWordChained.cons _ rfl (SpineBoundaryWordChained.cons _ rfl (SpineBoundaryWordChained.nil _)))
    rfl
    quadSortOrders_matchingsAgree

/-! ## `k = 3` FIXTURES — the positive-mid (`midWidth = 2`) distinct pair over the `L3·L4` survivors -/

/-- The mid-`2` `k = 3` bottom word: the two survivor strands `L3·L4 : base ⟶ base`. -/
def quadSortBottomWordMidTwo :
    ModalityPath adjointQuadrupleGraph AdjointQuadrupleMode.base AdjointQuadrupleMode.base := quadL3L4

/-- Mid-`2` order A first atom: `η1` at window `0` over the `L3·L4` survivors on the right. -/
def quadSortMidCupOneAtZero :
    SpineAtom adjointQuadrupleModeSignature AdjointQuadrupleMode.base AdjointQuadrupleMode.base where
  leftMidMode := AdjointQuadrupleMode.base
  rightMidMode := AdjointQuadrupleMode.base
  leftContext := ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.base
  generatorDom := ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.base
  generatorCod := quadL1L2
  generator := StringQuadTwoCell.unitOne
  rightContext := quadL3L4

/-- Mid-`2` order A second atom: `η3` at window `4` (leftContext `L1·L2·L3·L4`). -/
def quadSortMidCupThreeAtFour :
    SpineAtom adjointQuadrupleModeSignature AdjointQuadrupleMode.base AdjointQuadrupleMode.base where
  leftMidMode := AdjointQuadrupleMode.base
  rightMidMode := AdjointQuadrupleMode.base
  leftContext := composePath quadL1L2 quadL3L4
  generatorDom := ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.base
  generatorCod := quadL3L4
  generator := StringQuadTwoCell.unitThree
  rightContext := ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.base

/-- Mid-`2` order B first atom: `η3` at window `2` (leftContext = the `L3·L4` survivors). -/
def quadSortMidCupThreeAtTwo :
    SpineAtom adjointQuadrupleModeSignature AdjointQuadrupleMode.base AdjointQuadrupleMode.base where
  leftMidMode := AdjointQuadrupleMode.base
  rightMidMode := AdjointQuadrupleMode.base
  leftContext := quadL3L4
  generatorDom := ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.base
  generatorCod := quadL3L4
  generator := StringQuadTwoCell.unitThree
  rightContext := ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.base

/-- Mid-`2` order B second atom: `η1` at window `0` over the doubled `L3·L4·L3·L4` right block. -/
def quadSortMidCupOneAtZeroDoubled :
    SpineAtom adjointQuadrupleModeSignature AdjointQuadrupleMode.base AdjointQuadrupleMode.base where
  leftMidMode := AdjointQuadrupleMode.base
  rightMidMode := AdjointQuadrupleMode.base
  leftContext := ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.base
  generatorDom := ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.base
  generatorCod := quadL1L2
  generator := StringQuadTwoCell.unitOne
  rightContext := composePath quadL3L4 quadL3L4

/-- The mid-`2` `k = 3` distinct pair, order A: windows `[0, 4]`. -/
def quadSortMidOrderA :
    List (SpineAtom adjointQuadrupleModeSignature AdjointQuadrupleMode.base AdjointQuadrupleMode.base) :=
  [quadSortMidCupOneAtZero, quadSortMidCupThreeAtFour]

/-- The mid-`2` `k = 3` distinct pair, order B: windows `[2, 0]`. -/
def quadSortMidOrderB :
    List (SpineAtom adjointQuadrupleModeSignature AdjointQuadrupleMode.base AdjointQuadrupleMode.base) :=
  [quadSortMidCupThreeAtTwo, quadSortMidCupOneAtZeroDoubled]

/-- ★ decide pin: BOTH mid-`2` orders compute the SAME `matchingOfSpineList 2` — through-strand survivor links
`0 ↔ 4`, `1 ↔ 5` plus two disjoint fresh chords, order-independent. -/
theorem quadSortMidOrders_matchingsAgree :
    matchingOfSpineList 2 quadSortMidOrderA = matchingOfSpineList 2 quadSortMidOrderB := by decide

/-- ★ decide pin: the mid-`2` partner list is `[4, 5, 3, 2, 0, 1, 7, 6]` (survivor strands `0 ↔ 4` / `1 ↔ 5`
threading BETWEEN the two fresh chords `2 ↔ 3` / `6 ↔ 7`). -/
theorem quadSortMidOrderA_matchingComputes :
    (matchingOfSpineList 2 quadSortMidOrderA).partner = [4, 5, 3, 2, 0, 1, 7, 6] := by decide

/-- ★ Negative control (decide pin): the two mid-`2` orders are genuinely DISTINCT spines (window projections
`[0, 4] ≠ [2, 0]`). -/
theorem quadSortMidOrders_windowsDiffer :
    quadSortMidOrderA.map (fun spineAtom => spineAtom.leftContext.length)
      ≠ quadSortMidOrderB.map (fun spineAtom => spineAtom.leftContext.length) := by decide

/-- ★★ **THE `k = 3` POSITIVE-MID SORT DECISION FIRES** — the quadruple determinacy at `midWidth = 2` runs
end-to-end on the two orders of the distinct `{η1, η3}` double-cup OVER the `L3·L4` survivor through-strands
(equal matchings, `by decide`-pinned; distinct spines) — the survivor re-ranking regime at three colours. -/
theorem quadSortDecision_firesAtThreeMidTwo :
    SpineTraceEquiv adjointQuadrupleModeSignature quadSortMidOrderA quadSortMidOrderB :=
  genericMidPureCupDeterminacy_proof adjointStringConnectivityAtThree
    2 quadSortBottomWordMidTwo quadSortMidOrderA quadSortMidOrderB
    (AllCupArity.cons rfl rfl (AllCupArity.cons rfl rfl AllCupArity.nil))
    (AllCupArity.cons rfl rfl (AllCupArity.cons rfl rfl AllCupArity.nil))
    (SpineBoundaryChained.cons _ rfl (SpineBoundaryChained.cons _ rfl (SpineBoundaryChained.nil _)))
    (SpineBoundaryChained.cons _ rfl (SpineBoundaryChained.cons _ rfl (SpineBoundaryChained.nil _)))
    (SpineBoundaryWordChained.cons _ rfl (SpineBoundaryWordChained.cons _ rfl (SpineBoundaryWordChained.nil _)))
    (SpineBoundaryWordChained.cons _ rfl (SpineBoundaryWordChained.cons _ rfl (SpineBoundaryWordChained.nil _)))
    rfl
    quadSortMidOrders_matchingsAgree

/-! ## `k = 3` NESTED-cup input — the driver peels through a nested chord configuration -/

/-- The `k = 3` NESTED second atom: the unit `η2 : id_tip ⇒ L2·L3` at window `1`, INSIDE the `η1` chord
(leftContext the single letter `L1`, rightContext the single letter `L2`). -/
def quadNestedCupTwoAtOne :
    SpineAtom adjointQuadrupleModeSignature AdjointQuadrupleMode.base AdjointQuadrupleMode.base where
  leftMidMode := AdjointQuadrupleMode.tip
  rightMidMode := AdjointQuadrupleMode.tip
  leftContext :=
    ModalityPath.cons AdjointQuadrupleModality.letterOne
      (ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.tip)
  generatorDom := ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.tip
  generatorCod := quadL2L3
  generator := StringQuadTwoCell.unitTwo
  rightContext :=
    ModalityPath.cons AdjointQuadrupleModality.letterTwo
      (ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.base)

/-- The `k = 3` NESTED rainbow `[η1@0, η2@1]` — the second cup opens INSIDE the first cup's chord. -/
def quadNestedRainbow :
    List (SpineAtom adjointQuadrupleModeSignature AdjointQuadrupleMode.base AdjointQuadrupleMode.base) :=
  [quadDropUnitOneW0, quadNestedCupTwoAtOne]

/-- ★ decide pin: the nested rainbow's matching is the NESTED partner list `[3, 2, 1, 0]` (outer chord
`0 ↔ 3` enclosing inner chord `1 ↔ 2`) — a genuinely nested configuration, unlike the disjoint pairs above. -/
theorem quadNestedRainbow_matchingComputes :
    (matchingOfSpineList 0 quadNestedRainbow).partner = [3, 2, 1, 0] := by decide

/-- ★ **The `k = 3` sort decision RUNS on the NESTED-cup input** — the driver peels the inner cup, locates its
window-`1` chord inside the outer chord's span, and closes the loop (the below/middle window regimes of the
locate exercised on a nested configuration).  Pure-cup spines only produce planar (nested / disjoint) chords —
a "crossing-heavy" pure-cup pair is structurally impossible — so nested is the maximal chord-complexity regime
for the cup sort, recorded honestly. -/
theorem quadSortDecision_runsOnNestedRainbow :
    SpineTraceEquiv adjointQuadrupleModeSignature quadNestedRainbow quadNestedRainbow :=
  genericMidPureCupDeterminacy_proof adjointStringConnectivityAtThree
    0 quadLocateBottomWordW0 quadNestedRainbow quadNestedRainbow
    (AllCupArity.cons rfl rfl (AllCupArity.cons rfl rfl AllCupArity.nil))
    (AllCupArity.cons rfl rfl (AllCupArity.cons rfl rfl AllCupArity.nil))
    (SpineBoundaryChained.cons _ rfl (SpineBoundaryChained.cons _ rfl (SpineBoundaryChained.nil _)))
    (SpineBoundaryChained.cons _ rfl (SpineBoundaryChained.cons _ rfl (SpineBoundaryChained.nil _)))
    (SpineBoundaryWordChained.cons _ rfl (SpineBoundaryWordChained.cons _ rfl (SpineBoundaryWordChained.nil _)))
    (SpineBoundaryWordChained.cons _ rfl (SpineBoundaryWordChained.cons _ rfl (SpineBoundaryWordChained.nil _)))
    rfl rfl

/-! ## Road marker -/

/-- **★★ ESTABLISHED — the GENERIC FUELED CUP-SORT DRIVER + the ANY-WIDTH determinacy are machine-checked
(FC-4 r7, the driver tranche).**  `genericMidPureCupDeterminacy_proof cls` inhabits
`GenericMidPureCupDeterminacy cls` for EVERY adjoint-string connectivity class: ONE fueled word-threaded fold
(fuel = first spine length, the VFA selection-sort completeness shape) generic over `cls × midWidth` with NO
positivity premise — peel (r6 short-chord readoff), locate (r7 any-width fueled LOCATE), pin (r5 B2 SHARED-COD
cup pin — the rerouted atom pin at its consumption node), drop (r6 injectivity), recurse, re-append (the
`{signature}`-generic `genericSpineTraceEquiv_backAppendCongr`).  The HONESTY LAW discharged: at `k = 2` the
generic determinacy re-derives BOTH named shipped bricks (`stringPositiveMidPureCupDeterminacy_proof` and — at
`midWidth := 0` — `stringWidthZeroPureCupDeterminacyShared_proof`, each via the `shippedInhabitant` /
`viaGenericClassAtTwo` pair) and fires on the shipped distinct double-cup pair; at `k = 3` the quadruple
decision fires end-to-end on FRESH sort fixtures — the width-`0` distinct-generator two-order pair (matchings
`[1,0,3,2]` pinned by decide), the mid-`2` distinct pair over the `L3·L4` survivors (matchings
`[4,5,3,2,0,1,7,6]` pinned), and the nested rainbow (`[3,2,1,0]` pinned) — with window-projection and
generator-identity negative controls.  Crossing-heavy pure-cup inputs are structurally impossible (cup chords
are planar), recorded honestly.

  What this marker does NOT close (THE FLIP LAW): the census marker `fxString_hasNColourAtomPinReroute`
  (`StringKParameterizationCensus`) STAYS `false` in this file — the clause-by-clause closure adjudication is
  the sibling `StringNColourAtomPinRerouteClosure`, which supersedes the frozen owner by content marker.
  `= true`. -/
def fxString_hasGenericMidPureCupSortDriver : Bool := true

end FX1Poly.Polygraph
