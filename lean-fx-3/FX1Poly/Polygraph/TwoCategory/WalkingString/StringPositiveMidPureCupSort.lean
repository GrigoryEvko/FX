import FX1Poly.Polygraph.TwoCategory.WalkingString.StringPositiveMidLocateAux
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringPositiveMidDropLastCup
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringWidthZeroPureCupSort
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringPositiveMidValleyCellReducer

/-! # WalkingString/StringPositiveMidPureCupSort — the positive-mid pure-cup determinacy INHABITED: THE BRICK
(FC-3 r45, R4 + R5)

The brick `StringPositiveMidPureCupDeterminacy` (`StringPositiveMidCupSortResidual`, r40) — the ONE named
sub-Prop the whole adjoint-triple #2020 completeness+decision headline factors through after the r39–r42
collapse — is here INHABITED, zero-axiom.  It is the width-`0` pure-cup determinacy
`stringWidthZeroPureCupDeterminacyShared_proof` (r17, `StringWidthZeroPureCupSort`) re-parameterized
`0 ⤳ midWidth`: the fueled sort peels the shared last cup, reads its short chord in the second spine, bubbles
the partner to the tail (`stringMatchingLocateAuxMid`, R3), pins it by the SHARED-COD word pin
(`stringSpineAtom_eq_of_sharedCod_sameWindow`, generic), drops both by matching-injectivity
(`stringDropLastCup_matching_injective_mid`, R2), recurses handing the SHORTER shared top word, and
re-appends (`stringSpineTraceEquiv_backAppendCongr`, generic).

  * ★ `stringMatchingPureCupSpineSortFueledMid` (R4) — the fueled word-threaded sort at the `midWidth` seed.
    The BASE FLOOR is the small positive-mid delta (not the width-`0` `topCount = 0` shortcut): an empty first
    spine with equal `matchingOfSpineList midWidth` forces the second spine's processed open-wire count to the
    SURVIVOR count `midWidth`; since every trailing cup grows the open-wire count by exactly two
    (`stringMatchingOpenWiresCupEndSplit_mid`, P2a) and the processed count is `≥ midWidth`
    (`stringPureCupOpenWires_monotone`, cups only add wires), a non-empty second would exceed `midWidth` — so
    the second is empty.

  * ★★ `stringPositiveMidPureCupDeterminacy_proof` (R5) — the LITERAL brick, INHABITED.  The exact mirror of
    `stringWidthZeroPureCupDeterminacyShared_proof`, threading the extra `midWidth` / `0 < midWidth`.  The
    conclusion is `SpineTraceEquiv` (canonicalization up to disjoint-cup transpositions — the surviving
    transposition is REAL, covered by the equivalence, never a list equality).

With the brick inhabited, the `_ofBrick` tower (`StringPositiveMidValleyCellReducer`, r42) fires end-to-end:
`stringMatchingReductsShareSpineTrace_ofBrick stringPositiveMidPureCupDeterminacy_proof` inhabits the ONE
named completeness residual `StringMatchingReductsShareSpineTrace` UNCONDITIONALLY, so the base completeness
`convOfMapEq` and the full adjoint-triple word-problem DECISION become unconditional.  The now-unconditional
theorems are instantiated below.

## Literature grounding (RS 1204.4505 / Thiebaut 2508.19360)

The induction variable is the CUP/PEEL count, decreasing by one per innermost peel (Thiebaut Prop 2.7 "i
reduced by 1"; RS Lemma 2.2 "induction on the maximal index"); the through-strand survivor count `midWidth` is
a fixed ambient parameter carried as an INVARIANT on a separate rail (RS thread the defect count `p` through a
bijection to link states, never through the peel recursion).  The conclusion is the published two-part shape:
`same matching ⟹ identical sorted normal form` up to the diagram relations (Thiebaut Prop 2.6 "two equal Jones
normal forms are identical").

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

private theorem spineListTopWord_snoc {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (bottomWord : ModalityPath signature.graph sourceMode targetMode)
    (prefixAtoms : List (SpineAtom signature sourceMode targetMode))
    (lastAtom : SpineAtom signature sourceMode targetMode) :
    spineListTopWord bottomWord (prefixAtoms ++ [lastAtom])
      = composePath lastAtom.leftContext (composePath lastAtom.generatorCod lastAtom.rightContext) := by
  rw [spineListTopWord_append bottomWord prefixAtoms [lastAtom]]
  dsimp only [spineListTopWord]

/-! ## The base-floor apparatus: a pure-cup mid spine whose open-wire count is the survivor count is empty -/

/-- The processed open-wire count of a pure-cup spine is monotone in the fold: every cup step ADDS two wires,
so the count never drops below the seed's.  Structural recursion on the spine. -/
private theorem stringPureCupOpenWires_monotone {overallSource overallTarget : adjointTripleGraph.Mode} :
    (spine : List (SpineAtom adjointTripleModeSignature overallSource overallTarget)) →
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
          have ih := stringPureCupOpenWires_monotone rest restPure (stepAtom state atom)
          show state.openWires.length ≤ (processSpine (stepAtom state atom) rest).openWires.length
          exact Nat.le_trans grow ih

/-- The processed open-wire count of a pure-cup spine at the positive-mid seed is at least the survivor count
`midWidth` (the seed's open-wire count is `midWidth`, and cups only add). -/
private theorem stringPureCupOpenWires_ge_mid {overallSource overallTarget : adjointTripleGraph.Mode}
    (midWidth : Nat)
    (spine : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (pureCup : AllCupArity spine) :
    midWidth ≤ (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ spine).openWires.length := by
  have mono := stringPureCupOpenWires_monotone spine pureCup ⟨List.range midWidth, [], midWidth, 0⟩
  have seedLen : (⟨List.range midWidth, [], midWidth, 0⟩ : WireState).openWires.length = midWidth := by
    show (List.range midWidth).length = midWidth
    exact rangeLength midWidth
  rw [seedLen] at mono
  exact mono

/-- A pure-cup mid spine whose processed open-wire count is exactly the survivor count `midWidth` is empty:
each trailing cup grows the count by two (`stringMatchingOpenWiresCupEndSplit_mid`, P2a) and the prefix count
is `≥ midWidth`, so a non-empty spine would exceed `midWidth`. -/
private theorem stringPureCupSpine_nil_ofOpenWiresMid {overallSource overallTarget : adjointTripleGraph.Mode}
    (midWidth : Nat)
    (spine : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (pureCup : AllCupArity spine)
    (owMid : (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ spine).openWires.length = midWidth) :
    spine = [] := by
  cases listNilOrSnoc spine with
  | inl spineNil => exact spineNil
  | inr snocWit =>
      obtain ⟨t2, Clast2, spineSnoc⟩ := snocWit
      subst spineSnoc
      exfalso
      rw [stringMatchingOpenWiresCupEndSplit_mid midWidth t2 Clast2 pureCup] at owMid
      have ge := stringPureCupOpenWires_ge_mid midWidth t2 (allCupArity_prefix_ofAppend t2 [Clast2] pureCup)
      have contra : (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ t2).openWires.length + 2
          ≤ (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ t2).openWires.length := by
        rw [owMid]; exact ge
      exact absurd (Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide : 0 < 2)) contra)
        (Nat.lt_irrefl _)

/-- The base floor: an empty first spine with equal `matchingOfSpineList midWidth` forces the second spine
empty.  The second's `topCount` equals the empty spine's `topCount = midWidth` (the survivors), so its
processed open-wire count is `midWidth`, forcing it empty (`stringPureCupSpine_nil_ofOpenWiresMid`). -/
private theorem stringMatchingPureCupSpine_sort_nil_mid
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (midWidth : Nat)
    (secondList : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (secondPureCup : AllCupArity secondList)
    (matchEqual : matchingOfSpineList midWidth
        ([] : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
      = matchingOfSpineList midWidth secondList) :
    SpineTraceEquiv adjointTripleModeSignature [] secondList := by
  have topEq : (matchingOfSpineList midWidth
      ([] : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))).topCount
      = (matchingOfSpineList midWidth secondList).topCount := congrArg DiagramType.topCount matchEqual
  have lhsTop : (matchingOfSpineList midWidth
      ([] : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))).topCount = midWidth := by
    show (List.range midWidth).length = midWidth
    exact rangeLength midWidth
  have owMid : (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ secondList).openWires.length = midWidth := by
    rw [lhsTop] at topEq
    exact topEq.symm
  have secondNil : secondList = [] :=
    stringPureCupSpine_nil_ofOpenWiresMid midWidth secondList secondPureCup owMid
  rw [secondNil]
  exact SpineTraceEquiv.refl []

/-! ## The WORD-threaded sort assembly at the positive-mid seed -/

private theorem stringMatchingPureCupSpineSortFueledMid
    {overallSource overallTarget : adjointTripleGraph.Mode} :
    (midWidth : Nat) →
    (midPos : 0 < midWidth) →
    (fuel : Nat) →
    (bottomWord : ModalityPath adjointTripleGraph overallSource overallTarget) →
    (firstList secondList :
      List (SpineAtom adjointTripleModeSignature overallSource overallTarget)) →
    firstList.length ≤ fuel →
    SpineBoundaryChained midWidth firstList →
    SpineBoundaryChained midWidth secondList →
    SpineBoundaryWordChained bottomWord firstList →
    SpineBoundaryWordChained bottomWord secondList →
    spineListTopWord bottomWord firstList = spineListTopWord bottomWord secondList →
    AllCupArity firstList →
    AllCupArity secondList →
    matchingOfSpineList midWidth firstList = matchingOfSpineList midWidth secondList →
    SpineTraceEquiv adjointTripleModeSignature firstList secondList
  | midWidth, _, 0, _, firstList, secondList, lengthBound, _, _, _, _, _, _, secondPureCup, matchEqual => by
      cases listNilOrSnoc firstList with
      | inl firstNil => subst firstNil
                        exact stringMatchingPureCupSpine_sort_nil_mid midWidth secondList secondPureCup matchEqual
      | inr snocWit =>
          obtain ⟨t1, C1, firstSnoc⟩ := snocWit
          subst firstSnoc
          rw [lengthSnoc] at lengthBound
          exact absurd lengthBound (Nat.not_succ_le_zero _)
  | midWidth, midPos, fuel + 1, bottomWord, firstList, secondList, lengthBound, chainedFirst, chainedSecond,
      firstWordChained, secondWordChained, topWordEq, firstPureCup, secondPureCup, matchEqual => by
      cases listNilOrSnoc firstList with
      | inl firstNil => subst firstNil
                        exact stringMatchingPureCupSpine_sort_nil_mid midWidth secondList secondPureCup matchEqual
      | inr snocWit =>
      obtain ⟨t1, C1, firstSnoc⟩ := snocWit
      subst firstSnoc
      have t1LenBound : t1.length ≤ fuel := by
        rw [lengthSnoc] at lengthBound; exact Nat.le_of_succ_le_succ lengthBound
      have prefixChainedFirst : SpineBoundaryChained midWidth t1 :=
        spineBoundaryChained_prefix_ofAppend t1 [C1] midWidth chainedFirst
      have t1Pure : AllCupArity t1 := allCupArity_prefix_ofAppend t1 [C1] firstPureCup
      have prefixWordChainedFirst : SpineBoundaryWordChained bottomWord t1 :=
        spineBoundaryWordChained_prefix_ofAppend bottomWord t1 [C1] firstWordChained
      obtain ⟨c1Dom, c1Cod⟩ := allCupArity_lastCup_arity t1 C1 firstPureCup
      have c1Chord := stringMatchingLastCup_isShortChord_mid midWidth t1 C1 chainedFirst firstPureCup
      have chordSecond : natListGetAt
          (matchingOfSpineList midWidth secondList).partner (midWidth + C1.leftContext.length)
        = midWidth + C1.leftContext.length + 1 := by rw [← matchEqual]; exact c1Chord
      obtain ⟨pre2, backCup, locEquiv, locMatch, locPure, locChained, locWordChained, backWindow⟩ :=
        stringMatchingLocateAuxMid midWidth midPos bottomWord secondList chainedSecond secondWordChained
          secondPureCup C1.leftContext.length chordSecond
      obtain ⟨backDom, backCod⟩ := allCupArity_lastCup_arity pre2 backCup locPure
      have appendedEqual := matchEqual.trans locMatch
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
      have matchPrefixEqual : matchingOfSpineList midWidth t1 = matchingOfSpineList midWidth pre2 :=
        stringDropLastCup_matching_injective_mid midWidth t1 pre2 C1 chainedFirst locChained firstPureCup
          locPure appendedEqual
      have shorterTopWordEq : spineListTopWord bottomWord t1 = spineListTopWord bottomWord pre2 :=
        (spineListTopWord_prefix_eq_lastDomWord bottomWord t1 C1 firstWordChained).trans
          (spineListTopWord_prefix_eq_lastDomWord bottomWord pre2 C1 locWordChained).symm
      have prefixTrace : SpineTraceEquiv adjointTripleModeSignature t1 pre2 :=
        stringMatchingPureCupSpineSortFueledMid midWidth midPos fuel bottomWord t1 pre2 t1LenBound
          prefixChainedFirst
          (spineBoundaryChained_prefix_ofAppend pre2 [C1] midWidth locChained)
          prefixWordChainedFirst
          (spineBoundaryWordChained_prefix_ofAppend bottomWord pre2 [C1] locWordChained)
          shorterTopWordEq t1Pure
          (allCupArity_prefix_ofAppend pre2 [C1] locPure) matchPrefixEqual
      exact (stringSpineTraceEquiv_backAppendCongr prefixTrace C1).trans locEquiv.toSpineTraceEquiv.symm

/-- ★★ **THE BRICK — the positive-mid pure-cup determinacy, INHABITED (FC-3 r45, R5).**  The LITERAL
`StringPositiveMidPureCupDeterminacy`: two boundary-chained AND boundary-word-chained pure-cup string spines
over a POSITIVE mid-width bottom boundary (`0 < midWidth`, the through-strand survivor count) that share their
`spineListTopWord` and have EQUAL `matchingOfSpineList midWidth` are `SpineTraceEquiv`.  The exact mirror of
`stringWidthZeroPureCupDeterminacyShared_proof`, threading the extra `midWidth` / `0 < midWidth`: peel the last
cup of the first spine (`stringMatchingLastCup_isShortChord_mid`), read its short chord in the second, bubble
the partner cup to the tail (`stringMatchingLocateAuxMid`, R3), pin it by the SHARED-COD word pin (NOT length
rigidity), drop both by matching-injectivity (`stringDropLastCup_matching_injective_mid`, R2), recurse handing
the SHORTER shared top word, and re-append.  Seeds the fuel at `cupFirst.length`.  The conclusion is
`SpineTraceEquiv` — canonicalization up to disjoint-cup transpositions (the surviving transposition is REAL,
covered by the equivalence, never a list equality). -/
theorem stringPositiveMidPureCupDeterminacy_proof : StringPositiveMidPureCupDeterminacy := by
  intro overallSource overallTarget midWidth bottomWord cupFirst cupSecond pureA pureB chainedA chainedB
    wordA wordB topWordEq midPos matchEq
  exact stringMatchingPureCupSpineSortFueledMid midWidth midPos cupFirst.length bottomWord cupFirst cupSecond
    (Nat.le_refl cupFirst.length) chainedA chainedB wordA wordB topWordEq pureA pureB matchEq

/-! ## The now-unconditional tower, instantiated (the brick fires end-to-end) -/

/-- ★★ **The completeness reduct-existence residual, DISCHARGED unconditionally by the brick.**
`stringMatchingReductsShareSpineTrace_ofBrick` (`StringPositiveMidValleyCellReducer`, r42) fed the inhabited
brick: the ONE named residual `StringMatchingReductsShareSpineTrace` the completeness master gates on is now
inhabited with NO standing hypothesis.  This is the term that flips the masters. -/
theorem stringMatchingReductsShareSpineTrace_holds : StringMatchingReductsShareSpineTrace :=
  stringMatchingReductsShareSpineTrace_ofBrick stringPositiveMidPureCupDeterminacy_proof

/-- ★ **The base completeness `convOfMapEq`, UNCONDITIONAL.**  From the discharged residual: every parallel
pair with equal boundary matching is `StringSaturatedTwoCellConv`. -/
theorem stringConvOfMapEq_holds
    {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    (cellA cellB : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath)
    (matchingsEqual : matchingOf cellA = matchingOf cellB) :
    StringSaturatedTwoCellConv cellA cellB :=
  stringConvOfMapEq_ofReductsShareSpineTrace stringMatchingReductsShareSpineTrace_holds cellA cellB
    matchingsEqual

/-- ★ **The whole keystone (soundness r2 + completeness now unconditional).** -/
def stringSaturatedMatchingCanonicalization_holds : StringSaturatedMatchingCanonicalization :=
  stringSaturatedMatchingCanonicalization_ofReducts stringMatchingReductsShareSpineTrace_holds

/-- ★★ **The FULL adjoint-triple word-problem DECISION, now TOTAL (unconditional).**  `Decidable
(StringSaturatedTwoCellConv cellA cellB)` on EVERY parallel pair, with NO standing residual — the brick
discharged the last one. -/
def decidableStringSaturatedConv_holds
    {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    (cellA cellB : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath) :
    Decidable (StringSaturatedTwoCellConv cellA cellB) :=
  decidableStringSaturatedConv_ofReducts stringMatchingReductsShareSpineTrace_holds cellA cellB

/-! ## Anti-vacuity — the brick fires on a genuine positive-mid distinct pair -/

/-- ★★ **The brick FIRES on the shipped distinct double-cup at positive mid-width.**  Applying the inhabited
brick to the two firing orders of the disjoint double-cup over `midWidth = 2` survivors
(`stringPositiveMidDistinctDoubleCupLeftFirst` / `…RightFirst`, `StringPositiveMidCupSortResidual`) — genuinely
DISTINCT spines (leftContext-length projections `[0, 4] ≠ [2, 0]`) with EQUAL `matchingOfSpineList 2` — runs
the full fueled sort (peel, locate, shared-cod pin, matching-injective drop, recurse) and produces a
`SpineTraceEquiv` of the two DISTINCT spines.  `SpineTraceEquiv.refl` FAILS on this pair (distinct endpoints):
the sort is genuinely non-diagonal.  Every chaining / arity / word hypothesis is `rfl` (`composePath` computes
on the closed cons-lists); `0 < 2` and the `matchingOfSpineList 2` agreement by `decide`. -/
theorem stringPositiveMidBrick_firesOnDistinctDoubleCup :
    SpineTraceEquiv adjointTripleModeSignature
      stringPositiveMidDistinctDoubleCupLeftFirst stringPositiveMidDistinctDoubleCupRightFirst :=
  stringPositiveMidPureCupDeterminacy_proof
    2 stringGH
    stringPositiveMidDistinctDoubleCupLeftFirst stringPositiveMidDistinctDoubleCupRightFirst
    (AllCupArity.cons rfl rfl (AllCupArity.cons rfl rfl AllCupArity.nil))
    (AllCupArity.cons rfl rfl (AllCupArity.cons rfl rfl AllCupArity.nil))
    (SpineBoundaryChained.cons _ rfl (SpineBoundaryChained.cons _ rfl (SpineBoundaryChained.nil _)))
    (SpineBoundaryChained.cons _ rfl (SpineBoundaryChained.cons _ rfl (SpineBoundaryChained.nil _)))
    (SpineBoundaryWordChained.cons _ rfl (SpineBoundaryWordChained.cons _ rfl (SpineBoundaryWordChained.nil _)))
    (SpineBoundaryWordChained.cons _ rfl (SpineBoundaryWordChained.cons _ rfl (SpineBoundaryWordChained.nil _)))
    rfl (by decide)
    stringPositiveMidDistinctDoubleCup_matchingsAgree

/-! ## Honesty marker -/

/-- **★★ CLOSED — THE BRICK IS INHABITED; the doubly-positive wall falls, and the adjoint-triple
completeness+decision headline is UNCONDITIONAL (FC-3 r45, R4 + R5).**
`stringPositiveMidPureCupDeterminacy_proof` inhabits the LITERAL `StringPositiveMidPureCupDeterminacy`
(`StringPositiveMidCupSortResidual`) — two positive-mid pure-cup string spines sharing their `spineListTopWord`
with equal `matchingOfSpineList midWidth` (`0 < midWidth`) are `SpineTraceEquiv` — via the width-`0` fueled
sort re-parameterized `0 ⤳ midWidth`: the fueled word-threaded sort `stringMatchingPureCupSpineSortFueledMid`
peels the shared last cup (P2b readoff), locates the partner (`stringMatchingLocateAuxMid`, R3), pins it by the
SHARED-COD word pin, drops both (`stringDropLastCup_matching_injective_mid`, R2), and recurses; the base floor
forces the second spine empty from the survivor open-wire count.  The brick FIRES on the shipped distinct
double-cup at `midWidth = 2` (`stringPositiveMidBrick_firesOnDistinctDoubleCup`, genuinely non-diagonal).

  With the brick inhabited, the r42 `_ofBrick` tower fires end-to-end:
  `stringMatchingReductsShareSpineTrace_holds` inhabits the ONE named completeness residual
  `StringMatchingReductsShareSpineTrace` UNCONDITIONALLY; `stringConvOfMapEq_holds` is the unconditional base
  completeness; `decidableStringSaturatedConv_holds` is the now-TOTAL adjoint-triple word-problem decision.
  The masters `fxString_hasAdjointTripleCompleteness` (`StringMatchingCompleteness`) and
  `fxString_hasConvOfMapEqPortFlip` (`StringConvOfMapEqPort`) flip to `true` this round (per their literal
  texts — the named residual discharged / the unconditional `convOfMapEq` established).  `= true`. -/
def fxString_hasPositiveMidPureCupSort : Bool := true

end FX1Poly.Polygraph
