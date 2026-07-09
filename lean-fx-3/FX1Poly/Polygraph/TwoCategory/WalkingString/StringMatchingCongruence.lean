import FX1Poly.Polygraph.TwoCategory.WalkingString.StringMatchingModel
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingVcompLeftCongruence
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingVcompRightUnconditional
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingWhiskerLeftCongruence
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingWhiskerRightCongruence

/-! # WalkingString — the saturated-congruence bundle, PROVED (the second soundness residual discharged)

The full two-level soundness (`stringSaturatedConv_matchingOf_eq`) took two explicit premises: the union-find
Godement independence (`godementInvariant`, the `ofFull` input) and the four-field compositionality
(`StringMatchingSaturatedCongruence`).  This file discharges the SECOND unconditionally by PORTING the shipped
walking-adjunction congruence machinery to the three-generator adjoint-triple seed.

The `matchingOf` congruence cores are already signature-POLYMORPHIC — `matchingOf_whiskerLeft_congr` /
`matchingOf_whiskerRight_congr` are full congruences under a cup/cap generator discipline, and
`extractAfterProcessing_vcompLeft_ofSeed` / `extractAfterProcessing_vcompRight_ofSeed` /
`extractAfterProcessing_vcompRight_ofSeed_emptyMid` are seed-generic per-boundary cores.  The only
walking-adjunction-specific input in the shipped `_congruence` wrappers is the discipline witness
`cellHasCupCapGenerators_ofAdjunctionSignature`.  Here:

  * `cellHasCupCapGenerators_ofStringSignature` — the discipline is UNIVERSAL over the walking adjoint triple:
    its four generators are the two units (`0 ⇒ 2` cups) and the two counits (`2 ⇒ 0` caps), so every cell is
    cup/cap-disciplined by structural recursion, exactly as the single adjunction;
  * `matchingOf_vcompLeft_congr_ofDiscipline` / `matchingOf_vcompRight_congr_ofMidBoundaryPos_ofDiscipline` /
    `matchingOf_vcompRight_congr_ofDiscipline` — the vcomp boundary-dispatch wrappers, re-stated
    `{signature}`-GENERIC over an arbitrary cup/cap discipline (the exact bodies of the adjunction wrappers,
    with the discipline witness abstracted).  This is the honest port: the union-find is colour-BLIND
    (`stepAtom` reads only a generator's arity, never its `F`/`G`/`H` label), so cross-colour adjacency on the
    shared `G` is the SAME disjoint-window commutation as the single colour — no cross-colour critical pair;
  * ★ `stringMatchingSaturatedCongruence_proved` — the `StringMatchingSaturatedCongruence` bundle inhabitant,
    the four fields discharged by the generic cores with `cellHasCupCapGenerators_ofStringSignature`.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The cup/cap discipline is universal over the walking adjoint triple -/

/-- **The cup/cap discipline is universal over the walking adjoint triple.**  Its four 2-cell generators are the
lower/upper units (`nil ⇒ F·G`, `nil ⇒ G·H`, both `0 ⇒ 2` cups) and the lower/upper counits (`G·F ⇒ nil`,
`H·G ⇒ nil`, both `2 ⇒ 0` caps), so every cell satisfies `CellHasCupCapGenerators` by structural recursion —
identities are vacuous, composites and whiskerings recurse.  The three-generator analog of
`cellHasCupCapGenerators_ofAdjunctionSignature`. -/
theorem cellHasCupCapGenerators_ofStringSignature :
    {sourceMode targetMode : AdjointTripleMode} →
    {localDom localCod : ModalityPath adjointTripleGraph sourceMode targetMode} →
    (cell : RawTwoCellExpr adjointTripleModeSignature localDom localCod) →
    CellHasCupCapGenerators cell
  | _, _, _, _, .gen generator => by
      cases generator with
      | unitLower => exact Or.inl ⟨rfl, rfl⟩
      | counitLower => exact Or.inr ⟨rfl, rfl⟩
      | unitUpper => exact Or.inl ⟨rfl, rfl⟩
      | counitUpper => exact Or.inr ⟨rfl, rfl⟩
  | _, _, _, _, .id _ => True.intro
  | _, _, _, _, .vcomp cellAlpha cellBeta =>
      ⟨cellHasCupCapGenerators_ofStringSignature cellAlpha,
        cellHasCupCapGenerators_ofStringSignature cellBeta⟩
  | _, _, _, _, .whiskerLeft _ body => cellHasCupCapGenerators_ofStringSignature body
  | _, _, _, _, .whiskerRight _ body => cellHasCupCapGenerators_ofStringSignature body

/-! ## The vcomp boundary-dispatch congruences, re-stated `{signature}`-generic over a cup/cap discipline -/

/-- **The vcomp-LEFT matching congruence, generic over a cup/cap discipline.**  The exact body of the walking
adjunction's `matchingOf_vcompLeft_congruence`, with the discipline witness abstracted: the source boundary
dispatches between the canonical seed (inhabited boundary — the initial conditions package applies) and the
MODE3-B counter-shift proxy `⟨[], [], 1, 0⟩` (empty boundary), the seed-generic core
`extractAfterProcessing_vcompLeft_ofSeed` doing the run-composition. -/
theorem matchingOf_vcompLeft_congr_ofDiscipline {signature : ModeSignature}
    (discipline : {localSource localTarget : signature.graph.Mode} →
      {localDom localCod : ModalityPath signature.graph localSource localTarget} →
      (cell : RawTwoCellExpr signature localDom localCod) → CellHasCupCapGenerators cell)
    {sourceMode targetMode : signature.graph.Mode}
    {oneCellF oneCellG oneCellH : ModalityPath signature.graph sourceMode targetMode}
    {cellAlphaFirst cellAlphaSecond : RawTwoCellExpr signature oneCellF oneCellG}
    (cellBeta : RawTwoCellExpr signature oneCellG oneCellH)
    (matchingsEqual : matchingOf cellAlphaFirst = matchingOf cellAlphaSecond) :
    matchingOf (RawTwoCellExpr.vcomp cellAlphaFirst cellBeta)
      = matchingOf (RawTwoCellExpr.vcomp cellAlphaSecond cellBeta) := by
  show extractDiagram oneCellF.length
      (processSpine (canonicalMatchingSeed oneCellF.length)
        (RawTwoCellExpr.vcomp cellAlphaFirst cellBeta).spine)
    = extractDiagram oneCellF.length
        (processSpine (canonicalMatchingSeed oneCellF.length)
          (RawTwoCellExpr.vcomp cellAlphaSecond cellBeta).spine)
  have extractsEqual : extractDiagram oneCellF.length
      (processSpine (canonicalMatchingSeed oneCellF.length) cellAlphaFirst.spine)
    = extractDiagram oneCellF.length
        (processSpine (canonicalMatchingSeed oneCellF.length) cellAlphaSecond.spine) :=
    matchingsEqual
  cases Nat.lt_or_ge 0 oneCellF.length with
  | inl boundaryInhabited =>
      exact extractAfterProcessing_vcompLeft_ofSeed cellBeta oneCellF.length
        (canonicalMatchingSeed oneCellF.length)
        (matchingSwapStateConditions_initial oneCellF.length boundaryInhabited)
        (canonicalMatchingSeed_wireCount oneCellF.length)
        (discipline cellAlphaSecond)
        (discipline cellBeta)
        extractsEqual
  | inr boundaryAtMostZero =>
      have zeroLength : oneCellF.length = 0 :=
        Nat.le_antisymm boundaryAtMostZero (Nat.zero_le oneCellF.length)
      rw [zeroLength]
      rw [zeroLength] at extractsEqual
      have shiftAlphaFirst : extractDiagram 0
          (processSpine { openWires := List.range 0, links := [], nextFresh := 0, loops := 0 }
            cellAlphaFirst.spine)
        = extractDiagram 0
            (processSpine { openWires := [], links := [], nextFresh := 1, loops := 0 }
              cellAlphaFirst.spine) :=
        extractAfterProcessing_emptyBoundary_counterShift cellAlphaFirst.spine
          (zeroLength ▸ cellAlphaFirst.spineBoundaryChained_spine)
          (cellAlphaFirst.spineHasCupCapAtoms_spine (discipline cellAlphaFirst))
      have shiftAlphaSecond : extractDiagram 0
          (processSpine { openWires := List.range 0, links := [], nextFresh := 0, loops := 0 }
            cellAlphaSecond.spine)
        = extractDiagram 0
            (processSpine { openWires := [], links := [], nextFresh := 1, loops := 0 }
              cellAlphaSecond.spine) :=
        extractAfterProcessing_emptyBoundary_counterShift cellAlphaSecond.spine
          (zeroLength ▸ cellAlphaSecond.spineBoundaryChained_spine)
          (cellAlphaSecond.spineHasCupCapAtoms_spine (discipline cellAlphaSecond))
      have shiftCompositeFirst : extractDiagram 0
          (processSpine { openWires := List.range 0, links := [], nextFresh := 0, loops := 0 }
            (RawTwoCellExpr.vcomp cellAlphaFirst cellBeta).spine)
        = extractDiagram 0
            (processSpine { openWires := [], links := [], nextFresh := 1, loops := 0 }
              (RawTwoCellExpr.vcomp cellAlphaFirst cellBeta).spine) :=
        extractAfterProcessing_emptyBoundary_counterShift
          (RawTwoCellExpr.vcomp cellAlphaFirst cellBeta).spine
          (zeroLength ▸ (RawTwoCellExpr.vcomp cellAlphaFirst cellBeta).spineBoundaryChained_spine)
          ((RawTwoCellExpr.vcomp cellAlphaFirst cellBeta).spineHasCupCapAtoms_spine
            (discipline (RawTwoCellExpr.vcomp cellAlphaFirst cellBeta)))
      have shiftCompositeSecond : extractDiagram 0
          (processSpine { openWires := List.range 0, links := [], nextFresh := 0, loops := 0 }
            (RawTwoCellExpr.vcomp cellAlphaSecond cellBeta).spine)
        = extractDiagram 0
            (processSpine { openWires := [], links := [], nextFresh := 1, loops := 0 }
              (RawTwoCellExpr.vcomp cellAlphaSecond cellBeta).spine) :=
        extractAfterProcessing_emptyBoundary_counterShift
          (RawTwoCellExpr.vcomp cellAlphaSecond cellBeta).spine
          (zeroLength ▸ (RawTwoCellExpr.vcomp cellAlphaSecond cellBeta).spineBoundaryChained_spine)
          ((RawTwoCellExpr.vcomp cellAlphaSecond cellBeta).spineHasCupCapAtoms_spine
            (discipline (RawTwoCellExpr.vcomp cellAlphaSecond cellBeta)))
      have proxyConditions : MatchingSwapStateConditions 0
          { openWires := [], links := [], nextFresh := 1, loops := 0 } :=
        { bottomLe := Nat.zero_le 1
          forest := by exact True.intro
          nfPos := Nat.lt_succ_self 0
          fresh := ⟨fun _ absurdMem => (by cases absurdMem),
            fun _ absurdMem => (by cases absurdMem)⟩ }
      have proxyExtractsEqual : extractDiagram 0
          (processSpine { openWires := [], links := [], nextFresh := 1, loops := 0 }
            cellAlphaFirst.spine)
        = extractDiagram 0
            (processSpine { openWires := [], links := [], nextFresh := 1, loops := 0 }
              cellAlphaSecond.spine) :=
        (shiftAlphaFirst.symm.trans extractsEqual).trans shiftAlphaSecond
      have proxyComposite := extractAfterProcessing_vcompLeft_ofSeed cellBeta 0
        { openWires := [], links := [], nextFresh := 1, loops := 0 }
        proxyConditions zeroLength.symm
        (discipline cellAlphaSecond)
        (discipline cellBeta)
        proxyExtractsEqual
      exact (shiftCompositeFirst.trans proxyComposite).trans shiftCompositeSecond.symm

/-- **The vcomp-RIGHT matching congruence for an inhabited MID boundary, generic over a cup/cap discipline.**
The exact body of the walking adjunction's `matchingOf_vcompRight_congruence_ofMidBoundaryPos`, discipline
abstracted: the source boundary dispatches between the canonical seed and the counter-shift proxy; the
seed-generic core `extractAfterProcessing_vcompRight_ofSeed` glues the `beta`-premise (living at the mid seed)
through the `alpha`-fold. -/
theorem matchingOf_vcompRight_congr_ofMidBoundaryPos_ofDiscipline {signature : ModeSignature}
    (discipline : {localSource localTarget : signature.graph.Mode} →
      {localDom localCod : ModalityPath signature.graph localSource localTarget} →
      (cell : RawTwoCellExpr signature localDom localCod) → CellHasCupCapGenerators cell)
    {sourceMode targetMode : signature.graph.Mode}
    {oneCellF oneCellG oneCellH : ModalityPath signature.graph sourceMode targetMode}
    (cellAlpha : RawTwoCellExpr signature oneCellF oneCellG)
    {cellBetaFirst cellBetaSecond : RawTwoCellExpr signature oneCellG oneCellH}
    (midBoundaryPos : 0 < oneCellG.length)
    (matchingsEqual : matchingOf cellBetaFirst = matchingOf cellBetaSecond) :
    matchingOf (RawTwoCellExpr.vcomp cellAlpha cellBetaFirst)
      = matchingOf (RawTwoCellExpr.vcomp cellAlpha cellBetaSecond) := by
  show extractDiagram oneCellF.length
      (processSpine (canonicalMatchingSeed oneCellF.length)
        (RawTwoCellExpr.vcomp cellAlpha cellBetaFirst).spine)
    = extractDiagram oneCellF.length
        (processSpine (canonicalMatchingSeed oneCellF.length)
          (RawTwoCellExpr.vcomp cellAlpha cellBetaSecond).spine)
  have extractsEqual : extractDiagram oneCellG.length
      (processSpine (canonicalMatchingSeed oneCellG.length) cellBetaFirst.spine)
    = extractDiagram oneCellG.length
        (processSpine (canonicalMatchingSeed oneCellG.length) cellBetaSecond.spine) :=
    matchingsEqual
  cases Nat.lt_or_ge 0 oneCellF.length with
  | inl sourceInhabited =>
      exact extractAfterProcessing_vcompRight_ofSeed cellAlpha oneCellF.length
        (canonicalMatchingSeed oneCellF.length)
        (matchingSwapStateConditions_initial oneCellF.length sourceInhabited)
        (canonicalMatchingSeed_wireCount oneCellF.length)
        (canonicalMatchingSeed_wireListDistinct oneCellF.length)
        (discipline cellAlpha)
        (discipline cellBetaFirst)
        (discipline cellBetaSecond)
        midBoundaryPos extractsEqual
  | inr sourceAtMostZero =>
      have zeroLength : oneCellF.length = 0 :=
        Nat.le_antisymm sourceAtMostZero (Nat.zero_le oneCellF.length)
      rw [zeroLength]
      have shiftCompositeFirst : extractDiagram 0
          (processSpine { openWires := List.range 0, links := [], nextFresh := 0, loops := 0 }
            (RawTwoCellExpr.vcomp cellAlpha cellBetaFirst).spine)
        = extractDiagram 0
            (processSpine { openWires := [], links := [], nextFresh := 1, loops := 0 }
              (RawTwoCellExpr.vcomp cellAlpha cellBetaFirst).spine) :=
        extractAfterProcessing_emptyBoundary_counterShift
          (RawTwoCellExpr.vcomp cellAlpha cellBetaFirst).spine
          (zeroLength ▸ (RawTwoCellExpr.vcomp cellAlpha cellBetaFirst).spineBoundaryChained_spine)
          ((RawTwoCellExpr.vcomp cellAlpha cellBetaFirst).spineHasCupCapAtoms_spine
            (discipline (RawTwoCellExpr.vcomp cellAlpha cellBetaFirst)))
      have shiftCompositeSecond : extractDiagram 0
          (processSpine { openWires := List.range 0, links := [], nextFresh := 0, loops := 0 }
            (RawTwoCellExpr.vcomp cellAlpha cellBetaSecond).spine)
        = extractDiagram 0
            (processSpine { openWires := [], links := [], nextFresh := 1, loops := 0 }
              (RawTwoCellExpr.vcomp cellAlpha cellBetaSecond).spine) :=
        extractAfterProcessing_emptyBoundary_counterShift
          (RawTwoCellExpr.vcomp cellAlpha cellBetaSecond).spine
          (zeroLength ▸ (RawTwoCellExpr.vcomp cellAlpha cellBetaSecond).spineBoundaryChained_spine)
          ((RawTwoCellExpr.vcomp cellAlpha cellBetaSecond).spineHasCupCapAtoms_spine
            (discipline (RawTwoCellExpr.vcomp cellAlpha cellBetaSecond)))
      have proxyConditions : MatchingSwapStateConditions 0
          { openWires := [], links := [], nextFresh := 1, loops := 0 } :=
        { bottomLe := Nat.zero_le 1
          forest := by exact True.intro
          nfPos := Nat.lt_succ_self 0
          fresh := ⟨fun _ absurdMem => (by cases absurdMem),
            fun _ absurdMem => (by cases absurdMem)⟩ }
      have proxyDistinct : WireListDistinct ([] : List Nat) :=
        fun _ _ _ twoInRange => nomatch twoInRange
      have proxyComposite := extractAfterProcessing_vcompRight_ofSeed cellAlpha 0
        { openWires := [], links := [], nextFresh := 1, loops := 0 }
        proxyConditions zeroLength.symm proxyDistinct
        (discipline cellAlpha)
        (discipline cellBetaFirst)
        (discipline cellBetaSecond)
        midBoundaryPos extractsEqual
      exact (shiftCompositeFirst.trans proxyComposite).trans shiftCompositeSecond.symm

/-- **The vcomp-RIGHT matching congruence, generic over a cup/cap discipline — UNCONDITIONAL in the mid
boundary.**  The exact body of the walking adjunction's `matchingOf_vcompRight_congruence`: an inhabited mid
boundary routes to the positive-mid leg above; an empty mid boundary routes through the seed-generic empty-mid
core `extractAfterProcessing_vcompRight_ofSeed_emptyMid`, source boundary dispatched between the canonical seed
and the counter-shift proxy. -/
theorem matchingOf_vcompRight_congr_ofDiscipline {signature : ModeSignature}
    (discipline : {localSource localTarget : signature.graph.Mode} →
      {localDom localCod : ModalityPath signature.graph localSource localTarget} →
      (cell : RawTwoCellExpr signature localDom localCod) → CellHasCupCapGenerators cell)
    {sourceMode targetMode : signature.graph.Mode}
    {oneCellF oneCellG oneCellH : ModalityPath signature.graph sourceMode targetMode}
    (cellAlpha : RawTwoCellExpr signature oneCellF oneCellG)
    {cellBetaFirst cellBetaSecond : RawTwoCellExpr signature oneCellG oneCellH}
    (matchingsEqual : matchingOf cellBetaFirst = matchingOf cellBetaSecond) :
    matchingOf (RawTwoCellExpr.vcomp cellAlpha cellBetaFirst)
      = matchingOf (RawTwoCellExpr.vcomp cellAlpha cellBetaSecond) := by
  cases Nat.lt_or_ge 0 oneCellG.length with
  | inl midInhabited =>
      exact matchingOf_vcompRight_congr_ofMidBoundaryPos_ofDiscipline discipline cellAlpha
        midInhabited matchingsEqual
  | inr midAtMostZero =>
      have midBoundaryZero : oneCellG.length = 0 :=
        Nat.le_antisymm midAtMostZero (Nat.zero_le oneCellG.length)
      show extractDiagram oneCellF.length
          (processSpine (canonicalMatchingSeed oneCellF.length)
            (RawTwoCellExpr.vcomp cellAlpha cellBetaFirst).spine)
        = extractDiagram oneCellF.length
            (processSpine (canonicalMatchingSeed oneCellF.length)
              (RawTwoCellExpr.vcomp cellAlpha cellBetaSecond).spine)
      have extractsEqual : extractDiagram oneCellG.length
          (processSpine (canonicalMatchingSeed oneCellG.length) cellBetaFirst.spine)
        = extractDiagram oneCellG.length
            (processSpine (canonicalMatchingSeed oneCellG.length) cellBetaSecond.spine) :=
        matchingsEqual
      cases Nat.lt_or_ge 0 oneCellF.length with
      | inl sourceInhabited =>
          exact extractAfterProcessing_vcompRight_ofSeed_emptyMid cellAlpha
            oneCellF.length (canonicalMatchingSeed oneCellF.length)
            (matchingSwapStateConditions_initial oneCellF.length sourceInhabited)
            (canonicalMatchingSeed_wireCount oneCellF.length)
            (canonicalMatchingSeed_wireListDistinct oneCellF.length)
            (discipline cellAlpha)
            (discipline cellBetaFirst)
            (discipline cellBetaSecond)
            midBoundaryZero extractsEqual
      | inr sourceAtMostZero =>
          have zeroLength : oneCellF.length = 0 :=
            Nat.le_antisymm sourceAtMostZero (Nat.zero_le oneCellF.length)
          rw [zeroLength]
          have shiftCompositeFirst : extractDiagram 0
              (processSpine
                { openWires := List.range 0, links := [], nextFresh := 0, loops := 0 }
                (RawTwoCellExpr.vcomp cellAlpha cellBetaFirst).spine)
            = extractDiagram 0
                (processSpine { openWires := [], links := [], nextFresh := 1, loops := 0 }
                  (RawTwoCellExpr.vcomp cellAlpha cellBetaFirst).spine) :=
            extractAfterProcessing_emptyBoundary_counterShift
              (RawTwoCellExpr.vcomp cellAlpha cellBetaFirst).spine
              (zeroLength
                ▸ (RawTwoCellExpr.vcomp cellAlpha cellBetaFirst).spineBoundaryChained_spine)
              ((RawTwoCellExpr.vcomp cellAlpha cellBetaFirst).spineHasCupCapAtoms_spine
                (discipline (RawTwoCellExpr.vcomp cellAlpha cellBetaFirst)))
          have shiftCompositeSecond : extractDiagram 0
              (processSpine
                { openWires := List.range 0, links := [], nextFresh := 0, loops := 0 }
                (RawTwoCellExpr.vcomp cellAlpha cellBetaSecond).spine)
            = extractDiagram 0
                (processSpine { openWires := [], links := [], nextFresh := 1, loops := 0 }
                  (RawTwoCellExpr.vcomp cellAlpha cellBetaSecond).spine) :=
            extractAfterProcessing_emptyBoundary_counterShift
              (RawTwoCellExpr.vcomp cellAlpha cellBetaSecond).spine
              (zeroLength
                ▸ (RawTwoCellExpr.vcomp cellAlpha cellBetaSecond).spineBoundaryChained_spine)
              ((RawTwoCellExpr.vcomp cellAlpha cellBetaSecond).spineHasCupCapAtoms_spine
                (discipline (RawTwoCellExpr.vcomp cellAlpha cellBetaSecond)))
          have proxyConditions : MatchingSwapStateConditions 0
              { openWires := [], links := [], nextFresh := 1, loops := 0 } :=
            { bottomLe := Nat.zero_le 1
              forest := by exact True.intro
              nfPos := Nat.lt_succ_self 0
              fresh := ⟨fun _ absurdMem => (by cases absurdMem),
                fun _ absurdMem => (by cases absurdMem)⟩ }
          have proxyDistinct : WireListDistinct ([] : List Nat) :=
            fun _ _ _ twoInRange => nomatch twoInRange
          have proxyComposite := extractAfterProcessing_vcompRight_ofSeed_emptyMid cellAlpha
            0 { openWires := [], links := [], nextFresh := 1, loops := 0 }
            proxyConditions zeroLength.symm proxyDistinct
            (discipline cellAlpha)
            (discipline cellBetaFirst)
            (discipline cellBetaSecond)
            midBoundaryZero extractsEqual
          exact (shiftCompositeFirst.trans proxyComposite).trans shiftCompositeSecond.symm

/-! ## The whisker congruences at the string signature -/

/-- **The `whiskerLeft` field inhabitant at the walking adjoint triple — UNCONDITIONAL.**  Every string cell is
cup/cap-disciplined (`cellHasCupCapGenerators_ofStringSignature`), so the signature-polymorphic full congruence
`matchingOf_whiskerLeft_congr` applies with no side conditions. -/
theorem stringMatchingOf_whiskerLeft_congruence
    {sourceMode middleMode targetMode : AdjointTripleMode}
    (oneCell : ModalityPath adjointTripleGraph sourceMode middleMode)
    {oneCellG oneCellH : ModalityPath adjointTripleGraph middleMode targetMode}
    {cellBeta cellBetaPrime : RawTwoCellExpr adjointTripleModeSignature oneCellG oneCellH}
    (matchingsEqual : matchingOf cellBeta = matchingOf cellBetaPrime) :
    matchingOf (RawTwoCellExpr.whiskerLeft oneCell cellBeta)
      = matchingOf (RawTwoCellExpr.whiskerLeft oneCell cellBetaPrime) :=
  matchingOf_whiskerLeft_congr oneCell
    (cellHasCupCapGenerators_ofStringSignature cellBeta)
    (cellHasCupCapGenerators_ofStringSignature cellBetaPrime) matchingsEqual

/-- **The `whiskerRight` field inhabitant at the walking adjoint triple — UNCONDITIONAL.**  As above, via
`matchingOf_whiskerRight_congr`. -/
theorem stringMatchingOf_whiskerRight_congruence
    {sourceMode middleMode targetMode : AdjointTripleMode}
    {oneCellF oneCellG : ModalityPath adjointTripleGraph sourceMode middleMode}
    (oneCell : ModalityPath adjointTripleGraph middleMode targetMode)
    {cellAlpha cellAlphaPrime : RawTwoCellExpr adjointTripleModeSignature oneCellF oneCellG}
    (matchingsEqual : matchingOf cellAlpha = matchingOf cellAlphaPrime) :
    matchingOf (RawTwoCellExpr.whiskerRight oneCell cellAlpha)
      = matchingOf (RawTwoCellExpr.whiskerRight oneCell cellAlphaPrime) :=
  matchingOf_whiskerRight_congr oneCell
    (cellHasCupCapGenerators_ofStringSignature cellAlpha)
    (cellHasCupCapGenerators_ofStringSignature cellAlphaPrime) matchingsEqual

/-! ## ★ The saturated-congruence bundle, PROVED -/

/-- ★★ **The string's saturated-congruence compositionality is PROVED.**  Each of the four fields is the
corresponding `matchingOf` congruence at the string signature, discharged via the universal string discipline
`cellHasCupCapGenerators_ofStringSignature` — the whiskers via `stringMatchingOf_whiskerLeft_congruence` /
`stringMatchingOf_whiskerRight_congruence` (the signature-polymorphic full congruences), the vertical composites
via the generic boundary-dispatch wrappers above.  The bundle stops being a hypothesis of
`stringSaturatedConv_matchingOf_eq` and becomes a theorem — the SECOND named soundness residual is discharged
unconditionally. -/
theorem stringMatchingSaturatedCongruence_proved : StringMatchingSaturatedCongruence where
  vcompLeft := matchingOf_vcompLeft_congr_ofDiscipline cellHasCupCapGenerators_ofStringSignature
  vcompRight := matchingOf_vcompRight_congr_ofDiscipline cellHasCupCapGenerators_ofStringSignature
  whiskerLeft := @stringMatchingOf_whiskerLeft_congruence
  whiskerRight := @stringMatchingOf_whiskerRight_congruence

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the four-field `StringMatchingSaturatedCongruence` is PROVED.**  The second named residual
of the full two-level soundness reduction (`stringSaturatedConv_matchingOf_eq`) is discharged unconditionally by
porting the signature-polymorphic `matchingOf` congruence machinery to the three-generator seed: the discipline
`cellHasCupCapGenerators_ofStringSignature` is universal (four cups/caps), and the whisker/vcomp cores are
colour-BLIND, so the port needs no new mathematics beyond swapping the discipline witness.  The remaining
soundness input is now exactly the `ofFull` Godement leg — discharged in `StringMatchingSoundness` via the
cup/cap-discipline capstone.  `= true`. -/
def fxString_hasMatchingSaturatedCongruence : Bool := true

end FX1Poly.Polygraph
