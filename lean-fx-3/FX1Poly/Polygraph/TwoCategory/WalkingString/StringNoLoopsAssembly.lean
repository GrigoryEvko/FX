import FX1Poly.Polygraph.TwoCategory.WalkingString.StringCapPinWordChain
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringOrientationCapPreserves
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringFussCatalanCupPreserves

/-! # WalkingString — the NO-LOOPS assembly (STRING-JOINT r2, B3 — both walls glued, the headline flip)

The two per-step residuals FC-1 named are now BOTH shipped:

  * WALL 2 (`StringCapPinWordChain`) — the reachable-`capPin` fold: at each cap the window is in range and reads a cap
    word, DISCHARGED from the boundary-word chain;
  * WALL 1 (`StringOrientationCapPreserves`) — the CAP orientation preservation `stringOrientationDiscipline_stepCap`,
    the merge-dual of the shipped cup case.

This file GLUES them into the UNCONDITIONAL no-loops theorem.  The combined fold threads, from the fresh seed, the
static boundary-WORD chain, the joint reachable-class invariant (`StringJointInvariant`: forest / census /
non-crossing), and the orientation discipline with labels PINNED to `pathLabels boundaryWord`.  At each atom the joint
invariant is preserved (shipped `stringJointInvariant_stepAtom`), the discipline is preserved (cup via the shipped
16-region case, cap via WALL 1 — labels re-pinned by the shipped `advanceLabels`-tracks-`pathLabels`), and at each cap
the window's cap word (WALL 2, strengthened to `isCapWordOrdered = true`) feeds the chirality refutation
(`stringDisciplinedCap_windowDistinct`) for the distinctness `CapsDistinctAlongFold` wants.

## What closes here (each zero-axiom)

  * the two generator word facts `stringCupGeneratorCodWord_isCupWord` / `stringCapGeneratorDomWord_isCapWord`, the cap
    window's cap-word projection `stringCapWindow_isCapWord`, and the cup-orient `codLabels` wrapper;
  * ★ `stringOrientationDiscipline_stepAtom_ofWordChain` — one atom preserves the discipline over `pathLabels
    boundaryWord`, dispatching cup (shipped) / cap (WALL 1);
  * ★★ `stringCapsDistinctAlongFold_ofWordChain` — the combined fold produces `CapsDistinctAlongFold` UNCONDITIONALLY;
  * ★★ `stringMatchingOf_loops_zero` — the HEADLINE: `(matchingOf cell).loops = 0` for EVERY cup/cap string cell,
    hypothesis-free (FC-0's `stringMatchingOf_loops_zero_ofCapsDistinct` closes the conversion).

## FC-3 / #2020 distance (no overclaim)

This closes ingredient N2 (loop-freedom / acyclicity) for the string carrier ONLY.  It does NOT deliver FC completeness
or the #2020 multi-adjunction word-problem DECISION — those ride the matching/staircase completeness route
(`StringMatchingCompleteness`, `StringFussCatalanStaircase*`, SQ-5), all still open.  #2020 stays `in_progress`.

Raw Lean 4 + Init; the fold mirrors the shipped joint-invariant fold, the word facts are generator case analysis, the
transport is the shipped arity reductions.  `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free;
per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The generator word facts (the cup cod word / cap dom word chiralities) -/

/-- ★ **A cup generator's cod word is an ordered cup word.**  Casing the generator: the two CUP cases
(`unitLower` / `unitUpper`) read `(F,G)` / `(G,H)`, each an ordered cup word; the two CAP cases are excluded by
`domZero` (their dom word has length 2).  The cup dual of `stringCapGeneratorDomWord_notCupWord`. -/
theorem stringCupGeneratorCodWord_isCupWord {midSource midTarget : AdjointTripleMode}
    {generatorDom generatorCod : ModalityPath adjointTripleGraph midSource midTarget}
    (generator : StringTwoCell generatorDom generatorCod) (domZero : generatorDom.length = 0) :
    isCupWordOrdered (wireLabelListGetAt (pathLabels generatorCod) 0)
      (wireLabelListGetAt (pathLabels generatorCod) 1) = true := by
  cases generator with
  | unitLower => rfl
  | unitUpper => rfl
  | counitLower => exact absurd domZero (by decide)
  | counitUpper => exact absurd domZero (by decide)

/-- ★ **A cap generator's dom word is an ordered cap word.**  Casing the generator: the two CAP cases
(`counitLower` / `counitUpper`) read `(G,F)` / `(H,G)`, each an ordered cap word; the two CUP cases are excluded by
`codZero`.  The `isCapWordOrdered = true` STRENGTHENING of `stringCapGeneratorDomWord_notCupWord` (needed because the
cap-orient colour reads require the genuine cap word, not merely non-cup). -/
theorem stringCapGeneratorDomWord_isCapWord {midSource midTarget : AdjointTripleMode}
    {generatorDom generatorCod : ModalityPath adjointTripleGraph midSource midTarget}
    (generator : StringTwoCell generatorDom generatorCod) (codZero : generatorCod.length = 0) :
    isCapWordOrdered (wireLabelListGetAt (pathLabels generatorDom) 0)
      (wireLabelListGetAt (pathLabels generatorDom) 1) = true := by
  cases generator with
  | unitLower => exact absurd codZero (by decide)
  | unitUpper => exact absurd codZero (by decide)
  | counitLower => rfl
  | counitUpper => rfl

/-- ★★ **A cap window reads its `generatorDom` cap word as a genuine CAP word** (modulo the boundary-word
decomposition).  The `isCapWordOrdered = true` STRENGTHENING of `stringCapWindow_notCupWord`: same label reads
(`stringPathLabels_read_pastLeft` / `_belowLeft`), but reading the cap-word chirality
(`stringCapGeneratorDomWord_isCapWord`).  This is the WALL-2 fact WALL 1's cap-orient consumes. -/
theorem stringCapWindow_isCapWord {sourceMode targetMode : AdjointTripleMode}
    (atom : SpineAtom adjointTripleModeSignature sourceMode targetMode) (labels : List WireLabel)
    (labelsEq : labels = pathLabels
      (composePath atom.leftContext (composePath atom.generatorDom atom.rightContext)))
    (domTwo : atom.generatorDom.length = 2) (codZero : atom.generatorCod.length = 0) :
    isCapWordOrdered (wireLabelListGetAt labels atom.leftContext.length)
      (wireLabelListGetAt labels (atom.leftContext.length + 1)) = true := by
  subst labelsEq
  have domPos0 : 0 < atom.generatorDom.length := by rw [domTwo]; decide
  have domPos1 : 1 < atom.generatorDom.length := by rw [domTwo]; decide
  have past0 := stringPathLabels_read_pastLeft atom.leftContext
    (composePath atom.generatorDom atom.rightContext) 0
  rw [Nat.add_zero] at past0
  have below0 := stringPathLabels_read_belowLeft atom.generatorDom atom.rightContext 0 domPos0
  have past1 := stringPathLabels_read_pastLeft atom.leftContext
    (composePath atom.generatorDom atom.rightContext) 1
  have below1 := stringPathLabels_read_belowLeft atom.generatorDom atom.rightContext 1 domPos1
  have capWord := stringCapGeneratorDomWord_isCapWord atom.generator codZero
  rw [← below0, ← below1, ← past0, ← past1] at capWord
  exact capWord

/-! ## The cup-orient `codLabels` wrapper -/

/-- ★ **The CUP case of `preserves` over a `codLabels` list.**  Repackages the shipped `stringOrientationDiscipline_stepCup`
(stated over an explicit two-letter cod word) to accept a length-2 cod-label list that reads an ordered cup word — so
the boundary-word `advanceLabels` (which splices `pathLabels generatorCod`) plugs in directly. -/
theorem stringOrientationDiscipline_stepCup_codLabels (state : WireState) (labels : List WireLabel)
    (position : Nat) (codLabels : List WireLabel) (positionInRange : position ≤ state.openWires.length)
    (fresh : StringWireStateFresh state) (hforest : stringIsUnionFindForest state.links)
    (discipline : StringOrientationDiscipline state labels) (codTwo : codLabels.length = 2)
    (codCup : isCupWordOrdered (wireLabelListGetAt codLabels 0) (wireLabelListGetAt codLabels 1) = true) :
    StringOrientationDiscipline (stepCup state position) (wireLabelListInsertAt labels position codLabels) := by
  cases codLabels with
  | nil => exact Nat.noConfusion codTwo
  | cons labelL rest =>
      cases rest with
      | nil => exact Nat.noConfusion (Nat.succ.inj codTwo)
      | cons labelR rest2 =>
          cases rest2 with
          | nil =>
              exact stringOrientationDiscipline_stepCup state labels position labelL labelR positionInRange
                fresh hforest discipline codCup
          | cons _ _ => exact Nat.noConfusion (Nat.succ.inj (Nat.succ.inj codTwo))

/-! ## ★ One atom preserves the discipline over the boundary word -/

/-- ★★ **One cup/cap atom preserves the orientation discipline over `pathLabels boundaryWord`.**  Dispatching the
arity: a CUP applies the shipped 16-region `stringOrientationDiscipline_stepCup` (its cod word a cup word by
`stringCupGeneratorCodWord_isCupWord`, freshness + forest from the joint invariant); a CAP applies WALL 1's
`stringOrientationDiscipline_stepCap` (its window a cap word by `stringCapWindow_isCapWord`, forest + non-crossing from
the joint invariant).  Both re-pin the labels to `pathLabels (leftContext · generatorCod · rightContext)` via the
shipped `advanceLabels`-tracks-`pathLabels` (`stringAdvanceLabels_tracksWordChain`) and the arity reductions. -/
theorem stringOrientationDiscipline_stepAtom_ofWordChain {sourceMode targetMode : AdjointTripleMode}
    (seedBoundary : Nat) (state : WireState)
    (atom : SpineAtom adjointTripleModeSignature sourceMode targetMode)
    (boundaryWord : ModalityPath adjointTripleGraph sourceMode targetMode)
    (arity : AtomHasCupOrCapArity atom)
    (headFires : boundaryWord
      = composePath atom.leftContext (composePath atom.generatorDom atom.rightContext))
    (tracksEntry : state.openWires.length = atom.domBoundaryLength)
    (joint : StringJointInvariant seedBoundary state)
    (discipline : StringOrientationDiscipline state (pathLabels boundaryWord)) :
    StringOrientationDiscipline (stepAtom state atom)
      (pathLabels (composePath atom.leftContext (composePath atom.generatorCod atom.rightContext))) := by
  cases arity with
  | inl cupArity =>
      obtain ⟨domZero, codTwo⟩ := cupArity
      have positionInRange : atom.leftContext.length ≤ state.openWires.length := by
        rw [tracksEntry]
        show atom.leftContext.length
          ≤ atom.leftContext.length + atom.generatorDom.length + atom.rightContext.length
        exact Nat.le_trans (Nat.le_add_right atom.leftContext.length atom.generatorDom.length)
          (Nat.le_add_right (atom.leftContext.length + atom.generatorDom.length) atom.rightContext.length)
      have cupResult : StringOrientationDiscipline (stepCup state atom.leftContext.length)
          (wireLabelListInsertAt (pathLabels boundaryWord) atom.leftContext.length
            (pathLabels atom.generatorCod)) :=
        stringOrientationDiscipline_stepCup_codLabels state (pathLabels boundaryWord)
          atom.leftContext.length (pathLabels atom.generatorCod) positionInRange joint.fresh joint.forest
          discipline (pathLabels_length_two atom.generatorCod codTwo)
          (stringCupGeneratorCodWord_isCupWord atom.generator domZero)
      have stepEq : stepCup state atom.leftContext.length = stepAtom state atom :=
        (stepAtom_ofCupArity state atom domZero codTwo).symm
      have labelEq : wireLabelListInsertAt (pathLabels boundaryWord) atom.leftContext.length
            (pathLabels atom.generatorCod)
          = pathLabels (composePath atom.leftContext (composePath atom.generatorCod atom.rightContext)) :=
        (advanceLabels_ofCupArity (pathLabels boundaryWord) atom domZero codTwo).symm.trans
          (stringAdvanceLabels_tracksWordChain atom boundaryWord (Or.inl ⟨domZero, codTwo⟩) headFires)
      rw [stepEq, labelEq] at cupResult
      exact cupResult
  | inr capArity =>
      obtain ⟨domTwo, codZero⟩ := capArity
      have capInRange : atom.leftContext.length + 2 ≤ state.openWires.length := by
        rw [tracksEntry]
        show atom.leftContext.length + 2
          ≤ atom.leftContext.length + atom.generatorDom.length + atom.rightContext.length
        rw [domTwo]
        exact Nat.le_add_right (atom.leftContext.length + 2) atom.rightContext.length
      have capResult : StringOrientationDiscipline (stepCap state atom.leftContext.length)
          (wireLabelListRemoveTwoAt (pathLabels boundaryWord) atom.leftContext.length) :=
        stringOrientationDiscipline_stepCap state (pathLabels boundaryWord) atom.leftContext.length
          capInRange joint.forest joint.nonCrossing discipline
          (stringCapWindow_isCapWord atom (pathLabels boundaryWord) (congrArg pathLabels headFires) domTwo
            codZero)
      have stepEq : stepCap state atom.leftContext.length = stepAtom state atom :=
        (stepAtom_ofCapArity state atom domTwo codZero).symm
      have labelEq : wireLabelListRemoveTwoAt (pathLabels boundaryWord) atom.leftContext.length
          = pathLabels (composePath atom.leftContext (composePath atom.generatorCod atom.rightContext)) :=
        (advanceLabels_ofCapArity (pathLabels boundaryWord) atom domTwo codZero).symm.trans
          (stringAdvanceLabels_tracksWordChain atom boundaryWord (Or.inr ⟨domTwo, codZero⟩) headFires)
      rw [stepEq, labelEq] at capResult
      exact capResult

/-! ## ★★ The combined fold — `CapsDistinctAlongFold` UNCONDITIONALLY -/

/-- ★★ **`CapsDistinctAlongFold` DISCHARGED from the word chain + both walls.**  The combined fold threads the boundary
word chain, the joint invariant, the orientation discipline (labels `pathLabels boundaryWord`), and the length
invariant.  At each cap the window's cap word (`stringCapWindow_isCapWord`, WALL 2) → non-cup word
(`stringCapWord_not_cupWord`) → distinct component (`stringDisciplinedCap_windowDistinct`), giving the head obligation;
the tail recurses on the preserved joint invariant + preserved discipline (`stringOrientationDiscipline_stepAtom_ofWordChain`,
using WALL 1's cap-orient).  Structural list recursion; UNCONDITIONAL. -/
theorem stringCapsDistinctAlongFold_ofWordChain {sourceMode targetMode : AdjointTripleMode} :
    (atoms : List (SpineAtom adjointTripleModeSignature sourceMode targetMode)) →
    (state : WireState) →
    (boundaryWord : ModalityPath adjointTripleGraph sourceMode targetMode) → (seedBoundary : Nat) →
    SpineHasCupCapAtoms atoms →
    SpineBoundaryWordChained boundaryWord atoms →
    state.openWires.length = boundaryWord.length →
    StringJointInvariant seedBoundary state →
    StringOrientationDiscipline state (pathLabels boundaryWord) →
    CapsDistinctAlongFold state atoms
  | [], _, _, _, _, _, _, _, _ => trivial
  | atom :: rest, state, boundaryWord, seedBoundary, arityAll, wordChained, tracksLength, joint, discipline => by
      obtain ⟨headArity, tailArity⟩ := spineHasCupCapAtoms_tail arityAll
      obtain ⟨headFires, tailChained⟩ := spineBoundaryWordChained_tail wordChained
      have wordLenEqDom : boundaryWord.length = atom.domBoundaryLength := by
        rw [headFires]
        show (composePath atom.leftContext (composePath atom.generatorDom atom.rightContext)).length
          = atom.leftContext.length + atom.generatorDom.length + atom.rightContext.length
        rw [ModalityPath.length_composePath atom.leftContext
            (composePath atom.generatorDom atom.rightContext),
          ModalityPath.length_composePath atom.generatorDom atom.rightContext, Nat.add_assoc]
      have tracksEntry : state.openWires.length = atom.domBoundaryLength := tracksLength.trans wordLenEqDom
      have jointNew := stringJointInvariant_stepAtom seedBoundary state atom headArity tracksEntry joint
      have disciplineNew := stringOrientationDiscipline_stepAtom_ofWordChain seedBoundary state atom
        boundaryWord headArity headFires tracksEntry joint discipline
      have newTracks : (stepAtom state atom).openWires.length
          = (composePath atom.leftContext (composePath atom.generatorCod atom.rightContext)).length := by
        rw [stepAtom_openWires_tracksBoundary state atom headArity tracksEntry]
        show atom.leftContext.length + atom.generatorCod.length + atom.rightContext.length
          = (composePath atom.leftContext (composePath atom.generatorCod atom.rightContext)).length
        rw [ModalityPath.length_composePath atom.leftContext
            (composePath atom.generatorCod atom.rightContext),
          ModalityPath.length_composePath atom.generatorCod atom.rightContext, Nat.add_assoc]
      refine ⟨?_, ?_⟩
      · intro domTwo codZero
        have windowInRange : atom.leftContext.length + 1 < state.openWires.length := by
          rw [tracksEntry]
          show atom.leftContext.length + 1
            < atom.leftContext.length + atom.generatorDom.length + atom.rightContext.length
          rw [domTwo]
          exact Nat.lt_of_lt_of_le (Nat.lt_succ_self (atom.leftContext.length + 1))
            (Nat.le_add_right (atom.leftContext.length + 2) atom.rightContext.length)
        have windowCap := stringCapWindow_isCapWord atom (pathLabels boundaryWord)
          (congrArg pathLabels headFires) domTwo codZero
        have notCupWord := stringCapWord_not_cupWord (wireLabelListGetAt (pathLabels boundaryWord)
          atom.leftContext.length) (wireLabelListGetAt (pathLabels boundaryWord)
          (atom.leftContext.length + 1)) windowCap
        exact stringDisciplinedCap_windowDistinct state (pathLabels boundaryWord) atom.leftContext.length
          windowInRange notCupWord discipline
      · exact stringCapsDistinctAlongFold_ofWordChain rest (stepAtom state atom)
          (composePath atom.leftContext (composePath atom.generatorCod atom.rightContext)) seedBoundary
          tailArity tailChained newTracks jointNew disciplineNew

/-! ## ★★ The headline — the UNCONDITIONAL no-loops theorem -/

/-- ★★ **THE NO-LOOPS THEOREM (unconditional).**  For EVERY cup/cap-generated string cell, `(matchingOf cell).loops
= 0`.  The combined fold from the fresh seed produces `CapsDistinctAlongFold` (`stringCapsDistinctAlongFold_ofWordChain`,
seeded by `stringJointInvariant_initial` + `stringInitialDiscipline` + the boundary-word chain seed), and FC-0's
`stringMatchingOf_loops_zero_ofCapsDistinct` converts it to loop-freedom.  Both per-step residuals FC-1 owed are
DISCHARGED: `capPin` by the reachable-`capPin` word chain (WALL 2), `preserves` by the cup + cap orientation
preservation (cup shipped, cap WALL 1).  This closes ingredient N2 (loop-freedom); FC completeness / #2020 stay open. -/
theorem stringMatchingOf_loops_zero {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    (cell : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath)
    (cellCupCap : CellHasCupCapGenerators cell) :
    (matchingOf cell).loops = 0 :=
  stringMatchingOf_loops_zero_ofCapsDistinct cell
    (stringCapsDistinctAlongFold_ofWordChain cell.spine (stringInitialWireState sourcePath.length)
      sourcePath sourcePath.length
      (RawTwoCellExpr.spineHasCupCapAtoms_spine cell cellCupCap)
      (RawTwoCellExpr.spineBoundaryWordChained_spine cell)
      (stringInitialWireState_openWires_length sourcePath.length)
      (stringJointInvariant_initial sourcePath.length)
      (stringInitialDiscipline sourcePath.length (pathLabels sourcePath)
        (stringPathLabels_length sourcePath)))

/-! ## Non-vacuity -/

/-- ★ **The no-loops theorem on the cross-level cell** — `stringCrossLevelCell : G·F ⇒ G·H` (a real cap then a real
cup, in neither single adjunction) is loop-free by the UNCONDITIONAL theorem (not a bare `decide`). -/
theorem stringMatchingOf_loops_zero_stringCrossLevelCell :
    (matchingOf stringCrossLevelCell).loops = 0 :=
  stringMatchingOf_loops_zero stringCrossLevelCell ⟨Or.inr ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩

/-! ## Honesty marker -/

/-- **★★ ESTABLISHED — the UNCONDITIONAL no-loops theorem is CLOSED (STRING-JOINT r2 complete).**
`stringMatchingOf_loops_zero` proves `(matchingOf cell).loops = 0` for EVERY cup/cap string cell, HYPOTHESIS-FREE.  Both
per-step residuals FC-1 owed are DISCHARGED: WALL 2 (`StringCapPinWordChain`) discharges `capPin` (the reachable
cap-word fold), WALL 1 (`StringOrientationCapPreserves`) discharges the cap case of `preserves` (the merge-dual
cap-orient), and the shipped cup case + joint invariant + `advanceLabels`-tracking glue them.  The combined fold
`stringCapsDistinctAlongFold_ofWordChain` produces `CapsDistinctAlongFold` unconditionally; FC-0's reduction closes it.
This SUPERSEDES the FC-1 conditional `stringMatchingOf_loops_zero_ofDisciplinePreserved` (whose universal-over-disciplined
`capPin` is FALSE).  Ingredient N2 (loop-freedom / acyclicity) is CLOSED for the string carrier; FC completeness and the
#2020 multi-adjunction word-problem DECISION are NOT delivered (they ride the matching/staircase route, still open).
Zero-axiom.  `= true`. -/
def fxString_hasNoLoopsAssemblyComplete : Bool := true

end FX1Poly.Polygraph
