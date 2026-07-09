import FX1Poly.Polygraph.TwoCategory.WalkingString.StringFussCatalanSoundness

/-! # WalkingString — the strand-ORIENTATION discipline and the no-loops reduction (FC-1, piece A)

FC-0 (`StringFussCatalan`) reduced the general no-loops theorem `∀ cell, (matchingOf cell).loops = 0` to ONE named
union-find obligation over the bare `WireState` fold — `CapsDistinctAlongFold` (every cap fires on a
distinct-component window) — and left the UNCONDITIONAL theorem `fxString_hasNoLoopsTheorem := false`, naming the
remaining site as "the colour-refined open-ends discipline the FC-1 phase will build".  This file BUILDS that
discipline, ships everything about it that closes UNCONDITIONALLY, and ASSEMBLES the no-loops theorem modulo two
crisp per-step residuals — localizing FC-0's monolithic residual to the exact string port of the walking
adjunction's `ArcOpenEndsDiscipline` / `ArcDisciplineFold` / `ArcBoundaryTracking` apparatus.

## The strand-orientation invariant

`StringOrientationDiscipline (state, openLabels)` threads a label list in LOCKSTEP with the open wires and asserts:
any two SAME-component open positions `lowPos < highPos` read an ORDERED CUP WORD (`isCupWordOrdered`, one of
`{(F,G), (G,H)}`).  This is the LABEL refinement the single-parity walking-adjunction discipline lacks: at the
adjoint triple, caps fire at BOTH region parities (`counitLower` at a `tip` window `[G,F]`, `counitUpper` at a
`base` window `[H,G]`), so the adjunction's mode-only pin cannot refute `counitUpper` — the `F`-vs-`H` letter must
enter.  Both cap words fail `isCupWordOrdered` (`stringBothCapWords_notCupWord`), so ONE orient predicate refutes
BOTH cap parities — the exact capability the adjunction pin could not perform.

## What closes UNCONDITIONALLY (this file)

  * `stringDisciplinedCap_windowDistinct` — ★ the CHIRALITY REFUTATION: at a disciplined state, a cap window that
    reads a NON-cup word (i.e. a cap word) is NOT same-component.  The contrapositive of `orient`; the missing link
    FC-0 owed between the invariant and distinctness.
  * `stringInitialDiscipline` — the fresh seed satisfies the discipline (no links ⇒ no distinct same-component pair;
    the vacuous base).
  * `stringStepCap_loopsPreserved_ofDisciplined` — the discipline directly controls the loop count at a cap step.

## The no-loops theorem, ASSEMBLED modulo two named per-step residuals

`stringMatchingOf_loops_zero_ofDisciplinePreserved` proves `(matchingOf cell).loops = 0` for EVERY cell GIVEN:

  * `preserves` — the discipline is a FOLD INVARIANT (each `stepAtom` carries `(state, labels)` to
    `(stepAtom state atom, advanceLabels labels atom)` preserving the discipline).  This is the string port of the
    adjunction's `ArcDisciplineFold` — a cup splices a fresh 2-end component (index-shift + freshness), a cap merges
    two distinct arcs whose survivors nest by planarity;
  * `capPin` — at a cap atom the window labels are the cap's dom word (a cap word, in range).  This is the string
    port of `ArcBoundaryTracking`: the label fold tracks the intermediate 1-cell, so a cap's window reads its
    `generatorDom`.

Both residuals are TRUE (they hold for the shipped single-parity walking adjunction, colour-blind, over the enriched
`ArcWireState`) but their zero-axiom re-derivation over the label-refined bare `WireState` is a multi-round arc — so
`fxString_hasNoLoopsTheorem` stays `false`, honestly, with the residual now localized to exactly these two per-step
obligations (down from FC-0's whole `CapsDistinctAlongFold`).

Raw Lean 4 + Init; the refutation is the `orient` contrapositive, the seed is a range/`decide` vacuity, the
assembly is structural list recursion.  `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free;
per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private range plumbing (per-file copies, following the codebase pattern) -/

private theorem stringRangeLoopLength : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      have inner := stringRangeLoopLength count (count :: accumulated)
      show (List.range.loop count (count :: accumulated)).length = count + 1 + accumulated.length
      rw [inner]
      show count + (accumulated.length + 1) = count + 1 + accumulated.length
      rw [← Nat.add_assoc count accumulated.length 1, Nat.add_right_comm count accumulated.length 1]

private theorem stringRangeLength (count : Nat) : (List.range count).length = count := by
  show (List.range.loop count []).length = count
  rw [stringRangeLoopLength count []]; exact Nat.add_zero count

private theorem stringRangeLoopGetPast : (count : Nat) → (accumulated : List Nat) → (offset : Nat) →
    natListGetAt (List.range.loop count accumulated) (offset + count) = natListGetAt accumulated offset
  | 0, _, _ => rfl
  | count + 1, accumulated, offset => by
      have inner := stringRangeLoopGetPast count (count :: accumulated) (offset + 1)
      rw [Nat.add_assoc offset 1 count, Nat.add_comm 1 count] at inner
      exact inner

private theorem stringRangeLoopGetBelow : (count : Nat) → (accumulated : List Nat) →
    (index : Nat) → index < count →
    natListGetAt (List.range.loop count accumulated) index = index
  | 0, _, _, indexBelow => absurd indexBelow (Nat.not_succ_le_zero _)
  | count + 1, accumulated, index, indexBelow => by
      cases Nat.lt_or_ge index count with
      | inl below => exact stringRangeLoopGetBelow count (count :: accumulated) index below
      | inr atLeast =>
          have indexEq : index = count :=
            Nat.le_antisymm (Nat.le_of_succ_le_succ indexBelow) atLeast
          have pastRead := stringRangeLoopGetPast count (count :: accumulated) 0
          rw [Nat.zero_add count] at pastRead
          rw [indexEq]; exact pastRead

private theorem stringRangeGetBelow (count index : Nat) (indexBelow : index < count) :
    natListGetAt (List.range count) index = index :=
  stringRangeLoopGetBelow count [] index indexBelow

/-- The label sequence of a 1-cell has the same length as the 1-cell (one label per modality). -/
theorem stringPathLabels_length {sourceMode targetMode : AdjointTripleMode} :
    (path : ModalityPath adjointTripleGraph sourceMode targetMode) →
    (pathLabels path).length = path.length
  | ModalityPath.nil _ => rfl
  | ModalityPath.cons modality rest => by
      show (wireLabelOfModality modality :: pathLabels rest).length = rest.length + 1
      rw [List.length_cons, stringPathLabels_length rest]

/-! ## The strand-orientation discipline -/

/-- ★ **The strand-ORIENTATION discipline.**  `openLabels` runs in LOCKSTEP with `state.openWires` (`sameLengths`),
and (`orient`) any two SAME-component open positions `lowPos < highPos` read an ORDERED CUP WORD
(`isCupWordOrdered`, one of `{(F,G), (G,H)}`).  This is the string port of the walking adjunction's
`ArcOpenEndsDiscipline`, refined by the boundary LABEL: where the adjunction pins a same-component pair's window
PARITY to `base`, the adjoint triple must additionally distinguish `F` from `H` (both `base`-parity), since caps
fire at both parities.  The `orient` predicate carries exactly that distinction. -/
structure StringOrientationDiscipline (state : WireState) (openLabels : List WireLabel) : Prop where
  /-- The label list tracks the open wires one-for-one. -/
  sameLengths : openLabels.length = state.openWires.length
  /-- Any same-component open pair reads an ordered cup word. -/
  orient : ∀ lowPos highPos : Nat, lowPos < highPos → highPos < state.openWires.length →
    isSameComponent state.links (natListGetAt state.openWires lowPos)
        (natListGetAt state.openWires highPos) = true →
    isCupWordOrdered (wireLabelListGetAt openLabels lowPos)
      (wireLabelListGetAt openLabels highPos) = true

/-! ## ★ The chirality refutation — a disciplined cap window is distinct -/

/-- ★★ **CHIRALITY REFUTATION — at a disciplined state, a cap-word window is NOT same-component.**  If the window
`(pos, pos+1)` reads a NON-cup word (`isCupWordOrdered = false` — every cap word does, by
`stringBothCapWords_notCupWord`), then its two wires cannot be same-component: were they, `orient` would force the
window to read a CUP word, contradiction.  This is the contrapositive of `orient` and the exact missing link between
the invariant and the distinctness `CapsDistinctAlongFold` needs — and it handles BOTH cap parities uniformly (the
capability the single-parity adjunction pin lacks). -/
theorem stringDisciplinedCap_windowDistinct
    (state : WireState) (openLabels : List WireLabel) (pos : Nat)
    (windowInRange : pos + 1 < state.openWires.length)
    (notCupWord : isCupWordOrdered (wireLabelListGetAt openLabels pos)
        (wireLabelListGetAt openLabels (pos + 1)) = false)
    (discipline : StringOrientationDiscipline state openLabels) :
    isSameComponent state.links (natListGetAt state.openWires pos)
        (natListGetAt state.openWires (pos + 1)) = false := by
  cases sameEq : isSameComponent state.links (natListGetAt state.openWires pos)
      (natListGetAt state.openWires (pos + 1)) with
  | false => rfl
  | true =>
      have cupWord := discipline.orient pos (pos + 1) (Nat.lt_succ_self pos) windowInRange sameEq
      rw [cupWord] at notCupWord
      exact Bool.noConfusion notCupWord

/-- ★★ **Both cap words fail `isCupWordOrdered`.**  The lower cap word `(G,F)` (tip parity) and the upper cap word
`(H,G)` (base parity) both read `false` — so the SAME `orient` predicate refutes BOTH cap parities via
`stringDisciplinedCap_windowDistinct`.  This is precisely the string content beyond the single-parity walking
adjunction: `counitUpper`'s `(H,G)` window has the SAME base parity as the lower cup `(F,G)`, and only the `F`-vs-`H`
letter — read by `isCupWordOrdered`, not by parity — separates them. -/
theorem stringBothCapWords_notCupWord :
    isCupWordOrdered WireLabel.gWire WireLabel.fWire = false
      ∧ isCupWordOrdered WireLabel.hWire WireLabel.gWire = false := ⟨rfl, rfl⟩

/-! ## The seed satisfies the discipline (the vacuous base) -/

/-- ★ **The fresh seed satisfies the discipline.**  At `stringInitialWireState bottomCount` the union-find is empty
(`links = []`), so `isSameComponent` on two DISTINCT boundary indices is `false` — no same-component distinct pair
exists, and `orient` holds vacuously.  `sameLengths` holds when the initial labels have the right length (they are
`pathLabels sourcePath`, length `sourcePath.length = bottomCount`).  This is the string port of
`arcOpenEndsDiscipline_initial`. -/
theorem stringInitialDiscipline (bottomCount : Nat) (labels : List WireLabel)
    (labelsLen : labels.length = bottomCount) :
    StringOrientationDiscipline (stringInitialWireState bottomCount) labels := by
  refine ⟨?_, ?_⟩
  · show labels.length = (List.range bottomCount).length
    rw [labelsLen, stringRangeLength]
  · intro lowPos highPos lowLtHigh highLt sameTrue
    have highLtCount : highPos < bottomCount := by
      have lenEq : (stringInitialWireState bottomCount).openWires.length = bottomCount := by
        show (List.range bottomCount).length = bottomCount
        exact stringRangeLength bottomCount
      rw [lenEq] at highLt; exact highLt
    have lowLtCount : lowPos < bottomCount := Nat.lt_trans lowLtHigh highLtCount
    have lowGet : natListGetAt (stringInitialWireState bottomCount).openWires lowPos = lowPos := by
      show natListGetAt (List.range bottomCount) lowPos = lowPos
      exact stringRangeGetBelow bottomCount lowPos lowLtCount
    have highGet : natListGetAt (stringInitialWireState bottomCount).openWires highPos = highPos := by
      show natListGetAt (List.range bottomCount) highPos = highPos
      exact stringRangeGetBelow bottomCount highPos highLtCount
    rw [lowGet, highGet] at sameTrue
    -- `(stringInitialWireState _).links` is `[]`, and `isSameComponent [] a b` is defeq `(a == b)`
    have windowBeq : (lowPos == highPos) = true := sameTrue
    exact absurd (of_decide_eq_true windowBeq) (Nat.ne_of_lt lowLtHigh)

/-- ★ **The discipline controls the loop count at a cap step.**  A cap firing at a disciplined state on a cap-word
window keeps the loop count — the refutation (`stringDisciplinedCap_windowDistinct`) feeds FC-0's
`stringStepCap_loopsPreserved_ofDistinctWindow`.  So the orientation discipline directly forbids loop closure. -/
theorem stringStepCap_loopsPreserved_ofDisciplined
    (state : WireState) (openLabels : List WireLabel) (pos : Nat)
    (windowInRange : pos + 1 < state.openWires.length)
    (notCupWord : isCupWordOrdered (wireLabelListGetAt openLabels pos)
        (wireLabelListGetAt openLabels (pos + 1)) = false)
    (discipline : StringOrientationDiscipline state openLabels) :
    (stepCap state pos).loops = state.loops :=
  stringStepCap_loopsPreserved_ofDistinctWindow state pos
    (stringDisciplinedCap_windowDistinct state openLabels pos windowInRange notCupWord discipline)

/-! ## ★ The no-loops theorem, assembled modulo two named per-step residuals -/

/-- ★★ **`CapsDistinctAlongFold`, assembled from the discipline invariant.**  GIVEN a label companion fold
`advanceLabels`, the discipline's FOLD INVARIANCE (`preserves`), and the cap boundary Pin (`capPin`: at a cap atom
the window is in range and reads a NON-cup word), the fold's distinct-caps obligation holds outright: each cap's
head obligation comes from the refutation (`stringDisciplinedCap_windowDistinct`) fed by `capPin`, and the tail
recurses on the preserved discipline.  Structural list recursion.  This is the string port of the adjunction's
`arcOpenEndsDiscipline_processArcSpine`, threading the discipline through the whole fold. -/
theorem stringCapsDistinctAlongFold_ofDisciplinePreserved
    {sourceMode targetMode : AdjointTripleMode}
    (advanceLabels : List WireLabel →
      SpineAtom adjointTripleModeSignature sourceMode targetMode → List WireLabel)
    (preserves : ∀ (state : WireState) (labels : List WireLabel)
        (atom : SpineAtom adjointTripleModeSignature sourceMode targetMode),
        StringOrientationDiscipline state labels →
        StringOrientationDiscipline (stepAtom state atom) (advanceLabels labels atom))
    (capPin : ∀ (state : WireState) (labels : List WireLabel)
        (atom : SpineAtom adjointTripleModeSignature sourceMode targetMode),
        StringOrientationDiscipline state labels →
        atom.generatorDom.length = 2 → atom.generatorCod.length = 0 →
        atom.leftContext.length + 1 < state.openWires.length
          ∧ isCupWordOrdered (wireLabelListGetAt labels atom.leftContext.length)
              (wireLabelListGetAt labels (atom.leftContext.length + 1)) = false) :
    (atoms : List (SpineAtom adjointTripleModeSignature sourceMode targetMode)) →
    (state : WireState) → (labels : List WireLabel) →
    StringOrientationDiscipline state labels →
    CapsDistinctAlongFold state atoms
  | [], _, _, _ => trivial
  | atom :: rest, state, labels, discipline => by
      refine ⟨?_, ?_⟩
      · intro domTwo codZero
        obtain ⟨windowInRange, notCupWord⟩ := capPin state labels atom discipline domTwo codZero
        exact stringDisciplinedCap_windowDistinct state labels atom.leftContext.length
          windowInRange notCupWord discipline
      · exact stringCapsDistinctAlongFold_ofDisciplinePreserved advanceLabels preserves capPin
          rest (stepAtom state atom) (advanceLabels labels atom)
          (preserves state labels atom discipline)

/-- ★★ **The general no-loops theorem, assembled modulo the two per-step residuals.**  For EVERY string cell,
`(matchingOf cell).loops = 0` GIVEN the discipline's fold invariance (`preserves`) and the cap boundary Pin
(`capPin`): the fold from the fresh seed (which satisfies the discipline via `stringInitialDiscipline`, its labels
`pathLabels sourcePath` of length `sourcePath.length`) fires no loop-closing cap
(`stringCapsDistinctAlongFold_ofDisciplinePreserved`), and FC-0's `stringMatchingOf_loops_zero_ofCapsDistinct`
converts that to loop-freedom.  This LOCALIZES FC-0's monolithic `CapsDistinctAlongFold` residual to exactly the two
per-step obligations — the string port of `ArcDisciplineFold` + `ArcBoundaryTracking`. -/
theorem stringMatchingOf_loops_zero_ofDisciplinePreserved
    {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    (advanceLabels : List WireLabel →
      SpineAtom adjointTripleModeSignature sourceMode targetMode → List WireLabel)
    (preserves : ∀ (state : WireState) (labels : List WireLabel)
        (atom : SpineAtom adjointTripleModeSignature sourceMode targetMode),
        StringOrientationDiscipline state labels →
        StringOrientationDiscipline (stepAtom state atom) (advanceLabels labels atom))
    (capPin : ∀ (state : WireState) (labels : List WireLabel)
        (atom : SpineAtom adjointTripleModeSignature sourceMode targetMode),
        StringOrientationDiscipline state labels →
        atom.generatorDom.length = 2 → atom.generatorCod.length = 0 →
        atom.leftContext.length + 1 < state.openWires.length
          ∧ isCupWordOrdered (wireLabelListGetAt labels atom.leftContext.length)
              (wireLabelListGetAt labels (atom.leftContext.length + 1)) = false)
    (cell : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath) :
    (matchingOf cell).loops = 0 :=
  stringMatchingOf_loops_zero_ofCapsDistinct cell
    (stringCapsDistinctAlongFold_ofDisciplinePreserved advanceLabels preserves capPin cell.spine
      (stringInitialWireState sourcePath.length) (pathLabels sourcePath)
      (stringInitialDiscipline sourcePath.length (pathLabels sourcePath)
        (stringPathLabels_length sourcePath)))

/-! ## Honesty markers -/

/-- **★ ESTABLISHED — the strand-ORIENTATION discipline + the chirality refutation + the seed.**  The label-refined
invariant `StringOrientationDiscipline` is shipped; the CHIRALITY REFUTATION
(`stringDisciplinedCap_windowDistinct`) proves a disciplined cap-word window is NOT same-component — the missing
link FC-0 owed between the invariant and distinctness — and it refutes BOTH cap parities uniformly
(`stringBothCapWords_notCupWord`: `(G,F)` and `(H,G)` both fail `isCupWordOrdered`), the exact capability the
single-parity walking-adjunction pin cannot perform (only the `F`-vs-`H` letter separates the base-parity cap
`(H,G)` from the base-parity cup `(F,G)`).  The fresh seed satisfies the discipline (`stringInitialDiscipline`, the
vacuous base), and the discipline controls the loop count at a cap step
(`stringStepCap_loopsPreserved_ofDisciplined`).  All UNCONDITIONAL, zero-axiom.  `= true`. -/
def fxString_hasOrientationDiscipline : Bool := true

/-- **★ ESTABLISHED — the no-loops theorem ASSEMBLED, FC-0's residual LOCALIZED to two per-step obligations.**
`stringMatchingOf_loops_zero_ofDisciplinePreserved` proves `(matchingOf cell).loops = 0` for EVERY string cell GIVEN
exactly two per-step residuals: (1) `preserves` — the discipline is a fold invariant, and (2) `capPin` — a cap
window reads its `generatorDom` cap word.  The seed base is DISCHARGED (`stringInitialDiscipline`), the per-cap
distinctness is DISCHARGED from the discipline (`stringDisciplinedCap_windowDistinct`), the whole-fold threading is
DISCHARGED (`stringCapsDistinctAlongFold_ofDisciplinePreserved`), and FC-0's
`stringMatchingOf_loops_zero_ofCapsDistinct` closes the conversion.  So FC-0's monolithic `CapsDistinctAlongFold`
residual is now LOCALIZED to the two named per-step obligations — the same "assembled modulo residuals" shape as the
shipped soundness capstones.  `= true`. -/
def fxString_hasNoLoopsAssembledModuloTwoResiduals : Bool := true

/-- **OPEN — the UNCONDITIONAL no-loops flip stays a multi-round port; the two per-step residuals resist in-session.**
`stringMatchingOf_loops_zero_ofDisciplinePreserved` owes exactly two per-step obligations, both TRUE (they hold for
the shipped single-parity walking adjunction, colour-blind, over the enriched `ArcWireState`) but each a genuine
multi-round zero-axiom re-derivation over the label-refined BARE `WireState`:

  * `preserves` (the discipline is a fold invariant) — the string port of `ArcDisciplineFold`.  A cup preserves it
    by splicing a FRESH 2-end component whose ordered labels are the cup's cod word (needs the freshness invariant +
    the `natListInsertAt`/`natListGetAt` index-shift lemmas, none of which exist over the bare `WireState`); a cap
    preserves it by merging two DISTINCT arcs whose two survivors nest — and the surviving pair reads a cup word
    ONLY because of PLANARITY (the `ArcNonCrossingFold` non-crossing invariant), the genuinely new mathematics in
    the `(G,H)`/`(H,G)` subcase.
  * `capPin` (a cap window reads its `generatorDom`) — the string port of `ArcBoundaryTracking`, label-valued: the
    companion `advanceLabels` fold must be shown to track the intermediate 1-cell, so a cap's window equals its
    `generatorDom` cap word.

So `fxString_hasNoLoopsTheorem` (in `StringFussCatalan`) stays `false`, HONESTLY: the invariant, the refutation, the
seed, and the assembly are shipped; the two per-step residuals (index-shift + planarity + boundary-tracking) are the
exact remaining site, each mapped to its shipped adjunction analog.  This is a genuine finding — the flip is a
multi-round arc, not a one-shot induction.  `= false`. -/
def fxString_hasOrientationDisciplineFoldInvariance : Bool := false

end FX1Poly.Polygraph
