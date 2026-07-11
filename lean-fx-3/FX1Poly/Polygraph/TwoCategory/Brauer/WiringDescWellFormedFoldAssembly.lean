import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescFoldTargetHonest
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescBoundedBoundaryFold
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SaturatedMatchingGodement

/-! # BRAUER r20 — the `WellFormedBrauerFold` word-assembly + the per-phase window-fit discharge (the
corrected-target six-phase reduction, brick by brick)

The r19 wall node `fxBrauer_hasFoldTargetHonestAssembly = false` (`Brauer/WiringDescFoldTargetHonest.lean`) named
THREE unbuilt residuals for the general `foldRealizesTargetDiagramCorrected`: the through-strand cross-phase
T-CONNECT, T-ENUM (the E3 fold-alignment), and a **`WellFormedBrauerFold` proof for the corrected word**.  The last
of these is the connectivity-free, lowest-risk brick — a per-phase width-accounting reduction.  This file breaches
it at the reusable-lemma level (each phase word's well-formedness discharged from a single width obligation), plus
the word-level append-split that assembles the six phases, plus the eval-first through-strand connectivity probe,
and exercises the honest corrected target on fresh width-8 wild diagrams.

## What this file ships (each zero-axiom, structural, no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix`)

  * **`wellFormedBrauerFold_append`** / **`wellFormedBrauerFold_appendSplit`** — the WORD-level append law for
    `WellFormedBrauerFold` (the analog of `processBrauer_append`): a concatenation is well-formed iff each half is
    well-formed at its phase-boundary state.  This is the skeleton the six-phase assembly rides — the same five `++`
    seams `standardFormFold_appendSplit` splits, now at the well-formedness level.
  * **`wellFormedBrauerFold_crossingWord`** — a crossing staircase is well-formed from the single per-position bound
    `∀ pos ∈ positions, pos + 2 ≤ width` (the same hypothesis shape as the shipped `crossingWordFold_openWires_length`;
    the crossing is a `2 ⇒ 2` generator, so width is preserved through the fold).
  * **`wellFormedBrauerFold_cupWord`** — a cup word (a `0 ⇒ 2` generator, width GROWS) is well-formed from
    `∀ pos ∈ positions, pos ≤ width` (the window is `pos + 0 ≤ length`, and length only grows).
  * **`wellFormedBrauerFold_capZeros`** — the canonical cap block `capWord (natReplicate count 0)` (a `2 ⇒ 0`
    generator, width SHRINKS by 2 each) is well-formed from `count + count ≤ width` — the ONE genuinely
    counting-sensitive phase (needs `2·#capFeet ≤ bottomCount`).
  * **`wellFormedBrauerFold_circleWord`** — the circle block is well-formed UNCONDITIONALLY: each `cupAt 0` makes room
    for the following `capAt 0`, restoring the width.
  * ★ **the six-phase reduction** `wellFormedBrauerFold_standardFormWordExt5_ofPhases`: the corrected word is
    well-formed once each of the six phase words is well-formed at its phase-boundary state — the honest reduction of
    the general `WellFormedBrauerFold`-for-corrected-word obligation to the six per-phase width obligations.
  * ★ **the shipped coverage exposed** — `wellFormedBrauerFold_correctedWord_adversarialB` / `_nestedCups`: the FULL
    corrected word of the two r19 witnesses is well-formed, assembled through the phase-discharge lemmas.
  * ★ **the through-strand cross-phase connectivity, eval-first** (`throughStrandConnects_probe`): a through port's
    bottom foot and its final top boundary index share a union-find component in the phase-6 fold state — the concrete
    truth of the "through strand is a never-severed chain of joins" the general bridge would prove.
  * ★ **the honest target exercised on fresh width-8 wild diagrams** (`foldRealizesTargetDiagramCorrected_wild*`) —
    genuine boundary involutions (through / cup / cap / loop mixes) the corrected extractor routes back exactly.

## The honest residual (the general assembly stays OPEN)

The six-phase reduction takes the six per-phase well-formedness facts as hypotheses; feeding them from the corrected
extractor's fields needs, for the three crossing phases, the staircase position-bound
`∀ pos ∈ permutationToCrossingWord n perm, pos + 2 ≤ n`, and for the cap/cup phases the WIDTH-AT-BOUNDARY counting
identities (`2·#capFeet + #through = bottomCount`, `#through + 2·#cupArcs = topCount`) that fix each phase-boundary
width.  Those are the standing width-accounting residual; `fxBrauer_hasWellFormedFoldGeneralAssembly` stays `false`,
and the r19 wall `fxBrauer_hasFoldTargetHonestAssembly` and the masters stay `false` — #2013 does NOT close.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` in the audit twin; independent `#print axioms` clean. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## B1 — the WORD-level append law for `WellFormedBrauerFold` -/

/-- ★ **`WellFormedBrauerFold` COMBINES over word concatenation.**  If `word1` is well-formed at `state` and `word2`
is well-formed at the phase-boundary state `processBrauer state word1`, then the concatenation `word1 ++ word2` is
well-formed at `state`.  Structural on `word1` — the well-formedness analog of `processBrauer_append`, the skeleton
that assembles the six-phase corrected word from its per-phase well-formedness. -/
theorem wellFormedBrauerFold_append :
    (word1 : List BrauerAtom) → (state : WireState) → (word2 : List BrauerAtom) →
    WellFormedBrauerFold state word1 →
    WellFormedBrauerFold (processBrauer state word1) word2 →
    WellFormedBrauerFold state (word1 ++ word2)
  | [], _state, _word2, _wf1, wf2 => wf2
  | atom :: rest, state, word2, wf1, wf2 => by
      obtain ⟨gen, windowFit, wfRest⟩ := wf1
      exact ⟨gen, windowFit, wellFormedBrauerFold_append rest (stepBrauerAtom state atom) word2 wfRest wf2⟩

/-- ★ **`WellFormedBrauerFold` SPLITS over word concatenation.**  The converse of `wellFormedBrauerFold_append`: a
well-formed concatenation decomposes into the head half's well-formedness and the tail half's well-formedness at the
phase-boundary state.  Together the two directions make `WellFormedBrauerFold` a genuine append law. -/
theorem wellFormedBrauerFold_appendSplit :
    (word1 : List BrauerAtom) → (state : WireState) → (word2 : List BrauerAtom) →
    WellFormedBrauerFold state (word1 ++ word2) →
    WellFormedBrauerFold state word1 ∧ WellFormedBrauerFold (processBrauer state word1) word2
  | [], _state, _word2, wf => ⟨trivial, wf⟩
  | atom :: rest, state, word2, wf => by
      obtain ⟨gen, windowFit, wfRest⟩ := wf
      obtain ⟨wf1Rest, wf2⟩ := wellFormedBrauerFold_appendSplit rest (stepBrauerAtom state atom) word2 wfRest
      exact ⟨⟨gen, windowFit, wf1Rest⟩, wf2⟩

/-! ## B1 — the through-strand cross-phase connectivity, probed by evaluation FIRST -/

/-- ★ **The through strand connects across all six phases, evaluated by the kernel (the r18 discipline).**  For
`adversarialBDiagram` the through arc `1 ↔ top1` (boundary index `4`) has its bottom foot and its final top boundary
index SAME-COMPONENT in the phase-6 fold state of the CORRECTED six-phase word — the crossing in `bottomPerm`
re-represents the bottom foot with a fresh id, yet the union-find chain is never severed.  The two degenerate
through strands of the mixed word `[capAt 0, cupAt 2]` (`2 ↔ top0`, `3 ↔ top1`, no crossing touching them) connect
too.  This is the concrete truth of the "through strand is a never-severed chain of joins" the general cross-phase
bridge would prove; here it is read straight off the kernel. -/
theorem throughStrandConnects_probe :
    matchingSameComponent 3
        (processBrauer (brauerSeed 3)
          (standardFormWordExt5 (reconstructStandardFormExt5Corrected adversarialBDiagram))) 1 4 = true
      ∧ matchingSameComponent 4
        (processBrauer (brauerSeed 4) (capWord (natReplicate 1 0) ++ cupWord (natReplicate 1 2))) 2 4 = true
      ∧ matchingSameComponent 4
        (processBrauer (brauerSeed 4) (capWord (natReplicate 1 0) ++ cupWord (natReplicate 1 2))) 3 5 = true :=
  ⟨by decide, by decide, by decide⟩

/-! ## B2 — the per-phase width helpers (propext-free `Nat` cancellation) -/

/-- Right-cancellation of `Nat` addition — structural on the cancelled summand, `propext`-free (`Nat.add_right_cancel`
itself leaks `propext`, so it is re-derived here via `Nat.add_succ` + `Nat.succ.inj`). -/
private theorem natAddRightCancelClean : (right leftFirst leftSecond : Nat) →
    leftFirst + right = leftSecond + right → leftFirst = leftSecond
  | 0, leftFirst, leftSecond, equal => by rw [Nat.add_zero, Nat.add_zero] at equal; exact equal
  | right + 1, leftFirst, leftSecond, equal => by
      rw [Nat.add_succ leftFirst right, Nat.add_succ leftSecond right] at equal
      exact natAddRightCancelClean right leftFirst leftSecond (Nat.succ.inj equal)

/-- Firing a cup (`0 ⇒ 2`) at an in-range position GROWS the open-wire count by exactly two. -/
private theorem stepCupAt_length (state : WireState) (pos : Nat)
    (hle : pos ≤ state.openWires.length) :
    (stepBrauerAtom state (cupAt pos)).openWires.length = state.openWires.length + 2 := by
  obtain ⟨rightLen, hRight⟩ := Nat.le.dest hle
  show (stepWiring state pos cupWiring).openWires.length = state.openWires.length + 2
  have fits : state.openWires.length = pos + cupWiring.inputCount + rightLen := by
    show state.openWires.length = pos + 0 + rightLen
    rw [Nat.add_zero]; exact hRight.symm
  rw [stepWiring_openWires_length_fits state pos rightLen cupWiring fits]
  show pos + 2 + rightLen = state.openWires.length + 2
  rw [Nat.add_right_comm pos 2 rightLen, hRight]

/-- Firing a cap (`2 ⇒ 0`) at an in-range position SHRINKS the open-wire count by exactly two. -/
private theorem stepCapAt_length (state : WireState) (pos : Nat)
    (hfits : pos + 2 ≤ state.openWires.length) :
    (stepBrauerAtom state (capAt pos)).openWires.length + 2 = state.openWires.length := by
  obtain ⟨rightLen, fitsRaw⟩ := Nat.le.dest hfits
  show (stepWiring state pos capWiring).openWires.length + 2 = state.openWires.length
  have fits : state.openWires.length = pos + capWiring.inputCount + rightLen := by
    show state.openWires.length = pos + 2 + rightLen
    exact fitsRaw.symm
  rw [stepWiring_openWires_length_fits state pos rightLen capWiring fits]
  show pos + rightLen + 2 = state.openWires.length
  rw [Nat.add_right_comm pos rightLen 2]
  exact fitsRaw

/-! ## B2 — the four per-phase `WellFormedBrauerFold` discharge lemmas -/

/-- ★ **A crossing staircase is well-formed from the per-position bound.**  Folding `crossingWord positions` from a
state of open-wire count `width` is well-formed once every position satisfies `pos + 2 ≤ width` — the crossing is a
`2 ⇒ 2` generator, so the width is preserved and the single bound carries through the fold.  The same hypothesis
shape as the shipped `crossingWordFold_openWires_length`, now at the well-formedness level. -/
theorem wellFormedBrauerFold_crossingWord (width : Nat) :
    (positions : List Nat) → (state : WireState) →
    state.openWires.length = width →
    (∀ pos, pos ∈ positions → pos + 2 ≤ width) →
    WellFormedBrauerFold state (crossingWord positions)
  | [], _state, _lengthEq, _posBound => trivial
  | pos :: rest, state, lengthEq, posBound => by
      have posFits : pos + 2 ≤ state.openWires.length := by
        rw [lengthEq]; exact posBound pos (List.Mem.head rest)
      refine ⟨Or.inr (Or.inr rfl), posFits, ?_⟩
      obtain ⟨rightLen, fitsRaw⟩ := Nat.le.dest posFits
      have stepLen : (stepBrauerAtom state (crossingAt pos)).openWires.length = width := by
        show (stepWiring state pos crossingWiring).openWires.length = width
        rw [stepWiring_openWires_length_fits state pos rightLen crossingWiring fitsRaw.symm]
        show pos + 2 + rightLen = width
        rw [fitsRaw, lengthEq]
      exact wellFormedBrauerFold_crossingWord width rest (stepBrauerAtom state (crossingAt pos)) stepLen
        (fun laterPos laterMem => posBound laterPos (List.Mem.tail pos laterMem))

/-- ★ **A cup word is well-formed from the per-position bound.**  A cup is a `0 ⇒ 2` generator (window `pos + 0 ≤
length`), and firing it GROWS the open-wire count, so the bound `pos ≤ width` (with `width ≤` the current count) is
preserved through the fold — no shrinking to track. -/
theorem wellFormedBrauerFold_cupWord (width : Nat) :
    (positions : List Nat) → (state : WireState) →
    width ≤ state.openWires.length →
    (∀ pos, pos ∈ positions → pos ≤ width) →
    WellFormedBrauerFold state (cupWord positions)
  | [], _state, _widthLe, _posBound => trivial
  | pos :: rest, state, widthLe, posBound => by
      have posLe : pos ≤ state.openWires.length := Nat.le_trans (posBound pos (List.Mem.head rest)) widthLe
      refine ⟨Or.inl rfl, ?_, ?_⟩
      · show pos + 0 ≤ state.openWires.length
        rw [Nat.add_zero]; exact posLe
      · have widthLe' : width ≤ (stepBrauerAtom state (cupAt pos)).openWires.length := by
          rw [stepCupAt_length state pos posLe]
          exact Nat.le_trans widthLe (Nat.le_add_right state.openWires.length 2)
        exact wellFormedBrauerFold_cupWord width rest (stepBrauerAtom state (cupAt pos)) widthLe'
          (fun laterPos laterMem => posBound laterPos (List.Mem.tail pos laterMem))

/-- ★ **The canonical cap block is well-formed from the additive width bound.**  The cap block `capWord (natReplicate
count 0)` fires `count` caps all at position `0` (each a `2 ⇒ 0` generator SHRINKING the width by two), so it is
well-formed once `count + count ≤ width` — the ONE genuinely counting-sensitive phase (the standard-form instance
needs `2·#capFeet ≤ bottomCount`). -/
theorem wellFormedBrauerFold_capZeros :
    (count : Nat) → (state : WireState) →
    count + count ≤ state.openWires.length →
    WellFormedBrauerFold state (capWord (natReplicate count 0))
  | 0, _state, _fits => trivial
  | count + 1, state, fits => by
      have twoLower : 2 ≤ (count + 1) + (count + 1) :=
        Nat.add_le_add (Nat.succ_le_succ (Nat.zero_le count)) (Nat.succ_le_succ (Nat.zero_le count))
      have twoLe : 0 + 2 ≤ state.openWires.length := by
        rw [Nat.zero_add]; exact Nat.le_trans twoLower fits
      refine ⟨Or.inr (Or.inl rfl), twoLe, ?_⟩
      have shrink : (stepBrauerAtom state (capAt 0)).openWires.length + 2 = state.openWires.length :=
        stepCapAt_length state 0 twoLe
      have hEq : (count + 1) + (count + 1) = count + count + 2 := by
        rw [Nat.add_assoc, Nat.add_comm 1 (count + 1), Nat.add_assoc, Nat.add_assoc]
      have newFits : count + count ≤ (stepBrauerAtom state (capAt 0)).openWires.length := by
        have h1 : count + count + 2 ≤ (stepBrauerAtom state (capAt 0)).openWires.length + 2 := by
          rw [shrink, ← hEq]; exact fits
        obtain ⟨leftover, hLeft⟩ := Nat.le.dest h1
        refine Nat.le.intro (k := leftover) ?_
        have aligned : count + count + leftover + 2 = (stepBrauerAtom state (capAt 0)).openWires.length + 2 := by
          rw [Nat.add_right_comm (count + count) leftover 2]; exact hLeft
        exact natAddRightCancelClean 2 (count + count + leftover)
          (stepBrauerAtom state (capAt 0)).openWires.length aligned
      exact wellFormedBrauerFold_capZeros count (stepBrauerAtom state (capAt 0)) newFits

/-- ★ **The circle block is well-formed UNCONDITIONALLY.**  Each `cupAt 0` (window `0 ≤ length`, always true) makes
room for the following `capAt 0` (window `0 + 2 ≤ length + 2`, always true), restoring the width — so `circleWord
loops` is well-formed at any state, no width hypothesis needed. -/
theorem wellFormedBrauerFold_circleWord :
    (loops : Nat) → (state : WireState) → WellFormedBrauerFold state (circleWord loops)
  | 0, _state => trivial
  | loops + 1, state => by
      refine ⟨Or.inl rfl, Nat.zero_le _, ?_⟩
      refine ⟨Or.inr (Or.inl rfl), ?_, ?_⟩
      · show 0 + 2 ≤ (stepBrauerAtom state (cupAt 0)).openWires.length
        rw [stepCupAt_length state 0 (Nat.zero_le _)]
        exact Nat.add_le_add (Nat.zero_le state.openWires.length) (Nat.le_refl 2)
      · exact wellFormedBrauerFold_circleWord loops
          (stepBrauerAtom (stepBrauerAtom state (cupAt 0)) (capAt 0))

/-! ## B2 — the six-phase reduction: assemble the corrected word from the six per-phase obligations -/

/-- ★ **The six-phase `WellFormedBrauerFold` reduction.**  The corrected extractor's realized word
`standardFormWordExt5 form` is well-formed at the seed once each of its six phase words (bottom-crossing, cap,
middle-crossing, cup, top-crossing, circle) is well-formed at its phase-boundary state.  A clean five-fold
`wellFormedBrauerFold_append` at the five `++` seams `standardFormFold_appendSplit` splits — the honest reduction of
the general `WellFormedBrauerFold`-for-corrected-word obligation to the six per-phase width obligations. -/
theorem wellFormedBrauerFold_standardFormWordExt5_ofPhases (form : BrauerStandardFormExt5)
    (hBottom : WellFormedBrauerFold (brauerSeed form.bottomCount) (crossingWord form.bottomPerm))
    (hCap : WellFormedBrauerFold
        (processBrauer (brauerSeed form.bottomCount) (crossingWord form.bottomPerm)) (capWord form.capBlock))
    (hMiddle : WellFormedBrauerFold
        (processBrauer (brauerSeed form.bottomCount)
          (crossingWord form.bottomPerm ++ capWord form.capBlock)) (crossingWord form.middle))
    (hCup : WellFormedBrauerFold
        (processBrauer (brauerSeed form.bottomCount)
          (crossingWord form.bottomPerm ++ capWord form.capBlock ++ crossingWord form.middle))
        (cupWord form.cupBlock))
    (hTop : WellFormedBrauerFold
        (processBrauer (brauerSeed form.bottomCount)
          (crossingWord form.bottomPerm ++ capWord form.capBlock ++ crossingWord form.middle
            ++ cupWord form.cupBlock)) (crossingWord form.topPerm))
    (hCircle : WellFormedBrauerFold
        (processBrauer (brauerSeed form.bottomCount)
          (crossingWord form.bottomPerm ++ capWord form.capBlock ++ crossingWord form.middle
            ++ cupWord form.cupBlock ++ crossingWord form.topPerm)) (circleWord form.loops)) :
    WellFormedBrauerFold (brauerSeed form.bottomCount) (standardFormWordExt5 form) := by
  show WellFormedBrauerFold (brauerSeed form.bottomCount)
    (crossingWord form.bottomPerm ++ capWord form.capBlock ++ crossingWord form.middle
      ++ cupWord form.cupBlock ++ crossingWord form.topPerm ++ circleWord form.loops)
  exact wellFormedBrauerFold_append _ _ _
    (wellFormedBrauerFold_append _ _ _
      (wellFormedBrauerFold_append _ _ _
        (wellFormedBrauerFold_append _ _ _
          (wellFormedBrauerFold_append _ _ _ hBottom hCap) hMiddle) hCup) hTop) hCircle

/-! ## B2 — non-vacuity: the phase lemmas fire, and the FULL corrected word of the r19 witnesses is well-formed -/

/-- ★ **The phase-discharge lemmas fire on concrete blocks.**  A width-4 crossing staircase, a width-4 double-cap
block, a cup block over three wires, and a two-loop circle are each well-formed by the four phase lemmas. -/
theorem wellFormedBrauerFold_phaseLemmas_fire :
    WellFormedBrauerFold (brauerSeed 4) (crossingWord [0, 1, 2])
      ∧ WellFormedBrauerFold (brauerSeed 4) (capWord (natReplicate 2 0))
      ∧ WellFormedBrauerFold (brauerSeed 3) (cupWord [0, 1, 2])
      ∧ WellFormedBrauerFold (brauerSeed 5) (circleWord 2) :=
  ⟨wellFormedBrauerFold_crossingWord 4 [0, 1, 2] (brauerSeed 4) rfl (by decide),
   wellFormedBrauerFold_capZeros 2 (brauerSeed 4) (by decide),
   wellFormedBrauerFold_cupWord 3 [0, 1, 2] (brauerSeed 3) (Nat.le_refl 3) (by decide),
   wellFormedBrauerFold_circleWord 2 (brauerSeed 5)⟩

/-- ★★ **The FULL corrected word of adversarial-B is well-formed (coverage exposed).**  The corrected extractor's
six-phase word for `adversarialBDiagram` — `[crossingAt 1, capAt 0, cupAt 1, crossingAt 0, cupAt 0, capAt 0]` — is
well-formed at the seed: every atom is a Brauer generator firing in its current window.  This is the concrete
`WellFormedBrauerFold`-for-corrected-word the r19 wall named, exhibited on the triple-axis witness. -/
theorem wellFormedBrauerFold_correctedWord_adversarialB :
    WellFormedBrauerFold (brauerSeed adversarialBDiagram.bottomCount)
      (standardFormWordExt5 (reconstructStandardFormExt5Corrected adversarialBDiagram)) := by
  have hword : standardFormWordExt5 (reconstructStandardFormExt5Corrected adversarialBDiagram)
      = [crossingAt 1, capAt 0, cupAt 1, crossingAt 0, cupAt 0, capAt 0] := by decide
  rw [hword]
  exact ⟨Or.inr (Or.inr rfl), by decide, Or.inr (Or.inl rfl), by decide, Or.inl rfl, by decide,
    Or.inr (Or.inr rfl), by decide, Or.inl rfl, by decide, Or.inr (Or.inl rfl), by decide, trivial⟩

/-- ★★ **The FULL corrected word of the nested crossing cups is well-formed (coverage exposed).**  The corrected
extractor's word for `nestedCupsDiagram` — `[cupAt 0, cupAt 0, crossingAt 1, crossingAt 2]` — is well-formed at the
empty seed: the two cups make room for the two crossings.  The very witness that refuted the UNCORRECTED target has
a well-formed corrected word. -/
theorem wellFormedBrauerFold_correctedWord_nestedCups :
    WellFormedBrauerFold (brauerSeed nestedCupsDiagram.bottomCount)
      (standardFormWordExt5 (reconstructStandardFormExt5Corrected nestedCupsDiagram)) := by
  have hword : standardFormWordExt5 (reconstructStandardFormExt5Corrected nestedCupsDiagram)
      = [cupAt 0, cupAt 0, crossingAt 1, crossingAt 2] := by decide
  rw [hword]
  exact ⟨Or.inl rfl, by decide, Or.inl rfl, by decide, Or.inr (Or.inr rfl), by decide,
    Or.inr (Or.inr rfl), by decide, trivial⟩

/-! ## B3 — the honest corrected target exercised on fresh width-8 wild diagrams

The general `foldRealizesTargetDiagramCorrected` proof stays open (§ the WALL marker below); this section EXERCISES
the honest target as proof terms on fresh boundary involutions the r19 file never touched — four width-8 (or
mixed-split) diagrams spanning through strands, top cups, bottom caps, loops, and crossing routing.  Each is a
genuine boundary involution (the premise is satisfiable — the exercise is not vacuous) whose corrected six-phase
word routes back to it exactly. -/

/-- A width-8 all-through wild diagram: four bottom strands passing straight through to the top boundary
(`0↔top0, 1↔top1, 2↔top2, 3↔top3`). -/
def wildThroughDiagram : DiagramType :=
  { bottomCount := 4, topCount := 4, partner := [4, 5, 6, 7, 0, 1, 2, 3], loops := 0 }

/-- A mixed wild diagram: two through strands, two top cups, and two loops over a 2-bottom / 6-top split. -/
def wildCupLoopDiagram : DiagramType :=
  { bottomCount := 2, topCount := 6, partner := [7, 6, 3, 2, 5, 4, 1, 0], loops := 2 }

/-- A wild diagram with two bottom caps and two through strands over a 6-bottom / 2-top split. -/
def wildCapThroughDiagram : DiagramType :=
  { bottomCount := 6, topCount := 2, partner := [1, 0, 3, 2, 7, 6, 5, 4], loops := 0 }

/-- A width-8 all-through wild diagram with crossing routing (`0↔top1, 1↔top0, 2↔top3, 3↔top2`). -/
def wildCrossThroughDiagram : DiagramType :=
  { bottomCount := 4, topCount := 4, partner := [5, 4, 7, 6, 1, 0, 3, 2], loops := 0 }

/-- ★ **The width-8 all-through wild diagram is a boundary involution** — the premise of the corrected target is
genuinely satisfiable (each field `decide`-checked). -/
theorem isBoundaryInvolution_wildThrough :
    IsBoundaryInvolution (wildThroughDiagram.bottomCount + wildThroughDiagram.topCount)
      wildThroughDiagram.partner where
  hasBoundaryLength := rfl
  mapsInRange := by decide
  isSelfInverse := by decide
  isFixedPointFree := by decide

/-- ★ **The mixed through/cup/loop wild diagram is a boundary involution** — a second satisfiable premise witness. -/
theorem isBoundaryInvolution_wildCupLoop :
    IsBoundaryInvolution (wildCupLoopDiagram.bottomCount + wildCupLoopDiagram.topCount)
      wildCupLoopDiagram.partner where
  hasBoundaryLength := rfl
  mapsInRange := by decide
  isSelfInverse := by decide
  isFixedPointFree := by decide

/-- ★★ **The honest corrected target holds on the width-8 all-through wild diagram.**  Four through strands routed
back exactly by the corrected six-phase word. -/
theorem foldRealizesTargetDiagramCorrected_wildThrough :
    foldRealizesTargetDiagramCorrected wildThroughDiagram := fun _ => by decide

/-- ★★ **The honest corrected target holds on the mixed through/cup/loop wild diagram** — two through strands, two
top cups, and two loops all recovered. -/
theorem foldRealizesTargetDiagramCorrected_wildCupLoop :
    foldRealizesTargetDiagramCorrected wildCupLoopDiagram := fun _ => by decide

/-- ★★ **The honest corrected target holds on the cap/through wild diagram** — two bottom caps + two through
strands. -/
theorem foldRealizesTargetDiagramCorrected_wildCapThrough :
    foldRealizesTargetDiagramCorrected wildCapThroughDiagram := fun _ => by decide

/-- ★★ **The honest corrected target holds on the crossing-routed width-8 wild diagram** — four through strands with
crossing routing recovered. -/
theorem foldRealizesTargetDiagramCorrected_wildCrossThrough :
    foldRealizesTargetDiagramCorrected wildCrossThroughDiagram := fun _ => by decide

/-- ★ **The wild-diagram exercise bundle.**  All four fresh boundary involutions — through, cup+loop, cap+through,
and crossing-routed — satisfy the honest corrected target, exercising the arc-class routing (through / cup / cap /
loop / crossing) end to end on diagrams the r19 file never saw. -/
theorem foldRealizesTargetDiagramCorrected_wildBundle :
    foldRealizesTargetDiagramCorrected wildThroughDiagram
      ∧ foldRealizesTargetDiagramCorrected wildCupLoopDiagram
      ∧ foldRealizesTargetDiagramCorrected wildCapThroughDiagram
      ∧ foldRealizesTargetDiagramCorrected wildCrossThroughDiagram :=
  ⟨foldRealizesTargetDiagramCorrected_wildThrough, foldRealizesTargetDiagramCorrected_wildCupLoop,
   foldRealizesTargetDiagramCorrected_wildCapThrough, foldRealizesTargetDiagramCorrected_wildCrossThrough⟩

/-! ## B4 — the B1 honesty marker -/

/-- ★ **Honesty marker — the `WellFormedBrauerFold` append-split + the eval-first through-strand probe are SHIPPED
(r20 B1).**  `wellFormedBrauerFold_append` / `_appendSplit` give the word-level append law for `WellFormedBrauerFold`
(the analog of `processBrauer_append`), the skeleton the six-phase corrected word is assembled through.
`throughStrandConnects_probe` reads off the kernel that a through strand's bottom foot and its final top boundary
index share a union-find component in the phase-6 fold state (the corrected word's crossing phases re-represent the
foot with fresh ids, yet never sever the chain) — the concrete truth the general cross-phase bridge would prove.
`= true`. -/
def fxBrauer_hasWellFormedFoldAppendSplit : Bool := true

/-- ★ **Honesty marker — the per-phase `WellFormedBrauerFold` discharge lemmas + the six-phase reduction are SHIPPED
(r20 B2).**  `wellFormedBrauerFold_crossingWord` / `_cupWord` / `_capZeros` / `_circleWord` discharge each phase's
well-formedness from a single width obligation (crossing: `pos + 2 ≤ width`; cup: `pos ≤ width`; cap:
`count + count ≤ width`; circle: unconditional).  `wellFormedBrauerFold_standardFormWordExt5_ofPhases` assembles the
corrected word from the six per-phase obligations via the append-split (a clean five-fold combine at the seams
`standardFormFold_appendSplit` splits).  The lemmas FIRE (`wellFormedBrauerFold_phaseLemmas_fire`) and the FULL
corrected word of BOTH r19 witnesses — adversarial-B and the refuting nested cups — is well-formed
(`wellFormedBrauerFold_correctedWord_adversarialB` / `_nestedCups`).  `= true`. -/
def fxBrauer_hasWellFormedFoldPhaseDischarge : Bool := true

/-- ★ **Honesty marker — the honest corrected target is exercised on fresh width-8 wild diagrams (r20 B3).**  Four
boundary involutions the r19 file never touched — `wildThroughDiagram` / `wildCupLoopDiagram` /
`wildCapThroughDiagram` / `wildCrossThroughDiagram`, spanning through strands, top cups, bottom caps, loops, and
crossing routing — each satisfy `foldRealizesTargetDiagramCorrected` as proof terms
(`foldRealizesTargetDiagramCorrected_wildBundle`), with two premise-satisfiability witnesses
(`isBoundaryInvolution_wildThrough` / `_wildCupLoop`) confirming the exercise is not vacuous.  `= true`. -/
def fxBrauer_hasCorrectedTargetWildExercise : Bool := true

/-! ## B5 — the #2013 endgame ledger after r20 -/

/-- ★★★ **Honesty marker — the GENERAL `WellFormedBrauerFold`-for-corrected-word is SHIPPED (BRAUER r21).**  The r20
scaffold — the four per-phase discharge lemmas (`wellFormedBrauerFold_crossingWord` / `_cupWord` / `_capZeros` /
`_circleWord`), the six-phase reduction (`wellFormedBrauerFold_standardFormWordExt5_ofPhases`), and the word-level
append-split (`wellFormedBrauerFold_append` / `_appendSplit`) — is now FED from the corrected extractor's fields by
`wellFormedBrauerFold_correctedWord_general` (`Brauer/WiringDescWellFormedFoldWidth.lean`): for EVERY well-formed
boundary involution `d`, the corrected word `standardFormWordExt5 (reconstructStandardFormExt5Corrected d)` is
well-formed at the seed.  The feeding bridges (all zero-axiom, structural):

  * the staircase POSITION-BOUND `permutationToCrossingWord_posBound` on the two range-permutation read-offs
    (bottom / top crossing phases) and on ★ `throughStrandPerm_isBounded` (A′ — the middle order's `[0, #through)`
    boundedness, each emitted rank strict via the involution);
  * the crossing width-preservation `crossingWordFold_openWires_length` + the cap SHRINK / cup GROW block laws
    (`capBlockOpenWiresShrinkWidth` / `cupBlockOpenWiresGrowWidth`);
  * the two cruxes `capArcFeetTwiceThroughSumsToBottom` / `cupArcTwiceThroughSumsToTop` and ★ the through-count
    symmetry `throughStrandBottoms_length_eq_throughStrandTops` (the phase-boundary-width residual the two cruxes
    did NOT jointly close), fixing the phase-boundary widths.

This is the connectivity-free half of the r19 wall's third residual, DISCHARGED — a straight-line width-accounting
assembly, NO induction over the diagram, NO connectivity, NO arc classification.  BEYOND `WellFormedBrauerFold`, the
r19 wall's OTHER two residuals stay unbuilt: the through-strand cross-phase T-CONNECT (at boundary-index granularity
over arbitrary interior-crossing states — exercised here only as the eval-first `throughStrandConnects_probe`) and
T-ENUM / E3 fold-alignment.  So `fxBrauer_hasFoldAlignmentE3`, the tag-correspondence masters
`fxBrauer_hasTagCorrDisjoint` / `fxBrauer_hasTagCorrExtraction`, and the r19 wall
`fxBrauer_hasFoldTargetHonestAssembly` all stay honestly `false`; #2013 does NOT close.  `= true`. -/
def fxBrauer_hasWellFormedFoldGeneralAssembly : Bool := true

end FX1Poly.Polygraph
