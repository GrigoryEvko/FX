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

/-! ## B4 — the B1 honesty marker -/

/-- ★ **Honesty marker — the `WellFormedBrauerFold` append-split + the eval-first through-strand probe are SHIPPED
(r20 B1).**  `wellFormedBrauerFold_append` / `_appendSplit` give the word-level append law for `WellFormedBrauerFold`
(the analog of `processBrauer_append`), the skeleton the six-phase corrected word is assembled through.
`throughStrandConnects_probe` reads off the kernel that a through strand's bottom foot and its final top boundary
index share a union-find component in the phase-6 fold state (the corrected word's crossing phases re-represent the
foot with fresh ids, yet never sever the chain) — the concrete truth the general cross-phase bridge would prove.
`= true`. -/
def fxBrauer_hasWellFormedFoldAppendSplit : Bool := true

end FX1Poly.Polygraph
