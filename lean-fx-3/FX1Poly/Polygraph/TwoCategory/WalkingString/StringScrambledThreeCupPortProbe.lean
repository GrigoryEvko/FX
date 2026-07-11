import FX1Poly.Polygraph.TwoCategory.WalkingString.StringMatchingLastCupShortChord
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringWordChainAppend

/-! # WalkingString — the concrete THREE-CUP width-0 port truth-probe (FC-3 r16, B1/B3 anti-vacuity)

The r13 four-cup probe (`StringScrambledFourCupProbe`) validated the reorder + shared-top mechanism via a
`SpineAtomSwap` (no boundary chaining).  This file lands the complementary truth-probe the r16 PORTS
demand: a genuinely `SpineBoundaryChained 0` THREE-cup pure-cup width-0 spine on which the ported
last-cup short-chord readoff FIRES CONCRETELY, catching any vacuity in `stringMatchingLastCup_isShortChord`
and exercising the whole reused `WireState` union-find engine (the freshness fold over a two-cup prefix,
the boundary tracking, the forward-partner census) end-to-end at the adjoint-triple seed.

The spine is the nested rainbow of three lower unit cups `η : id_base ⇒ F·G`, each firing at window 0 with
a growing right context (`nil`, `F·G`, `F·G·F·G`) so the width chain threads `0 → 2 → 4 → 6`:

  * ★ `stringScrambledThreeCup_lastCupShortChord` — on the concrete three-cup width-0 spine, the ported
    `stringMatchingLastCup_isShortChord` reads the last cup's partner off `matchingOfSpineList 0` as the
    short chord `0 ↦ 1`.  The port is a general theorem, so this concrete firing is an anti-vacuity witness
    (the whole engine computes the chord on a real chained spine), not new content.
  * ★ `stringScrambledThreeCup_wordChainThreads` — the same three-cup spine is boundary-WORD-chained from
    its source word `nil` via the shipped W1 snoc `spineBoundaryWordChained_snoc`, confirming the word-chain
    substrate the sort's LOCATE threads fires on the concrete instance.

## What this probe does NOT do (the gate flag stays `false` — honestly)

This is an anti-vacuity firing of the shipped PORTS + word-chain substrate on a concrete instance, not the
sort.  `StringWidthZeroPureCupDeterminacyShared` is NOT inhabited; the fueled LOCATE / sort assembly
(NOVEL-B/C/D) is the r17 residual.  So `fxString_hasAdjointTripleCompleteness`
(`StringMatchingCompleteness`) stays `false`.

Raw Lean 4 + Init; the spine is three explicit `SpineAtom` records, the chain a threefold `cons` of
`rfl`s.  `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration
`#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- The length-4 right context `F·G·F·G : base ⟶ base` for the outer probe cup. -/
def stringProbeFGFG : ModalityPath adjointTripleGraph AdjointTripleMode.base AdjointTripleMode.base :=
  composePath stringFG stringFG

/-- The innermost probe cup `η` (window 0, empty right context): fires at width 0, produces `F·G`. -/
def stringProbeThreeCupInner :
    SpineAtom adjointTripleModeSignature AdjointTripleMode.base AdjointTripleMode.base :=
  ⟨AdjointTripleMode.base, AdjointTripleMode.base,
    ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base,
    ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base,
    stringFG, StringTwoCell.unitLower,
    ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base⟩

/-- The middle probe cup `η` (window 0, right context `F·G`): fires at width 2, produces width 4. -/
def stringProbeThreeCupMid :
    SpineAtom adjointTripleModeSignature AdjointTripleMode.base AdjointTripleMode.base :=
  ⟨AdjointTripleMode.base, AdjointTripleMode.base,
    ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base,
    ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base,
    stringFG, StringTwoCell.unitLower, stringFG⟩

/-- The outer probe cup `η` (window 0, right context `F·G·F·G`): fires at width 4, produces width 6. -/
def stringProbeThreeCupOuter :
    SpineAtom adjointTripleModeSignature AdjointTripleMode.base AdjointTripleMode.base :=
  ⟨AdjointTripleMode.base, AdjointTripleMode.base,
    ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base,
    ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base,
    stringFG, StringTwoCell.unitLower, stringProbeFGFG⟩

/-- The concrete three-cup width-0 spine, chained `0 → 2 → 4 → 6`. -/
def stringProbeThreeCupSpine :
    List (SpineAtom adjointTripleModeSignature AdjointTripleMode.base AdjointTripleMode.base) :=
  [stringProbeThreeCupInner, stringProbeThreeCupMid, stringProbeThreeCupOuter]

/-- The three-cup spine is boundary-length-chained from width `0` (each cup fires at its running width). -/
theorem stringProbeThreeCup_chained : SpineBoundaryChained 0 stringProbeThreeCupSpine :=
  SpineBoundaryChained.cons stringProbeThreeCupInner rfl
    (SpineBoundaryChained.cons stringProbeThreeCupMid rfl
      (SpineBoundaryChained.cons stringProbeThreeCupOuter rfl
        (SpineBoundaryChained.nil 6)))

/-- The three-cup spine is a pure-cup spine (every atom is a `(0, 2)` cup). -/
theorem stringProbeThreeCup_pureCup : AllCupArity stringProbeThreeCupSpine :=
  AllCupArity.cons rfl rfl (AllCupArity.cons rfl rfl (AllCupArity.cons rfl rfl AllCupArity.nil))

/-- ★ **The three-cup width-0 last-cup short-chord readoff fires concretely.**  On the concrete three-cup
width-0 spine, the ported `stringMatchingLastCup_isShortChord` reads the outer cup's partner off
`matchingOfSpineList 0`'s partner list as the short chord `0 ↦ 1`.  The whole reused `WireState` engine (the
freshness fold over the two-cup prefix, the boundary tracking, the forward-partner census) computes the
chord — an anti-vacuity witness for the r16 PORT 1 readoff at the adjoint-triple seed. -/
theorem stringScrambledThreeCup_lastCupShortChord :
    natListGetAt (matchingOfSpineList 0 stringProbeThreeCupSpine).partner 0 = 1 :=
  stringMatchingLastCup_isShortChord [stringProbeThreeCupInner, stringProbeThreeCupMid]
    stringProbeThreeCupOuter stringProbeThreeCup_chained stringProbeThreeCup_pureCup

/-- ★ **The three-cup spine is boundary-WORD-chained from its source word, threaded by W1 snoc.**  Starting
from the empty source word, each cup fires at the running boundary word; the shipped snoc
`spineBoundaryWordChained_snoc` extends the chain one cup at a time (the prefix's top word IS the next cup's
dom word).  Confirms the word-chain substrate the sort's LOCATE threads fires on the concrete instance. -/
theorem stringScrambledThreeCup_wordChainThreads :
    SpineBoundaryWordChained
      (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base)
      stringProbeThreeCupSpine :=
  SpineBoundaryWordChained.cons stringProbeThreeCupInner rfl
    (SpineBoundaryWordChained.cons stringProbeThreeCupMid rfl
      (SpineBoundaryWordChained.cons stringProbeThreeCupOuter rfl
        (SpineBoundaryWordChained.nil _)))

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the concrete THREE-CUP width-0 port truth-probe fires (FC-3 r16, B1/B3 anti-vacuity).**
`stringScrambledThreeCup_lastCupShortChord` fires the ported `stringMatchingLastCup_isShortChord` on a genuine
`SpineBoundaryChained 0` three-cup pure-cup spine, computing the short chord `0 ↦ 1` through the whole reused
`WireState` engine; `stringScrambledThreeCup_wordChainThreads` threads the boundary-WORD chain through the
same spine via the shipped W1 snoc.  Together they witness the r16 PORTS + word-chain substrate firing
concretely — the anti-vacuity check the recon calls for before the general sort.

  What this marker does NOT close (no gate flag flips): the fueled LOCATE / sort assembly (NOVEL-B/C/D)
  inhabiting `StringWidthZeroPureCupDeterminacyShared`.  So `fxString_hasAdjointTripleCompleteness`
  (`StringMatchingCompleteness`) stays `false`, honestly.  `= true`. -/
def fxString_hasScrambledThreeCupPortProbe : Bool := true

end FX1Poly.Polygraph
