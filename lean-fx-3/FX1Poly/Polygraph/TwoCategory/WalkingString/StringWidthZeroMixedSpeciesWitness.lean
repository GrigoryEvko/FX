import FX1Poly.Polygraph.TwoCategory.WalkingString.StringSeed
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringSpineTopWord
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPureCupSpine
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineBoundaryWordChain

/-! # WalkingString — the WIDTH-0 MIXED-SPECIES witness: single-species-at-width-0 is FALSE (FC-3 r13, B1)

The recon's species adjudication is DECISIVE and NEGATIVE: a width-0 pure-cup spine is **mixed-species**.  A base
cup (`unitLower`, cod `F·G`) and a tip cup (`unitUpper`, cod `G·H`) DO coexist in one width-0 boundary-word-chained
spine — NESTED via whiskering (the `StringTwoSpeciesMatchingProbe` finding: two colours co-occur at width 0 only
nested, since a transposable disjoint mixed pair is width ≥ 1).  So the colour dimension does NOT collapse, and the
width-0 sort must read cup species off the boundary WORD, not off lengths.

This file lands that adjudication as a machine-checked REFUTATION of single-species — the concrete nested witness the
recon proposed, truth-probed:

  * ★ `stringMixedWidthZeroSpine` — the two-atom spine `[baseCup, tipCup]` at the `base→base` endpoint, chained at
    the empty bottom word `nil`: a `base` cup `η = unitLower` (`id_base ⇒ F·G`) fires at `nil`, then a `tip` cup
    `η' = unitUpper` (`id_tip ⇒ G·H`) fires at the interior `tip` junction of `F·G` (left context `F`, right context
    `G`), building the top word `F·G·H·G`.
  * ★ `stringMixedWidthZeroSpine_chained` — it IS width-0 boundary-word-chained at `nil` (both `headFires` by `rfl`:
    the base cup's dom word is `nil`, the tip cup's dom word is `F·nil·G = F·G`).
  * ★ `stringMixedWidthZeroSpine_allCup` — it IS pure-cup (`AllCupArity`): both atoms carry cup arity `(0, 2)`.
  * ★ `stringMixedWidthZeroSpine_baseCup_mode` / `_tipCup_mode` — the two atoms sit at DIFFERENT endpoint modes
    (`base` vs `tip`), so by the shipped cup-cod forcing (`stringBaseCup_codForced` gives `F·G`,
    `stringTipCup_codForced` gives `G·H`, `StringWidthZeroForcingAdjudication`) they carry DIFFERENT cup species: no
    single endpoint mode covers a width-0 pure-cup spine.
  * ★ `stringMixedWidthZeroSpine_topWord` — the spine builds top word `F·G·H·G`, a pure-cup width-0 word CONTAINING
    the `coLeft = H` generator — impossible for a single lower-species (`F`/`G`-only) or single upper-species spine.
    The decisive artifact.
  * ★★ `stringWidthZeroMixedSpecies_exists` — the packaged existential: a width-0 boundary-word-chained pure-cup
    spine whose two atoms occupy the two distinct endpoint modes.  Single-species-at-width-0 is FALSE.

## What this does NOT do (the flag stays `false`, honestly)

This is the species TRUTH-PROBE (the B1 adjudication), not the sort.  The width-0 SORT
(`StringWidthZeroPureCupDeterminacyShared`) — the fueled partner-locate + matching-injective drop threading the shared
top word — is the multi-round content (r14/r15).  So `fxString_hasAdjointTripleCompleteness`
(`StringMatchingCompleteness`) stays `false`; this file confirms the mixed-species design, machine-checked, on the
concrete nested witness.

Raw Lean 4 + Init; the witness is two literal `SpineAtom` constructors, the chain / arity / mode facts by
`rfl` / constructor, the top word by `composePath` computation.  `propext`/`Quot.sound`/`Classical`/`sorry`/
`native_decide`/`omega`-free; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The two-atom mixed-species witness -/

/-- The lower cup `η = unitLower` (`id_base ⇒ F·G`) as a width-0 spine atom firing at the empty bottom word: both
whisker contexts are `nil`, so its domain boundary is `nil` and its codomain boundary is `F·G`. -/
def stringMixedBaseCup : SpineAtom adjointTripleModeSignature AdjointTripleMode.base AdjointTripleMode.base :=
  ⟨AdjointTripleMode.base, AdjointTripleMode.base,
    ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base,
    ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base,
    stringFG, StringTwoCell.unitLower,
    ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base⟩

/-- The upper cup `η' = unitUpper` (`id_tip ⇒ G·H`) as a width-0 spine atom firing at the INTERIOR `tip` junction of
`F·G`: left context `F` (`base⟶tip`), right context `G` (`tip⟶base`), so its domain boundary is `F·nil·G = F·G` and
its codomain boundary is `F·(G·H)·G = F·G·H·G`.  The `tip` endpoint mode is what forces the second, distinct cup
colour into the same width-0 spine. -/
def stringMixedTipCup : SpineAtom adjointTripleModeSignature AdjointTripleMode.base AdjointTripleMode.base :=
  ⟨AdjointTripleMode.tip, AdjointTripleMode.tip,
    singletonModalityPath (graph := adjointTripleGraph) AdjointTripleModality.left,
    ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip,
    stringGH, StringTwoCell.unitUpper,
    singletonModalityPath (graph := adjointTripleGraph) AdjointTripleModality.right⟩

/-- ★ **The width-0 MIXED-species pure-cup spine.**  A base cup then a nested tip cup, boundary-word-chained at the
empty bottom word `nil`. -/
def stringMixedWidthZeroSpine :
    List (SpineAtom adjointTripleModeSignature AdjointTripleMode.base AdjointTripleMode.base) :=
  [stringMixedBaseCup, stringMixedTipCup]

/-! ## The witness satisfies the width-0 pure-cup discipline -/

/-- ★ The mixed spine is boundary-word-chained at the empty bottom word `nil`: the base cup fires at `nil`
(`nil = nil·nil·nil`), the tip cup fires at `F·G` (`F·G = F·nil·G`), each `headFires` by `rfl`. -/
theorem stringMixedWidthZeroSpine_chained :
    SpineBoundaryWordChained
      (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base)
      stringMixedWidthZeroSpine := by
  dsimp only [stringMixedWidthZeroSpine]
  exact SpineBoundaryWordChained.cons _ rfl
    (SpineBoundaryWordChained.cons _ rfl (SpineBoundaryWordChained.nil _))

/-- ★ The mixed spine is pure-cup: both atoms carry cup arity `(0, 2)` (`nil` dom, length-2 cod `F·G` / `G·H`). -/
theorem stringMixedWidthZeroSpine_allCup : AllCupArity stringMixedWidthZeroSpine := by
  dsimp only [stringMixedWidthZeroSpine]
  exact AllCupArity.cons rfl stringFG_length
    (AllCupArity.cons rfl stringGH_length AllCupArity.nil)

/-! ## The two atoms sit at DIFFERENT endpoint modes -/

/-- ★ The base cup's endpoint mode is `base`. -/
theorem stringMixedWidthZeroSpine_baseCup_mode :
    stringMixedBaseCup.leftMidMode = AdjointTripleMode.base := rfl

/-- ★ The tip cup's endpoint mode is `tip` — DIFFERENT from the base cup's, so (by the shipped cup-cod forcing) the
two atoms carry different cup species within one width-0 spine. -/
theorem stringMixedWidthZeroSpine_tipCup_mode :
    stringMixedTipCup.leftMidMode = AdjointTripleMode.tip := rfl

/-! ## The decisive artifact: the top word contains the `H` generator -/

/-- ★ **The mixed spine builds top word `F·G·H·G`.**  Threading `spineListTopWord` from the empty bottom word lands
on the tip cup's codomain word `F·(G·H)·G`, a pure-cup width-0 word CONTAINING the `coLeft = H` generator — the letter
no single lower-species (`F`/`G`-only) spine can produce.  This is the concrete refutation of single-species. -/
theorem stringMixedWidthZeroSpine_topWord :
    spineListTopWord (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base)
        stringMixedWidthZeroSpine
      = composePath (singletonModalityPath (graph := adjointTripleGraph) AdjointTripleModality.left)
          (composePath stringGH
            (singletonModalityPath (graph := adjointTripleGraph) AdjointTripleModality.right)) := by
  rfl

/-- ★ The top word `F·G·H·G` has length 4: two length-1 context letters (`F`, `G`) around the length-2 upper-cup cod
`G·H`. -/
theorem stringMixedWidthZeroSpine_topWord_length :
    (spineListTopWord (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base)
        stringMixedWidthZeroSpine).length = 4 := rfl

/-! ## The packaged refutation -/

/-- ★★ **Single-species-at-width-0 is FALSE.**  There is a width-0 boundary-word-chained pure-cup string spine whose
two atoms occupy the two DISTINCT endpoint modes (`base` and `tip`).  By the shipped cup-cod forcing
(`stringBaseCup_codForced` / `stringTipCup_codForced`, `StringWidthZeroForcingAdjudication`) the base-mode atom's cod
is `F·G` and the tip-mode atom's cod is `G·H` — two different cup species in one width-0 spine.  So the width-0
pure-cup fragment is genuinely MIXED-species; the sort's atom pin must be WORD-driven (the recon's decisive
adjudication, machine-checked). -/
theorem stringWidthZeroMixedSpecies_exists :
    ∃ (baseCup tipCup :
        SpineAtom adjointTripleModeSignature AdjointTripleMode.base AdjointTripleMode.base),
      SpineBoundaryWordChained
          (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base) [baseCup, tipCup]
      ∧ AllCupArity [baseCup, tipCup]
      ∧ baseCup.leftMidMode = AdjointTripleMode.base
      ∧ tipCup.leftMidMode = AdjointTripleMode.tip :=
  ⟨stringMixedBaseCup, stringMixedTipCup, stringMixedWidthZeroSpine_chained,
    stringMixedWidthZeroSpine_allCup, stringMixedWidthZeroSpine_baseCup_mode,
    stringMixedWidthZeroSpine_tipCup_mode⟩

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — single-species-at-width-0 is FALSE; the width-0 pure-cup fragment is MIXED-species (FC-3 r13,
B1).**  The concrete nested witness `stringMixedWidthZeroSpine = [η, η']` is machine-checked: it is width-0
boundary-word-chained at `nil` (`stringMixedWidthZeroSpine_chained`), pure-cup (`stringMixedWidthZeroSpine_allCup`),
its two atoms occupy the DISTINCT endpoint modes `base` / `tip` (`stringMixedWidthZeroSpine_baseCup_mode` /
`_tipCup_mode`), and it builds top word `F·G·H·G` containing the `H` generator
(`stringMixedWidthZeroSpine_topWord`) — a pure-cup width-0 word no single lower-species spine can produce.  Packaged
as `stringWidthZeroMixedSpecies_exists`.  This is the recon's decisive species adjudication (base cup and tip cup DO
coexist in one width-0 spine, nested via whiskering), confirming the `StringTwoSpeciesMatchingProbe` finding from the
NESTED side: two colours at width 0 live NESTED, never as a transposable disjoint pair.

  What this marker does NOT close (no gate flag flips): the width-0 SORT
  (`StringWidthZeroPureCupDeterminacyShared`) — the fueled partner-locate + matching-injective drop threading the
  shared top word — is the r14/r15 content.  So `fxString_hasAdjointTripleCompleteness` stays `false`, honestly.
  `= true`. -/
def fxString_hasWidthZeroMixedSpeciesWitness : Bool := true

end FX1Poly.Polygraph
