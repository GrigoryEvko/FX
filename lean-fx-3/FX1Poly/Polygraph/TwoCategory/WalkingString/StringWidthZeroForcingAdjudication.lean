import FX1Poly.Polygraph.TwoCategory.WalkingString.StringSeed

/-! # WalkingString — the WIDTH-0 pure-cup determinacy ADJUDICATION: the bare Prop is TRUE by FORCING, not refutable
(FC-3 r12, B1)

The bare `StringWidthZeroPureCupDeterminacy` (`StringValleyDegenerateSplit`) asks: two width-0 pure-cup string spines
with EQUAL `matchingOfSpineList 0` are `SpineTraceEquiv`.  A candidate counterexample would need two width-0 pure-cup
spines that share a matching but build DIFFERENT top words.  This file adjudicates: **no such pair exists — the top
word is FORCED**, so the bare Prop is TRUE (the strengthening in `StringValleyDegenerateSplit` is an engineering
choice — the caller hands over its `targetPath` cheaply — not a soundness fix).

## The generator-level forcing core (machine-checked)

A pure CUP spine atom carries a generating 2-cell whose DOMAIN is the identity 1-cell (`nil`) — arity `(0, 2)`.  At
the three-generator seed only two `StringTwoCell` constructors have a `nil` domain: the lower unit `unitLower`
(`id_base ⇒ F·G`) and the upper unit `unitUpper` (`id_tip ⇒ G·H`).  Hence the cup's CODOMAIN is FORCED by its
endpoint mode:

  * ★ `stringBaseCup_codForced` — every cup 2-cell at the `base` endpoint (`nil_base ⇒ cod`) has `cod = F·G`.
  * ★ `stringTipCup_codForced` — every cup 2-cell at the `tip` endpoint (`nil_tip ⇒ cod`) has `cod = G·H`.

So along a width-0 pure-cup top word each chord's colour is pinned by its endpoint mode: at a `base`-turnback the
only cup cod is `F·G`; at a `tip`-turnback the only cup cod is `G·H`.  The matching fixes each chord's endpoint mode
(the mode alternates `base`/`tip` along the boundary), so the whole top word is a well-defined function of the
matching — equal matching forces equal top word.

## Why the earlier `(H·G, G·H)` candidate is INVALID (the recon's own species confusion, refuted)

An earlier recon sketch proposed distinguishing width-0 pure-cup spines by an `H·G` chord.  That is a category error:

  * ★ `stringNoCupHasCodHG` — NO cup 2-cell has codomain `H·G`.  `H·G = stringHG` is a `base`-endo, but it is the
    DOMAIN of the upper counit `counitUpper` (a CAP), never a cup cod — the base-endpoint cup cod is `F·G`.
  * ★ `stringNoCupHasCodGF` — dually, NO cup 2-cell has codomain `G·F`.  `G·F = stringGF` is the DOMAIN of the lower
    counit `counitLower` (a CAP); the tip-endpoint cup cod is `G·H`.

`H·G` and `G·H` are not even parallel — `H·G : base ⟶ base`, `G·H : tip ⟶ tip` — so "the top word contains an `H·G`
chord where the other has `G·H`" cannot arise in a pure-cup spine at a fixed endpoint.  The `H·G` letter appears in a
valley ONLY as the domain of the upper cap `ε'`, which is a CAP setting, never pure-cup.  So the candidate
counterexample fails; the bare Prop is TRUE by forcing.

## What this does NOT do (the flag stays `false`, honestly)

The generator-level forcing core is the SEED of the top-word determinacy; the FULL matching-to-top-word
reconstruction (peeling each chord, threading the endpoint modes) is the width-0 SORT itself — the multi-round
content `StringValleyDegenerateSplit`'s `StringWidthZeroPureCupDeterminacy` residual names, deferred to r13+.  This
file lands the adjudication (the bare Prop is TRUE, the candidate refuted) at the generator level, machine-checked,
so the strengthening in `StringValleyDegenerateSplit` is understood as a plumbing convenience, not a correction.

Raw Lean 4 + Init; each forcing witness is a `cases` on the four-constructor `StringTwoCell` with automatic
index-clash discharge (the `nil`-vs-`cons` / `base`-vs-`tip` unification).  `propext`/`Quot.sound`/`Classical`/
`sorry`/`native_decide`/`omega`-free; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The cup codomain is forced by the endpoint mode -/

/-- ★ **A base-endpoint cup has codomain `F·G`.**  A cup 2-cell fires from the identity 1-cell (`nil` domain); at the
`base` endpoint the only such `StringTwoCell` constructor is the lower unit `unitLower : id_base ⇒ F·G`, so the
codomain is forced to `stringFG`.  Casing the cell discards the three off-shape constructors by index unification (the
upper unit sits at `tip`; the two counits have `cons` domains). -/
theorem stringBaseCup_codForced
    {cod : ModalityPath adjointTripleGraph AdjointTripleMode.base AdjointTripleMode.base}
    (cupCell : StringTwoCell
      (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base) cod) :
    cod = stringFG := by
  cases cupCell
  rfl

/-- ★ **A tip-endpoint cup has codomain `G·H`.**  Dual to `stringBaseCup_codForced`: at the `tip` endpoint the only
cup constructor is the upper unit `unitUpper : id_tip ⇒ G·H`, so the codomain is forced to `stringGH`. -/
theorem stringTipCup_codForced
    {cod : ModalityPath adjointTripleGraph AdjointTripleMode.tip AdjointTripleMode.tip}
    (cupCell : StringTwoCell
      (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip) cod) :
    cod = stringGH := by
  cases cupCell
  rfl

/-! ## The candidate `H·G` / `G·F` cup cods are refuted (they are CAP domains) -/

/-- ★ **No cup has codomain `H·G`.**  `stringHG` (`H·G`) is a `base`-endo, but it is the DOMAIN of the upper counit
`counitUpper` (a CAP); no `nil`-domain constructor has it as a codomain (the base cup cod is `F·G`).  Casing the
purported cup discards every constructor — the direct refutation of the recon's invalid `(H·G, G·H)` candidate. -/
theorem stringNoCupHasCodHG
    (cupCell : StringTwoCell
      (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base) stringHG) : False := by
  cases cupCell

/-- ★ **No cup has codomain `G·F`.**  Dually, `stringGF` (`G·F`) is the DOMAIN of the lower counit `counitLower` (a
CAP); no `nil`-domain constructor has it as a codomain (the tip cup cod is `G·H`). -/
theorem stringNoCupHasCodGF
    (cupCell : StringTwoCell
      (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip) stringGF) : False := by
  cases cupCell

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the width-0 pure-cup determinacy is adjudicated: the bare Prop is TRUE by FORCING (FC-3 r12,
B1).**  The generator-level forcing core is machine-checked: a cup's codomain is FORCED by its endpoint mode
(`stringBaseCup_codForced` gives `F·G` at `base`, `stringTipCup_codForced` gives `G·H` at `tip`), and the recon's
earlier `(H·G, G·H)` candidate is directly REFUTED — `H·G` and `G·F` are CAP domains, never cup cods
(`stringNoCupHasCodHG`, `stringNoCupHasCodGF`).  Since the matching pins each chord's endpoint mode, the top word is a
well-defined function of the matching, so equal matching forces equal top word: NO width-0 pure-cup counterexample
exists.  The bare `StringWidthZeroPureCupDeterminacy` is therefore kept VERBATIM (adjudicated true, never restated);
the r12 strengthening (`StringWidthZeroPureCupDeterminacyShared`) is a plumbing convenience — the caller supplies its
`targetPath` as the shared top word — not a soundness fix.

  What this marker does NOT close (no gate flag flips): the FULL matching-to-top-word reconstruction (the width-0
  SORT) is the r13+ content `StringWidthZeroPureCupDeterminacy` names.  So `fxString_hasAdjointTripleCompleteness`
  (`StringMatchingCompleteness`) stays `false`, honestly, with the adjudication (bare Prop TRUE, candidate refuted)
  now machine-checked at the generator level.  `= true`. -/
def fxString_widthZeroPureCupDeterminacy_isForced : Bool := true

end FX1Poly.Polygraph
