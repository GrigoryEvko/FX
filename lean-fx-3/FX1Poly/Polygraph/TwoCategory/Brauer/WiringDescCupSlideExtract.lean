import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCupSlide

/-! # WP-BRAUER-4 r4 — the V2 extraction-fold MOVE SET + the banked fold residual (B3)

The cellular extraction normal form (Graham–Lehrer standard form: caps-bottom / crossing-middle / cups-top) sorts a
generator word into three blocks by sinking cups upward and caps downward past the crossing block, then straightening
the crossing block.  With the cup-slide row now a first-class `BrauerConvFree8` move, the CUP-SINK step's move set is
complete (the r4 slide census named the adjacent-straddle cup slide as the one missing move —
`fxBrauer_hasCupSlideStraddleFinding`; it is now `BrauerConvFree8.cupSlide`).

## What this file ships (ADDITIVE, over `BrauerConvFree8`)

The full V2 cup-sink move set, each lifted to / expressed in `BrauerConvFree8`:

  * **The adjacent-straddle cup slide, whiskered into arbitrary context** (`cupSlideStraddleFree8_inContext`) — the
    new cup-sinking primitive the V1 ctor set lacked.
  * **The distant (disjoint-support) cup slides** (`distantCupCrossingSlideFree8` / `distantCupCapSlideFree8` /
    `distantCupCupSlideFree8`) — lifted from the shipped `BrauerConvFree7` interchange derivations via `ofFree7`.
  * **The untwist-normalization input state** (`untwistNormalize_conv8` / `untwistNF_conv8`) — the hypothesis-free
    convertibility of a word to its untwist normal form (no σ trapped on an arc's own legs), the fold's seed.
  * **The crossing-block straightening engine** (`crossingWords_equalPerm_conv8`) — Matsumoto for `S_n` via the comb
    fold, lifted to `BrauerConvFree8`.

Plus a genuine COMPOSITE demonstration (`cupSink_composite_demo`) chaining the new cup slide with an interchange —
a two-distinct-move `BrauerConvFree8` reduction the V1 (seven-relation) closure could not perform (the cup slide is
its load-bearing first move).

## The banked residual — where the full fold jams (honest partial)

The extraction-fold ASSEMBLY target is
`brauerWords_equalMatching_conv (n) (w1 w2) (diagEq : brauerDiagramOf n w1 = brauerDiagramOf n w2) :
  BrauerConvFree8 w1 w2`
via the pass sequence: (1) untwist-normalize both (SHIPPED, `untwistNormalize_conv8`); (2) sink cups to the front
(SHIPPED move set: `cupSlideStraddleFree8_inContext` + the distant slides); (3) sink caps to the back (the ∗-dual
cap slides, `capSlideRelation` is shipped); (4) straighten the crossing block (SHIPPED,
`crossingWords_equalPerm_conv8`); (5) **match the cup/cap half-diagrams by the boundary `DiagramType`.**  Pass (5)
is the JAM: it needs the boundary-width-aware readback that reads a `DiagramType` back into the standard-form
assembly — the SAME residual the r4 readback (`fxBrauer_hasCrossingOnlyReadback`, `Brauer/WiringDescBrauerLedger.lean`)
and the pure-cup `internalCupCountsAgree` / `diagramAgree` residuals (tracker C1/C2) name.  The MOVE SET is complete;
the sorting DRIVER that decides WHERE to cut cups from caps (the arc-selection windowPin) is the shipped
`Brauer/WiringDescInsertion` planar-selection machinery, and its composition into a single fold that consumes a
`DiagramType` is the unbuilt driver.  So `fxBrauer_hasBrauerV2ExtractionFold` is honestly `false` — the residual is a
DRIVER + readback, not a missing move.

Raw Lean 4 + Init; structural recursion, no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The adjacent-straddle cup slide as a contextual `BrauerConvFree8` move (the new cup-sink primitive) -/

/-- ★ **The cup slide, whiskered into arbitrary horizontal + vertical context.**  For any prefix / suffix and any
horizontal offset `shift`, the cup-slide row fires: `prefix ++ (⟨cup then crossing⟩ ++ suffix)` is `BrauerConvFree8`
to `prefix ++ (⟨crossing then cup⟩ ++ suffix)`.  This is the cup-sinking primitive the V1 ctor set lacked — the fold
applies it inside a window to move a cup one position past a straddling crossing. -/
theorem cupSlideStraddleFree8_inContext (prefixWord suffixWord : List BrauerAtom) (shift : Nat) :
    BrauerConvFree8 (prefixWord ++ (shiftWord shift cupSlideRelation.lhs ++ suffixWord))
      (prefixWord ++ (shiftWord shift cupSlideRelation.rhs ++ suffixWord)) :=
  BrauerConvFree8.whiskerLeft prefixWord
    (BrauerConvFree8.whiskerRight suffixWord (BrauerConvFree8.cupSlide shift))

/-! ## The distant (disjoint-support) cup slides, lifted to `BrauerConvFree8` -/

/-- ★ **Distant cup / crossing slide** at V2 — the disjoint-support cup-past-crossing commute (`ofFree7` of the
shipped interchange derivation). -/
theorem distantCupCrossingSlideFree8 (cupPos crossingPos : Nat) (disjoint : cupPos ≤ crossingPos) :
    BrauerConvFree8 [cupAt cupPos, crossingAt (crossingPos + 2)] [crossingAt crossingPos, cupAt cupPos] :=
  BrauerConvFree8.ofFree7 (distantCupCrossingSlideFree cupPos crossingPos disjoint)

/-- ★ **Distant cup / cap slide** at V2. -/
theorem distantCupCapSlideFree8 (cupPos capPos : Nat) (disjoint : cupPos ≤ capPos) :
    BrauerConvFree8 [cupAt cupPos, capAt (capPos + 2)] [capAt capPos, cupAt cupPos] :=
  BrauerConvFree8.ofFree7 (distantCupCapSlideFree cupPos capPos disjoint)

/-- ★ **Distant cup / cup slide** at V2. -/
theorem distantCupCupSlideFree8 (cupPosLeft cupPosRight : Nat) (disjoint : cupPosLeft ≤ cupPosRight) :
    BrauerConvFree8 [cupAt cupPosLeft, cupAt (cupPosRight + 2)] [cupAt cupPosRight, cupAt cupPosLeft] :=
  BrauerConvFree8.ofFree7 (distantCupCupSlideFree cupPosLeft cupPosRight disjoint)

/-! ## The untwist-normalization input state, lifted to `BrauerConvFree8` -/

/-- ★ **The untwist normal form is `BrauerConvFree8`-convertible to its input (hypothesis-free).**  The fold's seed:
kill every `σ ∘ cup` / `cap ∘ σ` redex first, so no crossing is trapped on an arc's own legs.  `ofFree7` of the
shipped `untwistNormalize_conv`. -/
theorem untwistNormalize_conv8 (fuel : Nat) (word : List BrauerAtom) :
    BrauerConvFree8 word (untwistNormalize fuel word) :=
  BrauerConvFree8.ofFree7 (untwistNormalize_conv fuel word)

/-- ★ The seeded untwist normal form is `BrauerConvFree8`-convertible to its input. -/
theorem untwistNF_conv8 (word : List BrauerAtom) : BrauerConvFree8 word (untwistNF word) :=
  BrauerConvFree8.ofFree7 (untwistNF_conv word)

/-! ## The crossing-block straightening engine, lifted to `BrauerConvFree8` -/

/-- ★ **Crossing-only straightening at V2 (Matsumoto for `S_n`).**  Two crossing words realizing the same
through-strand permutation are `BrauerConvFree8`-convertible — the crossing-block engine of the middle sort.
`ofFree7` of the shipped comb-fold breach. -/
theorem crossingWords_equalPerm_conv8 (generatorCount : Nat) (word1 word2 : List Nat)
    (hRange1 : mentionsOnlyBelow generatorCount word1 = true)
    (hRange2 : mentionsOnlyBelow generatorCount word2 = true)
    (permEq : permuteOfCrossingWord (generatorCount + 1) word1
      = permuteOfCrossingWord (generatorCount + 1) word2) :
    BrauerConvFree8 (crossingWord word1) (crossingWord word2) :=
  BrauerConvFree8.ofFree7 (crossingWords_equalPerm_conv generatorCount word1 word2 hRange1 hRange2 permEq)

/-! ## A genuine composite — the cup slide chains with an interchange (a V1-impossible reduction) -/

/-- ★ **Composite cup-sink demonstration.**  `[cupAt 0, crossingAt 1, crossingAt 2]` is `BrauerConvFree8` to
`[cupAt 1, crossingAt 2, crossingAt 0]` via TWO distinct moves: (1) the new cup slide (whiskered by the trailing
crossing) sinks the cup one position — `[cupAt 0, crossingAt 1, crossingAt 2] ~ [cupAt 1, crossingAt 0, crossingAt 2]`;
(2) the interchange (disjoint crossings at `0` and `2`) commutes them —
`[cupAt 1, crossingAt 0, crossingAt 2] ~ [cupAt 1, crossingAt 2, crossingAt 0]`.  The cup slide is the LOAD-BEARING
first move: the V1 (seven-relation) closure could not perform it, so this composite is genuinely a V2-only reduction. -/
theorem cupSink_composite_demo :
    BrauerConvFree8 [cupAt 0, crossingAt 1, crossingAt 2] [cupAt 1, crossingAt 2, crossingAt 0] :=
  BrauerConvFree8.trans
    (BrauerConvFree8.whiskerRight [crossingAt 2] (BrauerConvFree8.cupSlide 0))
    (BrauerConvFree8.whiskerLeft [cupAt 1]
      (brauerConvFree8_ofFree (BrauerConvFree.interchange 0 2 crossingWiring crossingWiring (by decide))))

/-! ## Honesty markers -/

/-- ★ **Honesty marker — the V2 cup-sink MOVE SET is complete.**  Every move the cellular extraction fold's cup-sink
step needs is now a `BrauerConvFree8` lemma: the adjacent-straddle cup slide whiskered into arbitrary context
(`cupSlideStraddleFree8_inContext`, the new primitive the V1 ctor set lacked), the distant disjoint-support slides
(`distantCupCrossingSlideFree8` / `distantCupCapSlideFree8` / `distantCupCupSlideFree8`), the untwist-normalization
seed (`untwistNormalize_conv8`), and the crossing-block straightening engine (`crossingWords_equalPerm_conv8`).
Non-vacuity: `cupSink_composite_demo` chains the new cup slide with an interchange, a V1-impossible reduction.
`= true`. -/
def fxBrauer_hasCupSinkMoveSet : Bool := true

/-- **Honesty marker — the FULL V2 extraction fold is NOT yet assembled (banked residual).**  The MOVE SET is
complete (`fxBrauer_hasCupSinkMoveSet`), but the extraction-fold ASSEMBLY
`brauerWords_equalMatching_conv (diagEq : brauerDiagramOf n w1 = brauerDiagramOf n w2) : BrauerConvFree8 w1 w2`
is not built.  The banked jam is pass (5) of the sort — MATCHING the cup/cap half-diagrams by the boundary
`DiagramType`: it needs the boundary-width-aware readback (the SAME residual the r4
`fxBrauer_hasCrossingOnlyReadback` names, and the pure-cup `internalCupCountsAgree` / `diagramAgree` residuals track),
composed with the shipped `Brauer/WiringDescInsertion` planar arc-selection DRIVER into one fold consuming a
`DiagramType`.  So the residual is a DRIVER + readback, not a missing move — the completeness residual
`fxBrauer_hasBrauerCompleteness` (`Brauer/WiringDesc.lean`) stays honestly `false`.  `= false`. -/
def fxBrauer_hasBrauerV2ExtractionFold : Bool := false

end FX1Poly.Polygraph
