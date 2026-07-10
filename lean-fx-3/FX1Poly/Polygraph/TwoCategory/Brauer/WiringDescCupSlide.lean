import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescBrauerSlides

/-! # WP-BRAUER-4 r4 — the V2 presentation: the cup-slide row (ADDITIVE over the seven Lehrer–Zhang relations)

The r3 seven-relation presentation (`brauerPresentation7`, two snakes + R2 + R3 + R1 cap-slide + the two untwist rows)
left ONE shipped-ctor gap the r4 slide census named: the ADJACENT-STRADDLE cup slide — a crossing braiding ONE cup
leg with an external strand — the ∗-dual of the shipped `capSlideRelation` (Lehrer–Zhang relation (2.7) "Sliding"
`(A⊗I)∘(I⊗X) = (I⊗A)∘(X⊗I)`; its ∗-transform `(I⊗X)∘(U⊗I) = (X⊗I)∘(I⊗U)` is the cup slide).  The finding
`fxBrauer_hasCupSlideStraddleFinding` (`Brauer/WiringDescBrauerSlides.lean`) recorded it as a TRUE diagram identity
(`cupSlideStraddle_diagramEq`, hence a genuine `BrauerConv`) with EQUAL crossing parity, not derivable from the
shipped seven-relation ctor set.

## The derivation gate — attempted, deferred to the explicit row

Lehrer–Zhang list only the cap slide (2.7) explicitly and obtain the cup slide as its ∗-transform under the closure
clause "and their transforms under ∗ and ♯".  Two honest fixes exist: (i) add the cup-slide row directly (a valid
representative of LZ's complete set); (ii) run the categorical "yanking" derivation `cupSlide ⟸ snake_L ∘ capSlide ∘
snake_R, then X∘X=I`, whose ingredients — BOTH snake orientations (`snakeRelation`, `snakeMirrorRelation`), the cap
slide (`capSlideRelation`), crossing involutivity, and co-de-looping (`cupUntwistRelation`) — ARE all shipped
`BrauerConvFree7` moves.  We attempted (ii): the snake-bend start typechecks
(`[cupAt 0, crossingAt 1] ~ [cupAt 1, capAt 0, cupAt 0, crossingAt 1]` via `whiskerRight`/`symm`/`snake`), but the
naive bend is CIRCULAR — it reproduces the same adjacent-straddle configuration one level up (the introduced cap
sits at the bottom, far from the top crossing, and commuting the crossing down to meet it re-encounters the same
cup-leg straddle).  Completing the mate at the positioned-word level is a genuine multi-step string-diagram
construction (interchange to walk the crossing past the cup, `capSlide` at the cap, then snake removal), out of
scope for one focused attempt.  So we take (i): the explicit row.  This is NOT a hard wall — the pair has equal
crossing parity (`cupSlideStraddle_parity_eq`) and lies in the classically-complete Lehrer–Zhang closure — the
constructive positioned-word yanking is deferred, and the row is the literature-faithful representative.

## What this file ships (ADDITIVE — every V1 datum and theorem is untouched)

  * **`cupSlideRelation`** — the straddle-form DATA row `[cupAt 0, crossingAt 1] ~ [cupAt 1, crossingAt 0]` over one
    bottom wire.  This is exactly Lehrer–Zhang ∗(2.7) `(I⊗X)∘(U⊗I) = (X⊗I)∘(I⊗U)`, and the r4 minimal witness
    `cupSlideStraddle_diagramEq` is its shift-0 instance.  Diagram-sound by `decide`.
  * **`brauerPresentation8`** = `brauerPresentation7 ++ [cupSlideRelation]` — the V2 relation set = V1 (the seven
    Lehrer–Zhang relations) plus the cup slide.  `brauerPresentation7` is untouched; V2 CONTAINS V1 as a prefix.
  * **`BrauerConvFree8`** — the V2 syntactic over-approximation, ADDITIVE over `BrauerConvFree7` via `ofFree7`, with
    the cup-slide row at any horizontal offset.  It genuinely CONTAINS `BrauerConvFree7`
    (`brauerConvFree8_ofFree7`), and a fortiori the five-relation `BrauerConvFree` (`brauerConvFree8_ofFree`) — every
    V1 conversion is a V2 conversion.
  * The V2 soundness arm (`brauerConv_cupSlide_inWiderContext`) lives in the sibling `WiringDescCupSlideSoundness`.

Raw Lean 4 + Init; structural recursion, no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The cup-slide DATA row (the ∗-dual of `capSlideRelation`) -/

/-- ★ **R8 CUP SLIDE** `(I⊗X)∘(U⊗I) = (X⊗I)∘(I⊗U)` — a cup then a crossing braiding its near leg with the external
strand slides to the cup created on the other side: `[cupAt 0, crossingAt 1] ~ [cupAt 1, crossingAt 0]` over one
bottom wire.  Lehrer–Zhang ∗(2.7) "Sliding" (the ∗-transform of `capSlideRelation`).  Orientation is forced: the cup
PRODUCES, so the crossing follows it, straddling one produced leg and the external strand. -/
def cupSlideRelation : BrauerRelation :=
  { boundaryCount := 1, lhs := [cupAt 0, crossingAt 1], rhs := [cupAt 1, crossingAt 0] }

/-- The cup slide is diagram-sound — both sides read `{ bottomCount := 1, topCount := 3, partner := [2, 3, 0, 1],
loops := 0 }` (bottom `0` ~ top `1`; top `0` ~ top `2`, the cup nesting over the external strand from either side).
This is the r4 minimal witness
`cupSlideStraddle_diagramEq` restated over the row's own projections. -/
theorem cupSlide_diagram_sound :
    brauerDiagramOf cupSlideRelation.boundaryCount cupSlideRelation.lhs
      = brauerDiagramOf cupSlideRelation.boundaryCount cupSlideRelation.rhs := by decide

/-! ## The V2 presentation `brauerPresentation8` = V1 (`brauerPresentation7`) + the cup slide -/

/-- ★ The **eight-relation V2 presentation**, as a value: the shipped seven Lehrer–Zhang relations
(`brauerPresentation7`) EXTENDED with the cup-slide row.  `brauerPresentation7` (hence `brauerPresentation`, the
original five) is untouched; V2 CONTAINS V1 as a prefix (`brauerPresentation8` = `brauerPresentation7 ++ …`). -/
def brauerPresentation8 : List BrauerRelation :=
  brauerPresentation7 ++ [cupSlideRelation]

/-- ★ **Every relation of the V2 presentation is diagram-sound** — the seven V1 witnesses
(`brauerPresentation7_allSound`) together with the cup-slide witness. -/
theorem brauerPresentation8_allSound :
    (brauerDiagramOf snakeRelation.boundaryCount snakeRelation.lhs
        = brauerDiagramOf snakeRelation.boundaryCount snakeRelation.rhs)
    ∧ (brauerDiagramOf snakeMirrorRelation.boundaryCount snakeMirrorRelation.lhs
        = brauerDiagramOf snakeMirrorRelation.boundaryCount snakeMirrorRelation.rhs)
    ∧ (brauerDiagramOf crossingInvolutionRelation.boundaryCount crossingInvolutionRelation.lhs
        = brauerDiagramOf crossingInvolutionRelation.boundaryCount crossingInvolutionRelation.rhs)
    ∧ (brauerDiagramOf yangBaxterRelation.boundaryCount yangBaxterRelation.lhs
        = brauerDiagramOf yangBaxterRelation.boundaryCount yangBaxterRelation.rhs)
    ∧ (brauerDiagramOf capSlideRelation.boundaryCount capSlideRelation.lhs
        = brauerDiagramOf capSlideRelation.boundaryCount capSlideRelation.rhs)
    ∧ (brauerDiagramOf cupUntwistRelation.boundaryCount cupUntwistRelation.lhs
        = brauerDiagramOf cupUntwistRelation.boundaryCount cupUntwistRelation.rhs)
    ∧ (brauerDiagramOf capUntwistRelation.boundaryCount capUntwistRelation.lhs
        = brauerDiagramOf capUntwistRelation.boundaryCount capUntwistRelation.rhs)
    ∧ (brauerDiagramOf cupSlideRelation.boundaryCount cupSlideRelation.lhs
        = brauerDiagramOf cupSlideRelation.boundaryCount cupSlideRelation.rhs) :=
  ⟨snake_diagram_sound, snakeMirror_diagram_sound, crossingInvolution_diagram_sound,
    yangBaxter_diagram_sound, capSlide_diagram_sound, cupUntwist_diagram_sound, capUntwist_diagram_sound,
    cupSlide_diagram_sound⟩

/-! ## `BrauerConvFree8` — the V2 syntactic over-approximation (ADDITIVE over `BrauerConvFree7`)

`BrauerConvFree7` (V1) is embedded verbatim via `ofFree7`, then closed under equivalence (`symm` / `trans`) and
congruence (`whiskerLeft` / `whiskerRight`) together with the cup-slide row at ANY horizontal offset.  Exact mirror
of how `BrauerConvFree7` was built over `BrauerConvFree`.  Since it contains `BrauerConvFree7` and the cup-slide row,
it over-approximates the true V2 (eight-relation) closure. -/
inductive BrauerConvFree8 : List BrauerAtom → List BrauerAtom → Prop
  /-- Embed the whole V1 over-approximation `BrauerConvFree7` (equivalence, the seven relations at any offset,
  interchange, both whiskerings). -/
  | ofFree7 {wordLeft wordRight : List BrauerAtom} :
      BrauerConvFree7 wordLeft wordRight → BrauerConvFree8 wordLeft wordRight
  /-- Symmetry (closes the cup-slide row under symmetry). -/
  | symm {wordLeft wordRight : List BrauerAtom} :
      BrauerConvFree8 wordLeft wordRight → BrauerConvFree8 wordRight wordLeft
  /-- Transitivity. -/
  | trans {wordLeft wordMid wordRight : List BrauerAtom} :
      BrauerConvFree8 wordLeft wordMid → BrauerConvFree8 wordMid wordRight → BrauerConvFree8 wordLeft wordRight
  /-- ★ R8 cup slide `(I⊗X)∘(U⊗I) = (X⊗I)∘(I⊗U)` at horizontal offset `shift`. -/
  | cupSlide (shift : Nat) :
      BrauerConvFree8 (shiftWord shift cupSlideRelation.lhs) (shiftWord shift cupSlideRelation.rhs)
  /-- Vertical congruence on the left: prepend a common word. -/
  | whiskerLeft {wordLeft wordRight : List BrauerAtom} (prefixWord : List BrauerAtom) :
      BrauerConvFree8 wordLeft wordRight → BrauerConvFree8 (prefixWord ++ wordLeft) (prefixWord ++ wordRight)
  /-- Vertical congruence on the right: append a common word. -/
  | whiskerRight {wordLeft wordRight : List BrauerAtom} (suffixWord : List BrauerAtom) :
      BrauerConvFree8 wordLeft wordRight → BrauerConvFree8 (wordLeft ++ suffixWord) (wordRight ++ suffixWord)

/-- ★ **`BrauerConvFree8` genuinely CONTAINS `BrauerConvFree7`** — the V1-into-V2 embedding: every V1 (seven-relation)
conversion is a V2 conversion.  Just `ofFree7`. -/
theorem brauerConvFree8_ofFree7 {wordLeft wordRight : List BrauerAtom}
    (conv : BrauerConvFree7 wordLeft wordRight) : BrauerConvFree8 wordLeft wordRight :=
  BrauerConvFree8.ofFree7 conv

/-- ★ **The five-relation `BrauerConvFree` also embeds into `BrauerConvFree8`** — every original-presentation
conversion is a V2 conversion (through the two-step `ofFree`/`ofFree7`). -/
theorem brauerConvFree8_ofFree {wordLeft wordRight : List BrauerAtom}
    (conv : BrauerConvFree wordLeft wordRight) : BrauerConvFree8 wordLeft wordRight :=
  BrauerConvFree8.ofFree7 (BrauerConvFree7.ofFree conv)

/-! ## Non-vacuity — the cup-slide straddle IS derivable in `BrauerConvFree8` -/

/-- ★ **The cup-slide straddle is derivable in `BrauerConvFree8`** (at offset `0`) — the exact pair the V1
seven-relation ctor set could not provide as a first-class move (`fxBrauer_hasCupSlideStraddleFinding`).  `shiftWord
0` is definitionally the identity. -/
theorem brauerConvFree8_cupSlide_derivable :
    BrauerConvFree8 [cupAt 0, crossingAt 1] [cupAt 1, crossingAt 0] :=
  BrauerConvFree8.cupSlide 0

/-- The old seven relations still embed — R6 cup untwist at the seed, via `ofFree7`.  Non-vacuity that the extension
retains the V1 closure. -/
theorem brauerConvFree8_cupUntwist_seed :
    BrauerConvFree8 [cupAt 0, crossingAt 0] [cupAt 0] :=
  BrauerConvFree8.ofFree7 brauerConvFree7_cupUntwist_derivable

/-- The cup-slide firing genuinely relates DISTINCT words — the row is a proper, inhabited move. -/
theorem brauerConvFree8_cupSlide_distinct :
    [cupAt 0, crossingAt 1] ≠ [cupAt 1, crossingAt 0] := by decide

/-! ## Honesty markers -/

/-- ★ **Honesty marker — the cup-slide DATA row is SHIPPED (the V2 presentation change).**  `cupSlideRelation`
(`[cupAt 0, crossingAt 1] ~ [cupAt 1, crossingAt 0]`, Lehrer–Zhang ∗(2.7) "Sliding") is added as a DATA row with its
`decide` diagram-soundness (`cupSlide_diagram_sound`), resolving the r4 straddle finding's bequest.  The derivation
gate was attempted (the yanking chain's ingredients are all shipped `BrauerConvFree7` moves) but the naive
snake-bend is circular and the full positioned-word mate is out of scope for one focused attempt; the row is the
literature-faithful representative of Lehrer–Zhang's complete set.  ADDITIVE: `capSlideRelation` and the whole
`brauerPresentation7` are untouched; `fxBrauer_hasCupSlideStraddleFinding` (the true historical finding) stays
`true`, its bequest now discharged.  `= true`. -/
def fxBrauer_hasBrauerCupSlideRow : Bool := true

/-- ★ **Honesty marker — V2 = V1 + the cup slide, additively, with the V1-into-V2 embedding.**  The V2 presentation
`brauerPresentation8` is `brauerPresentation7 ++ [cupSlideRelation]` (V1 is a prefix, byte-identical), all eight
relations diagram-sound (`brauerPresentation8_allSound`); the V2 syntactic over-approximation `BrauerConvFree8`
extends `BrauerConvFree7` via `ofFree7`, so every V1 conversion is a V2 conversion (`brauerConvFree8_ofFree7`, and a
fortiori `brauerConvFree8_ofFree` for the original five), and the cup-slide straddle — unreachable at V1 — is
derivable at V2 (`brauerConvFree8_cupSlide_derivable`).  The version relationship is honest: V2 strictly extends V1
by one primitive move, V1 is untouched.  `= true`. -/
def fxBrauer_hasBrauerV2Presentation : Bool := true

end FX1Poly.Polygraph
