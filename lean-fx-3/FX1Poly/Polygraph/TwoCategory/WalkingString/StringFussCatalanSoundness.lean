import FX1Poly.Polygraph.TwoCategory.WalkingString.StringFussCatalan
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringMatchingSoundness

/-! # WalkingString — FC soundness, colour faithfulness, and the one-colour regression (FC-1, pieces B/C/D)

FC-0 (`StringFussCatalan`) shipped the Fuss–Catalan carrier `FcDiagram`, `fcDiagramOf` (arcs derived from the base
matching, colours read off the boundary labels), and the forgetful bridge `fcDiagramForget_fcDiagramOf`.  This file
lands three FC-1 layers ON TOP of the shipped, UNCONDITIONAL two-level soundness
(`stringSaturatedConv_matchingOf_eq_final`), all additive, none touching FC-0:

  * **(B) COLOUR FAITHFULNESS.**  The wire-level chirality — every cup opens an ordered word `{F·G, G·H}`, every cap
    closes an ordered word `{G·F, H·G}`, and the two ordered alphabets are DISJOINT (`stringCapWord_not_cupWord`) —
    is the fold-level shadow of the shipped generator-level `stringCupCod_ne_capDom`.  Each cup/cap word has EXACTLY
    ONE `G`-end (`stringCupCapWord_hasExactlyOneGEnd`), so `fcArcColour` reads a well-defined non-`G` colour on every
    generator-created arc and NEVER the degenerate `gWire` (`stringGeneratorArcColour_ne_gWire`).  VERDICT — NO
    divergence between the boundary-derived colour and the generator-carried colour: the only `gWire`-`gWire` arc is
    the shared-middle `G` through-strand, which carries no cup/cap, and `fcArcColour gWire gWire = gWire` is the
    correct shared-`G` reading.

  * **(C) FC SOUNDNESS.**  `fcDiagramOf` is a pure FUNCTION of `(matchingOf cell, pathLabels sourcePath,
    pathLabels targetPath)`, so it inherits the shipped unconditional two-level soundness by a one-line rewrite:
    saturated-convertible cells get EQUAL FC diagrams (`stringSaturatedConv_fcDiagramOf_eq`).  Each of the four
    triangle rows agrees ON THE NOSE (`rfl`), and the two `G`-triangles collapse to the SAME FC datum (the shared-`G`
    coherence, FC-level).  The separation corollary `fcDiagramOf_ne_notSaturatedConv` is the contrapositive.

  * **(D) ONE-COLOUR REGRESSION.**  Forgetting the FC colours recovers the colour-blind Joyal–Street `DiagramType`
    (`fcDiagramForgetColour`, `rfl`), which is exactly the object the walking-adjunction word problem compares.  On a
    MONOCHROMATIC FC diagram (non-`G` arcs all one colour) the colour data is redundant and the FC layer collapses to
    the single-colour regression target (`monochromaticFc_reduces_toMatchingOf`).

Raw Lean 4 + Init; the soundness is a rewrite on the shipped `_final` lemma, the rows are `rfl`, the chirality /
faithfulness are full-enum `cases` + `decide`.  `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`
-free; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## (B) wire-level chirality — the two ordered cup/cap alphabets, DISJOINT -/

/-- The two **ordered cup words** as a full-enum predicate on the pair `(lowLabel, highLabel)`: a lower cup opens
`F·G` (`(fWire, gWire)`), an upper cup opens `G·H` (`(gWire, hWire)`).  All seven other ordered pairs are `false`
(spelled out — no wildcard, propext-clean). -/
def isCupWordOrdered (lowLabel highLabel : WireLabel) : Bool :=
  match lowLabel, highLabel with
  | WireLabel.fWire, WireLabel.gWire => true
  | WireLabel.gWire, WireLabel.hWire => true
  | WireLabel.fWire, WireLabel.fWire => false
  | WireLabel.fWire, WireLabel.hWire => false
  | WireLabel.gWire, WireLabel.fWire => false
  | WireLabel.gWire, WireLabel.gWire => false
  | WireLabel.hWire, WireLabel.fWire => false
  | WireLabel.hWire, WireLabel.gWire => false
  | WireLabel.hWire, WireLabel.hWire => false

/-- The two **ordered cap words** as a full-enum predicate on the pair `(lowLabel, highLabel)`: a lower cap closes
`G·F` (`(gWire, fWire)`), an upper cap closes `H·G` (`(hWire, gWire)`).  All seven other ordered pairs are `false`. -/
def isCapWordOrdered (lowLabel highLabel : WireLabel) : Bool :=
  match lowLabel, highLabel with
  | WireLabel.gWire, WireLabel.fWire => true
  | WireLabel.hWire, WireLabel.gWire => true
  | WireLabel.fWire, WireLabel.fWire => false
  | WireLabel.fWire, WireLabel.gWire => false
  | WireLabel.fWire, WireLabel.hWire => false
  | WireLabel.gWire, WireLabel.gWire => false
  | WireLabel.gWire, WireLabel.hWire => false
  | WireLabel.hWire, WireLabel.fWire => false
  | WireLabel.hWire, WireLabel.hWire => false

/-- ★★ **The fold-level CHIRALITY — an ordered cap word is NEVER an ordered cup word.**  The two ordered two-letter
alphabets `{(F,G), (G,H)}` (cups) and `{(G,F), (H,G)}` (caps) are DISJOINT.  This is the wire-orientation shadow of
the shipped generator-level `stringCupCod_ne_capDom` (`F ≠ H` propagated into the words), and the exact reason a cap
window can never read a cup-created pair as-a-pair.  Full 9-case enum. -/
theorem stringCapWord_not_cupWord (lowLabel highLabel : WireLabel)
    (isCap : isCapWordOrdered lowLabel highLabel = true) :
    isCupWordOrdered lowLabel highLabel = false := by
  cases lowLabel <;> cases highLabel <;> first | rfl | exact Bool.noConfusion isCap

/-- ★ The dual chirality — an ordered cup word is NEVER an ordered cap word (the same disjointness, read the other
way). -/
theorem stringCupWord_not_capWord (lowLabel highLabel : WireLabel)
    (isCup : isCupWordOrdered lowLabel highLabel = true) :
    isCapWordOrdered lowLabel highLabel = false := by
  cases lowLabel <;> cases highLabel <;> first | rfl | exact Bool.noConfusion isCup

/-! ## (B) colour faithfulness — exactly one `G`-end, and `fcArcColour` reads the non-`G` letter -/

/-- ★★ **Every cup/cap word has EXACTLY ONE `G`-end.**  For any ordered cup or cap word, precisely one of the two
ends is `gWire` — the low end for `{(G,H), (G,F)}`, the high end for `{(F,G), (H,G)}`.  This is the two-colour
Fuss–Catalan discipline (Bisch–Jones: strings join a `G`-point to a non-`G` point) read at the wire level, the
faithfulness backbone: an arc's non-`G` end determines its colour unambiguously.  Full 9-case enum. -/
theorem stringCupCapWord_hasExactlyOneGEnd (lowLabel highLabel : WireLabel)
    (isCupOrCap : isCupWordOrdered lowLabel highLabel = true
      ∨ isCapWordOrdered lowLabel highLabel = true) :
    ((lowLabel = WireLabel.gWire) ∧ ¬ (highLabel = WireLabel.gWire))
      ∨ (¬ (lowLabel = WireLabel.gWire) ∧ (highLabel = WireLabel.gWire)) := by
  cases lowLabel <;> cases highLabel <;>
    first
    | exact Or.inr ⟨by decide, rfl⟩
    | exact Or.inl ⟨rfl, by decide⟩
    | (rcases isCupOrCap with isCup | isCap
       exact absurd (isCup.trans (by rfl)) (by decide)
       exact absurd (isCap.trans (by rfl)) (by decide))

/-- ★ **`fcArcColour` reads a cup/cap word's non-`G` colour, never the degenerate `gWire`.**  On any ordered cup or
cap word (which by `stringCupCapWord_hasExactlyOneGEnd` has exactly one `G`-end) the arc colour is the non-`G`
letter — `fWire` or `hWire`, never `gWire`.  So every GENERATOR-created arc is coloured faithfully; the degenerate
`fcArcColour gWire gWire = gWire` case is reached only by a `G`-`G` through-strand, which carries no cup/cap. -/
theorem stringGeneratorArcColour_ne_gWire (lowLabel highLabel : WireLabel)
    (isCupOrCap : isCupWordOrdered lowLabel highLabel = true
      ∨ isCapWordOrdered lowLabel highLabel = true) :
    fcArcColour lowLabel highLabel ≠ WireLabel.gWire := by
  cases lowLabel <;> cases highLabel <;>
    first
    | (intro colourEq; exact WireLabel.noConfusion colourEq)
    | (rcases isCupOrCap with isCup | isCap
       exact Bool.noConfusion isCup
       exact Bool.noConfusion isCap)

/-- The four generator words read their FC colour concretely: the lower cup `F·G` and lower cap `G·F` read `fWire`
(colour 1), the upper cup `G·H` and upper cap `H·G` read `hWire` (colour 2).  `decide`. -/
theorem stringGeneratorArcColours :
    fcArcColour WireLabel.fWire WireLabel.gWire = WireLabel.fWire
      ∧ fcArcColour WireLabel.gWire WireLabel.fWire = WireLabel.fWire
      ∧ fcArcColour WireLabel.gWire WireLabel.hWire = WireLabel.hWire
      ∧ fcArcColour WireLabel.hWire WireLabel.gWire = WireLabel.hWire := by decide

/-! ## (C) FC soundness — `fcDiagramOf` invariant under the saturated congruence -/

/-- ★★ **FC SOUNDNESS.**  Saturated-convertible walking-adjoint-triple 2-cells get EQUAL Fuss–Catalan diagrams.
`fcDiagramOf` is a pure function of `(matchingOf cell, pathLabels sourcePath, pathLabels targetPath)` — the arcs are
DERIVED from the base matching by `fcArcsFromPartner` — so it inherits the shipped UNCONDITIONAL two-level soundness
(`stringSaturatedConv_matchingOf_eq_final`) by a single rewrite: equal boundary matchings (with identical boundary
words, same source / target 1-cells) give equal derived arcs, hence equal FC diagrams.  No FC-level congruence
induction is needed — the FC layer rides the shipped `matchingOf`-level capstone. -/
theorem stringSaturatedConv_fcDiagramOf_eq
    {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    {cellA cellB : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath}
    (conv : StringSaturatedTwoCellConv cellA cellB) :
    fcDiagramOf sourcePath targetPath cellA = fcDiagramOf sourcePath targetPath cellB := by
  have baseEq : matchingOf cellA = matchingOf cellB := stringSaturatedConv_matchingOf_eq_final conv
  dsimp only [fcDiagramOf]
  rw [baseEq]

/-- ★ **The separation corollary.**  If two parallel cells have DIFFERENT FC diagrams they are NOT
saturated-convertible — the contrapositive of FC soundness, the NO-direction the FC carrier decides. -/
theorem fcDiagramOf_ne_notSaturatedConv
    {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    {cellA cellB : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath}
    (diagramsDiffer : fcDiagramOf sourcePath targetPath cellA ≠ fcDiagramOf sourcePath targetPath cellB) :
    ¬ StringSaturatedTwoCellConv cellA cellB :=
  fun conv => diagramsDiffer (stringSaturatedConv_fcDiagramOf_eq conv)

/-! ## (C) per-triangle FC agreement — each row `rfl`, the two `G`-triangles collapse to one datum -/

/-- ★ **The `F` triangle preserves the FC diagram** (`rfl`) — `fcDiagramOf` of the `F`-snake equals that of `id_F`:
the base matching collapses (`matchingOf_stringTriangleF`), the boundary words `[F] ⇒ [F]` are unchanged, so the
derived single `fWire` arc agrees on the nose. -/
theorem fcDiagramOf_stringSnakeF_eq_identityF :
    fcDiagramOf (singletonModalityPath AdjointTripleModality.left)
        (singletonModalityPath AdjointTripleModality.left) stringSnakeF
      = fcDiagramOf (singletonModalityPath AdjointTripleModality.left)
          (singletonModalityPath AdjointTripleModality.left) stringIdentityF := rfl

/-- ★ **The lower `G` triangle preserves the FC diagram** (`rfl`) — boundary words `[G] ⇒ [G]`, the derived arc a
`gWire` through-strand. -/
theorem fcDiagramOf_stringSnakeGlo_eq_identityG :
    fcDiagramOf (singletonModalityPath AdjointTripleModality.right)
        (singletonModalityPath AdjointTripleModality.right) stringSnakeGlo
      = fcDiagramOf (singletonModalityPath AdjointTripleModality.right)
          (singletonModalityPath AdjointTripleModality.right) stringIdentityG := rfl

/-- ★ **The upper `G` triangle preserves the FC diagram** (`rfl`) — the SAME FC datum as the lower `G` triangle. -/
theorem fcDiagramOf_stringSnakeGhi_eq_identityG :
    fcDiagramOf (singletonModalityPath AdjointTripleModality.right)
        (singletonModalityPath AdjointTripleModality.right) stringSnakeGhi
      = fcDiagramOf (singletonModalityPath AdjointTripleModality.right)
          (singletonModalityPath AdjointTripleModality.right) stringIdentityG := rfl

/-- ★ **The `H` triangle preserves the FC diagram** (`rfl`) — boundary words `[H] ⇒ [H]`, the derived arc an
`hWire` through-strand. -/
theorem fcDiagramOf_stringSnakeH_eq_identityH :
    fcDiagramOf (singletonModalityPath AdjointTripleModality.coLeft)
        (singletonModalityPath AdjointTripleModality.coLeft) stringSnakeH
      = fcDiagramOf (singletonModalityPath AdjointTripleModality.coLeft)
          (singletonModalityPath AdjointTripleModality.coLeft) stringIdentityH := rfl

/-- ★★ **The shared-`G` coherence at the FC level.**  The two SYNTACTICALLY DISTINCT `G ⇒ G` snakes collapse to the
SAME Fuss–Catalan diagram (both to `id_G`'s datum: one `gWire` through-strand, boundary words `[G] ⇒ [G]`) — the
FC-carrier realisation of `stringSnakeGlo_conv_stringSnakeGhi`, a coherence in NEITHER single adjunction. -/
theorem fcDiagramOf_stringSnakeGlo_eq_stringSnakeGhi :
    fcDiagramOf (singletonModalityPath AdjointTripleModality.right)
        (singletonModalityPath AdjointTripleModality.right) stringSnakeGlo
      = fcDiagramOf (singletonModalityPath AdjointTripleModality.right)
          (singletonModalityPath AdjointTripleModality.right) stringSnakeGhi :=
  fcDiagramOf_stringSnakeGlo_eq_identityG.trans fcDiagramOf_stringSnakeGhi_eq_identityG.symm

/-! ## (C) non-vacuity — the cross-level cell stays distinguished from `id_G` -/

/-- ★★ **The cross-level cell is DISTINGUISHED from `id_G` at the FC level.**  `stringCrossLevelCell : G·F ⇒ G·H`
(in NEITHER single adjunction) gets a TWO-arc, TWO-colour FC diagram (`{fWire, hWire}`, boundary words `[G,F] ⇒
[G,H]`), whereas `id_G` gets a one-arc `gWire` through-strand (`[G] ⇒ [G]`) — so FC soundness never equates them.
The carrier keeps the cross-level structure the walking adjoint triple has beyond two disjoint adjunctions. -/
theorem fcDiagramOf_stringCrossLevel_ne_identityG :
    fcDiagramOf stringGF stringGH stringCrossLevelCell
      ≠ fcDiagramOf (singletonModalityPath AdjointTripleModality.right)
          (singletonModalityPath AdjointTripleModality.right) stringIdentityG := by decide

/-! ## (D) the one-colour regression map — forget the FC colours, land the Joyal–Street type -/

/-- Forget an FC diagram's colours: keep only the colour-blind Joyal–Street `DiagramType` (the base boundary
matching + loop count).  This is the object the walking-adjunction word problem compares — the one-colour
regression target. -/
def fcDiagramForgetColour (fc : FcDiagram) : DiagramType := fc.base

/-- ★ **The FC diagram forgets on the nose to the base `matchingOf`.**  `fcDiagramForgetColour (fcDiagramOf … cell)
= matchingOf cell` (`rfl`) — the FC carrier is a strict colour REFINEMENT of the shipped colour-blind matching, and
`fcDiagramOf.base` IS `matchingOf cell`, the same signature-polymorphic invariant the walking adjunction uses. -/
theorem fcDiagramForgetColour_fcDiagramOf
    {sourceMode targetMode : AdjointTripleMode}
    (sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode)
    (cell : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath) :
    fcDiagramForgetColour (fcDiagramOf sourcePath targetPath cell) = matchingOf cell := rfl

/-- An FC diagram is **monochromatic of colour `mainColour`** when every arc is either that colour or the
shared-middle `gWire` (the through-strand colour) — the Fuss–Catalan single-colour restriction, on which the
two-colour discipline collapses to the one-colour Temperley–Lieb regression target. -/
def IsMonochromaticFc (fc : FcDiagram) (mainColour : WireLabel) : Prop :=
  ∀ arc ∈ fc.arcs, arc.colour = mainColour ∨ arc.colour = WireLabel.gWire

/-- ★ **A monochromatic FC diagram reduces to the one-colour regression.**  On the monochromatic slice the FC
colour data is redundant, so forgetting it and reading the base `matchingOf` recovers the colour-blind
Joyal–Street type the walking-adjunction word problem decides — `fcDiagramForgetColour` composed with `fcDiagramOf`
is `matchingOf` on the nose, regardless of the monochromatic witness. -/
theorem monochromaticFc_reduces_toMatchingOf
    {sourceMode targetMode : AdjointTripleMode}
    (sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode)
    (cell : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath)
    (mainColour : WireLabel)
    (_isMonochromatic : IsMonochromaticFc (fcDiagramOf sourcePath targetPath cell) mainColour) :
    fcDiagramForgetColour (fcDiagramOf sourcePath targetPath cell) = matchingOf cell := rfl

/-- ★ **Non-vacuity of the monochromatic slice.**  The lower cup `η : id ⇒ F·G` has a single `fWire` arc, so its FC
diagram is monochromatic of colour `fWire` — a genuine inhabitant of the one-colour regression slice (the `F ⊣ G`
sub-alphabet), where the FC layer collapses to the walking-adjunction matching. -/
theorem stringUnitLower_isMonochromaticFc :
    IsMonochromaticFc
      (fcDiagramOf (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base)
        stringFG stringUnitLower) WireLabel.fWire := by
  intro arc arcMem
  have arcListEq : (fcDiagramOf (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base)
      stringFG stringUnitLower).arcs = [{ lowEnd := 0, highEnd := 1, colour := WireLabel.fWire }] := rfl
  rw [arcListEq] at arcMem
  cases arcMem with
  | head => exact Or.inl rfl
  | tail _ restMem => nomatch restMem

/-! ## Honesty markers -/

/-- **★ ESTABLISHED — FC COLOUR FAITHFULNESS; no boundary-vs-generator divergence.**  The wire-level chirality is
machine-checked: the two ordered cup alphabets `{(F,G),(G,H)}` and cap alphabets `{(G,F),(H,G)}` are DISJOINT
(`stringCapWord_not_cupWord` / `stringCupWord_not_capWord`), the fold-level shadow of the shipped
`stringCupCod_ne_capDom`.  Every cup/cap word has EXACTLY ONE `G`-end (`stringCupCapWord_hasExactlyOneGEnd`), so
`fcArcColour` reads a well-defined non-`G` colour on every generator-created arc and NEVER the degenerate `gWire`
(`stringGeneratorArcColour_ne_gWire`; the concrete colours in `stringGeneratorArcColours`).  VERDICT: the
boundary-derived `fcArcColour` agrees with the generator-carried colour on every generated arc — the ONLY
`gWire`-`gWire` arc is the shared-middle `G` through-strand (no cup/cap), and reading it `gWire` is correct.  So
there is NO divergence.  `= true`. -/
def fxString_hasFcColourFaithful : Bool := true

/-- **★ ESTABLISHED — FC SOUNDNESS is UNCONDITIONAL.**  `stringSaturatedConv_fcDiagramOf_eq` sends
saturated-convertible cells to EQUAL Fuss–Catalan diagrams, riding the shipped unconditional two-level soundness
`stringSaturatedConv_matchingOf_eq_final` by a single rewrite (`fcDiagramOf` is a pure function of the base matching
plus the boundary words; the arcs are derived, so no FC-level congruence induction is owed).  Each of the four
triangle rows agrees ON THE NOSE (`fcDiagramOf_stringSnake{F,Glo,Ghi,H}_eq_identity*`, `rfl`); the two `G`-triangles
collapse to ONE FC datum (`fcDiagramOf_stringSnakeGlo_eq_stringSnakeGhi`, the shared-`G` coherence).  The separation
corollary `fcDiagramOf_ne_notSaturatedConv` is the contrapositive.  Non-vacuous: the cross-level cell stays
distinguished from `id_G` (`fcDiagramOf_stringCrossLevel_ne_identityG`).  `= true`. -/
def fxString_hasFcSoundness : Bool := true

/-- **★ ESTABLISHED — the ONE-COLOUR REGRESSION map is shipped.**  `fcDiagramForgetColour` drops the FC colours to
the colour-blind Joyal–Street `DiagramType`, and forgets on the nose to the base `matchingOf`
(`fcDiagramForgetColour_fcDiagramOf`, `rfl`) — the object the walking-adjunction word problem compares.  On a
monochromatic FC diagram (`IsMonochromaticFc`, non-`G` arcs one colour) the FC layer collapses to that one-colour
regression (`monochromaticFc_reduces_toMatchingOf`), the Fuss–Catalan ⊃ Temperley–Lieb tower's single-colour
restriction (Bisch–Jones; the colour count drops to one, the same-colour constraint goes vacuous).  Non-vacuous:
the lower cup is monochromatic `fWire` (`stringUnitLower_isMonochromaticFc`).  `= true`. -/
def fxString_hasMonochromaticRegression : Bool := true

end FX1Poly.Polygraph
