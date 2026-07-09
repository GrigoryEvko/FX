import FX1Poly.Polygraph.TwoCategory.WalkingString.StringSaturatedConv
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.MatchingDecision

/-! # WalkingString — the TWO-LEVEL (two-colour) matching model + per-triangle soundness

The walking adjunction's saturated 2-cell decision runs through the Joyal–Street boundary MATCHING `matchingOf`
(the `DiagramType`): a free 2-cell is a planar string diagram, a cup opens two wires, a cap closes two, and the
topological type is the boundary partner-matching plus the loop count.  `matchingOf` is signature-POLYMORPHIC —
`stepAtom` reads a generator's arity off `generatorDom.length, generatorCod.length` (`0 ⇒ 2` = cup, `2 ⇒ 0` =
cap), blind to the signature — so it computes on the three-generator walking-adjoint-triple seed with ZERO
modification.  This file builds the TWO-LEVEL refinement and the per-triangle soundness.

## The two-level (two-colour) matching

The adjoint triple's string diagram has cups/caps at TWO levels:

  * **colour 1** — the `F ⊣ G` zig-zags (`η` opens an `F`-wire and a `G`-wire, `ε` closes a `G`-wire and an
    `F`-wire),
  * **colour 2** — the `G ⊣ H` zig-zags (`η'` opens a `G`-wire and an `H`-wire, `ε'` closes an `H`-wire and a
    `G`-wire),

sharing the middle `G`: a `G`-strand can be a leg of a colour-1 cup/cap OR a colour-2 cup/cap.  The two-level
datum is the base `matchingOf` (the boundary partner-matching + loops, colour-BLIND — it computes on the seed for
free) REFINED by the `F`/`G`/`H` label of every boundary port (`ColouredDiagramType`).  A boundary `G`-port is
where the two colours can meet; a `G`-strand opened colour-1 and closed colour-2 is a CROSS-LEVEL wire.

## Per-triangle soundness (the four zig-zag collapses, each `rfl`)

Each of the four triangle identities STRAIGHTENS a zig-zag at its level, and the boundary matching collapses each
snake to its identity ON THE NOSE — `matchingOf stringSnakeF = matchingOf stringIdentityF`, and the three
siblings, all `rfl` (the same phenomenon as the adjunction's `matchingOf_triangleLeft`).  Both `G`-triangles
(`triangleGlo` colour 1 and `triangleGhi` colour 2) collapse to the SAME `matchingOf stringIdentityG`, so the
shared-`G` coupling is matching-sound too.  These four `rfl` collapses ARE the two-level matching's per-level
soundness — the backed, unconditional content this round ships.

## The FULL two-level soundness — UNCONDITIONAL (both cross-level residuals discharged in round 2)

The full soundness (`StringSaturatedTwoCellConv a b → matchingOf a = matchingOf b`) reduces, EXACTLY as the
adjunction's `saturatedConv_matchingOf_eq`, to two named residuals: the union-find Godement INDEPENDENCE
(`godementInvariant`, the `ofFull` input — via the polymorphic `matchingOf_sound_of_godementInvariant`) and the
matching's saturated-CONGRUENCE compositionality (`StringMatchingSaturatedCongruence`, the four congruences).  The
four triangle cases are `rfl`; `refl`/`symm`/`trans` chain.  Round 2 DISCHARGES BOTH residuals unconditionally: the
congruence bundle is proved in `WalkingString/StringMatchingCongruence`
(`stringMatchingSaturatedCongruence_proved`, the colour-blind whisker/vcomp cores ported from the walking
adjunction), and the cross-colour `ofFull` Godement is discharged in `WalkingString/StringMatchingSoundness` by the
shipped cup/cap capstone (`stringSaturatedConv_matchingOf_eq_ofBoundaryDiscipline`, the `godementInvariant` premise
GONE).  The apparent NEW content inside `godementInvariant` — a colour-1 cup/cap horizontally ADJACENT to a colour-2
cup/cap on a SHARED `G`-wire (the `triangleGlo`/`triangleGhi` overlap on the central strand) — is NOT a cross-colour
critical pair: the union-find is colour-BLIND, so cross-colour adjacency is exactly the disjoint-window fragment the
single-colour Godement already commuted (`fxString_hasCrossColourGodementObstruction = false`).  So
`fxString_hasAdjointTripleSoundness` flips `:= true` unconditionally; the assembled term is
`stringSaturatedConv_matchingOf_eq_final` (base) / `stringSaturatedConv_colouredMatchingOf_eq_final` (two-level).

Raw Lean 4 + Init; the collapses are `rfl`, the reduction is induction reusing the polymorphic shipped lemmas.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph

/-! ## Wire labels: the `F` / `G` / `H` colour of a strand -/

/-- The label of a single wire in the two-level string diagram: the modality generator it is a strand of —
`F` (colour-1-only), `G` (the SHARED middle, where the two colours meet), or `H` (colour-2-only). -/
inductive WireLabel where
  /-- The `F = left` strand (belongs to the lower adjunction `F ⊣ G` only). -/
  | fWire
  /-- The `G = right` strand (the SHARED middle — a leg of a colour-1 OR a colour-2 cup/cap). -/
  | gWire
  /-- The `H = coLeft` strand (belongs to the upper adjunction `G ⊣ H` only). -/
  | hWire
deriving DecidableEq

/-- The wire label of a modality generator: `F ↦ fWire`, `G ↦ gWire`, `H ↦ hWire`.  Full-enum match, constant
motive — propext-clean. -/
def wireLabelOfModality {sourceMode targetMode : AdjointTripleMode}
    (modality : AdjointTripleModality sourceMode targetMode) : WireLabel :=
  match modality with
  | AdjointTripleModality.left => WireLabel.fWire
  | AdjointTripleModality.right => WireLabel.gWire
  | AdjointTripleModality.coLeft => WireLabel.hWire

/-- The label sequence of a 1-cell (a modality path): the `F`/`G`/`H` colour of each of its strands, left to
right.  Cons-only structural recursion — propext-clean. -/
def pathLabels {sourceMode targetMode : AdjointTripleMode}
    (path : ModalityPath adjointTripleGraph sourceMode targetMode) : List WireLabel :=
  match path with
  | ModalityPath.nil _ => []
  | ModalityPath.cons modality rest => wireLabelOfModality modality :: pathLabels rest

/-! ## The two-level (two-colour) diagram type -/

/-- ★ The **two-level (two-colour) topological type** of a walking-adjoint-triple 2-cell: the base boundary
matching + loop count (`matchingOf`, colour-blind) REFINED by the `F`/`G`/`H` label of every boundary port.  The
`bottomLabels` are fixed by the source 1-cell, the `topLabels` by the target 1-cell; a `gWire` boundary port is
where the colour-1 and colour-2 matchings can meet.  A flat datum — equality decidable and computing. -/
structure ColouredDiagramType where
  /-- The base boundary partner-matching + loop count (the colour-blind Joyal–Street type). -/
  base : DiagramType
  /-- The `F`/`G`/`H` label of each bottom-boundary port (fixed by the source 1-cell). -/
  bottomLabels : List WireLabel
  /-- The `F`/`G`/`H` label of each top-boundary port (fixed by the target 1-cell). -/
  topLabels : List WireLabel
deriving DecidableEq

/-- ★ The **two-level matching** of a walking-adjoint-triple 2-cell: its base boundary matching, plus the colour
labels of its source and target 1-cells.  Reads the cross-level structure (which ports are `G`-strands the two
colours share). -/
def colouredMatchingOf {sourceMode targetMode : AdjointTripleMode}
    (sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode)
    (cell : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath) : ColouredDiagramType where
  base := matchingOf cell
  bottomLabels := pathLabels sourcePath
  topLabels := pathLabels targetPath

/-! ## Per-triangle soundness at the BASE level (the four zig-zag collapses, each `rfl`) -/

/-- ★★ **The `F` triangle is FREE in the boundary matching** — `matchingOf stringSnakeF = matchingOf
stringIdentityF` (`rfl`).  The colour-1 `F`-snake straightens to a single `F` through-strand. -/
theorem matchingOf_stringTriangleF : matchingOf stringSnakeF = matchingOf stringIdentityF := rfl

/-- ★★ **The lower `G` triangle is FREE in the boundary matching** — `matchingOf stringSnakeGlo = matchingOf
stringIdentityG` (`rfl`).  The colour-1 `G`-snake straightens to a single `G` through-strand. -/
theorem matchingOf_stringTriangleGlo : matchingOf stringSnakeGlo = matchingOf stringIdentityG := rfl

/-- ★★ **The upper `G` triangle is FREE in the boundary matching** — `matchingOf stringSnakeGhi = matchingOf
stringIdentityG` (`rfl`).  The colour-2 `G`-snake straightens to the SAME `G` through-strand as the colour-1 one:
the shared-`G` coupling is matching-sound. -/
theorem matchingOf_stringTriangleGhi : matchingOf stringSnakeGhi = matchingOf stringIdentityG := rfl

/-- ★★ **The `H` triangle is FREE in the boundary matching** — `matchingOf stringSnakeH = matchingOf
stringIdentityH` (`rfl`).  The colour-2 `H`-snake straightens to a single `H` through-strand. -/
theorem matchingOf_stringTriangleH : matchingOf stringSnakeH = matchingOf stringIdentityH := rfl

/-! ## Per-triangle soundness at the TWO-LEVEL level (each `rfl`) -/

/-- ★ **The `F` triangle preserves the TWO-LEVEL matching** (`rfl`) — the base collapses and the boundary labels
(`[F]` both) are unchanged.  The colour-1 `F`-zig-zag is two-level-sound. -/
theorem colouredMatchingOf_stringTriangleF :
    colouredMatchingOf _ _ stringSnakeF = colouredMatchingOf _ _ stringIdentityF := rfl

/-- ★ **The lower `G` triangle preserves the TWO-LEVEL matching** (`rfl`) — boundary labels `[G]`. -/
theorem colouredMatchingOf_stringTriangleGlo :
    colouredMatchingOf _ _ stringSnakeGlo = colouredMatchingOf _ _ stringIdentityG := rfl

/-- ★ **The upper `G` triangle preserves the TWO-LEVEL matching** (`rfl`) — the SAME two-level datum as the lower
`G` triangle (both `[G] ⇒ [G]`, base a `G` through-strand): the shared-`G` coupling is two-level-sound, the
colour-2 straightening agreeing with the colour-1 one. -/
theorem colouredMatchingOf_stringTriangleGhi :
    colouredMatchingOf _ _ stringSnakeGhi = colouredMatchingOf _ _ stringIdentityG := rfl

/-- ★ **The `H` triangle preserves the TWO-LEVEL matching** (`rfl`) — boundary labels `[H]`. -/
theorem colouredMatchingOf_stringTriangleH :
    colouredMatchingOf _ _ stringSnakeH = colouredMatchingOf _ _ stringIdentityH := rfl

/-! ## ★ Non-vacuity: the triangles are GENUINE new relations (saturated but not free) -/

/-- The `F`-snake fires two generators (`η`, `ε`); its identity fires none — so their generator counts differ. -/
theorem stringSnakeF_generatorCount_ne_identity :
    stringSnakeF.generatorCount ≠ stringIdentityF.generatorCount := by decide

/-- ★★ **The `F` triangle is a GENUINE new relation.**  `stringSnakeF` is `StringSaturatedTwoCellConv` to
`stringIdentityF` (the triangle) YET provably NOT `TwoCellConvFull` to it (different generator count — a
`TwoCellConvFull` invariant).  So saturation straightens exactly the colour-1 `F`-zig-zag the free system leaves
standing; the walking adjoint triple's presentation is non-vacuous, not a re-labelling of the free 2-category. -/
theorem stringSnakeF_saturatedButNotFree :
    StringSaturatedTwoCellConv stringSnakeF stringIdentityF
      ∧ ¬ TwoCellConvFull adjointTripleModeSignature stringSnakeF stringIdentityF :=
  ⟨StringSaturatedTwoCellConv.triangleF,
    TwoCellConvFull.not_of_generatorCount_ne stringSnakeF_generatorCount_ne_identity⟩

/-! ## ★ Non-vacuity: a genuine CROSS-LEVEL cell (in neither single adjunction) -/

/-- ★ The **cross-level cell** `G·F ⇒ G·H`: the lower counit `ε` (colour 1) vertically composed with the upper
unit `η'` (colour 2), meeting on the shared `G`.  Its source `G·F` mentions `F` (only in `F ⊣ G`) and its target
`G·H` mentions `H` (only in `G ⊣ H`), so this cell lives in the sub-presentation of NEITHER single adjunction —
it is the walking realisation of the adjoint-string comparison map through the shared middle `G`. -/
def stringCrossLevelCell : RawTwoCellExpr adjointTripleModeSignature stringGF stringGH :=
  RawTwoCellExpr.vcomp stringCounitLower stringUnitUpper

/-- The cross-level cell fires exactly two generators — one colour-1 atom (`ε`) and one colour-2 atom (`η'`). -/
theorem stringCrossLevel_generatorCount : stringCrossLevelCell.generatorCount = 2 := rfl

/-- The source and target label sequences of the cross-level cell — `[G, F]` (colour 1's `F`) and `[G, H]`
(colour 2's `H`), each sharing the leading `G`.  The two-level model READS both colours off one cell. -/
theorem stringGF_stringGH_labels :
    pathLabels stringGF = [WireLabel.gWire, WireLabel.fWire]
      ∧ pathLabels stringGH = [WireLabel.gWire, WireLabel.hWire] :=
  ⟨rfl, rfl⟩

/-- ★★ **The cross-level cell is read by the two-level matching, and mentions BOTH colours.**  Its
`colouredMatchingOf` has `bottomLabels = [G, F]` (the colour-1 `F`) and `topLabels = [G, H]` (the colour-2 `H`) —
so it is a genuine cross-level cell, distinct from anything in either single adjunction (which never sees the
other colour's generator).  The base matching computes too: two boundary caps/cups across the shared `G`. -/
theorem stringCrossLevel_colouredMatchingOf :
    colouredMatchingOf stringGF stringGH stringCrossLevelCell
      = { base := { bottomCount := 2, topCount := 2, partner := [1, 0, 3, 2], loops := 0 },
          bottomLabels := [WireLabel.gWire, WireLabel.fWire],
          topLabels := [WireLabel.gWire, WireLabel.hWire] } := rfl

/-! ## The saturated-congruence compositionality bundle (the second soundness residual) -/

/-- The two-level matching's invariance under the four SATURATED CONGRUENCE constructors, bundled — the second
soundness residual (the first being `godementInvariant`).  Each field is a compositionality of the boundary
matching (stacking / whiskering a sub-cell with a fixed context depends on the sub-cell only through its
matching); the string analog of the adjunction's `MatchingSaturatedCongruence`, at the three-generator seed. -/
structure StringMatchingSaturatedCongruence : Prop where
  /-- Compositionality under the LEFT factor of a vertical composite. -/
  vcompLeft : {sourceMode targetMode : AdjointTripleMode} →
    {oneCellF oneCellG oneCellH : ModalityPath adjointTripleGraph sourceMode targetMode} →
    {cellAlpha cellAlpha' : RawTwoCellExpr adjointTripleModeSignature oneCellF oneCellG} →
    (cellBeta : RawTwoCellExpr adjointTripleModeSignature oneCellG oneCellH) →
    matchingOf cellAlpha = matchingOf cellAlpha' →
    matchingOf (RawTwoCellExpr.vcomp cellAlpha cellBeta) = matchingOf (RawTwoCellExpr.vcomp cellAlpha' cellBeta)
  /-- Compositionality under the RIGHT factor of a vertical composite. -/
  vcompRight : {sourceMode targetMode : AdjointTripleMode} →
    {oneCellF oneCellG oneCellH : ModalityPath adjointTripleGraph sourceMode targetMode} →
    (cellAlpha : RawTwoCellExpr adjointTripleModeSignature oneCellF oneCellG) →
    {cellBeta cellBeta' : RawTwoCellExpr adjointTripleModeSignature oneCellG oneCellH} →
    matchingOf cellBeta = matchingOf cellBeta' →
    matchingOf (RawTwoCellExpr.vcomp cellAlpha cellBeta) = matchingOf (RawTwoCellExpr.vcomp cellAlpha cellBeta')
  /-- Compositionality under a LEFT whiskering. -/
  whiskerLeft : {sourceMode middleMode targetMode : AdjointTripleMode} →
    (oneCell : ModalityPath adjointTripleGraph sourceMode middleMode) →
    {oneCellG oneCellH : ModalityPath adjointTripleGraph middleMode targetMode} →
    {cellBeta cellBeta' : RawTwoCellExpr adjointTripleModeSignature oneCellG oneCellH} →
    matchingOf cellBeta = matchingOf cellBeta' →
    matchingOf (RawTwoCellExpr.whiskerLeft oneCell cellBeta)
      = matchingOf (RawTwoCellExpr.whiskerLeft oneCell cellBeta')
  /-- Compositionality under a RIGHT whiskering. -/
  whiskerRight : {sourceMode middleMode targetMode : AdjointTripleMode} →
    {oneCellF oneCellG : ModalityPath adjointTripleGraph sourceMode middleMode} →
    (oneCell : ModalityPath adjointTripleGraph middleMode targetMode) →
    {cellAlpha cellAlpha' : RawTwoCellExpr adjointTripleModeSignature oneCellF oneCellG} →
    matchingOf cellAlpha = matchingOf cellAlpha' →
    matchingOf (RawTwoCellExpr.whiskerRight oneCell cellAlpha)
      = matchingOf (RawTwoCellExpr.whiskerRight oneCell cellAlpha')

/-! ## ★ The FULL two-level soundness, reduced to exactly two named residuals -/

/-- ★ **The SOUNDNESS direction, proven modulo the two named residuals.**  Given the union-find Godement
INDEPENDENCE (`godementInvariant`, the `ofFull` input, via the polymorphic `matchingOf_sound_of_godementInvariant`)
and the two-level matching's saturated-congruence COMPOSITIONALITY (`congruence`), the base boundary matching
`matchingOf` is invariant under the COMPLETE `StringSaturatedTwoCellConv` — the FOUR triangle cases ON THE NOSE
(`matchingOf_stringTriangle{F,Glo,Ghi,H}`, `rfl`), the congruences by `congruence`, the structural / whisker /
interchange laws through `matchingOf_sound_of_godementInvariant`, and `refl`/`symm`/`trans` chained.  The genuine
NEW content — the cross-colour transposition on the shared `G` — is confined to `godementInvariant` at the
three-generator seed (see `fxString_hasAdjointTripleSoundness`). -/
theorem stringSaturatedConv_matchingOf_eq
    (godementInvariant : ∀ {overallSource overallTarget : AdjointTripleMode} (bottomCount : Nat)
        (state : WireState)
        {firstList secondList : List (SpineAtom adjointTripleModeSignature overallSource overallTarget)},
        SpineGodementStep adjointTripleModeSignature firstList secondList →
        extractAfterProcessing bottomCount state firstList = extractAfterProcessing bottomCount state secondList)
    (congruence : StringMatchingSaturatedCongruence)
    {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    {cellA cellB : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath}
    (conv : StringSaturatedTwoCellConv cellA cellB) : matchingOf cellA = matchingOf cellB := by
  induction conv with
  | ofFull convFull => exact matchingOf_sound_of_godementInvariant godementInvariant convFull
  | triangleF => exact matchingOf_stringTriangleF
  | triangleGlo => exact matchingOf_stringTriangleGlo
  | triangleGhi => exact matchingOf_stringTriangleGhi
  | triangleH => exact matchingOf_stringTriangleH
  | vcompCongrLeft cellBeta _ inductionHypothesis => exact congruence.vcompLeft cellBeta inductionHypothesis
  | vcompCongrRight cellAlpha _ inductionHypothesis => exact congruence.vcompRight cellAlpha inductionHypothesis
  | whiskerLeftCongr oneCell _ inductionHypothesis => exact congruence.whiskerLeft oneCell inductionHypothesis
  | whiskerRightCongr oneCell _ inductionHypothesis => exact congruence.whiskerRight oneCell inductionHypothesis
  | refl _ => rfl
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ firstHypothesis secondHypothesis => exact firstHypothesis.trans secondHypothesis

/-- ★ **The FULL two-level soundness lifts to `colouredMatchingOf`.**  Saturated-convertible cells have the SAME
boundary matching (`stringSaturatedConv_matchingOf_eq`, modulo the two residuals) AND identical boundary labels
(same source / target 1-cells), so their two-level matchings agree — the two-colour datum is sound wherever the
base is. -/
theorem stringSaturatedConv_colouredMatchingOf_eq
    (godementInvariant : ∀ {overallSource overallTarget : AdjointTripleMode} (bottomCount : Nat)
        (state : WireState)
        {firstList secondList : List (SpineAtom adjointTripleModeSignature overallSource overallTarget)},
        SpineGodementStep adjointTripleModeSignature firstList secondList →
        extractAfterProcessing bottomCount state firstList = extractAfterProcessing bottomCount state secondList)
    (congruence : StringMatchingSaturatedCongruence)
    {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    {cellA cellB : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath}
    (conv : StringSaturatedTwoCellConv cellA cellB) :
    colouredMatchingOf sourcePath targetPath cellA = colouredMatchingOf sourcePath targetPath cellB := by
  dsimp only [colouredMatchingOf]
  rw [stringSaturatedConv_matchingOf_eq godementInvariant congruence conv]

/-! ## Honesty markers -/

/-- **★ ESTABLISHED — the TWO-LEVEL (two-colour) matching model is shipped.**  `colouredMatchingOf` refines the
polymorphic Joyal–Street boundary matching `matchingOf` (colour-blind, computing on the three-generator seed for
free) by the `F`/`G`/`H` label of every boundary port (`pathLabels`).  It genuinely reads cross-level structure:
the cross-level cell `G·F ⇒ G·H` (`stringCrossLevelCell`, in NEITHER single adjunction) has `bottomLabels = [G,F]`
and `topLabels = [G,H]` (`stringCrossLevel_colouredMatchingOf`), mentioning BOTH colours.  `= true`. -/
def fxString_hasTwoLevelMatchingModel : Bool := true

/-- **★ ESTABLISHED — the PER-LEVEL (per-triangle) matching soundness is backed, unconditional.**  Each of the
four triangle identities preserves the two-level matching ON THE NOSE: at the base level
`matchingOf_stringTriangle{F,Glo,Ghi,H}` (`rfl`) and at the two-level level
`colouredMatchingOf_stringTriangle{F,Glo,Ghi,H}` (`rfl`).  The two `G`-triangles (colour 1 and colour 2) collapse
to the SAME `matchingOf stringIdentityG`, so the shared-`G` coupling is matching-sound.  The triangles are GENUINE
new relations, not free (`stringSnakeF_saturatedButNotFree`: saturated-convertible to the identity yet NOT
`TwoCellConvFull` to it, by generator count).  This is the per-level zig-zag-collapse soundness the round ships
unconditionally.  `= true`. -/
def fxString_hasPerLevelTriangleMatchingSoundness : Bool := true

/-- **★ ESTABLISHED — the FULL two-level soundness is UNCONDITIONAL; the cross-colour Godement is DISCHARGED.**
`stringSaturatedConv_matchingOf_eq` (this file) proves `matchingOf` invariant under the COMPLETE
`StringSaturatedTwoCellConv` GIVEN two premises: (1) the union-find Godement INDEPENDENCE `godementInvariant` (the
`ofFull` input) and (2) the compositionality bundle `StringMatchingSaturatedCongruence`.  Round 2 DISCHARGES
both, in `WalkingString/StringMatchingCongruence` and `WalkingString/StringMatchingSoundness`:

  * the congruence bundle is PROVED (`stringMatchingSaturatedCongruence_proved`) — the whisker/vcomp `matchingOf`
    cores are signature-POLYMORPHIC and colour-BLIND, so the walking-adjunction machinery ports to the
    three-generator seed by swapping the discipline witness (`cellHasCupCapGenerators_ofStringSignature`);
  * the cross-colour `ofFull` Godement is DISCHARGED (`stringSaturatedConv_matchingOf_eq_ofBoundaryDiscipline`,
    `godementInvariant` premise GONE) by the shipped cup/cap capstone `matchingOf_sound_ofCupCapCells_allBoundaries`.

★ **The cross-level residual is NOT a coupling obstruction.**  The Godement transposition of a colour-1 cup/cap
adjacent to a colour-2 cup/cap on the SHARED `G`-wire (the `triangleGlo` / `triangleGhi` overlap) is, at the
colour-BLIND union-find, exactly the disjoint-window cup/cap fragment the single-colour Godement already
commuted — the shared `G` couples the colours only at the LABEL level (`pathLabels`), invisible to the
connectivity model, so no cross-colour critical pair exists
(`fxString_hasCrossColourGodementObstruction = false`).  The assembled unconditional soundness is
`stringSaturatedConv_matchingOf_eq_final` (base) / `stringSaturatedConv_colouredMatchingOf_eq_final` (two-level).
Non-vacuous: the two distinct `G`-snakes are identified (`stringSnakeGlo_colouredMatchingOf_eq_stringSnakeGhi`)
while the cross-level cell `G·F ⇒ G·H` stays distinguished from `id_G`
(`stringCrossLevel_colouredMatchingOf_ne_identityG`).  `= true`. -/
def fxString_hasAdjointTripleSoundness : Bool := true

end FX1Poly.Polygraph
