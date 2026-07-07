import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.MonotoneFaithful
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SaturatedMatchingStaircaseReduction

/-! # mode-3 keystone — the ZIG-ZAG straightens in ARBITRARY VERTICAL CONTEXT (the "partial-overlap wall" tested)

A prior verdict flagged the partial-overlap adjacency (an adjacent cup-cap partner pair — the cap consumes
one wire the cup created, a zig-zag sharing exactly one leg) as a WALL, citing the FREE-level obstructions
`ArcCupCancelObstruction` / `ArcCapCapSwapObstruction`.  Those live over `SpineTraceEquiv` / the free composite,
where the two snake generators cannot be removed (generator count is a free-conversion invariant).

★ **This file MACHINE-CHECKS that the obstruction does NOT transfer to `SaturatedTwoCellConv`.**  Over the
saturated relation the TRIANGLE identity is an available generating move (`SaturatedTwoCellConv.triangleLeft` /
`triangleRight`), so the zig-zag STRAIGHTENS — and, crucially, it straightens not only at the seed but inside an
ARBITRARY VERTICAL CONTEXT, by whiskering the collapse through the vcomp congruences.  The free obstruction is a
free/saturated conflation; at the saturated level the partial-overlap partner pair is exactly the triangle in
context, which re-routes to a through-strand.

  * `zigzagStraightensInVcompContext` — THE MASTER MOVE: any zig-zag `snake : pathG ⟹ pathG` that collapses to
    `id_{pathG}` straightens inside ANY vertical context `pre ⊟ (snake ⊟ post) ≈ pre ⊟ post`.  Proof:
    `vcompCongrLeft` fires the collapse, free `vcompIdLeft` drops the resulting identity, `vcompCongrRight`
    transports under `pre`.
  * `zigzagStraightensPrefix` / `zigzagStraightensSuffix` — the boundary instances (no `pre`, no `post`).
  * `seedLeftSnakeStraightensInContext` / `seedRightSnakeStraightensInContext` — the SEED zig-zag (the minimal
    concrete partial-overlap partner pair) straightens in arbitrary vertical context, fed `triangleLeft` /
    `triangleRight`.
  * `staircaseZigZagStraightensInContext` — the CANONICAL-STAIRCASE zig-zag at ANY block position and ANY width
    straightens in arbitrary vertical context, fed the shipped `staircaseSnakeWhiskeredCollapses`.  So the
    straightening is uniform across the whole staircase alphabet, in context.

Raw Lean 4 + Init; every proof is saturated congruence + `triangleLeft`/`triangleRight` + the free `vcompId`
laws — no cast, no classical, no `sorry`.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The master move: a collapsing zig-zag straightens in arbitrary vertical context -/

/-- ★★ **The MASTER straightening move.**  Any 2-cell `snake : pathG ⟹ pathG` that is saturated-convertible to
the identity `id_{pathG}` (a collapsing zig-zag — the cup-cap partner pair the free system cannot remove)
STRAIGHTENS inside an ARBITRARY vertical context: for any parallel `pre : pathF ⟹ pathG` and `post : pathG ⟹
pathH`, `pre ⊟ (snake ⊟ post) ≈ pre ⊟ post`.  This is the exact refutation of the "partial-overlap wall": the
triangle-collapse fires under the vcomp congruences, so the zig-zag re-routes to a through-strand in place, with
the surrounding context untouched.  Fed `triangleLeft`/`triangleRight` it handles the seed snake; fed
`staircaseSnakeWhiskeredCollapses` it handles the canonical staircase at any block/width. -/
theorem zigzagStraightensInVcompContext {modeA modeB : AdjunctionMode}
    {pathF pathG pathH : ModalityPath adjunctionGraph modeA modeB}
    (snake : RawTwoCellExpr adjunctionModeSignature pathG pathG)
    (collapses : SaturatedTwoCellConv snake
      (RawTwoCellExpr.id (signature := adjunctionModeSignature) pathG))
    (pre : RawTwoCellExpr adjunctionModeSignature pathF pathG)
    (post : RawTwoCellExpr adjunctionModeSignature pathG pathH) :
    SaturatedTwoCellConv
      (RawTwoCellExpr.vcomp pre (RawTwoCellExpr.vcomp snake post))
      (RawTwoCellExpr.vcomp pre post) :=
  SaturatedTwoCellConv.vcompCongrRight pre
    (SaturatedTwoCellConv.trans
      (SaturatedTwoCellConv.vcompCongrLeft post collapses)
      (SaturatedTwoCellConv.ofConv (TwoCellConv.ofStep (TwoCellStep.vcompIdLeft post))))

/-- ★ **Prefix instance** — a collapsing zig-zag at the FRONT straightens: `snake ⊟ post ≈ post`.  The
partial-overlap partner pair leading a spine is removed; the tail is untouched. -/
theorem zigzagStraightensPrefix {modeA modeB : AdjunctionMode}
    {pathG pathH : ModalityPath adjunctionGraph modeA modeB}
    (snake : RawTwoCellExpr adjunctionModeSignature pathG pathG)
    (collapses : SaturatedTwoCellConv snake
      (RawTwoCellExpr.id (signature := adjunctionModeSignature) pathG))
    (post : RawTwoCellExpr adjunctionModeSignature pathG pathH) :
    SaturatedTwoCellConv (RawTwoCellExpr.vcomp snake post) post :=
  SaturatedTwoCellConv.trans
    (SaturatedTwoCellConv.vcompCongrLeft post collapses)
    (SaturatedTwoCellConv.ofConv (TwoCellConv.ofStep (TwoCellStep.vcompIdLeft post)))

/-- ★ **Suffix instance** — a collapsing zig-zag at the END straightens: `pre ⊟ snake ≈ pre`. -/
theorem zigzagStraightensSuffix {modeA modeB : AdjunctionMode}
    {pathF pathG : ModalityPath adjunctionGraph modeA modeB}
    (snake : RawTwoCellExpr adjunctionModeSignature pathG pathG)
    (collapses : SaturatedTwoCellConv snake
      (RawTwoCellExpr.id (signature := adjunctionModeSignature) pathG))
    (pre : RawTwoCellExpr adjunctionModeSignature pathF pathG) :
    SaturatedTwoCellConv (RawTwoCellExpr.vcomp pre snake) pre :=
  SaturatedTwoCellConv.trans
    (SaturatedTwoCellConv.vcompCongrRight pre collapses)
    (SaturatedTwoCellConv.ofConv (TwoCellConv.ofStep (TwoCellStep.vcompIdRight pre)))

/-! ## Step 1 — the MINIMAL concrete zig-zag (the seed snake) straightens -/

/-- ★ **The minimal partial-overlap partner pair straightens — the sanity gate.**  The seed left snake
`(η ▷ L) ⊟ (L ◁ ε)` — a cup then a cap sharing exactly one leg — is `SaturatedTwoCellConv` to its straightened
form `id_L`.  This is `SaturatedTwoCellConv.triangleLeft` verbatim; the concrete witness that the shipped triangle
DOES give the minimal straightening (the free obstruction `adjunctionSeedLeftSnake_not_conv_id` notwithstanding). -/
theorem minimalZigZagStraightens :
    SaturatedTwoCellConv adjunctionSeedLeftSnake
      (RawTwoCellExpr.id (signature := adjunctionModeSignature)
        (singletonModalityPath AdjunctionModality.left)) :=
  SaturatedTwoCellConv.triangleLeft

/-! ## Step 2 — the seed and staircase zig-zags straighten in ARBITRARY vertical context -/

/-- ★ **The SEED left zig-zag straightens in arbitrary vertical context** — `pre ⊟ (leftSnake ⊟ post) ≈
pre ⊟ post` for any surrounding `pre`, `post`.  The master move fed the left triangle. -/
theorem seedLeftSnakeStraightensInContext
    {pathF pathH : ModalityPath adjunctionGraph AdjunctionMode.base AdjunctionMode.tip}
    (pre : RawTwoCellExpr adjunctionModeSignature pathF
      (singletonModalityPath AdjunctionModality.left))
    (post : RawTwoCellExpr adjunctionModeSignature
      (singletonModalityPath AdjunctionModality.left) pathH) :
    SaturatedTwoCellConv
      (RawTwoCellExpr.vcomp pre (RawTwoCellExpr.vcomp adjunctionSeedLeftSnake post))
      (RawTwoCellExpr.vcomp pre post) :=
  zigzagStraightensInVcompContext adjunctionSeedLeftSnake SaturatedTwoCellConv.triangleLeft pre post

/-- ★ **The SEED right zig-zag straightens in arbitrary vertical context** — the dual. -/
theorem seedRightSnakeStraightensInContext
    {pathF pathH : ModalityPath adjunctionGraph AdjunctionMode.tip AdjunctionMode.base}
    (pre : RawTwoCellExpr adjunctionModeSignature pathF
      (singletonModalityPath AdjunctionModality.right))
    (post : RawTwoCellExpr adjunctionModeSignature
      (singletonModalityPath AdjunctionModality.right) pathH) :
    SaturatedTwoCellConv
      (RawTwoCellExpr.vcomp pre (RawTwoCellExpr.vcomp adjunctionSeedRightSnake post))
      (RawTwoCellExpr.vcomp pre post) :=
  zigzagStraightensInVcompContext adjunctionSeedRightSnake SaturatedTwoCellConv.triangleRight pre post

/-- ★ **The CANONICAL-STAIRCASE zig-zag straightens in arbitrary vertical context, at ANY block position and
width.**  The staircase snake — a cup STEP `rawFaceStep 0 (rightBlocks+1)` immediately followed by its matching cap
STEP `rawDegenStep 0 rightBlocks`, whiskered to block position `leftBlocks` — collapses to the whiskered identity
(`staircaseSnakeWhiskeredCollapses`), so it straightens inside any vertical context.  This is the whole staircase
alphabet's zig-zag straightening, in context — exactly the innermost-partner-pair reduction a valley-normalization
driver repeats.  The uniform refutation of the partial-overlap wall across the staircase, not just at the seed. -/
theorem staircaseZigZagStraightensInContext (leftBlocks rightBlocks : Nat)
    {pathF pathH : ModalityPath adjunctionGraph AdjunctionMode.base AdjunctionMode.base}
    (pre : RawTwoCellExpr adjunctionModeSignature pathF
      (composePath (leftRightPow leftBlocks) (leftRightPow (rightBlocks + 1))))
    (post : RawTwoCellExpr adjunctionModeSignature
      (composePath (leftRightPow leftBlocks) (leftRightPow (rightBlocks + 1))) pathH) :
    SaturatedTwoCellConv
      (RawTwoCellExpr.vcomp pre
        (RawTwoCellExpr.vcomp
          (RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature) (leftRightPow leftBlocks)
            (RawTwoCellExpr.vcomp (rawFaceStep 0 (rightBlocks + 1)) (rawDegenStep 0 rightBlocks)))
          post))
      (RawTwoCellExpr.vcomp pre post) :=
  zigzagStraightensInVcompContext _ (staircaseSnakeWhiskeredCollapses leftBlocks rightBlocks) pre post

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the partial-overlap partner pair straightens in ARBITRARY VERTICAL CONTEXT (the "wall" was a
free/saturated conflation).**  `zigzagStraightensInVcompContext` proves that any zig-zag collapsing to the identity
(the cup-cap partner pair the free system cannot remove — the free obstructions `ArcCupCancelObstruction` /
`ArcCapCapSwapObstruction` are over `SpineTraceEquiv`, not `SaturatedTwoCellConv`) re-routes to a through-strand
inside any surrounding `pre ⊟ · ⊟ post`, via the triangle-collapse under the vcomp congruences.  Instantiated at
the SEED (`seedLeftSnakeStraightensInContext` / `…Right`) and across the WHOLE canonical staircase at any block
position and width (`staircaseZigZagStraightensInContext`).  So the saturated TRIANGLE genuinely resolves the
partial overlap; the free obstruction does NOT transfer.  What this marker does NOT yet claim: the TERMINATING
valley-normalization driver that brings a non-adjacent partner pair adjacent (via `saturatedGodementExchange`) and
iterates the straightening to a pure cap-then-cup valley — that is the remaining `MatchingStaircaseReconstructs`
content.  `= true`. -/
def fxMode_hasZigZagStraightensInContext : Bool := true

end FX1Poly.Polygraph
