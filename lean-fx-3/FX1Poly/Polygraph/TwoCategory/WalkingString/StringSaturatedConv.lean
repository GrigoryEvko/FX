import FX1Poly.Polygraph.TwoCategory.WalkingString.StringSeed
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.WhiskerFunctoriality

/-! # WalkingString — the SATURATED walking-adjoint-triple 2-cell convertibility (the FOUR triangle identities)

The walking-adjoint-triple seed (`StringSeed`) posits two units and two counits as 2-cell GENERATORS; the adjoint
triple `F ⊣ G ⊣ H` is those generators SUBJECT to FOUR triangle identities — TWO per adjunction:

  * `F ⊣ G` (colour 1) contributes the two snakes on `F` and on `G`,
  * `G ⊣ H` (colour 2) contributes the two snakes on `G` and on `H`.

This file ships the SATURATED 2-cell convertibility of the seed: the completed free-strict-2-category
convertibility (`TwoCellConvFull`, embedded by `ofFull`) augmented with the FOUR triangle identities as generating
equations, made a genuine congruence by the four one-hole congruence closures plus `refl` / `symm` / `trans`.  It
is the walking adjoint triple's analog of the adjunction's `SaturatedTwoCellConv` (TWO triangles) and the walking
monad's `MonadSaturatedTwoCellConv` (three monad laws) — the free 2-category on `F ⊣ G ⊣ H`.

## The four triangle identities (each adjunction contributes two)

  * **`triangleF`**   `(η ▷ F) ⊟ (F ◁ ε)   ≈ id_F`  — the `F ⊣ G` snake on `F`  (colour 1).
  * **`triangleGlo`** `(G ◁ η) ⊟ (ε ▷ G)   ≈ id_G`  — the `F ⊣ G` snake on `G`  (colour 1).
  * **`triangleGhi`** `(η' ▷ G) ⊟ (G ◁ ε') ≈ id_G`  — the `G ⊣ H` snake on `G`  (colour 2).
  * **`triangleH`**   `(H ◁ η') ⊟ (ε' ▷ H) ≈ id_H`  — the `G ⊣ H` snake on `H`  (colour 2).

## ★ The genuine cross-level coupling (not two disjoint adjunctions)

The central 1-cell `G` is straightened by TWO DIFFERENT triangles — `triangleGlo` (colour 1, via `η`/`ε`) and
`triangleGhi` (colour 2, via `η'`/`ε'`).  Both have boundary `G ⇒ G`, so the two SYNTACTICALLY DISTINCT snakes
`stringSnakeGlo` and `stringSnakeGhi` are BOTH saturated-convertible to `id_G`, hence to EACH OTHER — a coherence
`stringSnakeGlo ≈ id_G ≈ stringSnakeGhi` expressible in NEITHER single adjunction (`F ⊣ G` has no `η'`/`ε'`;
`G ⊣ H` has no `η`/`ε`).  `stringSnakeGlo_conv_stringSnakeGhi` witnesses it.

Raw Lean 4 + Init; the relation is an inductive `Prop`, its witnesses are constructors, so every declaration is
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free.  Per-declaration `#assert_no_axioms`
gated in the audit twin. -/

namespace FX1Poly.Polygraph

/-! ## The generators embedded as free 2-cells -/

/-- The lower unit `η : id_base ⇒ F·G` embedded as a free 2-cell (the lower CUP). -/
def stringUnitLower :
    RawTwoCellExpr adjointTripleModeSignature
      (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base) stringFG :=
  RawTwoCellExpr.gen StringTwoCell.unitLower

/-- The lower counit `ε : G·F ⇒ id_tip` embedded as a free 2-cell (the lower CAP). -/
def stringCounitLower :
    RawTwoCellExpr adjointTripleModeSignature stringGF
      (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip) :=
  RawTwoCellExpr.gen StringTwoCell.counitLower

/-- The upper unit `η' : id_tip ⇒ G·H` embedded as a free 2-cell (the upper CUP). -/
def stringUnitUpper :
    RawTwoCellExpr adjointTripleModeSignature
      (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip) stringGH :=
  RawTwoCellExpr.gen StringTwoCell.unitUpper

/-- The upper counit `ε' : H·G ⇒ id_base` embedded as a free 2-cell (the upper CAP). -/
def stringCounitUpper :
    RawTwoCellExpr adjointTripleModeSignature stringHG
      (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base) :=
  RawTwoCellExpr.gen StringTwoCell.counitUpper

/-! ## The four identity 2-cells the triangles straighten the snakes to -/

/-- The identity 2-cell on `F` — the RHS of `triangleF`. -/
def stringIdentityF :
    RawTwoCellExpr adjointTripleModeSignature
      (singletonModalityPath AdjointTripleModality.left) (singletonModalityPath AdjointTripleModality.left) :=
  RawTwoCellExpr.id (signature := adjointTripleModeSignature) (singletonModalityPath AdjointTripleModality.left)

/-- The identity 2-cell on `G` — the RHS of BOTH `triangleGlo` and `triangleGhi` (the shared-`G` coherence). -/
def stringIdentityG :
    RawTwoCellExpr adjointTripleModeSignature
      (singletonModalityPath AdjointTripleModality.right) (singletonModalityPath AdjointTripleModality.right) :=
  RawTwoCellExpr.id (signature := adjointTripleModeSignature) (singletonModalityPath AdjointTripleModality.right)

/-- The identity 2-cell on `H` — the RHS of `triangleH`. -/
def stringIdentityH :
    RawTwoCellExpr adjointTripleModeSignature
      (singletonModalityPath AdjointTripleModality.coLeft) (singletonModalityPath AdjointTripleModality.coLeft) :=
  RawTwoCellExpr.id (signature := adjointTripleModeSignature) (singletonModalityPath AdjointTripleModality.coLeft)

/-! ## The four snakes (zig-zags) -/

/-- The **`F`-snake** of the lower adjunction: `(η ▷ F) ⊟ (F ◁ ε) : F ⇒ F` — the unit whiskered on the right by
`F`, then the counit whiskered on the left by `F`.  `triangleF` asserts it is `id_F`. -/
def stringSnakeF :
    RawTwoCellExpr adjointTripleModeSignature
      (singletonModalityPath AdjointTripleModality.left) (singletonModalityPath AdjointTripleModality.left) :=
  RawTwoCellExpr.vcomp
    (RawTwoCellExpr.whiskerRight (signature := adjointTripleModeSignature)
      (singletonModalityPath AdjointTripleModality.left) stringUnitLower)
    (RawTwoCellExpr.whiskerLeft (signature := adjointTripleModeSignature)
      (singletonModalityPath AdjointTripleModality.left) stringCounitLower)

/-- The **lower `G`-snake** (colour 1): `(G ◁ η) ⊟ (ε ▷ G) : G ⇒ G` — the `F ⊣ G` snake on the shared `G`.
`triangleGlo` asserts it is `id_G`. -/
def stringSnakeGlo :
    RawTwoCellExpr adjointTripleModeSignature
      (singletonModalityPath AdjointTripleModality.right) (singletonModalityPath AdjointTripleModality.right) :=
  RawTwoCellExpr.vcomp
    (RawTwoCellExpr.whiskerLeft (signature := adjointTripleModeSignature)
      (singletonModalityPath AdjointTripleModality.right) stringUnitLower)
    (RawTwoCellExpr.whiskerRight (signature := adjointTripleModeSignature)
      (singletonModalityPath AdjointTripleModality.right) stringCounitLower)

/-- The **upper `G`-snake** (colour 2): `(η' ▷ G) ⊟ (G ◁ ε') : G ⇒ G` — the `G ⊣ H` snake on the shared `G`.
`triangleGhi` asserts it is `id_G`.  DISTINCT from `stringSnakeGlo` (different generators), same boundary `G ⇒ G`
— the shared-`G` coupling. -/
def stringSnakeGhi :
    RawTwoCellExpr adjointTripleModeSignature
      (singletonModalityPath AdjointTripleModality.right) (singletonModalityPath AdjointTripleModality.right) :=
  RawTwoCellExpr.vcomp
    (RawTwoCellExpr.whiskerRight (signature := adjointTripleModeSignature)
      (singletonModalityPath AdjointTripleModality.right) stringUnitUpper)
    (RawTwoCellExpr.whiskerLeft (signature := adjointTripleModeSignature)
      (singletonModalityPath AdjointTripleModality.right) stringCounitUpper)

/-- The **`H`-snake** of the upper adjunction: `(H ◁ η') ⊟ (ε' ▷ H) : H ⇒ H`.  `triangleH` asserts it is `id_H`. -/
def stringSnakeH :
    RawTwoCellExpr adjointTripleModeSignature
      (singletonModalityPath AdjointTripleModality.coLeft) (singletonModalityPath AdjointTripleModality.coLeft) :=
  RawTwoCellExpr.vcomp
    (RawTwoCellExpr.whiskerLeft (signature := adjointTripleModeSignature)
      (singletonModalityPath AdjointTripleModality.coLeft) stringUnitUpper)
    (RawTwoCellExpr.whiskerRight (signature := adjointTripleModeSignature)
      (singletonModalityPath AdjointTripleModality.coLeft) stringCounitUpper)

/-! ## The saturated 2-cell convertibility -/

/-- ★ The **saturated 2-cell convertibility** of the walking adjoint triple `F ⊣ G ⊣ H`: the completed
free-strict-2-category convertibility (`TwoCellConvFull`, embedded by `ofFull`) augmented with the FOUR triangle
identities (two per adjunction) as generating equations, closed under the four one-hole congruences and
`refl`/`symm`/`trans` into a genuine congruence.  Two free 2-cells are equal AS 2-cells of the walking adjoint
triple exactly when they are `StringSaturatedTwoCellConv`-related. -/
inductive StringSaturatedTwoCellConv :
    {sourceMode targetMode : AdjointTripleMode} →
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode} →
    RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath →
    RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath → Prop where
  /-- Embed the completed free-strict-2-category convertibility (structural laws + interchange + whisker
  functoriality + disjoint-whisker exchange + congruence closure). -/
  | ofFull {sourceMode targetMode : AdjointTripleMode}
      {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
      {cellAlpha cellBeta : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath} :
      TwoCellConvFull adjointTripleModeSignature cellAlpha cellBeta →
      StringSaturatedTwoCellConv cellAlpha cellBeta
  /-- The **`F` triangle** `(η ▷ F) ⊟ (F ◁ ε) ≈ id_F` (colour 1, `F ⊣ G`). -/
  | triangleF : StringSaturatedTwoCellConv stringSnakeF stringIdentityF
  /-- The **lower `G` triangle** `(G ◁ η) ⊟ (ε ▷ G) ≈ id_G` (colour 1, `F ⊣ G`). -/
  | triangleGlo : StringSaturatedTwoCellConv stringSnakeGlo stringIdentityG
  /-- The **upper `G` triangle** `(η' ▷ G) ⊟ (G ◁ ε') ≈ id_G` (colour 2, `G ⊣ H`) — straightens the SHARED `G`
  by the OTHER adjunction. -/
  | triangleGhi : StringSaturatedTwoCellConv stringSnakeGhi stringIdentityG
  /-- The **`H` triangle** `(H ◁ η') ⊟ (ε' ▷ H) ≈ id_H` (colour 2, `G ⊣ H`). -/
  | triangleH : StringSaturatedTwoCellConv stringSnakeH stringIdentityH
  /-- Congruence in the LEFT factor of a vertical composite. -/
  | vcompCongrLeft {sourceMode targetMode : AdjointTripleMode}
      {oneCellF oneCellG oneCellH : ModalityPath adjointTripleGraph sourceMode targetMode}
      {cellAlpha cellAlpha' : RawTwoCellExpr adjointTripleModeSignature oneCellF oneCellG}
      (cellBeta : RawTwoCellExpr adjointTripleModeSignature oneCellG oneCellH) :
      StringSaturatedTwoCellConv cellAlpha cellAlpha' →
      StringSaturatedTwoCellConv (RawTwoCellExpr.vcomp cellAlpha cellBeta)
        (RawTwoCellExpr.vcomp cellAlpha' cellBeta)
  /-- Congruence in the RIGHT factor of a vertical composite. -/
  | vcompCongrRight {sourceMode targetMode : AdjointTripleMode}
      {oneCellF oneCellG oneCellH : ModalityPath adjointTripleGraph sourceMode targetMode}
      (cellAlpha : RawTwoCellExpr adjointTripleModeSignature oneCellF oneCellG)
      {cellBeta cellBeta' : RawTwoCellExpr adjointTripleModeSignature oneCellG oneCellH} :
      StringSaturatedTwoCellConv cellBeta cellBeta' →
      StringSaturatedTwoCellConv (RawTwoCellExpr.vcomp cellAlpha cellBeta)
        (RawTwoCellExpr.vcomp cellAlpha cellBeta')
  /-- Congruence under a left whiskering (so a triangle fires whiskered by a 1-cell). -/
  | whiskerLeftCongr {sourceMode middleMode targetMode : AdjointTripleMode}
      (oneCell : ModalityPath adjointTripleGraph sourceMode middleMode)
      {oneCellG oneCellH : ModalityPath adjointTripleGraph middleMode targetMode}
      {cellBeta cellBeta' : RawTwoCellExpr adjointTripleModeSignature oneCellG oneCellH} :
      StringSaturatedTwoCellConv cellBeta cellBeta' →
      StringSaturatedTwoCellConv (RawTwoCellExpr.whiskerLeft oneCell cellBeta)
        (RawTwoCellExpr.whiskerLeft oneCell cellBeta')
  /-- Congruence under a right whiskering. -/
  | whiskerRightCongr {sourceMode middleMode targetMode : AdjointTripleMode}
      {oneCellF oneCellG : ModalityPath adjointTripleGraph sourceMode middleMode}
      (oneCell : ModalityPath adjointTripleGraph middleMode targetMode)
      {cellAlpha cellAlpha' : RawTwoCellExpr adjointTripleModeSignature oneCellF oneCellG} :
      StringSaturatedTwoCellConv cellAlpha cellAlpha' →
      StringSaturatedTwoCellConv (RawTwoCellExpr.whiskerRight oneCell cellAlpha)
        (RawTwoCellExpr.whiskerRight oneCell cellAlpha')
  /-- Reflexivity. -/
  | refl {sourceMode targetMode : AdjointTripleMode}
      {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
      (cell : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath) :
      StringSaturatedTwoCellConv cell cell
  /-- Symmetry. -/
  | symm {sourceMode targetMode : AdjointTripleMode}
      {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
      {cellAlpha cellBeta : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath} :
      StringSaturatedTwoCellConv cellAlpha cellBeta → StringSaturatedTwoCellConv cellBeta cellAlpha
  /-- Transitivity. -/
  | trans {sourceMode targetMode : AdjointTripleMode}
      {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
      {cellAlpha cellBeta cellGamma : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath} :
      StringSaturatedTwoCellConv cellAlpha cellBeta → StringSaturatedTwoCellConv cellBeta cellGamma →
      StringSaturatedTwoCellConv cellAlpha cellGamma

/-! ## Embeddings: every free-system convertibility lifts to the saturated relation -/

/-- The free `TwoCellConv` (structural laws + interchange) lifts to the saturated relation. -/
theorem StringSaturatedTwoCellConv.ofConv {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath}
    (conv : TwoCellConv adjointTripleModeSignature cellAlpha cellBeta) :
    StringSaturatedTwoCellConv cellAlpha cellBeta :=
  StringSaturatedTwoCellConv.ofFull (TwoCellConvFull.ofConv conv)

/-! ## The four triangle-identity witnesses (the saturation-flag content) -/

/-- ★ **The `F` triangle holds in the saturated relation** — `(η ▷ F) ⊟ (F ◁ ε) ≈ id_F` (colour 1). -/
theorem stringTriangleFHolds : StringSaturatedTwoCellConv stringSnakeF stringIdentityF :=
  StringSaturatedTwoCellConv.triangleF

/-- ★ **The lower `G` triangle holds** — `(G ◁ η) ⊟ (ε ▷ G) ≈ id_G` (colour 1). -/
theorem stringTriangleGloHolds : StringSaturatedTwoCellConv stringSnakeGlo stringIdentityG :=
  StringSaturatedTwoCellConv.triangleGlo

/-- ★ **The upper `G` triangle holds** — `(η' ▷ G) ⊟ (G ◁ ε') ≈ id_G` (colour 2). -/
theorem stringTriangleGhiHolds : StringSaturatedTwoCellConv stringSnakeGhi stringIdentityG :=
  StringSaturatedTwoCellConv.triangleGhi

/-- ★ **The `H` triangle holds** — `(H ◁ η') ⊟ (ε' ▷ H) ≈ id_H` (colour 2). -/
theorem stringTriangleHHolds : StringSaturatedTwoCellConv stringSnakeH stringIdentityH :=
  StringSaturatedTwoCellConv.triangleH

/-! ## ★ The cross-level coupling on the shared `G` (not two disjoint adjunctions) -/

/-- ★★ **The shared-`G` coherence.**  The two SYNTACTICALLY DISTINCT `G ⇒ G` snakes — `stringSnakeGlo` (colour 1,
via the lower adjunction's `η`/`ε`) and `stringSnakeGhi` (colour 2, via the upper adjunction's `η'`/`ε'`) — are
saturated-convertible to EACH OTHER, both collapsing to `id_G`.  This coherence lives in NEITHER single adjunction
(`F ⊣ G` lacks `η'`/`ε'`, `G ⊣ H` lacks `η`/`ε`); it is the genuine cross-level interaction the shared middle `G`
creates, so the walking adjoint triple is NOT two disjoint copies of the walking adjunction. -/
theorem stringSnakeGlo_conv_stringSnakeGhi :
    StringSaturatedTwoCellConv stringSnakeGlo stringSnakeGhi :=
  StringSaturatedTwoCellConv.trans StringSaturatedTwoCellConv.triangleGlo
    (StringSaturatedTwoCellConv.symm StringSaturatedTwoCellConv.triangleGhi)

/-- Smoke: the `F` triangle fires UNDER a right-whisker context — `(η ▷ F) ⊟ (F ◁ ε) ▷ G ≈ id_F ▷ G` — exercising
the congruence closure together with a triangle generator (a genuine congruence, the whiskered triangle). -/
theorem stringTriangleFWhiskeredHolds :
    StringSaturatedTwoCellConv
      (RawTwoCellExpr.whiskerRight (signature := adjointTripleModeSignature)
        (singletonModalityPath AdjointTripleModality.right) stringSnakeF)
      (RawTwoCellExpr.whiskerRight (signature := adjointTripleModeSignature)
        (singletonModalityPath AdjointTripleModality.right) stringIdentityF) :=
  StringSaturatedTwoCellConv.whiskerRightCongr _ StringSaturatedTwoCellConv.triangleF

/-! ## Honesty markers -/

/-- **ESTABLISHED.**  The SATURATED walking-adjoint-triple 2-cell convertibility
(`StringSaturatedTwoCellConv`) — the completed free-strict-2-category convertibility plus the FOUR triangle
identities (two per adjunction, `F ⊣ G` and `G ⊣ H`) as a congruence — is shipped, and all four triangles hold
(`stringTriangleFHolds` / `stringTriangleGloHolds` / `stringTriangleGhiHolds` / `stringTriangleHHolds`).  The
shared-`G` coupling is genuine: the two distinct `G ⇒ G` snakes are convertible to each other
(`stringSnakeGlo_conv_stringSnakeGhi`) through `id_G`, a coherence in NEITHER single adjunction.  `= true`. -/
def fxString_hasAdjointTripleSaturatedConvRelation : Bool := true

end FX1Poly.Polygraph
