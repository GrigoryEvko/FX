import FX1Poly.Polygraph.TwoCategory.WalkingCohesion.CohesionNonThinness

/-! # WalkingCohesion/CohesionInvariantModel — per-boundary boundedness REFUTED: the unit hom `id ⇒ shape` is INFINITE

r1 shipped the presentation + saturated congruence + the thin per-modality fragment, walling the FULL decision on
cross-modality thinness.  r2 REFUTED thinness itself: a sound `ℤ/2`-parity invariant (`cohesionParity`) separates
the shape monad unit from the lower-adjunction route at the hom `id ⇒ shape`, so the free walker is provably not
locally posetal.  r2's Bool invariant proves the hom has AT LEAST TWO convertibility classes.

This r3 lane asks the boundedness question the r2 refutation left open: is the walker decidable WITHOUT thinness,
via BOUNDEDLY-many per-boundary representatives?  The answer is a decisive **NO** — the same seam r2 found is
BOTTOMLESS.  We ship the fuller invariant (a `ℤ`-valued FLAT DEGREE refining r2's Bool parity), an explicit
PUMP FAMILY realizing every degree on the FIXED boundary `id ⇒ shape`, and hence an injection `ℕ ↪ (Hom id⇒shape /
conv)`: the hom has INFINITELY many convertibility classes.  Per-boundary boundedness is REFUTED, decisively, one
level up from r2's thinness refutation.

## The fuller invariant: the `ℤ` flat degree `#flatCounit − #flatComul`

The `ℤ`-linear "count generators, whisker-transparent" functional `cohesionFlatDegree := #flatCounit − #flatComul`
is a SOUND congruence invariant: the only saturation laws touching `flatCounit`/`flatComul` are the flat
comonad's counit laws (which pair one of each — `flatComul` then `flatCounit`, degree `(−1) + 1 = 0 = id`),
coassociativity (two `flatComul` each side), and flat idempotence (one `flatCounit` each side) — all balanced;
every non-flat law weighs `0`.  r2's `genParity` is precisely this degree taken mod 2.

Because `Int.add_assoc` / `Int.add_comm` / `Int.zero_add` LEAK `propext` in Lean core (only `Int.add_zero` is
clean), we do NOT fold into `Int`.  Instead we realize the difference `#flatCounit − #flatComul` as a two-count
BALANCE on `Nat` (whose `add_assoc` / `add_comm` / `add_left_comm` / `zero_add` are all `propext`-free):
`cohesionFlatBalanced α β := #flatCounit α + #flatComul β = #flatCounit β + #flatComul α`, i.e. the `Nat` cross-form
of "the two integer degrees are equal".  Reflexivity/symmetry are `Nat.add_comm`, transitivity needs one
hand-proven `Nat` right-cancellation (structural on the cancelled addend, `propext`-free), and the vcomp
congruences are pure `Nat` middle-four rearrangements.  A genuine `ℤ` invariant, `propext`-free.

## The pump: the adjunction cup creates a flat the comonad counit destroys (no triangle straightens it)

`cohesionFlatBubbleCell : shape ⇒ shape` is a degree-`1` ENDO 2-cell: the lower `ʃ ⊣ ♭` unit `η` (whiskered)
creates a `flat` next to `shape`, the flat COMONAD counit `ε^♭` (NOT the adjunction cap `ε`) destroys it, and
`μ^ʃ` re-merges the two shapes.  No triangle identity can straighten this zig-zag — the cup is closed by the
comonad counit, not the adjunction cap — so the bubble's degree `1 ≠ 0` is not collapsed.  `cohesionUnitPumpCell n`
stacks `n` bubbles after the shape unit `η^ʃ`, giving a cell `id ⇒ shape` of degree exactly `n`.  Distinct `n`
give provably non-convertible cells (sound flat degree), so `n ↦ [pump n]` injects `ℕ` into the hom classes.

## Disposition (HONEST-FAIL-FORWARD)

Per-boundary boundedness is REFUTED (`cohesionUnitHom_notPerBoundaryBounded`), so route A (bounded enumeration) is
DEAD, just as r2 killed thinness.  A COMPLETE faithful invariant model (route B as a decider) is out of reach: it
is the walking-adjoint-triple completeness problem (`fxString_hasAdjointTripleCompleteness = false`), and cohesion
is strictly harder; the `ℤ` degree is sound but abelian, blind to planar order, so it SEPARATES but cannot decide.
The genuine landing is the invariant used as a REFUTATION (mirroring r2 one level up) plus the per-modality thin
fragment as the useful decided scope.  `fxCohesion_hasCohesionQuadrupleDecision` therefore STAYS `false` — now for a
PROVED reason (the unit hom is INFINITE), strictly stronger than r2's "not forced thin".  The exact residual: any
POSITIVE decision on the infinite cross-modality/unit homs, which — per Rosebrugh–Wood (*Distributive Adjoint
Strings*, TAC 1995), whose free idempotent-adjoint-string 2-category's free completion reconstructs the simplicial
2-category Δ — needs a genuinely RICHER (Δ-shaped) model, not mere boundedness; and per Post–Markov the general
finitely-presented-2-category word problem is undecidable, escapable only by a finite convergent presentation.

Non-vacuity: the invariant SEPARATES the r2 pair (`id ⇒ shape`, degrees `0` vs `1`) and AGREES on the r1
idempotence pair and a triangle pair; all three are DECIDED (one `isFalse`, two `isTrue`) below.

Raw Lean 4 + Init; `genCount` is a structural `Nat` fold, the soundness is structural induction over the `Prop`
relations, the separation is `Nat.noConfusion` — every declaration is
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free.  Per-declaration `#assert_no_axioms`
gated in the audit twin. -/

namespace FX1Poly.Polygraph

/-! ## Clean `Nat` rearrangement primitives (all `propext`-free) -/

/-- Right cancellation on `Nat`, hand-proven STRUCTURALLY on the cancelled addend (`Nat.add_right_cancel` itself
leaks `propext` in core; this recursion uses only `Nat.succ.inj`, which is axiom-free).  The one cancellation the
flat-balance transitivity needs. -/
theorem natAddRightCancel : ∀ (addend leftVal rightVal : Nat),
    leftVal + addend = rightVal + addend → leftVal = rightVal
  | 0, _, _, cancelled => cancelled
  | Nat.succ _, _, _, cancelled => natAddRightCancel _ _ _ (Nat.succ.inj cancelled)

/-- The four-fold middle rearrangement `(a + b) + (c + d) = (a + c) + (b + d)` on `Nat` — the additive analog of
r2's `xorMiddleFour`, proved from the `propext`-free `Nat.add_assoc` / `Nat.add_left_comm`.  Discharges the
interchange law's degree obligation and threads the vcomp-congruence balance rearrangements. -/
theorem natMiddleFour (valA valB valC valD : Nat) :
    (valA + valB) + (valC + valD) = (valA + valC) + (valB + valD) := by
  rw [Nat.add_assoc valA valB (valC + valD), Nat.add_left_comm valB valC valD,
    Nat.add_assoc valA valC (valB + valD)]

/-! ## The generic `Nat` count homomorphism (any signature, any generator weighting) -/

/-- ★ The **generator count** of a free 2-cell, over ANY signature and ANY generator weighting `weight`: a `Nat`
homomorphism — a generator weighs `weight`, an identity weighs `0`, a vertical composite ADDS its factors, and
whiskering is TRANSPARENT (a 1-cell action carries no generator content).  The `Nat` (commutative-monoid) analog
of r2's `genParity`; structural recursion over the five 2-cell constructors, constant `Nat` motive: `propext`-free.
Two of these (counting `flatCounit`, counting `flatComul`) combine into the `ℤ` flat degree via the balance. -/
def genCount {signature : ModeSignature}
    (weight : {sourceMode targetMode : signature.graph.Mode} →
      {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
      signature.twoCell sourcePath targetPath → Nat) :
    {sourceMode targetMode : signature.graph.Mode} →
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
    RawTwoCellExpr signature sourcePath targetPath → Nat
  | _, _, _, _, .gen generator => weight generator
  | _, _, _, _, .id _ => 0
  | _, _, _, _, .vcomp cellAlpha cellBeta => genCount weight cellAlpha + genCount weight cellBeta
  | _, _, _, _, .whiskerLeft _ cellBeta => genCount weight cellBeta
  | _, _, _, _, .whiskerRight _ cellAlpha => genCount weight cellAlpha

/-- The count is invisible to a boundary cast (`castBoundary` is `Eq.rec`, collapsing to the identity once its two
boundary equalities are substituted). -/
theorem genCount_castBoundary {signature : ModeSignature}
    (weight : {sourceMode targetMode : signature.graph.Mode} →
      {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
      signature.twoCell sourcePath targetPath → Nat)
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath sourcePath' targetPath targetPath' : ModalityPath signature.graph sourceMode targetMode}
    (hsource : sourcePath = sourcePath') (htarget : targetPath = targetPath')
    (cell : RawTwoCellExpr signature sourcePath targetPath) :
    genCount weight (RawTwoCellExpr.castBoundary hsource htarget cell) = genCount weight cell := by
  cases hsource; cases htarget; rfl

/-- The count is preserved by a single structural 3-cell rewrite `TwoCellStep` — the structural laws only rearrange
generators (identity absorption is `Nat.zero_add`, associativity is `Nat.add_assoc`, interchange is
`natMiddleFour`). -/
theorem genCount_step {signature : ModeSignature}
    (weight : {sourceMode targetMode : signature.graph.Mode} →
      {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
      signature.twoCell sourcePath targetPath → Nat)
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr signature sourcePath targetPath}
    (step : TwoCellStep signature cellAlpha cellBeta) :
    genCount weight cellAlpha = genCount weight cellBeta := by
  induction step with
  | vcompIdLeft _ => exact Nat.zero_add _
  | vcompIdRight _ => rfl
  | vcompAssoc _ _ _ => exact Nat.add_assoc _ _ _
  | whiskerLeftId _ _ => rfl
  | whiskerRightId _ _ => rfl
  | whiskerLeftVcomp _ _ _ => rfl
  | whiskerRightVcomp _ _ _ => rfl
  | vcompCongrLeft _ _ ih => dsimp only [genCount]; rw [ih]
  | vcompCongrRight _ _ ih => dsimp only [genCount]; rw [ih]
  | whiskerLeftCongr _ _ ih => dsimp only [genCount]; exact ih
  | whiskerRightCongr _ _ ih => dsimp only [genCount]; exact ih
  | interchange _ _ _ _ =>
      dsimp only [genCount, RawTwoCellExpr.hcomp]
      exact natMiddleFour _ _ _ _

/-- The count is preserved by structural convertibility `TwoCellConv` (reflexive-symmetric-transitive closure). -/
theorem genCount_conv {signature : ModeSignature}
    (weight : {sourceMode targetMode : signature.graph.Mode} →
      {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
      signature.twoCell sourcePath targetPath → Nat)
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr signature sourcePath targetPath}
    (conv : TwoCellConv signature cellAlpha cellBeta) :
    genCount weight cellAlpha = genCount weight cellBeta := by
  induction conv with
  | ofStep step => exact genCount_step weight step
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- ★ The count is preserved by the COMPLETED convertibility `TwoCellConvFull` (structural + whisker
functoriality: unit-whisker stripping, composite-whisker splitting, disjoint-whisker exchange — all
same-generator, threaded through boundary casts the count cannot see). -/
theorem genCount_convFull {signature : ModeSignature}
    (weight : {sourceMode targetMode : signature.graph.Mode} →
      {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
      signature.twoCell sourcePath targetPath → Nat)
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr signature sourcePath targetPath}
    (convFull : TwoCellConvFull signature cellAlpha cellBeta) :
    genCount weight cellAlpha = genCount weight cellBeta := by
  induction convFull with
  | ofConv conv => exact genCount_conv weight conv
  | whiskerLeftUnit _ => rfl
  | whiskerRightUnit _ => rw [genCount_castBoundary]; rfl
  | whiskerLeftComp _ _ _ => rw [genCount_castBoundary]; rfl
  | whiskerRightComp _ _ _ => rw [genCount_castBoundary]; rfl
  | whiskerExchange _ _ _ => rw [genCount_castBoundary]; rfl
  | vcompCongrLeft _ _ ih => dsimp only [genCount]; rw [ih]
  | vcompCongrRight _ _ ih => dsimp only [genCount]; rw [ih]
  | whiskerLeftCongr _ _ ih => dsimp only [genCount]; exact ih
  | whiskerRightCongr _ _ ih => dsimp only [genCount]; exact ih
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-! ## The cohesion flat-count weights and the two counts -/

/-- The `flatCounit`-count weight: `flatCounit` weighs `1`, every other generator `0`.  Full ten-constructor
enumeration, constant `Nat` motive (a wildcard arm would leak `propext`). -/
def cohesionFlatUpWeight {sourceMode targetMode : CohesionMode}
    {sourcePath targetPath : ModalityPath cohesionGraph sourceMode targetMode}
    (generator : CohesionTwoCell sourcePath targetPath) : Nat :=
  match generator with
  | .shapeUnit => 0
  | .shapeMul => 0
  | .flatCounit => 1
  | .flatComul => 0
  | .sharpUnit => 0
  | .sharpMul => 0
  | .unitShapeFlat => 0
  | .counitShapeFlat => 0
  | .unitFlatSharp => 0
  | .counitFlatSharp => 0

/-- The `flatComul`-count weight: `flatComul` weighs `1`, every other generator `0`. -/
def cohesionFlatDownWeight {sourceMode targetMode : CohesionMode}
    {sourcePath targetPath : ModalityPath cohesionGraph sourceMode targetMode}
    (generator : CohesionTwoCell sourcePath targetPath) : Nat :=
  match generator with
  | .shapeUnit => 0
  | .shapeMul => 0
  | .flatCounit => 0
  | .flatComul => 1
  | .sharpUnit => 0
  | .sharpMul => 0
  | .unitShapeFlat => 0
  | .counitShapeFlat => 0
  | .unitFlatSharp => 0
  | .counitFlatSharp => 0

/-- The **flat-counit count** `#flatCounit` of a free cohesion 2-cell — the POSITIVE part of the `ℤ` flat degree. -/
def cohesionFlatUpCount {sourceMode targetMode : CohesionMode}
    {sourcePath targetPath : ModalityPath cohesionGraph sourceMode targetMode}
    (cell : RawTwoCellExpr cohesionModeSignature sourcePath targetPath) : Nat :=
  genCount cohesionFlatUpWeight cell

/-- The **flat-comul count** `#flatComul` of a free cohesion 2-cell — the NEGATIVE part of the `ℤ` flat degree. -/
def cohesionFlatDownCount {sourceMode targetMode : CohesionMode}
    {sourcePath targetPath : ModalityPath cohesionGraph sourceMode targetMode}
    (cell : RawTwoCellExpr cohesionModeSignature sourcePath targetPath) : Nat :=
  genCount cohesionFlatDownWeight cell

/-- The flat-counit count is preserved by the completed structural convertibility (signature-pinned so the weight
inference resolves — the `convFull` argument fixes `signature := cohesionModeSignature`). -/
theorem cohesionFlatUpCount_convFull {sourceMode targetMode : CohesionMode}
    {sourcePath targetPath : ModalityPath cohesionGraph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr cohesionModeSignature sourcePath targetPath}
    (convFull : TwoCellConvFull cohesionModeSignature cellAlpha cellBeta) :
    cohesionFlatUpCount cellAlpha = cohesionFlatUpCount cellBeta := by
  show genCount cohesionFlatUpWeight cellAlpha = genCount cohesionFlatUpWeight cellBeta
  exact genCount_convFull cohesionFlatUpWeight convFull

/-- The flat-comul count is preserved by the completed structural convertibility. -/
theorem cohesionFlatDownCount_convFull {sourceMode targetMode : CohesionMode}
    {sourcePath targetPath : ModalityPath cohesionGraph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr cohesionModeSignature sourcePath targetPath}
    (convFull : TwoCellConvFull cohesionModeSignature cellAlpha cellBeta) :
    cohesionFlatDownCount cellAlpha = cohesionFlatDownCount cellBeta := by
  show genCount cohesionFlatDownWeight cellAlpha = genCount cohesionFlatDownWeight cellBeta
  exact genCount_convFull cohesionFlatDownWeight convFull

/-- ★ The **flat degree balance** — the `Nat` cross-form of "the two integer flat degrees `#flatCounit − #flatComul`
are equal": `#flatCounit α + #flatComul β = #flatCounit β + #flatComul α`.  This is the `ℤ`-flat-degree invariant
realized WITHOUT `Int` (whose group laws leak `propext`); it is symmetric, so reflexivity/symmetry are trivial and
only transitivity spends the hand-proven `Nat` cancellation. -/
def cohesionFlatBalanced {sourceMode targetMode : CohesionMode}
    {sourcePath targetPath : ModalityPath cohesionGraph sourceMode targetMode}
    (cellA cellB : RawTwoCellExpr cohesionModeSignature sourcePath targetPath) : Prop :=
  cohesionFlatUpCount cellA + cohesionFlatDownCount cellB
    = cohesionFlatUpCount cellB + cohesionFlatDownCount cellA

/-! ## Balance algebra helpers -/

/-- Transitivity of the flat balance (the `Nat` cross-form of `ℤ`-difference transitivity), via the one hand-proven
right cancellation. -/
theorem cohesionFlatBalance_trans {upA downA upB downB upC downC : Nat}
    (hAB : upA + downB = upB + downA) (hBC : upB + downC = upC + downB) :
    upA + downC = upC + downA := by
  apply natAddRightCancel (upB + downB)
  calc (upA + downC) + (upB + downB)
      = (upA + downB) + (upB + downC) := by
        rw [natMiddleFour upA downC upB downB, Nat.add_comm downC downB,
          ← natMiddleFour upA downB upB downC]
    _ = (upB + downA) + (upC + downB) := by rw [hAB, hBC]
    _ = (upC + downA) + (upB + downB) := by
        rw [natMiddleFour upB downA upC downB, Nat.add_comm upB upC,
          ← natMiddleFour upC downA upB downB]

/-- Adding the SAME count pair to the RIGHT operand of a balance preserves it (the vcomp-left congruence
rearrangement — pure `Nat`, no cancellation). -/
theorem cohesionFlatBalance_addBoth {upA downA upB downB : Nat} (upExtra downExtra : Nat)
    (hAB : upA + downB = upB + downA) :
    (upA + upExtra) + (downB + downExtra) = (upB + upExtra) + (downA + downExtra) := by
  rw [natMiddleFour upA upExtra downB downExtra, hAB, natMiddleFour upB upExtra downA downExtra]

/-- Adding the SAME count pair to the LEFT operand of a balance preserves it (the vcomp-right congruence
rearrangement). -/
theorem cohesionFlatBalance_addBothLeft {upA downA upB downB : Nat} (upExtra downExtra : Nat)
    (hAB : upA + downB = upB + downA) :
    (upExtra + upA) + (downExtra + downB) = (upExtra + upB) + (downExtra + downA) := by
  rw [natMiddleFour upExtra upA downExtra downB, hAB, natMiddleFour upExtra upB downExtra downA]

/-! ## The flat balance is a sound invariant of the saturated cohesion congruence -/

/-- ★ **The flat degree balance is a sound invariant of the saturated cohesion congruence.**  Convertible free
2-cells have equal flat degree — the completed convertibility preserves BOTH counts (`genCount_convFull`, so the
balance holds by `Nat.add_comm`), every flat comonad counit/coassoc/idempotence law balances (`(−1)+1 = 0`, etc. as
concrete `Nat` cross-equalities, `rfl`), every non-flat law weighs `0` on both sides, and the congruences /
transitivity thread the balance helpers.  Hence any flat-degree DIFFERENCE proves non-convertibility. -/
theorem cohesionFlatBalanced_satConv {sourceMode targetMode : CohesionMode}
    {sourcePath targetPath : ModalityPath cohesionGraph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr cohesionModeSignature sourcePath targetPath}
    (conv : CohesionSaturatedTwoCellConv cellAlpha cellBeta) :
    cohesionFlatBalanced cellAlpha cellBeta := by
  induction conv with
  | ofFull convFull =>
      dsimp only [cohesionFlatBalanced]
      rw [cohesionFlatUpCount_convFull convFull, cohesionFlatDownCount_convFull convFull]
  | shapeLeftUnit => rfl
  | shapeRightUnit => rfl
  | shapeAssoc => rfl
  | shapeIdempotence => rfl
  | flatLeftCounit => rfl
  | flatRightCounit => rfl
  | flatCoassoc => rfl
  | flatIdempotence => rfl
  | sharpLeftUnit => rfl
  | sharpRightUnit => rfl
  | sharpAssoc => rfl
  | sharpIdempotence => rfl
  | triangleShapeFlatOnShape => rfl
  | triangleShapeFlatOnFlat => rfl
  | triangleFlatSharpOnFlat => rfl
  | triangleFlatSharpOnSharp => rfl
  | vcompCongrLeft cellBeta _ ih =>
      exact cohesionFlatBalance_addBoth (cohesionFlatUpCount cellBeta) (cohesionFlatDownCount cellBeta) ih
  | vcompCongrRight cellAlpha _ ih =>
      exact cohesionFlatBalance_addBothLeft (cohesionFlatUpCount cellAlpha) (cohesionFlatDownCount cellAlpha) ih
  | whiskerLeftCongr _ _ ih => exact ih
  | whiskerRightCongr _ _ ih => exact ih
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact cohesionFlatBalance_trans ih1 ih2

/-! ## The flat bubble: a degree-1 endo 2-cell (adjunction cup, comonad kill, shape merge) -/

/-- ★ The **flat bubble** `shape ⇒ shape` — the lower `ʃ ⊣ ♭` unit `η` whiskered to create a `flat` next to
`shape` (`shape ⇒ shape·flat·shape`), the flat COMONAD counit `ε^♭` whiskered to destroy it
(`shape·flat·shape ⇒ shape·shape`), then `μ^ʃ` re-merging the two shapes (`shape·shape ⇒ shape`).  The `flat` is
created by the ADJUNCTION cup and killed by the COMONAD counit (NOT the adjunction cap), so NO triangle identity
straightens the zig-zag — its flat degree `1` survives.  The engine of the pump. -/
def cohesionFlatBubbleCell : RawTwoCellExpr cohesionModeSignature cohesionShape cohesionShape :=
  RawTwoCellExpr.vcomp
    (RawTwoCellExpr.whiskerRight (signature := cohesionModeSignature) cohesionShape cohesionUnitShapeFlatCell)
    (RawTwoCellExpr.vcomp
      (RawTwoCellExpr.whiskerLeft (signature := cohesionModeSignature) cohesionShape
        (RawTwoCellExpr.whiskerRight (signature := cohesionModeSignature) cohesionShape cohesionFlatCounitCell))
      cohesionShapeMulCell)

/-- The flat bubble has flat-counit count `1` (one `flatCounit`, from the comonad kill). -/
theorem cohesionFlatBubble_upCount : cohesionFlatUpCount cohesionFlatBubbleCell = 1 := rfl

/-- The flat bubble has flat-comul count `0` (it uses NO `flatComul` — the cup is the adjunction unit, not the
comonad comultiplication). -/
theorem cohesionFlatBubble_downCount : cohesionFlatDownCount cohesionFlatBubbleCell = 0 := rfl

/-! ## The pump family on the FIXED boundary `id ⇒ shape` -/

/-- ★ The **unit-hom pump** `id ⇒ shape` at level `n` — the shape monad unit `η^ʃ` followed by `n` flat bubbles.
All levels sit over the SAME boundary `id ⇒ shape` (the exact hom r2 separated into two classes), and
`cohesionUnitPumpCell n` has flat degree exactly `n`. -/
def cohesionUnitPumpCell :
    Nat → RawTwoCellExpr cohesionModeSignature
      (ModalityPath.nil (graph := cohesionGraph) CohesionMode.point) cohesionShape
  | 0 => cohesionShapeUnitCell
  | Nat.succ n => RawTwoCellExpr.vcomp (cohesionUnitPumpCell n) cohesionFlatBubbleCell

/-- The pump at level `n` has flat-counit count exactly `n` (each bubble contributes one `flatCounit`). -/
theorem cohesionUnitPumpCell_upCount (n : Nat) : cohesionFlatUpCount (cohesionUnitPumpCell n) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      show cohesionFlatUpCount (cohesionUnitPumpCell n) + cohesionFlatUpCount cohesionFlatBubbleCell = n + 1
      rw [ih, cohesionFlatBubble_upCount]

/-- The pump at level `n` has flat-comul count `0` for every `n` (no bubble uses `flatComul`). -/
theorem cohesionUnitPumpCell_downCount (n : Nat) : cohesionFlatDownCount (cohesionUnitPumpCell n) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      show cohesionFlatDownCount (cohesionUnitPumpCell n) + cohesionFlatDownCount cohesionFlatBubbleCell = 0
      rw [ih, cohesionFlatBubble_downCount]

/-- ★ **Every natural number is realized as a flat degree on the fixed boundary `id ⇒ shape`.**  For each `n`, the
pump `cohesionUnitPumpCell n` is a cell `id ⇒ shape` with flat-counit count `n` and flat-comul count `0` (integer
flat degree `n`). -/
theorem cohesionUnitHom_hasCellOfEveryFlatDegree (n : Nat) :
    ∃ cell : RawTwoCellExpr cohesionModeSignature
      (ModalityPath.nil (graph := cohesionGraph) CohesionMode.point) cohesionShape,
      cohesionFlatUpCount cell = n ∧ cohesionFlatDownCount cell = 0 :=
  ⟨cohesionUnitPumpCell n, cohesionUnitPumpCell_upCount n, cohesionUnitPumpCell_downCount n⟩

/-! ## The infinitude of the unit hom `id ⇒ shape` -/

/-- ★★★ **The pump indices land in DISTINCT convertibility classes.**  If two pump cells are saturated-convertible
then their flat degrees agree; since `cohesionUnitPumpCell n` has integer flat degree `n` (up `n`, down `0`), the
balance forces `n = m`.  So `n ↦ [cohesionUnitPumpCell n]` INJECTS `ℕ` into the convertibility classes of the hom
`id ⇒ shape` — the hom has INFINITELY many classes. -/
theorem cohesionUnitPump_injectiveModConv {n m : Nat}
    (conv : CohesionSaturatedTwoCellConv (cohesionUnitPumpCell n) (cohesionUnitPumpCell m)) : n = m := by
  have hbal : cohesionFlatUpCount (cohesionUnitPumpCell n) + cohesionFlatDownCount (cohesionUnitPumpCell m)
      = cohesionFlatUpCount (cohesionUnitPumpCell m) + cohesionFlatDownCount (cohesionUnitPumpCell n) :=
    cohesionFlatBalanced_satConv conv
  rw [cohesionUnitPumpCell_upCount, cohesionUnitPumpCell_upCount, cohesionUnitPumpCell_downCount,
    cohesionUnitPumpCell_downCount] at hbal
  exact hbal

/-- ★ **Distinct pump levels are NON-convertible.**  The contrapositive of injectivity: `n ≠ m` implies the pump
cells `cohesionUnitPumpCell n` and `cohesionUnitPumpCell m` are not saturated-convertible. -/
theorem cohesionUnitPump_notConvertible_of_ne {n m : Nat} (hne : n ≠ m) :
    ¬ CohesionSaturatedTwoCellConv (cohesionUnitPumpCell n) (cohesionUnitPumpCell m) :=
  fun conv => hne (cohesionUnitPump_injectiveModConv conv)

/-- ★★ **No finite representative set covers the hom `id ⇒ shape` (per-boundary boundedness REFUTED).**  At most
ONE pump level converts to any given cell: if `cohesionUnitPumpCell n` and `cohesionUnitPumpCell m` both convert to
the same `target`, then `n = m`.  Hence no single representative — indeed no finite set — can represent all pump
cells up to convertibility; the walker is NOT decidable via bounded per-boundary representatives. -/
theorem cohesionUnitHom_notPerBoundaryBounded
    (target : RawTwoCellExpr cohesionModeSignature
      (ModalityPath.nil (graph := cohesionGraph) CohesionMode.point) cohesionShape)
    {n m : Nat}
    (hn : CohesionSaturatedTwoCellConv (cohesionUnitPumpCell n) target)
    (hm : CohesionSaturatedTwoCellConv (cohesionUnitPumpCell m) target) : n = m :=
  cohesionUnitPump_injectiveModConv (hn.trans (CohesionSaturatedTwoCellConv.symm hm))

/-! ## Non-vacuity: the invariant SEPARATES the r2 pair and AGREES on the identifications -/

/-- The flat degree SEPARATES the r2 refutation pair: the shape monad unit has flat degree `0` (up `0`, down `0`)
and the lower-adjunction route has flat degree `1` (up `1` from its comonad counit, down `0`). -/
theorem cohesionR2Pair_flatCounts :
    (cohesionFlatUpCount cohesionShapeUnitCell = 0 ∧ cohesionFlatDownCount cohesionShapeUnitCell = 0) ∧
      cohesionFlatUpCount cohesionShapeUnitViaLowerAdjunctionCell = 1 ∧
      cohesionFlatDownCount cohesionShapeUnitViaLowerAdjunctionCell = 0 :=
  ⟨⟨rfl, rfl⟩, rfl, rfl⟩

/-- ★ **The r2 refutation pair is DECIDED `isFalse` by the flat degree** (degrees `0` vs `1`): the shape monad unit
and the lower-adjunction route over `id ⇒ shape` are non-convertible.  A finer refutation than r2's `ℤ/2` parity —
it places the pair as levels `0` and `1` of the infinite tower. -/
theorem cohesionR2Pair_notConvertible :
    ¬ CohesionSaturatedTwoCellConv cohesionShapeUnitCell cohesionShapeUnitViaLowerAdjunctionCell := by
  intro conv
  have hbal : cohesionFlatUpCount cohesionShapeUnitCell
        + cohesionFlatDownCount cohesionShapeUnitViaLowerAdjunctionCell
      = cohesionFlatUpCount cohesionShapeUnitViaLowerAdjunctionCell
        + cohesionFlatDownCount cohesionShapeUnitCell :=
    cohesionFlatBalanced_satConv conv
  have h01 : (0 : Nat) = 1 := hbal
  exact Nat.noConfusion h01

/-- ★ **The three non-vacuity verdicts, DECIDED through the shipped invariant + witnesses.**  The r2 refutation
pair is `isFalse` (flat degree separates it, `cohesionR2Pair_notConvertible`); the r1 idempotence pair
(`shape ⇒ shape` unit composites) is `isTrue` (shape idempotence, `cohesionShapeUnitComposites_viaIdempotence`);
a triangle pair (`ʃ ⊣ ♭` snake on `shape`) is `isTrue` (`triangleShapeFlatOnShape`).  So the invariant is not the
degenerate everything-distinct one — it separates a genuine non-convertible pair while respecting two genuine
identifications. -/
theorem cohesionFlatBalance_decidesThreeNonVacuously :
    (¬ CohesionSaturatedTwoCellConv cohesionShapeUnitCell cohesionShapeUnitViaLowerAdjunctionCell) ∧
      CohesionSaturatedTwoCellConv cohesionShapeLeftUnitCell cohesionShapeRightUnitCell ∧
      CohesionSaturatedTwoCellConv cohesionShapeFlatSnakeOnShapeCell cohesionShapeIdCell :=
  ⟨cohesionR2Pair_notConvertible, cohesionShapeUnitComposites_viaIdempotence,
    CohesionSaturatedTwoCellConv.triangleShapeFlatOnShape⟩

/-- The r2 refutation pair as an explicit `isFalse` decision (the shipped decision on this scope). -/
def decideCohesionR2Pair :
    Decidable (CohesionSaturatedTwoCellConv cohesionShapeUnitCell cohesionShapeUnitViaLowerAdjunctionCell) :=
  isFalse cohesionR2Pair_notConvertible

/-- The r1 idempotence pair as an explicit `isTrue` decision. -/
def decideCohesionIdempotencePair :
    Decidable (CohesionSaturatedTwoCellConv cohesionShapeLeftUnitCell cohesionShapeRightUnitCell) :=
  isTrue cohesionShapeUnitComposites_viaIdempotence

/-- A triangle pair as an explicit `isTrue` decision. -/
def decideCohesionTrianglePair :
    Decidable (CohesionSaturatedTwoCellConv cohesionShapeFlatSnakeOnShapeCell cohesionShapeIdCell) :=
  isTrue CohesionSaturatedTwoCellConv.triangleShapeFlatOnShape

/-! ## Honesty markers -/

/-- ★★ **ESTABLISHED — the fuller `ℤ` flat-degree invariant ships.**  `= true`: `cohesionFlatBalanced` is a
machine-checked sound congruence invariant (`cohesionFlatBalanced_satConv`), the `ℤ`-difference
`#flatCounit − #flatComul` realized `propext`-free as a two-count `Nat` balance (`Int`'s group laws leak `propext`),
refining r2's `ℤ/2` parity to a full integer degree.  It separates the r2 pair (degrees `0`/`1`) and agrees on the
idempotence and triangle identifications (`cohesionFlatBalance_decidesThreeNonVacuously`). -/
def fxCohesion_hasFlatDegreeInvariant : Bool := true

/-- ★★★ **ESTABLISHED — per-boundary boundedness is REFUTED; the unit hom `id ⇒ shape` is INFINITE.**  `= false`
(boundedness does NOT hold), backed by `cohesionUnitPump_injectiveModConv` (an injection `ℕ ↪` the convertibility
classes of `id ⇒ shape` via the pump family), `cohesionUnitPump_notConvertible_of_ne`, and
`cohesionUnitHom_notPerBoundaryBounded` (at most one pump level per class, so no finite representative set covers
the hom).  The pump's engine is the flat bubble: the adjunction cup creates a `flat` the COMONAD counit destroys,
a zig-zag NO triangle straightens (`cohesionFlatBubbleCell`, flat degree `1`).  This DECISIVELY answers the r3
boundedness question: route A (bounded per-boundary enumeration) is DEAD, one level up from r2's thinness
refutation — the very hom r2 split into two classes has INFINITELY many. -/
def fxCohesion_hasPerBoundaryBoundedness : Bool := false

/-- ★★ **Honesty marker — the COHESION QUADRUPLE DECISION stays the WALL, now for a PROVED reason.**  r1 walled the
full decision on cross-modality thinness (not forced); r2 refuted thinness; r3 proves the residual is not merely
open but INFINITE: the unit hom `id ⇒ shape` has infinitely many convertibility classes
(`cohesionUnitPump_injectiveModConv`), so NO total per-boundary decision exists via boundedness.  A COMPLETE
faithful invariant model is out of reach — it is the walking-adjoint-triple completeness problem
(`fxString_hasAdjointTripleCompleteness = false`), and per Rosebrugh–Wood (*Distributive Adjoint Strings*, TAC 1995)
the free idempotent-adjoint-string 2-category's free completion reconstructs the simplicial 2-category Δ, so the
honest ambient is Δ-shaped, not bounded; per Post–Markov the general finitely-presented-2-category word problem is
undecidable, escapable only by a finite convergent presentation.  The genuine landing is the `ℤ` flat degree used
as a REFUTATION plus the per-modality thin fragment as the decided scope; `fxCohesion_hasCohesionQuadrupleDecision`
(in `CohesionDecision`) STAYS `false`, now upgraded from "not forced thin" to "PROVED infinite cross-modality/unit
homs".  This lane does NOT flip a global decision; it walls the residual honestly, decisively.  `= false`. -/
def fxCohesion_hasUnitHomDecision : Bool := false

end FX1Poly.Polygraph
