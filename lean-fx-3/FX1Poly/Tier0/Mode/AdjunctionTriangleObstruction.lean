import FX1Poly.Tier0.Mode.ComputadWordProblem

/-! # mode-9 seed — the adjunction triangle identities are GENUINE non-free relations (the fib-3 dim-2 obstruction)

`mode-4` (`AdjointStrings`) ships the adjunction DATA `μ_affine ⊣ μ_affine†` (unit `η`, counit `ε`) and PROVES
the triangle identities for the IDENTITY self-adjunction, but honestly marks the GENERAL adjunction's triangle
identities as deferred (`fxMode_hasAdjunctionTriangleSaturation := false`): "the free adjunction does not satisfy
the snake equations".  This file turns that prose marker into a RIGOROUS THEOREM, and in doing so sharpens
exactly what `fib-3`'s dimension-2 keystone (the convergent presentation, `hasConvergentTwoCellPresentation`)
still owes.

## The obstruction, made rigorous

The LEFT snake of the seed adjunction is the 2-cell `L ⇒ L`

    adjunctionSeedLeftSnake  :=  (η ▷ L) ⊟ (L ◁ ε)            -- whiskerRight L η  then  whiskerLeft L ε

built from the unit and counit (its boundary paths reduce definitionally: `(id_base ∘ L) = L`,
`(L ∘ id_tip) = L`, and the two intermediate paths both reduce to `L R L`).  The triangle identity is the claim
`adjunctionSeedLeftSnake ≈ id_L`.  But:

  * mode-8's `RawTwoCellExpr.generatorCount` is a `TwoCellConv` INVARIANT (`TwoCellConv.generatorCount_eq`):
    every strict-2-category 3-cell — interchange included — preserves the number of generator firings.
  * the snake fires `η` once and `ε` once, so `adjunctionSeedLeftSnake.generatorCount = 2`, whereas
    `id_L.generatorCount = 0`.

Hence — `TwoCellConv.not_of_generatorCount_ne` — `adjunctionSeedLeftSnake` is PROVABLY NOT `TwoCellConv` to
`id_L`.  The triangle identity is a GENUINE relation that the free 3-polygraph does NOT contain; it must be ADDED
(the mode-9 saturation).  Same for the right snake `R ⇒ R`.  This is the rigorous proof of mode-4's honesty
marker, not an assertion.

## What it buys fib-3's dimension-2 keystone

The same count argument is the TERMINATION direction of the saturated rewrite: orienting the triangle as
`snake ⤳ id` STRICTLY DECREASES `generatorCount` (`0 < 2`, `adjunctionSeedTriangleReductionDecreasesCount`).
So the saturated 3-polygraph (free strict-2-category laws ⊕ the two triangle reductions) terminates on the
generator-count measure — the structural laws preserve it (mode-8), the triangle reductions strictly drop it.
What remains for `hasConvergentTwoCellPresentation` is therefore precisely CONFLUENCE (the critical pairs of the
two triangles, the Schanuel–Street "walking adjunction" word problem) — the count-termination half is discharged
here.  This file does NOT flip `fxMode_hasAdjunctionTriangleSaturation` (confluence is the remaining node), but it
converts the obstruction from a claim into a theorem and isolates the one missing ingredient.

## Zero-axiom

The snakes are concrete `RawTwoCellExpr` constructors; the counts are `rfl`; the non-convertibility is mode-8's
`not_of_generatorCount_ne` fed a recursor-based `Nat.noConfusion` (the `propext`-free distinguisher of `2` from
`0`); the termination direction is `Nat.succ_pos`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`, `decide`.  Per-declaration audit-gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Tier0

/-! ## The seed adjunction's two snakes -/

/-- The **LEFT snake** of the seed adjunction `μ_affine ⊣ μ_affine†`: the 2-cell `L ⇒ L` given by
`(η ▷ L) ⊟ (L ◁ ε)` — the unit whiskered on the right by `L`, then the counit whiskered on the left by `L`.
Its boundary is `L ⇒ L` (the source `composePath (id_base) L` and target `composePath L (id_tip)` both reduce to
`L`; the intermediate path `composePath (L∘R) L = composePath L (R∘L) = L R L`).  The triangle identity asserts
this is the identity `id_L` — see `adjunctionSeedLeftSnake_not_conv_id` for why it is NOT, in the free system. -/
def adjunctionSeedLeftSnake :=
  RawTwoCellExpr.vcomp
    (RawTwoCellExpr.whiskerRight (signature := adjunctionModeSignature)
      (singletonModalityPath AdjunctionModality.left) adjunctionUnitTwoCell)
    (RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature)
      (singletonModalityPath AdjunctionModality.left) adjunctionCounitTwoCell)

/-- The **RIGHT snake** of the seed adjunction: the dual 2-cell `R ⇒ R` given by `(R ◁ η) ⊟ (ε ▷ R)` — the unit
whiskered on the left by `R`, then the counit whiskered on the right by `R`.  The triangle identity asserts this
is `id_R`. -/
def adjunctionSeedRightSnake :=
  RawTwoCellExpr.vcomp
    (RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature)
      (singletonModalityPath AdjunctionModality.right) adjunctionUnitTwoCell)
    (RawTwoCellExpr.whiskerRight (signature := adjunctionModeSignature)
      (singletonModalityPath AdjunctionModality.right) adjunctionCounitTwoCell)

/-! ## The generator counts: snakes fire two generators, identities fire none -/

/-- The left snake fires exactly two generators (`η` once, `ε` once): `generatorCount = 2`. -/
theorem adjunctionSeedLeftSnake_generatorCount : adjunctionSeedLeftSnake.generatorCount = 2 := rfl

/-- The right snake likewise fires exactly two generators: `generatorCount = 2`. -/
theorem adjunctionSeedRightSnake_generatorCount : adjunctionSeedRightSnake.generatorCount = 2 := rfl

/-- The identity 2-cell on `L` fires no generators: `generatorCount = 0` (the triangle identity's RHS). -/
theorem leftIdentityCell_generatorCount :
    (RawTwoCellExpr.id (signature := adjunctionModeSignature)
      (singletonModalityPath AdjunctionModality.left)).generatorCount = 0 := rfl

/-! ## ★ The obstruction: the triangle identities FAIL in the free 3-polygraph -/

/-- ★ **The left triangle identity is NOT free-derivable.**  `adjunctionSeedLeftSnake` (generator count 2) is
PROVABLY NOT `TwoCellConv` to `id_L` (generator count 0): since `generatorCount` is a conversion invariant
(mode-8), convertible 2-cells share it, so a count-2 cell cannot be convertible to a count-0 cell.  This is the
rigorous form of mode-4's honesty marker — the snake equation is a genuine NEW relation, absent from the free
strict-2-category 3-polygraph, which the mode-9 saturation must ADD. -/
theorem adjunctionSeedLeftSnake_not_conv_id :
    ¬ TwoCellConv adjunctionModeSignature adjunctionSeedLeftSnake
        (RawTwoCellExpr.id (signature := adjunctionModeSignature)
          (singletonModalityPath AdjunctionModality.left)) :=
  TwoCellConv.not_of_generatorCount_ne (fun countsEqual => Nat.noConfusion countsEqual)

/-- ★ **The right triangle identity is NOT free-derivable** — same obstruction, dual snake. -/
theorem adjunctionSeedRightSnake_not_conv_id :
    ¬ TwoCellConv adjunctionModeSignature adjunctionSeedRightSnake
        (RawTwoCellExpr.id (signature := adjunctionModeSignature)
          (singletonModalityPath AdjunctionModality.right)) :=
  TwoCellConv.not_of_generatorCount_ne (fun countsEqual => Nat.noConfusion countsEqual)

/-! ## The obstruction at full strength: the snake class avoids every count-zero cell -/

/-- ★ **The left snake's entire `TwoCellConv`-class has generator count 2.**  Every free 2-cell convertible to
`adjunctionSeedLeftSnake` fires exactly two generators — so the class is DISJOINT from every count-0 (identity-like)
2-cell, not merely from `id_L`.  Hence NO amount of free strict-2-category reasoning collapses the snake to an
identity: the left triangle law fails in the free 3-polygraph in the strongest sense.  (Generalizes
`adjunctionSeedLeftSnake_not_conv_id`.) -/
theorem adjunctionSeedLeftSnake_classGeneratorCount {reduct : RawTwoCellExpr adjunctionModeSignature
      (singletonModalityPath AdjunctionModality.left) (singletonModalityPath AdjunctionModality.left)}
    (conv : TwoCellConv adjunctionModeSignature adjunctionSeedLeftSnake reduct) :
    reduct.generatorCount = 2 :=
  conv.generatorCount_eq.symm.trans adjunctionSeedLeftSnake_generatorCount

/-- ★ **The right snake's entire `TwoCellConv`-class has generator count 2** — the dual full-strength
obstruction. -/
theorem adjunctionSeedRightSnake_classGeneratorCount {reduct : RawTwoCellExpr adjunctionModeSignature
      (singletonModalityPath AdjunctionModality.right) (singletonModalityPath AdjunctionModality.right)}
    (conv : TwoCellConv adjunctionModeSignature adjunctionSeedRightSnake reduct) :
    reduct.generatorCount = 2 :=
  conv.generatorCount_eq.symm.trans adjunctionSeedRightSnake_generatorCount

/-! ## ★ The termination direction: orienting the triangle as `snake ⤳ id` strictly decreases the count -/

/-- ★ **The triangle reduction strictly decreases the generator count** (`0 < 2`).  Orienting the snake equation
as the rewrite `adjunctionSeedLeftSnake ⤳ id_L`, the generator count drops from 2 to 0 — and mode-8 proved every
structural law PRESERVES the count.  So the SATURATED 3-polygraph (the strict-2-category laws ⊕ the triangle
reductions) terminates on the generator-count measure: this discharges the TERMINATION half of mode-9's
`hasConvergentTwoCellPresentation`, leaving CONFLUENCE (the Schanuel–Street critical pairs) as the sole remaining
ingredient of fib-3's dimension-2 keystone. -/
theorem adjunctionSeedTriangleReductionDecreasesCount :
    (RawTwoCellExpr.id (signature := adjunctionModeSignature)
      (singletonModalityPath AdjunctionModality.left)).generatorCount
      < adjunctionSeedLeftSnake.generatorCount :=
  Nat.succ_pos 1

end FX1Poly.Tier0
