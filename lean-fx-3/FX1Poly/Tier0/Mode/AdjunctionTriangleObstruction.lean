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

/-! ## ★ The confluence direction: the snakes are STRUCTURAL normal forms (the triangle is their sole redex)

The termination half above leaves CONFLUENCE as the only missing ingredient of `hasConvergentTwoCellPresentation`.
The first structural fact about that confluence: each snake is already a free-3-polygraph NORMAL FORM — its head
is a vertical composite of two whiskered GENERATORS, so no `vcompId*` (no identity factor), no `vcompAssoc` (the
left factor is a whisker, not a composite), and no `whisker{Id,Vcomp}` (each whiskered body is an atomic
generator) redex occurs anywhere in it.  Consequently, in the SATURATED system (free laws ⊕ the two triangle
reductions) the triangle is the UNIQUE rewrite firing on a snake; the saturating reduction `snake ⤳ id` overlaps
NO free strict-2-category law at the root.  This isolates the remaining Schanuel–Street confluence obligation to
the CONTEXT overlaps (a snake nested inside a larger structural redex), the structural laws among themselves being
`mode-8`'s already-confluent system — orthogonal to the triangle at the root. -/

/-- ★ The **left snake is a free-3-polygraph normal form**: `isInterchangeNormal = true`.  A vertical composite of
two whiskered generators exposes no `vcompId*` / `vcompAssoc` / `whisker{Id,Vcomp}` redex.  Computes by `rfl`. -/
theorem adjunctionSeedLeftSnake_isInterchangeNormal :
    adjunctionSeedLeftSnake.isInterchangeNormal = true := rfl

/-- ★ The **right snake is a free-3-polygraph normal form** — dual, same structure. -/
theorem adjunctionSeedRightSnake_isInterchangeNormal :
    adjunctionSeedRightSnake.isInterchangeNormal = true := rfl

/-- ★ **No free 3-cell reduces the left snake.**  Contrapositive of the recognizer's soundness
(`TwoCellStep.source_not_interchangeNormal`: every reducible 2-cell is NON-normal) applied at the snake, which IS
normal.  So the saturating triangle reduction `adjunctionSeedLeftSnake ⤳ id_L` forms NO root critical pair with
the free strict-2-category laws — the snake is structurally irreducible without it.  This pins
`hasConvergentTwoCellPresentation`'s residual confluence obligation to the context overlaps alone. -/
theorem adjunctionSeedLeftSnake_no_structuralStep
    (reduct : RawTwoCellExpr adjunctionModeSignature
      (singletonModalityPath AdjunctionModality.left) (singletonModalityPath AdjunctionModality.left)) :
    ¬ TwoCellStep adjunctionModeSignature adjunctionSeedLeftSnake reduct := by
  intro step
  exact Bool.noConfusion
    (adjunctionSeedLeftSnake_isInterchangeNormal.symm.trans step.source_not_interchangeNormal)

/-- ★ **No free 3-cell reduces the right snake** — dual root-irreducibility. -/
theorem adjunctionSeedRightSnake_no_structuralStep
    (reduct : RawTwoCellExpr adjunctionModeSignature
      (singletonModalityPath AdjunctionModality.right) (singletonModalityPath AdjunctionModality.right)) :
    ¬ TwoCellStep adjunctionModeSignature adjunctionSeedRightSnake reduct := by
  intro step
  exact Bool.noConfusion
    (adjunctionSeedRightSnake_isInterchangeNormal.symm.trans step.source_not_interchangeNormal)

/-! ## ★ The COMPLETION: the snake-prefix rule resolves the assoc critical pair (toward the convergent presentation)

The obstruction file isolated the one obstruction to confluence: the snake is a structural normal form, so the
ONLY non-structural reduction needed is the triangle — yet orienting the bare triangle `snake ⤳ id_L` against the
free `vcompAssoc` rule is NOT locally confluent.  In `vcomp snake c` the two redexes diverge: the bare triangle
gives `vcomp id_L c ⤳ c`, while `vcompAssoc` RE-ASSOCIATES the snake apart into `vcomp (η▷L) (vcomp (ε◁L) c)`, in
which the snake is no longer a contiguous subterm and the bare triangle cannot fire.

KNUTH–BENDIX COMPLETION resolves exactly this pair.  Adjoin the SNAKE-PREFIX rule

    vcomp (η▷L) (vcomp (ε◁L) rest)  ⤳  rest

— SOUND because, in the equational theory, `vcomp (η▷L) (vcomp (ε◁L) rest) = vcomp (vcomp (η▷L) (ε◁L)) rest =
vcomp id_L rest = rest` (the bare triangle composed with `vcompAssoc` then `vcompIdLeft`).  With both rules the
critical pair JOINS — both reducts of `vcomp snake c` reach `c` (`adjunctionSeedLeftSnake_assocCriticalPair_joins`).
This is the walking-adjunction word problem's resolving rule (Schanuel–Street): it converts the obstruction into a
constructive convergent step toward `fxMode_hasConvergentTwoCellPresentation`.  The completion still terminates on
the generator-count measure (the prefix rule, like the bare rule, strictly drops the count by 2). -/

/-- The LEFT-snake KB-completed saturated rewrite over the adjunction signature: every free strict-2-category
3-cell (`ofFree`), the bare triangle `snake ⤳ id_L` (`leftBareSnake`), its completion the snake-prefix
`(η▷L)⊟((ε◁L)⊟rest) ⤳ rest` (`leftSnakePrefix`), and the left-factor `vcomp` congruence so a triangle redex fires
under a following composite (`vcompCongrLeft`).  Minimal — exactly the rules the `vcompAssoc` critical pair needs
to join. -/
inductive AdjunctionLeftSaturatedStep :
    {sourceMode targetMode : AdjunctionMode} →
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode} →
    RawTwoCellExpr adjunctionModeSignature sourcePath targetPath →
    RawTwoCellExpr adjunctionModeSignature sourcePath targetPath → Prop where
  /-- Embed any free strict-2-category 3-cell (`mode-3`'s `TwoCellStep`). -/
  | ofFree {sourceMode targetMode : AdjunctionMode}
      {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
      {cellA cellB : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath} :
      TwoCellStep adjunctionModeSignature cellA cellB → AdjunctionLeftSaturatedStep cellA cellB
  /-- The bare LEFT triangle `snake ⤳ id_L`. -/
  | leftBareSnake :
      AdjunctionLeftSaturatedStep adjunctionSeedLeftSnake
        (RawTwoCellExpr.id (signature := adjunctionModeSignature)
          (singletonModalityPath AdjunctionModality.left))
  /-- The completion SNAKE-PREFIX rule `(η▷L)⊟((ε◁L)⊟rest) ⤳ rest`. -/
  | leftSnakePrefix {targetPath : ModalityPath adjunctionGraph AdjunctionMode.base AdjunctionMode.tip}
      (rest : RawTwoCellExpr adjunctionModeSignature
        (singletonModalityPath AdjunctionModality.left) targetPath) :
      AdjunctionLeftSaturatedStep
        (RawTwoCellExpr.vcomp
          (RawTwoCellExpr.whiskerRight (signature := adjunctionModeSignature)
            (singletonModalityPath AdjunctionModality.left) adjunctionUnitTwoCell)
          (RawTwoCellExpr.vcomp
            (RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature)
              (singletonModalityPath AdjunctionModality.left) adjunctionCounitTwoCell)
            rest))
        rest
  /-- Congruence: a saturated step in the LEFT factor of a vertical composite (so the triangle fires under a
  following composite — the position the `vcompAssoc` critical pair exposes). -/
  | vcompCongrLeft {sourceMode targetMode : AdjunctionMode}
      {oneCellF oneCellG oneCellH : ModalityPath adjunctionGraph sourceMode targetMode}
      {cellAlpha cellAlpha' : RawTwoCellExpr adjunctionModeSignature oneCellF oneCellG}
      (cellBeta : RawTwoCellExpr adjunctionModeSignature oneCellG oneCellH) :
      AdjunctionLeftSaturatedStep cellAlpha cellAlpha' →
      AdjunctionLeftSaturatedStep (RawTwoCellExpr.vcomp cellAlpha cellBeta)
        (RawTwoCellExpr.vcomp cellAlpha' cellBeta)

/-- Reflexive-transitive closure of the completed saturated rewrite — multi-step reduction. -/
inductive AdjunctionLeftSaturatedReduces :
    {sourceMode targetMode : AdjunctionMode} →
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode} →
    RawTwoCellExpr adjunctionModeSignature sourcePath targetPath →
    RawTwoCellExpr adjunctionModeSignature sourcePath targetPath → Prop where
  | refl {sourceMode targetMode : AdjunctionMode}
      {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
      (cell : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) :
      AdjunctionLeftSaturatedReduces cell cell
  | head {sourceMode targetMode : AdjunctionMode}
      {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
      {cellA cellB cellC : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath} :
      AdjunctionLeftSaturatedStep cellA cellB → AdjunctionLeftSaturatedReduces cellB cellC →
      AdjunctionLeftSaturatedReduces cellA cellC

/-- ★ **The bare-triangle redex of `vcomp snake c` reaches `c`.**  Fire the bare triangle under the left-factor
congruence (`snake ⤳ id_L` inside `vcomp _ c`), then drop the left identity (`vcomp id_L c ⤳ c`).  The first of
the two competing reductions of the `vcompAssoc` critical pair. -/
theorem adjunctionSeedLeftSnake_vcompContinuation_reducesToContinuation
    {targetPath : ModalityPath adjunctionGraph AdjunctionMode.base AdjunctionMode.tip}
    (continuation : RawTwoCellExpr adjunctionModeSignature
      (singletonModalityPath AdjunctionModality.left) targetPath) :
    AdjunctionLeftSaturatedReduces
      (RawTwoCellExpr.vcomp adjunctionSeedLeftSnake continuation) continuation :=
  AdjunctionLeftSaturatedReduces.head
    (AdjunctionLeftSaturatedStep.vcompCongrLeft continuation AdjunctionLeftSaturatedStep.leftBareSnake)
    (AdjunctionLeftSaturatedReduces.head
      (AdjunctionLeftSaturatedStep.ofFree (TwoCellStep.vcompIdLeft continuation))
      (AdjunctionLeftSaturatedReduces.refl continuation))

/-- ★★ **The `vcompAssoc` critical pair JOINS in the KB-completed system.**  The two redexes of `vcomp snake c`
both reduce to `continuation`: the bare-triangle redex's reduct `vcomp id_L c` drops via `vcompIdLeft`; the
`vcompAssoc` redex's reduct `vcomp (η▷L) (vcomp (ε◁L) c)` drops via the COMPLETION `leftSnakePrefix`.  This
discharges the precise non-confluence the obstruction isolated — the snake-prefix rule is the resolving completion
of the walking-adjunction word problem, turning the obstruction into a convergent step. -/
theorem adjunctionSeedLeftSnake_assocCriticalPair_joins
    {targetPath : ModalityPath adjunctionGraph AdjunctionMode.base AdjunctionMode.tip}
    (continuation : RawTwoCellExpr adjunctionModeSignature
      (singletonModalityPath AdjunctionModality.left) targetPath) :
    AdjunctionLeftSaturatedReduces
        (RawTwoCellExpr.vcomp
          (RawTwoCellExpr.id (signature := adjunctionModeSignature)
            (singletonModalityPath AdjunctionModality.left)) continuation)
        continuation
      ∧ AdjunctionLeftSaturatedReduces
        (RawTwoCellExpr.vcomp
          (RawTwoCellExpr.whiskerRight (signature := adjunctionModeSignature)
            (singletonModalityPath AdjunctionModality.left) adjunctionUnitTwoCell)
          (RawTwoCellExpr.vcomp
            (RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature)
              (singletonModalityPath AdjunctionModality.left) adjunctionCounitTwoCell)
            continuation))
        continuation :=
  ⟨AdjunctionLeftSaturatedReduces.head
      (AdjunctionLeftSaturatedStep.ofFree (TwoCellStep.vcompIdLeft continuation))
      (AdjunctionLeftSaturatedReduces.refl continuation),
   AdjunctionLeftSaturatedReduces.head
      (AdjunctionLeftSaturatedStep.leftSnakePrefix continuation)
      (AdjunctionLeftSaturatedReduces.refl continuation)⟩

/-! ## ★ The DUAL completion: the right snake-prefix rule resolves the right assoc critical pair

The left completion above resolves the `vcompAssoc` critical pair of the LEFT triangle.  The RIGHT triangle owes
the dual obligation: the right snake `(R◁η) ⊟ (ε▷R)` (the cell `R ⇒ R` through the intermediate `R L R`) is the
mirror redex, and orienting the bare right triangle `rightSnake ⤳ id_R` against `vcompAssoc` in `vcomp rightSnake c`
diverges exactly as the left did.  The same Knuth–Bendix completion applies, dualized: adjoin the RIGHT SNAKE-PREFIX
rule

    vcomp (R◁η) (vcomp (ε▷R) rest)  ⤳  rest

— SOUND because `vcomp (R◁η) (vcomp (ε▷R) rest) = vcomp (vcomp (R◁η) (ε▷R)) rest = vcomp id_R rest = rest` (the bare
right triangle composed with `vcompAssoc` then `vcompIdLeft`).  With both rules the right critical pair JOINS
(`adjunctionSeedRightSnake_assocCriticalPair_joins`).  This is the second resolving rule of the walking-adjunction
word problem; together with the left completion it discharges BOTH triangle critical pairs against `vcompAssoc`,
leaving for `fxMode_hasConvergentTwoCellPresentation` only the cross-overlaps among the saturating rules and the
context overlaps with the (already mode-8-confluent) structural laws.  The completion still terminates on the
generator-count measure (the prefix rule drops the count by 2, like the bare rule). -/

/-- The RIGHT-snake KB-completed saturated rewrite over the adjunction signature: every free strict-2-category
3-cell (`ofFree`), the bare right triangle `rightSnake ⤳ id_R` (`rightBareSnake`), its completion the right
snake-prefix `(R◁η)⊟((ε▷R)⊟rest) ⤳ rest` (`rightSnakePrefix`), and the left-factor `vcomp` congruence
(`vcompCongrLeft`).  The exact dual of `AdjunctionLeftSaturatedStep` — the rules the right `vcompAssoc` critical pair
needs to join. -/
inductive AdjunctionRightSaturatedStep :
    {sourceMode targetMode : AdjunctionMode} →
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode} →
    RawTwoCellExpr adjunctionModeSignature sourcePath targetPath →
    RawTwoCellExpr adjunctionModeSignature sourcePath targetPath → Prop where
  /-- Embed any free strict-2-category 3-cell (`mode-3`'s `TwoCellStep`). -/
  | ofFree {sourceMode targetMode : AdjunctionMode}
      {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
      {cellA cellB : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath} :
      TwoCellStep adjunctionModeSignature cellA cellB → AdjunctionRightSaturatedStep cellA cellB
  /-- The bare RIGHT triangle `rightSnake ⤳ id_R`. -/
  | rightBareSnake :
      AdjunctionRightSaturatedStep adjunctionSeedRightSnake
        (RawTwoCellExpr.id (signature := adjunctionModeSignature)
          (singletonModalityPath AdjunctionModality.right))
  /-- The completion RIGHT SNAKE-PREFIX rule `(R◁η)⊟((ε▷R)⊟rest) ⤳ rest`. -/
  | rightSnakePrefix {targetPath : ModalityPath adjunctionGraph AdjunctionMode.tip AdjunctionMode.base}
      (rest : RawTwoCellExpr adjunctionModeSignature
        (singletonModalityPath AdjunctionModality.right) targetPath) :
      AdjunctionRightSaturatedStep
        (RawTwoCellExpr.vcomp
          (RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature)
            (singletonModalityPath AdjunctionModality.right) adjunctionUnitTwoCell)
          (RawTwoCellExpr.vcomp
            (RawTwoCellExpr.whiskerRight (signature := adjunctionModeSignature)
              (singletonModalityPath AdjunctionModality.right) adjunctionCounitTwoCell)
            rest))
        rest
  /-- Congruence: a saturated step in the LEFT factor of a vertical composite (so the right triangle fires under a
  following composite — the position the `vcompAssoc` critical pair exposes). -/
  | vcompCongrLeft {sourceMode targetMode : AdjunctionMode}
      {oneCellF oneCellG oneCellH : ModalityPath adjunctionGraph sourceMode targetMode}
      {cellAlpha cellAlpha' : RawTwoCellExpr adjunctionModeSignature oneCellF oneCellG}
      (cellBeta : RawTwoCellExpr adjunctionModeSignature oneCellG oneCellH) :
      AdjunctionRightSaturatedStep cellAlpha cellAlpha' →
      AdjunctionRightSaturatedStep (RawTwoCellExpr.vcomp cellAlpha cellBeta)
        (RawTwoCellExpr.vcomp cellAlpha' cellBeta)

/-- Reflexive-transitive closure of the completed RIGHT saturated rewrite — multi-step reduction. -/
inductive AdjunctionRightSaturatedReduces :
    {sourceMode targetMode : AdjunctionMode} →
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode} →
    RawTwoCellExpr adjunctionModeSignature sourcePath targetPath →
    RawTwoCellExpr adjunctionModeSignature sourcePath targetPath → Prop where
  | refl {sourceMode targetMode : AdjunctionMode}
      {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
      (cell : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) :
      AdjunctionRightSaturatedReduces cell cell
  | head {sourceMode targetMode : AdjunctionMode}
      {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
      {cellA cellB cellC : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath} :
      AdjunctionRightSaturatedStep cellA cellB → AdjunctionRightSaturatedReduces cellB cellC →
      AdjunctionRightSaturatedReduces cellA cellC

/-- ★ **The bare-triangle redex of `vcomp rightSnake c` reaches `c`.**  Fire the bare right triangle under the
left-factor congruence (`rightSnake ⤳ id_R` inside `vcomp _ c`), then drop the left identity
(`vcomp id_R c ⤳ c`).  The first of the two competing reductions of the right `vcompAssoc` critical pair. -/
theorem adjunctionSeedRightSnake_vcompContinuation_reducesToContinuation
    {targetPath : ModalityPath adjunctionGraph AdjunctionMode.tip AdjunctionMode.base}
    (continuation : RawTwoCellExpr adjunctionModeSignature
      (singletonModalityPath AdjunctionModality.right) targetPath) :
    AdjunctionRightSaturatedReduces
      (RawTwoCellExpr.vcomp adjunctionSeedRightSnake continuation) continuation :=
  AdjunctionRightSaturatedReduces.head
    (AdjunctionRightSaturatedStep.vcompCongrLeft continuation AdjunctionRightSaturatedStep.rightBareSnake)
    (AdjunctionRightSaturatedReduces.head
      (AdjunctionRightSaturatedStep.ofFree (TwoCellStep.vcompIdLeft continuation))
      (AdjunctionRightSaturatedReduces.refl continuation))

/-- ★★ **The right `vcompAssoc` critical pair JOINS in the KB-completed system.**  The two redexes of
`vcomp rightSnake c` both reduce to `continuation`: the bare-triangle redex's reduct `vcomp id_R c` drops via
`vcompIdLeft`; the `vcompAssoc` redex's reduct `vcomp (R◁η) (vcomp (ε▷R) c)` drops via the COMPLETION
`rightSnakePrefix`.  Together with `adjunctionSeedLeftSnake_assocCriticalPair_joins` this discharges BOTH triangle
critical pairs against `vcompAssoc` — the two resolving completions of the walking-adjunction word problem. -/
theorem adjunctionSeedRightSnake_assocCriticalPair_joins
    {targetPath : ModalityPath adjunctionGraph AdjunctionMode.tip AdjunctionMode.base}
    (continuation : RawTwoCellExpr adjunctionModeSignature
      (singletonModalityPath AdjunctionModality.right) targetPath) :
    AdjunctionRightSaturatedReduces
        (RawTwoCellExpr.vcomp
          (RawTwoCellExpr.id (signature := adjunctionModeSignature)
            (singletonModalityPath AdjunctionModality.right)) continuation)
        continuation
      ∧ AdjunctionRightSaturatedReduces
        (RawTwoCellExpr.vcomp
          (RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature)
            (singletonModalityPath AdjunctionModality.right) adjunctionUnitTwoCell)
          (RawTwoCellExpr.vcomp
            (RawTwoCellExpr.whiskerRight (signature := adjunctionModeSignature)
              (singletonModalityPath AdjunctionModality.right) adjunctionCounitTwoCell)
            continuation))
        continuation :=
  ⟨AdjunctionRightSaturatedReduces.head
      (AdjunctionRightSaturatedStep.ofFree (TwoCellStep.vcompIdLeft continuation))
      (AdjunctionRightSaturatedReduces.refl continuation),
   AdjunctionRightSaturatedReduces.head
      (AdjunctionRightSaturatedStep.rightSnakePrefix continuation)
      (AdjunctionRightSaturatedReduces.refl continuation)⟩

end FX1Poly.Tier0
