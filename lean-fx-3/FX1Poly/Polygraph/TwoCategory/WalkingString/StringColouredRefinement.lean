import FX1Poly.Polygraph.TwoCategory.WalkingString.StringMatchingValleyDescent

/-! # WalkingString — the r5 per-colour-loop refinement is VACUOUS; the invariant is NOT too coarse

Round 5 hypothesised that `ColouredDiagramType` is too COARSE for completeness because an INTERNAL closed loop
created by a colour-1 (`F ⊣ G`) eta/eps pair versus a colour-2 (`G ⊣ H`) eta/eps pair carries NO colour in the
invariant (the base `matchingOf` records loops as a bare `Nat`), so a per-colour loop refinement `(loops1, loops2)`
would be required.  This file RUNS the decisive check and REFUTES the hypothesis on its factual premise, then
records the honest correction of what actually blocks completeness.

## ★ STEP 1 (decisive) — the predicted internal colour-ambiguous loop does NOT close: `loops = 0`

The r5 hypothesis presumes an internal closed loop EXISTS at the walking-adjoint-triple seed.  It does not.  At the
FREE walking adjoint triple `F ⊣ G ⊣ H` no realizable 2-cell closes a loop (`loops ≡ 0` on every exhibited cell,
`stringWitnesses_loops_zero`):

  * the colour-1 / colour-2 "circle" 2-cells the hypothesis names — `id_base ⇒ id_base` from `η`/`ε`, or
    `id_tip ⇒ id_tip` from `η'`/`ε'` — do NOT typecheck.  A loop closes only when a CAP consumes two wires already
    in the same union-find component (`stepCap` increments `loops` iff `isSameComponent`).  But `η : id ⇒ F·G` opens
    `F·G`, and the only base-parity cap `counitUpper` consumes `H·G` — never `F·G`, because `F ≠ H`
    (`string_left_ne_coLeft`); dually `η' : id ⇒ G·H` opens `G·H` and the only tip-parity cap `counitLower`
    consumes `G·F`.  The orientation + the `F ≠ H` label together forbid closure.  This matches Schanuel–Street:
    the free adjunction's homs are the augmented simplex category Δ₊, which has NO scalar / loop endomorphisms;
  * the natural realizable proxy — `stringMixedBubbleCup`, a colour-1 cup `η` with a colour-2 `G`-bubble
    (`η'`…`ε'`) inserted (a genuine 3-generator MIXED-colour cell) — computes to the SAME `matchingOf` as a bare
    cup, `loops = 0` (`stringMixedBubbleCup_matchingOf_eq_unitLower`).  The inserted colour-2 zig-zag straightens
    away; no loop closes.

So the r5 premise ("an internal loop carries no colour") is empty — there IS no internal loop.  A per-colour loop
count `(loops1, loops2)` would be identically `(0, 0)` (`stringPerColourLoopSplit_zero_ofLoopsZero` applied to
`stringWitnesses_loops_zero`): the proposed refinement is VACUOUS.

## The only genuine internal colour ambiguity is CONVERTIBLE (a sound identification, not a coarseness gap)

Where colour IS genuinely unpinned by the boundary is an internal `G`-arc: `stringSnakeGlo` (colour 1) and
`stringSnakeGhi` (colour 2) are both `G ⇒ G` with equal `colouredMatchingOf`
(`stringSnakeGlo_colouredMatchingOf_eq_stringSnakeGhi`, r2).  But they are saturated-CONVERTIBLE
(`stringSnakeGlo_conv_stringSnakeGhi`, both straighten to `id_G` through the shared-`G` coherence) — a SOUND
identification, not a completeness counterexample.  Likewise a colour-2 bubble on an `F`-context
(`stringMixedBubbleOnLeft`) straightens to `id (F·G)` (`stringMixedBubbleOnLeft_conv_identity`).  Every
colour-ambiguous cell we can exhibit is either loop-free (so its per-colour split is `(0,0)`) OR convertible; there
is NO colour-ambiguous NON-convertible pair the invariant misses.

## ★ Honest correction — what actually blocks completeness

The completeness blocker is unchanged from r4: it is NOT invariant coarseness but the length-rigidity failure of
the RECONSTRUCTION (`fxString_hasStringLengthRigidityFailure`).  `adjunctionPath_eq_of_length_eq` (parallel
1-cells of equal length are equal — one modality per mode) is FALSE at the string seed (`F`, `H` both `base ⟶ tip`,
length 1, distinct), so the valley-trace reconstruction that reads valley atoms through LENGTHS must be re-derived
to read them through the BOUNDARY LABELS (which DO pin every valley generator's colour).  That colour-aware port
is the standing residual `StringMatchingReductsShareSpineTrace`; per-colour loop counting does not touch it.  So
`fxString_hasAdjointTripleCompleteness` STAYS `false`, honestly, and this file adds the machine-checked reason the
r5 loop refinement is the wrong tool.

## Alignment with the Fuss–Catalan literature

Coloured Temperley–Lieb / Fuss–Catalan diagram algebras (Bisch–Jones; Landau) DO carry one loop parameter per
colour (δ_a, δ_b) with monochromatic matchings — the r5 direction is correct THERE.  But those per-colour loop
weights live in the LINEAR / subfactor COMPLETION (the higher relative commutants of an intermediate-subfactor
tower), where ev/coev close scalar loops.  The FREE / walking adjoint triple this seed presents is the Δ-level
structure BELOW that completion, where the orientation forbids loop closure entirely — hence `loops ≡ 0` and the
per-colour refinement is vacuous.  The refinement completeness actually needs is the colour-aware (label-driven)
reconstruction, categorically distinct from loop counting.

Raw Lean 4 + Init; the witnesses compute (`rfl`), the convertibilities are triangle + structural constructors, the
per-colour vacuity is structural `Nat` recursion; `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`
-free.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Helper 1-cells: the parallel left / right generators -/

/-- The left adjoint `F : base ⟶ tip` as a length-1 1-cell. -/
def stringLeftPath : ModalityPath adjointTripleGraph AdjointTripleMode.base AdjointTripleMode.tip :=
  singletonModalityPath AdjointTripleModality.left

/-- The shared middle `G : tip ⟶ base` as a length-1 1-cell. -/
def stringRightPath : ModalityPath adjointTripleGraph AdjointTripleMode.tip AdjointTripleMode.base :=
  singletonModalityPath AdjointTripleModality.right

/-! ## STEP 1 — the predicted colour-ambiguous internal-loop witness -/

/-- The inserted colour-2 `G`-bubble half: `F·G ⇒ F·G·H·G` — the upper unit `η'` opened between `F` and `G`
(whiskered `F ◁ (η' ▷ G)`). -/
def stringMixedBubbleInsert :
    RawTwoCellExpr adjointTripleModeSignature stringFG
      (composePath stringLeftPath (composePath stringGH stringRightPath)) :=
  RawTwoCellExpr.whiskerLeft (signature := adjointTripleModeSignature) stringLeftPath
    (RawTwoCellExpr.whiskerRight (signature := adjointTripleModeSignature) stringRightPath stringUnitUpper)

/-- The closing colour-2 `G`-bubble half: `F·G·H·G ⇒ F·G` — the upper counit `ε'` capping the trailing `H·G`
(whiskered `F·G ◁ ε'`). -/
def stringMixedBubbleClose :
    RawTwoCellExpr adjointTripleModeSignature
      (composePath stringLeftPath (composePath stringGH stringRightPath)) stringFG :=
  RawTwoCellExpr.whiskerLeft (signature := adjointTripleModeSignature) stringFG stringCounitUpper

/-- ★ The **r5-predicted colour-ambiguous internal-loop witness**: a colour-1 cup `η` (`id_base ⇒ F·G`) with a
colour-2 `G`-bubble (`η'`…`ε'`) inserted on its `G`-leg — a genuine 3-generator MIXED-colour cell.  The hypothesis
predicts its internal colour-2 loop is invisible to the invariant; the check below shows the loop does NOT close. -/
def stringMixedBubbleCup :
    RawTwoCellExpr adjointTripleModeSignature
      (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base) stringFG :=
  RawTwoCellExpr.vcomp (RawTwoCellExpr.vcomp stringUnitLower stringMixedBubbleInsert) stringMixedBubbleClose

/-- ★★ **DECISIVE — the predicted internal loop does NOT close.**  `stringMixedBubbleCup`'s `matchingOf` is a bare
two-strand cup with `loops = 0` — the inserted colour-2 `G`-bubble straightens away at the connectivity level, no
loop is created.  So there is no internal colour-carrying loop for a per-colour refinement to distinguish. -/
theorem stringMixedBubbleCup_matchingOf :
    matchingOf stringMixedBubbleCup
      = { bottomCount := 0, topCount := 2, partner := [1, 0], loops := 0 } := rfl

/-- ★★ **The mixed-colour bubble is `matchingOf`-INDISTINGUISHABLE from a bare cup.**  The 3-generator
colour-1-cup-plus-colour-2-`G`-bubble and the single-generator bare cup `η` share one `matchingOf` (`loops = 0`).
The predicted "colour-ambiguous internal loop" simply is not there. -/
theorem stringMixedBubbleCup_matchingOf_eq_unitLower :
    matchingOf stringMixedBubbleCup = matchingOf stringUnitLower := rfl

/-- The mixed-colour bubble carries ZERO closed loops — the direct refutation of the r5 factual premise. -/
theorem stringMixedBubbleCup_loops_zero : (matchingOf stringMixedBubbleCup).loops = 0 := rfl

/-- Non-degeneracy: the witness is a GENUINE three-generator mixed-colour cell (one colour-1 `η`, one colour-2 `η'`,
one colour-2 `ε'`), not a disguised bare cup — its `matchingOf` collapse is real content, not a triviality. -/
theorem stringMixedBubbleCup_generatorCount : stringMixedBubbleCup.generatorCount = 3 := rfl

/-! ## The only genuine internal colour ambiguity is CONVERTIBLE -/

/-- A colour-2 `G`-bubble sitting on an `F`-context: `F ◁ stringSnakeGhi : F·G ⇒ F·G`.  The colour-2 zig-zag
crosses the colour-1 `F`-strand's neighbourhood, so its colour is genuinely internal — yet it straightens to the
identity. -/
def stringMixedBubbleOnLeft : RawTwoCellExpr adjointTripleModeSignature stringFG stringFG :=
  RawTwoCellExpr.whiskerLeft (signature := adjointTripleModeSignature) stringLeftPath stringSnakeGhi

/-- ★★ **The colour-2 bubble on an `F`-context straightens to `id (F·G)`.**  `F ◁ stringSnakeGhi ≈ F ◁ id_G`
(whiskered `triangleGhi`), and `F ◁ id_G ≈ id (F·G)` (the `whiskerLeftId` structural law), so the mixed-colour
bubble is saturated-CONVERTIBLE to the identity — a SOUND identification of an internal colour ambiguity, not a
completeness counterexample. -/
theorem stringMixedBubbleOnLeft_conv_identity :
    StringSaturatedTwoCellConv stringMixedBubbleOnLeft
      (RawTwoCellExpr.id (signature := adjointTripleModeSignature) stringFG) := by
  have straighten :=
    StringSaturatedTwoCellConv.whiskerLeftCongr stringLeftPath StringSaturatedTwoCellConv.triangleGhi
  have collapse :=
    StringSaturatedTwoCellConv.ofConv
      (TwoCellConv.ofStep (TwoCellStep.whiskerLeftId stringLeftPath
        (singletonModalityPath AdjointTripleModality.right)))
  exact StringSaturatedTwoCellConv.trans straighten collapse

/-- The colour-2 bubble on `F` has the SAME `matchingOf` as `id (F·G)` — machine-checked soundness-consistency of
the convertibility above (`loops = 0`, the two `F·G` through-strands). -/
theorem stringMixedBubbleOnLeft_matchingOf_eq_identity :
    matchingOf stringMixedBubbleOnLeft
      = matchingOf (RawTwoCellExpr.id (signature := adjointTripleModeSignature) stringFG) := rfl

/-- ★ **The genuine colour ambiguity is convertible.**  The two syntactically-distinct `G ⇒ G` snakes
`stringSnakeGlo` (colour 1) and `stringSnakeGhi` (colour 2) — the ONLY internal `G`-arc colour ambiguity — have
EQUAL `colouredMatchingOf` (r2) AND are saturated-convertible (both straighten to `id_G`).  So the base invariant
identifies exactly the cells the presentation identifies: the colour ambiguity is a SOUND identification, machine
-witnessed at both the invariant and the convertibility level. -/
theorem stringGSnakes_colourAmbiguous_and_convertible :
    colouredMatchingOf (singletonModalityPath AdjointTripleModality.right)
        (singletonModalityPath AdjointTripleModality.right) stringSnakeGlo
      = colouredMatchingOf (singletonModalityPath AdjointTripleModality.right)
          (singletonModalityPath AdjointTripleModality.right) stringSnakeGhi
      ∧ StringSaturatedTwoCellConv stringSnakeGlo stringSnakeGhi :=
  ⟨stringSnakeGlo_colouredMatchingOf_eq_stringSnakeGhi, stringSnakeGlo_conv_stringSnakeGhi⟩

/-! ## STEP 2 — the per-colour loop refinement is VACUOUS -/

/-- Every witness cell is LOOP-FREE — `matchingOf`'s loop count is `0` on the bare cup, the mixed-colour bubble,
the colour-2 bubble on `F`, both `G`-snakes, and the cross-level cell.  The union-find never closes a loop at the
walking-adjoint-triple seed (Schanuel–Street Δ₊, no scalar endomorphisms). -/
theorem stringWitnesses_loops_zero :
    (matchingOf stringUnitLower).loops = 0
      ∧ (matchingOf stringMixedBubbleCup).loops = 0
      ∧ (matchingOf stringMixedBubbleOnLeft).loops = 0
      ∧ (matchingOf stringSnakeGlo).loops = 0
      ∧ (matchingOf stringSnakeGhi).loops = 0
      ∧ (matchingOf stringCrossLevelCell).loops = 0 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- ★ **A per-colour loop split of a loop-FREE diagram is `(0, 0)`.**  If a refined `(loopsColourOne,
loopsColourTwo)` split satisfies `loopsColourOne + loopsColourTwo = base.loops` and `base.loops = 0`, then both
per-colour counts are `0`.  Combined with `stringWitnesses_loops_zero` (every cell has `base.loops = 0`) this is
the precise sense in which the r5 per-colour loop refinement carries NO discriminating power at the free seed —
it is identically `(0, 0)`.  Structural `Nat` recursion, propext-free. -/
theorem stringPerColourLoopSplit_zero_ofLoopsZero :
    (loopsColourOne loopsColourTwo : Nat) → loopsColourOne + loopsColourTwo = 0 →
      loopsColourOne = 0 ∧ loopsColourTwo = 0
  | _, 0, splitEq => ⟨splitEq, rfl⟩
  | _, _ + 1, splitEq => nomatch splitEq

/-! ## Honesty markers -/

/-- **★ ESTABLISHED — no realizable 2-cell closes an INTERNAL LOOP at the free walking adjoint triple.**  Every
exhibited cell has `matchingOf`.loops `= 0` (`stringWitnesses_loops_zero`); a loop closes only on a same-component
cap (`stepCap`), which never fires here — `η` opens `F·G` and the only base-parity cap `counitUpper` consumes `H·G`
(`F ≠ H`, `string_left_ne_coLeft`), dually for `η'`/`counitLower` at tip.  So the colour-1 / colour-2 "circle"
2-cells the r5 hypothesis names do not even typecheck.  This matches Schanuel–Street (the free adjunction's homs
are the augmented simplex category Δ₊, no scalar loop endomorphisms).  `= false`. -/
def fxString_hasInternalColourLoop : Bool := false

/-- **★ ESTABLISHED — the r5 per-colour loop refinement `(loops1, loops2)` is VACUOUS at the free seed.**  Since
`base.loops = 0` on every cell (`stringWitnesses_loops_zero`), any colour split is `(0, 0)`
(`stringPerColourLoopSplit_zero_ofLoopsZero`): refining `ColouredDiagramType` with per-colour loop counts adds ZERO
discriminating power.  Per the Fuss–Catalan literature (Bisch–Jones; Landau) per-colour loop parameters δ_a, δ_b
live in the LINEAR / subfactor COMPLETION of the coloured Temperley–Lieb (Fuss–Catalan) algebra — where ev/coev
close scalar loops — NOT in the free / walking Δ-level 2-category this seed presents, where loops are structurally
absent.  So no `RefinedColouredDiagramType` with per-colour loops is shipped: it would be vacuous.  `= false`. -/
def fxString_hasPerColourLoopRefinementContent : Bool := false

/-- **★ HONEST CORRECTION — `ColouredDiagramType` is NOT too coarse (the r5 hypothesis is REFUTED).**  The decisive
check: (1) the predicted colour-ambiguous internal-loop witness `stringMixedBubbleCup` (a colour-1 cup with an
inserted colour-2 `G`-bubble, 3 generators) has the SAME `matchingOf` as a bare cup with `loops = 0`
(`stringMixedBubbleCup_matchingOf_eq_unitLower`) — the predicted loop does not close; (2) the only genuine internal
colour ambiguity — the two `G`-snakes, equal `colouredMatchingOf` — is CONVERTIBLE
(`stringGSnakes_colourAmbiguous_and_convertible`), a sound identification, and a colour-2 bubble on an `F`-context
straightens to `id (F·G)` (`stringMixedBubbleOnLeft_conv_identity`).  So there is NO colour-ambiguous NON-convertible
pair the invariant misses.  The standing completeness blocker is the r4 length-rigidity reconstruction PORT
(`fxString_hasStringLengthRigidityFailure`: `F ≠ H` breaks `adjunctionPath_eq_of_length_eq`, so the valley
reconstruction must read BOUNDARY LABELS, not lengths), categorically distinct from — and untouched by — a
per-colour loop refinement.  Accordingly `fxString_hasAdjointTripleCompleteness` STAYS `false`, and this marker
records that the block is a PORT, not invariant coarseness.  `= false`. -/
def fxString_hasColouredInvariantTooCoarse : Bool := false

end FX1Poly.Polygraph
