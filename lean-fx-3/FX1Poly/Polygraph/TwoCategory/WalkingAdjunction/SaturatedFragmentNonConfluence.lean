import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SaturatedFragmentNewman
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.OrientedReducer

/-! # SaturatedFragmentNonConfluence — ★★ the fragment's local confluence is FALSE (SAT-NF brick D2)

The planned SAT-NF brick D discharge is IMPOSSIBLE: `SaturatedInterchangeFreeLocallyConfluent`
is refuted, zero-axiom.  The counterexample is the **whiskered snake**
`whiskerLeft R (leftSnake)`:

  * the CONGRUENCE path fires the bare triangle inside the whisker and then collapses the
    whiskered identity — reaching `id (R·L)`;
  * the DISTRIBUTION path fires `whiskerLeftVcomp` at the root, splitting the snake's two
    factors into separately-whiskered `vcomp` factors — and the triangle patterns match only
    BARE factors (`η ▷ L`, `L ◁ ε`), never whisker-wrapped ones, so the distributed snake
    `vcomp (R ◁ (η ▷ L)) (R ◁ (L ◁ ε))` is FROZEN: a normal form distinct from `id`.

One term, two irreducible normal forms — not joinable, so the fragment is not confluent and
(SN + Newman, contrapositively) not locally confluent.  The obstruction is NOT the interchange
(already withdrawn): it is that TERM-LEVEL rewriting with literal triangle patterns loses
redexes under whisker distribution.  Pasting-diagram rewriting (Guiraud–Malbos) does not see
this because diagram redexes are whisker-invariant by construction; a term-level fix would need
CONTEXT-CLOSED triangle rule families (one rule per whisker context — a redesign, not a
discharge).  Consequently the D1 conditionals (`decidableSaturatedFragmentEquational`,
`saturatedFragmentNormalize_isCanonical`) are VACUOUS at this rule set, and the saturated
word-problem decision rides the MATCHING route (SAT-ARC-REC → SAT-COMPLETE → SAT-DECIDE)
exclusively.

  * `whiskeredSnakePeak` / `whiskeredSnakeDistributedNormal` / `whiskeredSnakeIdentityNormal`
    — the peak and its two normal forms;
  * the two reduction chains + the two irreducibility certificates (the brick-B reducer
    computes `none` on both normal forms BY `rfl` — completeness turns the halt into
    irreducibility);
  * ★ `saturatedFragment_notConfluent` — the divergent-normal-forms assembly;
  * ★★ `saturatedFragment_notLocallyConfluent` — Newman contrapositively over the shipped SN.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The whiskered-snake peak and its two normal forms -/

/-- The **whiskered snake** — the left snake under a `whiskerLeft` by `R`: the peak of the
non-joinable pair.  Boundary `R·L ⇒ R·L` at `tip ⟶ tip`. -/
def whiskeredSnakePeak :
    RawTwoCellExpr adjunctionModeSignature
      (composePath (singletonModalityPath AdjunctionModality.right)
        (singletonModalityPath AdjunctionModality.left))
      (composePath (singletonModalityPath AdjunctionModality.right)
        (singletonModalityPath AdjunctionModality.left)) :=
  RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature)
    (singletonModalityPath AdjunctionModality.right) adjunctionSeedLeftSnake

/-- Normal form ONE — the **frozen distributed snake** `(R ◁ (η ▷ L)) ⊟ (R ◁ (L ◁ ε))`:
whisker distribution split the triangle redex across the `vcomp`, and no fragment rule matches
whisker-wrapped snake factors. -/
def whiskeredSnakeDistributedNormal :
    RawTwoCellExpr adjunctionModeSignature
      (composePath (singletonModalityPath AdjunctionModality.right)
        (singletonModalityPath AdjunctionModality.left))
      (composePath (singletonModalityPath AdjunctionModality.right)
        (singletonModalityPath AdjunctionModality.left)) :=
  RawTwoCellExpr.vcomp
    (RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature)
      (singletonModalityPath AdjunctionModality.right) leftSnakeUnitFactor)
    (RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature)
      (singletonModalityPath AdjunctionModality.right) leftSnakeCounitFactor)

/-- Normal form TWO — the **identity** `id (R·L)`: the bare triangle fired inside the whisker,
then the whiskered identity collapsed. -/
def whiskeredSnakeIdentityNormal :
    RawTwoCellExpr adjunctionModeSignature
      (composePath (singletonModalityPath AdjunctionModality.right)
        (singletonModalityPath AdjunctionModality.left))
      (composePath (singletonModalityPath AdjunctionModality.right)
        (singletonModalityPath AdjunctionModality.left)) :=
  RawTwoCellExpr.id (signature := adjunctionModeSignature)
    (composePath (singletonModalityPath AdjunctionModality.right)
      (singletonModalityPath AdjunctionModality.left))

/-! ## The two reduction chains -/

/-- The DISTRIBUTION leg: one root `whiskerLeftVcomp` step splits the whiskered snake. -/
theorem whiskeredSnakePeak_reducesTo_distributed :
    Core.ReflTransClosure (fun cellA cellB => SaturatedStepInterchangeFree cellA cellB)
      whiskeredSnakePeak whiskeredSnakeDistributedNormal :=
  Core.ReflTransClosure.head
    (SaturatedStepInterchangeFree.ofStructural
      (TwoCellStepInterchangeFree.whiskerLeftVcomp (signature := adjunctionModeSignature)
        (singletonModalityPath AdjunctionModality.right)
        leftSnakeUnitFactor leftSnakeCounitFactor))
    (Core.ReflTransClosure.refl _)

/-- The TRIANGLE leg: fire the bare left triangle under the whisker, then collapse the
whiskered identity. -/
theorem whiskeredSnakePeak_reducesTo_identity :
    Core.ReflTransClosure (fun cellA cellB => SaturatedStepInterchangeFree cellA cellB)
      whiskeredSnakePeak whiskeredSnakeIdentityNormal :=
  Core.ReflTransClosure.head
    (SaturatedStepInterchangeFree.whiskerLeftCongr
      (singletonModalityPath AdjunctionModality.right)
      SaturatedStepInterchangeFree.leftBareSnake)
    (Core.ReflTransClosure.head
      (SaturatedStepInterchangeFree.ofStructural
        (TwoCellStepInterchangeFree.whiskerLeftId (signature := adjunctionModeSignature)
          (singletonModalityPath AdjunctionModality.right)
          (singletonModalityPath AdjunctionModality.left)))
      (Core.ReflTransClosure.refl _))

/-! ## Irreducibility — the brick-B reducer halts on both, and its completeness certifies -/

/-- The distributed snake is IRREDUCIBLE: the sound+complete fragment reducer computes `none`
on it (kernel computation), and reducer completeness turns the halt into normality. -/
theorem whiskeredSnakeDistributedNormal_irreducible :
    ∀ next, ¬ SaturatedStepInterchangeFree whiskeredSnakeDistributedNormal next :=
  saturatedReduceOnce_isNormal_of_none rfl

/-- The identity is IRREDUCIBLE — same reducer-halt certificate. -/
theorem whiskeredSnakeIdentityNormal_irreducible :
    ∀ next, ¬ SaturatedStepInterchangeFree whiskeredSnakeIdentityNormal next :=
  saturatedReduceOnce_isNormal_of_none rfl

/-- The two normal forms are DISTINCT — `vcomp` vs `id` head constructors. -/
theorem whiskeredSnake_normalForms_distinct :
    whiskeredSnakeDistributedNormal ≠ whiskeredSnakeIdentityNormal := by
  intro equalForms
  dsimp only [whiskeredSnakeDistributedNormal, whiskeredSnakeIdentityNormal] at equalForms
  nomatch equalForms

/-! ## ★★ The falsification -/

/-- ★ **The saturated interchange-free fragment is NOT confluent**: the whiskered snake
reduces to two distinct irreducible normal forms, which cannot join. -/
theorem saturatedFragment_notConfluent :
    ¬ Core.Confluent
      (fun (cellA cellB : RawTwoCellExpr adjunctionModeSignature
          (composePath (singletonModalityPath AdjunctionModality.right)
            (singletonModalityPath AdjunctionModality.left))
          (composePath (singletonModalityPath AdjunctionModality.right)
            (singletonModalityPath AdjunctionModality.left))) =>
        SaturatedStepInterchangeFree cellA cellB) :=
  notConfluent_of_divergentNormalForms
    whiskeredSnakePeak_reducesTo_distributed
    whiskeredSnakePeak_reducesTo_identity
    whiskeredSnakeDistributedNormal_irreducible
    whiskeredSnakeIdentityNormal_irreducible
    whiskeredSnake_normalForms_distinct

/-- ★★ **The fragment's local confluence is FALSE** — `SaturatedInterchangeFreeLocallyConfluent`
is refuted.  By Newman contrapositively: the fragment IS strongly normalizing, so were it
locally confluent it would be confluent, contradicting the whiskered-snake divergence.  The
SAT-NF brick-D discharge is therefore IMPOSSIBLE at this rule set: term-level rewriting with
literal triangle patterns loses redexes under whisker distribution (the pasting-diagram
convergence of Guiraud–Malbos does not transport to raw terms without context-closed rules). -/
theorem saturatedFragment_notLocallyConfluent :
    ¬ SaturatedInterchangeFreeLocallyConfluent := by
  intro locallyConfluent
  exact notWeaklyConfluent_of_notConfluent
    (WellFounded.intro (fun cell => saturatedStepInterchangeFree_isStronglyNormalizing cell))
    saturatedFragment_notConfluent
    (locallyConfluent
      (sourcePath := composePath (singletonModalityPath AdjunctionModality.right)
        (singletonModalityPath AdjunctionModality.left))
      (targetPath := composePath (singletonModalityPath AdjunctionModality.right)
        (singletonModalityPath AdjunctionModality.left)))

end FX1Poly.Polygraph
