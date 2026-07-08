import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupMixedReselectionReduction
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcStuckSpineDecided

/-! # ArcStuckCompletenessCharacterization — the general STUCK-case completeness, characterized precisely

The peel-last dichotomy (`ArcStuckSpineNonSingleton`) isolates the walking-adjunction reconstruction's hard core
into the STUCK case: a closed spine (first atom a cup, last atom a cap, no boundary cup, no seed cap), where
`arcStructureOf` is NOT injective (`stuckSpines_arcStructure_eq`) yet the two arc-equal witnesses ARE
swap-connected (`spineTraceEquiv_doubleSnake_nestedSnake`; the decider returns `isTrue`,
`ArcStuckSpineDecided`).  The GENERAL stuck completeness — every two arc-equal closed spines are
`SpineTraceEquiv` — is the sub-regime of the shipped unified target `MixedTailArcCompleteness`
(`ArcCupMixedReselectionReduction`) reached when no owner cup and no seed cap exist.

This file characterizes that residual precisely, walling the two candidate routes the recon named:

  * **(2a) saturation-class membership.**  The FREE decider `decideAtomicTraceEquivViaSaturation`
    (`ClassSaturation`) decides each arc-equal pair by BFS-saturating the seed's swap ~-class and testing
    membership — and `saturateClass_isSound` is UNCONDITIONAL (membership alone gives `AtomicTraceEquiv`, no
    exhaustion gate).  So a UNIFORM "arc-equal ⟹ membership at some fuel" hypothesis would DISCHARGE the whole
    target.  `UniformSaturationMembership` names exactly that hypothesis, and
    `mixedTailArcCompleteness_of_uniformSaturationMembership` proves it SUFFICIENT.  This is the wall: route (2a)
    is NOT a shortcut — it is at least as strong as the theorem it would prove.  The only membership witnesses
    that exist are per-instance kernel `decide`s (`nestedSnake_spine_mem_doubleSnakeSwapClass`); there is no
    uniform-fuel membership lemma over unbounded closed spines, because producing one over all seeds IS the
    completeness (via the unconditional soundness), and the reverse (completeness ⟹ fixed-fuel membership) needs
    the per-seed frontier-exhaustion gate — no fuel bounds all seeds.

  * **(2b) matching-based (Joyal-Street) reconstruction.**  Induct on the planar matching, sliding whole
    zig-zags past each other by interchange, building the swap path directly (NOT by peeling: the peel
    decomposition is separately REFUTED — `ArcStuckHeadLeftCancel.atomicTraceEquiv_notLeftCancellable_atSeed`
    shows the letters are a DYNAMIC, not static Mazurkiewicz, trace).  This is the honest route and is TRUE on
    the hardest known instance, but is research-grade.  The literature pins the ceiling exactly: Delpeuch-Vicary
    (arXiv:1804.07832, LMCS 18:1) Thm 7.8 gives a complete matching invariant only in the CONNECTED case;
    Thm A.21 shows a FLAT matching+counts invariant is INCOMPLETE on disconnected diagrams (enclosed components
    "spin", so faces compare by an UNORDERED SET of sub-components — the complete invariant is a structural
    TREE), and Forest-Mimram (arXiv:2109.05369, MSCS 32.5) 4.3 shows for the SELF-DUAL endo-adjunction full
    coherence FAILS (the bubble endomorphism "is not expected to be an identity"), so universal completeness is
    genuinely open at the seed and false in the self-dual regime.

So the general stuck completeness stays a NAMED deep-open residual: `MixedTailArcCompleteness` restricted to
closed spines, with route (2a) walled circular here and route (2b) the honest (research-grade) direction.  No gate
flip; `fxMode_hasArcStructureReconstruction` stays `false`.

Raw Lean 4 + Init; the sufficiency reduction is the unconditional `saturateClass_isSound` composed with
`AtomicTraceEquiv.toSpineTraceEquiv`, no `decide` on open goals.  Per-declaration `#assert_no_axioms` gated in the
audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Route (2a) — the uniform saturation-membership hypothesis -/

/-- **Route (2a) as one hypothesis.**  For any two boundary-chained walking-adjunction spines over a positive
bottom boundary whose arc structures agree, the second lies in the first's swap-saturation class at SOME fuel.
This is the FREE decider's accept-side witness (`decideAtomicTraceEquivViaSaturation` accepts by finding the
target in the seed's saturated ~-class), lifted from per-instance `decide` to a UNIFORM statement over all closed
(indeed all) configurations.  It is exactly the input that would discharge `MixedTailArcCompleteness` through the
unconditional saturation soundness. -/
def UniformSaturationMembership : Prop :=
  ∀ {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (firstList secondList :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget)),
    SpineBoundaryChained bottomCount firstList →
    SpineBoundaryChained bottomCount secondList →
    0 < bottomCount →
    arcStructureOfSpineList bottomCount firstList
        = arcStructureOfSpineList bottomCount secondList →
    ∃ fuel : Nat,
      secondList ∈ saturateClass adjunctionModeDecEq adjunctionModalityDecEq adjunctionTwoCellDecEq
        fuel firstList

/-! ## Route (2a) is SUFFICIENT — the wall (no shortcut) -/

/-- ★ **Route (2a) discharges the whole target — so it is NOT a shortcut.**  Granted
`UniformSaturationMembership`, `MixedTailArcCompleteness` follows: for each arc-equal pair, the membership
supplies a fuel and a class-membership proof; the UNCONDITIONAL saturation soundness
(`saturateClass_isSound`, no frontier-exhaustion gate) reads off `AtomicTraceEquiv firstList secondList`, and
`AtomicTraceEquiv.toSpineTraceEquiv` lifts it to the block-level `SpineTraceEquiv` the target concludes.  Hence
route (2a)'s uniform membership is AT LEAST as strong as the completeness it would prove — the honest wall on
the saturation-class route: the general "arc-equal ⟹ membership" is the completeness itself, not a weaker
computable step. -/
theorem mixedTailArcCompleteness_of_uniformSaturationMembership
    (membership : UniformSaturationMembership) : MixedTailArcCompleteness := by
  intro overallSource overallTarget bottomCount firstList secondList firstChained secondChained
    seedPositive arcEqual
  obtain ⟨fuel, memberMem⟩ :=
    membership bottomCount firstList secondList firstChained secondChained seedPositive arcEqual
  exact (saturateClass_isSound adjunctionModeDecEq adjunctionModalityDecEq adjunctionTwoCellDecEq
    memberMem).toSpineTraceEquiv

/-! ## The hardest known stuck instance is already covered by (2a) -/

/-- **The hardest known stuck instance is a (2a) witness.**  The nested snake IS in the double snake's
saturation class (`nestedSnake_spine_mem_doubleSnakeSwapClass`), so the double/nested stuck pair — the two
DISTINCT arc-equal four-atom closed spines of `ArcStuckSpineNonSingleton` — is exactly the shape
`UniformSaturationMembership` asserts for ALL closed pairs, and `mixedTailArcCompleteness_of_uniformSaturationMembership`
turns it into the shipped `spineTraceEquiv_doubleSnake_nestedSnake`.  This records that the general residual is
the UNIFORMITY (over all closed configurations), not any single instance — every instance is decided
`isTrue`. -/
theorem stuckHardestInstance_isSaturationMember :
    nestedSnakeOnLeft.spine ∈ doubleSnakeSwapClass 8 :=
  nestedSnake_spine_mem_doubleSnakeSwapClass

/-! ## Honesty marker -/

/-- **Honesty marker — the general STUCK completeness is characterized: (2a) walled circular, (2b) deep-open.**
`UniformSaturationMembership` names route (2a) (arc-equal ⟹ swap-class membership, uniformly), and
`mixedTailArcCompleteness_of_uniformSaturationMembership` proves it SUFFICIENT for the whole target
`MixedTailArcCompleteness` via the unconditional `saturateClass_isSound` + `AtomicTraceEquiv.toSpineTraceEquiv`.
So (2a) is no shortcut — it is at least as strong as the completeness it would prove (the reverse needs the
per-seed frontier-exhaustion gate, and no fuel bounds all seeds, so only per-instance `decide`s exist, e.g.
`stuckHardestInstance_isSaturationMember`).  Route (2b), the matching-based Joyal-Street reconstruction, is the
honest direction but research-grade, with the literature ceiling pinned: Delpeuch-Vicary Thm A.21 (flat
matching+counts is INCOMPLETE on disconnected diagrams; the complete invariant is a structural TREE of unordered
sub-component sets) and Forest-Mimram 4.3 (the SELF-DUAL endo-adjunction is NOT fully coherent).

What this marker does NOT claim: the general stuck completeness itself (a named deep-open residual —
`MixedTailArcCompleteness` on closed spines), nor any refutation of it at the seed (the hardest known instance is
decided `isTrue`, `ArcStuckSpineDecided`).  No gate flip; `fxMode_hasArcStructureReconstruction` stays `false`.
`= true`. -/
def fxMode_hasArcStuckCompletenessCharacterization : Bool := true

end FX1Poly.Polygraph
