import FX1Poly.Polygraph.Homology.CrossedModuleTorusAsphericity

/-! # FX1Poly/Polygraph/Homology/CrossedModuleAsphericityRestingFrontier — the honest resting
    adjudication for the crossed-module `π₂`-vs-`H₂` cross-check program (WP-2GROUP r10)

The r7-r9 arc delivered, zero-axiom and lane-clean, the PRESENTED-scope program:

  * r7 (`CrossedModuleCyclicPower`) — the general boundary `∂ₙ ζₙ = []`, the proper-power certificate
    `sⁿ` (∀ `n ≥ 2`), the commutator opening `[a, b]`, and ★ the `H₂` cross-check star
    `h2CrossCheckStar` (`π₂` and abelianized `H₂` are INDEPENDENT invariants, either vanishing while the
    other does not, in BOTH directions).
  * r8 (`CrossedModuleCyclicPowerInvariant`) — the general `ZZ[ZZ/n]` list-rotation separating invariant,
    mechanizing `π₂⟨s | sⁿ⟩ ≠ 0` at the element level (Lyndon's PROPER-power side).
  * r9 (`CrossedModuleTorusAsphericity`) — the complementary `ZZ[ZZ^2]` torus relation-module invariant,
    its Peiffer-invariance, and the machine-checked kernel-vanishing witnesses + Fox-Jacobian record.

r10 finds the round-sized rung list EMPTY: every remaining node is research-frontier or lane-corrupting.
Following the TOWER-ANICK resting precedent (the explicit in-file resting adjudication + the frontier
named), THIS module records the rest.  It ships NO star flip — `h2CrossCheckStar` stays byte-identical,
pinned here by `rfl` — and names the three legs of the frontier with their classical citations and the
concrete reason each is non-round-sized.

## THE FRONTIER TABLE (three research-frontier / lane-blocked legs)

1. **Lyndon universal leg** — the UNIVERSAL `π₂` claims, at general scope:
     - `π₂⟨s | sⁿ⟩ ≅ ZZ[G]/(N)` surjectivity (r8's `relationModuleIsoStatus`), and
     - `π₂⟨a, b | [a, b]⟩ = 0` via `ZZ[ZZ^2]`-injectivity `ker(∂₂) = 0` + Koszul shift-injectivity
       `y·(1 - b) = 0 ⟹ y = 0` (r9's `relationModuleInjectivityStatus`, `koszulShiftInjectivityStatus`).
     Classical: Lyndon's Identity Theorem — `r` not a proper power ⟺ the relation module is free ⟺ the
     2-complex is aspherical (Lyndon, *Cohomology theory of groups with a single defining relation*,
     Ann. of Math. 52 (1950)).  NON-round-sized: the vanishing/iso direction needs the free-crossed-module
     normal form at general `n` and the domain-injectivity lemma over `ZZ[a^±, b^±]` — a research-frontier
     argument mechanized in NO prover (mathlib4 stops at abstract `groupCohomology.H2` cocycles; no
     relation module, no `π₂`-of-presentation-complex exists anywhere).  CITED, never claimed.

2. **Hopf / relation-module iso leg** — the inherited r6 Hopf-shadow cokernel isomorphism.  Classical:
     Hopf's formula `H₂(G) ≅ (R ∩ [F, F]) / [F, R]` for `R → F → G` a free presentation (Hopf 1942; Brown,
     *Cohomology of Groups*, §II.5) — giving `H₂(ZZ/n) = 0` (rank-1-free `F` ⟹ `[F, F] = 1`) and
     `H₂(ZZ^2) = ZZ` (the single relator is itself a commutator, the Schur multiplier of the free abelian
     group of rank 2).  NON-round-sized: the coker iso is walled behind a Smith-normal-form certificate /
     a `Quot`, both banned in this lane (NO QUOTIENTS; no `SmithNormalForm` import).

3. **Abelianized-`H₂` machine backing leg** — wiring the star's `abelianizedH2` tags to the in-lane
     chain-complex `H₂` machines: `cyclicThreeDegreeTwoHomologyIsZero` (the `ZZ/3` `H₂ = 0` instance) for
     the top row, and a fresh `H₂(T²) = ZZ` chain-complex node for the bottom row.  NON-round-sized: the
     chain-complex sub-tree carries a Homology→Omega edge (`SteinerFoundation.AugmentedDirectedComplex`)
     plus `IntMatrix`; importing it into the currently-clean crossed-module sub-tree would inject that
     edge, violating the "no Homology-Omega edge" law for THIS sub-lane.  It is an ORCHESTRATOR-level
     decision, not a build this round; the `ZZ²` side has no chain-complex instance to wire at all.

## THE `π₂` / `H₂` INDEPENDENCE (why the cross-check pair is canonical)

The two rows sit at opposite ends of the Hopf exact sequence obtained by applying homology to the
universal cover of the presentation 2-complex `K`:

    0 → H₃(K̃) → π₂(K) → H₂(K) → H₂(G) → 0

(Brown-Huebschmann, *Identities among relations*, 1982).  `⟨s | sⁿ⟩` (proper power, non-aspherical):
`π₂ ≠ 0` while `H₂(G) = 0`.  `⟨a, b | [a, b]⟩` (aspherical, `T² = K(ZZ², 1)`): `π₂ = 0` while `H₂(G) = ZZ`.
The presented cross-check `h2CrossCheckStar` IS the canonical instantiation of this independence.

Read the meaning from THIS docstring and the pinned `rfl` facts, never from a name.  An honest rest beats
a padded round: the presented layer is complete; the universal legs are the research frontier. -/

namespace FX1Poly.Polygraph.Homology

/-- The kind of wall standing in front of a resting-frontier leg — each leg has a DIFFERENT reason it is
non-round-sized, so the three constructors name the three distinct wall-kinds honestly. -/
inductive AsphericityFrontierStatus where
  /-- A classical theorem CITED, unmechanized in any proof assistant (mathlib4 stops at abstract `H₂`
  cocycles; no relation module / `π₂`-of-presentation formalization exists). -/
  | classicalCitedResearchFrontier
  /-- An inherited earlier-round residual walled behind a Smith-certificate / `Quot`, both lane-banned. -/
  | inheritedQuotWalledResidual
  /-- Blocked this round by a lane law (the chain-complex sub-tree's Homology→Omega edge); wiring it is an
  orchestrator-level decision, not an in-lane build. -/
  | laneLawBlockedOrchestratorDecision

/-- ★ **The r10 resting frontier** — the three legs that remain after the presented-scope program is
complete, each classified by its honest wall-kind.  No leg is a bounded `rfl`-sized rung. -/
structure CrossedModuleAsphericityRestingFrontier where
  /-- The universal `π₂` iso / vanishing (`⟨s | sⁿ⟩` surjectivity + `⟨a, b | [a, b]⟩` injectivity), Lyndon. -/
  lyndonUniversalLeg : AsphericityFrontierStatus
  /-- The inherited r6 Hopf-shadow cokernel isomorphism (Hopf's formula), Smith-cert / `Quot`-walled. -/
  hopfRelationModuleIsoLeg : AsphericityFrontierStatus
  /-- Wiring the star's `abelianizedH2` tags to the Omega-edged chain-complex `H₂` machines. -/
  abelianizedH2MachineBackingLeg : AsphericityFrontierStatus

/-- ★★ **The resting frontier, filled.**  Lyndon universal = classical research frontier (unmechanized);
Hopf coker iso = inherited `Quot`-walled residual; abelianized-`H₂` backing = lane-law-blocked
(orchestrator decision).  Each closes by `rfl`. -/
def crossedModuleAsphericityRestingFrontier : CrossedModuleAsphericityRestingFrontier :=
  { lyndonUniversalLeg := AsphericityFrontierStatus.classicalCitedResearchFrontier
  , hopfRelationModuleIsoLeg := AsphericityFrontierStatus.inheritedQuotWalledResidual
  , abelianizedH2MachineBackingLeg := AsphericityFrontierStatus.laneLawBlockedOrchestratorDecision }

/-- ★ **No star flip (bottom row).**  The r7 `h2CrossCheckStar` stays byte-identical: the commutator row's
establishment field is still `asphericityResidualR9`, because the universal `π₂⟨a, b | [a, b]⟩ = 0` is the
walled Lyndon leg (NOT delivered this round).  Flipping it would be a fabricated claim; this `rfl` pins the
honest value so any accidental future edit to the star breaks THIS build. -/
theorem crossedModuleAsphericityStarStaysAtR9Residual :
    h2CrossCheckStar.commutatorAsphericalRow.establishment
      = CyclicPowerObligationStatus.asphericityResidualR9 := rfl

/-- ★ **No star flip (top row).**  The proper-power row's establishment stays `shippedThisRound` — the
PRESENTED `π₂⟨s | sⁿ⟩ ≠ 0` was delivered (r8), and nothing about it changes at rest.  `rfl`. -/
theorem crossedModuleAsphericityStarTopRowStaysShipped :
    h2CrossCheckStar.cyclicProperPowerRow.establishment
      = CyclicPowerObligationStatus.shippedThisRound := rfl

/-- ★ **The r10 resting marker.**  The walker RESTS at its honest frontier: the round-sized rung list is
empty; the presented-scope program (general boundary + separating invariant + torus relation-module
invariant + Peiffer-invariance + kernel-vanishing + the `H₂` cross-check star) is complete zero-axiom, and
the three remaining legs (Lyndon universal identity theorem, Hopf / relation-module iso, the Omega-walled
abelianized-`H₂` machine backing) are the research frontier — CITED in the module docstring's frontier
table, never claimed.  No star flip (pinned by the two `rfl` facts above).  An honest rest beats a padded
round. -/
def crossedModuleAsphericityWalkerRestsAtHonestFrontier : Bool := true

end FX1Poly.Polygraph.Homology
