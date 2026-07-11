import FX1Poly.Polygraph.Omega.InvolutionSquierBasis
import FX1Poly.Polygraph.Omega.MonadCoherentPresentation
import FX1Poly.Polygraph.Omega.CyclicThreeDemonstrator
import FX1Poly.Polygraph.Omega.IdempotentSemigroupDemonstrator
import FX1Poly.Polygraph.Omega.PresentationOpDualityWithId
import FX1Poly.Polygraph.Omega.WalkingEquivalencePresentation
import FX1Poly.Polygraph.Omega.FrobeniusMonadPresentation
import FX1Poly.Polygraph.Omega.WalkingStrongMonadPresentation

/-! # Polygraph/Omega/SquierFamilyCensus — the WP-SQUIER family census (the #2082 state, WP-SQUIER r2)

★ **The state of the WP-SQUIER capstone after the family round — a machine-checked census, NOT a
capstone close.**  This file records how many of the decided-9 walkers have an Omega-lane Squier coherent
presentation (four, after this round), which are op-dual-reachable but unshipped (four), and which is
genuinely walled (one — the walking adjunction).  The four shipped presentations are GROUNDED here in a
single machine-checked conjunction (`squierFamilyFourWalkersCoherentlyPresented`), so the count-of-four is
proof-carrying, not a bare tally.

## The Omega-lane Squier COHERENT-PRESENTATION census (the subject of this round)

| Walker                              | Rule / CP shape          | Coherent presentation | Where |
|-------------------------------------|--------------------------|-----------------------|-------|
| walking involution `<s\|ss=>id>`    | 1 / 1                    | shipped               | `InvolutionDemonstrator` + `InvolutionSquierBasis` |
| walking monad `<t\|eta,mu>`         | 2 / 5                    | shipped               | `MonadCoherentPresentation` |
| walking cyclic-3 `<s\|sss=>id>`     | 1 / 2 (new-shape)        | shipped THIS ROUND    | `CyclicThreeDemonstrator` |
| idempotent semigroup `<e\|ee=>e>`   | 1 / 1 (half-globular)    | shipped THIS ROUND    | `IdempotentSemigroupDemonstrator` |
| walking comonad = op(monad)         | 2 / 5                    | op-dual reachable, unshipped | — |
| idempotent comonad = op(idem)       | 1 / 1                    | op-dual reachable, unshipped | — |
| walking KZ = monad (abelianized)    | —                        | op-dual reachable, unshipped | — |
| walking co-KZ = comonad             | —                        | op-dual reachable, unshipped | — |
| walking adjunction                  | non-convergent           | ⛔ WALLED              | — |

→ **4 of 9** decided walkers have an Omega-lane coherent presentation after this round (involution, monad,
cyclic-3, idempotent).  4 are op-dual-reachable but unshipped in Omega.  1 (the adjunction) is genuinely
walled.

## The single walled walker (the exact goal + blocking node)

**JAM — the walking adjunction has NO Omega-lane coherent presentation.**  Goal: the walking adjunction
`<L, R | eta : id => R.L, eps : L.R => id | triangles>` exhibited as a convergent Squier presentation with
its critical pairs joined.  FALSE at this scope: the adjunction rewriting is NON-CONVERGENT — the
Schanuel–Street zig-zag critical branching does not confluently join (the snake `eta`/`eps` triangle
overlaps regenerate). Blocking node: the Schanuel–Street confluence node (the zig-zag critical pair with no
convergent completion).  Recorded by `fxOmega4_walkingAdjunctionCoherentPresentationWalledR2 = true`.

## The four op-dual-reachable-but-unshipped walkers

The comonad, idempotent comonad, KZ, and co-KZ are reachable from the shipped presentations by op-duality
(reverse every 2-cell), but the Squier PRESENTATION does not auto-transport across op-duality the way
homology does (op-duality is unimodular negation on the boundary matrices, so the Homology lane transports;
the presentation's critical-pair JOINS must be re-drawn).  So they are reachable, not shipped this round.
Recorded by `fxOmega4_squierFamilyOpDualReachableUnshippedR2 = true`.

## The multi-object walkers (outside the decided-9)

Brauer / Frobenius are multi-object walkers living in the Amalgam / Brauer lanes — OUTSIDE the decided-9.
They are walled for the SINGLE-MODE `OmegaComputad` family pattern used here (`modeCarrier := Unit`): the
family idiom does not encode multi-object presentations without a mode-carrier upgrade.  Recorded by
`fxOmega4_multiObjectWalkersOutsideDecidedNineR2 = true`.

## The Homology-lane contrast (NAMED only — NOT imported, the r1 read-only discipline)

Do NOT conflate this census with the Homology-lane census.  There, 8 of 9 have COMPUTED homology
(`PresentationOpDualityHomology`, `walkersWithComputedHomologyCountAfterOpDuality = 8`), because homology
transports through op-duality (unimodular negation) whereas Squier PRESENTATIONS do not auto-transport.
Homology's sole residual is ALSO the walking adjunction.  The idempotent-semigroup homology is `H1 = 0`
(the unit factor); cyclic-3 is `H1 = ZZ/3`.  These correspondences are NAMED here, never imported.

## NOT a capstone close (honest)

The WP-SQUIER capstone (the convergent-implies-coherent story for EVERY decided walker) is NOT closed by
this round.  `fxOmega4_squierCapstoneClosedR2 = false`: four of nine are shipped, four are op-dual-
reachable-but-unshipped, one is genuinely walled — the capstone needs the walled walker (the adjunction)
either resolved or PERMANENTLY walled, and the four op-dual reachables shipped or waived.  This file is the
state ledger, not the close.

Raw Lean 4 + Init; a machine-checked census (a label enumeration + a grounded conjunction + `Bool`
markers), every declaration axiom-free.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

/-! ## The decided-9 walker enumeration -/

/-- The **decided-9 walkers** — the nine walkers whose word problem is decided (the WP-SQUIER family).
This is the census index; the coherent-presentation status of each is `squierFamilyStatus`. -/
inductive SquierFamilyWalker
  /-- The walking involution `<s | s.s => id>` (1 rule / 1 critical pair). -/
  | walkingInvolution
  /-- The walking monad `<t | eta, mu>` (2 rules / 5 critical pairs). -/
  | walkingMonad
  /-- The walking cyclic-3 `<s | s.s.s => id>` (1 rule / 2 critical pairs, new-shape). -/
  | walkingCyclicThree
  /-- The idempotent semigroup `<e | e.e => e>` (1 rule / 1 critical pair, half-globular). -/
  | idempotentSemigroup
  /-- The walking comonad = op(monad). -/
  | walkingComonad
  /-- The idempotent comonad = op(idempotent semigroup). -/
  | idempotentComonad
  /-- The walking KZ doctrine = monad (abelianized). -/
  | walkingKZ
  /-- The walking co-KZ doctrine = comonad. -/
  | walkingCoKZ
  /-- The walking adjunction (non-convergent — the walled residual). -/
  | walkingAdjunction

/-- The complete enumeration of the decided-9 walkers — NINE, listed. -/
def allSquierFamilyDecidedWalkers : List SquierFamilyWalker :=
  [.walkingInvolution, .walkingMonad, .walkingCyclicThree, .idempotentSemigroup,
    .walkingComonad, .idempotentComonad, .walkingKZ, .walkingCoKZ, .walkingAdjunction]

/-- ★ **The decided-walker count is exactly NINE** — kernel-checked (`rfl`). -/
theorem squierFamilyDecidedWalkerCountIsNine : allSquierFamilyDecidedWalkers.length = 9 := rfl

/-- ★ **The decided-9 enumeration is EXHAUSTIVE** — every walker appears (full case split). -/
theorem allSquierFamilyDecidedWalkersExhaustive :
    ∀ walker : SquierFamilyWalker, walker ∈ allSquierFamilyDecidedWalkers
  | .walkingInvolution => List.Mem.head _
  | .walkingMonad => List.Mem.tail _ (List.Mem.head _)
  | .walkingCyclicThree => List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  | .idempotentSemigroup =>
      List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  | .walkingComonad =>
      List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
  | .idempotentComonad =>
      List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.head _)))))
  | .walkingKZ =>
      List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
  | .walkingCoKZ =>
      List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
  | .walkingAdjunction =>
      List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))

/-! ## The coherent-presentation status of each walker -/

/-- The **coherent-presentation status** of a decided walker over the Omega-lane Squier substrate. -/
inductive SquierFamilyCoherentPresentationStatus
  /-- A coherent presentation is shipped over the `OmegaComputad` substrate. -/
  | shippedOmegaLane
  /-- Reachable by op-duality from a shipped presentation, but not shipped in the Omega lane this round. -/
  | opDualReachableUnshipped
  /-- Genuinely walled — the presentation is non-convergent, no coherent completion at this scope. -/
  | walled

/-- The status map: four shipped, four op-dual-reachable-but-unshipped, one walled (the adjunction). -/
def squierFamilyStatus : SquierFamilyWalker → SquierFamilyCoherentPresentationStatus
  | .walkingInvolution => .shippedOmegaLane
  | .walkingMonad => .shippedOmegaLane
  | .walkingCyclicThree => .shippedOmegaLane
  | .idempotentSemigroup => .shippedOmegaLane
  | .walkingComonad => .opDualReachableUnshipped
  | .idempotentComonad => .opDualReachableUnshipped
  | .walkingKZ => .opDualReachableUnshipped
  | .walkingCoKZ => .opDualReachableUnshipped
  | .walkingAdjunction => .walled

/-- The four walkers with a SHIPPED Omega-lane coherent presentation, enumerated. -/
def allSquierFamilyShippedWalkers : List SquierFamilyWalker :=
  [.walkingInvolution, .walkingMonad, .walkingCyclicThree, .idempotentSemigroup]

/-- ★ **The shipped coherent-presentation count is exactly FOUR** — kernel-checked (`rfl`). -/
theorem squierFamilyShippedWalkerCountIsFour : allSquierFamilyShippedWalkers.length = 4 := rfl

/-! ## The grounded census — the four shipped presentations, machine-checked in one conjunction -/

/-- ★ **The four-shipped-presentations statement (the grounded census content).**  A `Prop` conjunction of
the four Omega-lane coherent-presentation statements: the involution's coherent resolution, the walking
monad's five-pair presentation, the cyclic-3 two-pair presentation, and the idempotent semigroup's
one-pair presentation. -/
def SquierFamilyFourWalkersCoherentlyPresentedStatement : Prop :=
  InvolutionCoherentResolution ∧
  MonadWalkerCoherentPresentationStatement ∧
  CyclicThreeWalkerCoherentPresentationStatement ∧
  IdempotentSemigroupWalkerCoherentPresentationStatement

/-- ★★ **THE GROUNDED FOUR-OF-NINE CENSUS.**  All four shipped Omega-lane Squier coherent presentations
assembled into ONE machine-checked datum — so `squierFamilyShippedWalkerCountIsFour` is proof-carrying,
not a bare tally.  Each conjunct is the already-verified coherent presentation of its walker
(`involutionCriticalPairResolved`, `monadWalkerCoherentPresentation`,
`cyclicThreeWalkerCoherentPresentation`, `idempotentSemigroupWalkerCoherentPresentation`). -/
theorem squierFamilyFourWalkersCoherentlyPresented :
    SquierFamilyFourWalkersCoherentlyPresentedStatement :=
  ⟨involutionCriticalPairResolved, monadWalkerCoherentPresentation,
    cyclicThreeWalkerCoherentPresentation, idempotentSemigroupWalkerCoherentPresentation⟩

/-! ## The census markers -/

/-- ★ **THE FOUR-OF-NINE CENSUS (recorded).**  `= true` records the WP-SQUIER family state after the r2
family round: four of the decided-9 walkers (involution, monad, cyclic-3, idempotent) have an Omega-lane
Squier coherent presentation, machine-checked by `squierFamilyFourWalkersCoherentlyPresented`.  Two of the
four (cyclic-3, idempotent) shipped THIS ROUND. -/
def fxOmega4_squierFamilyCoherentPresentationCensusFourOfNineR2 : Bool := true

/-- ★ **WALL — the walking adjunction has NO Omega-lane coherent presentation.**  `= true` records the
sole walled walker of the decided-9: the walking adjunction is NON-CONVERGENT, its Schanuel–Street zig-zag
critical branching does not confluently join.  Blocking node: the Schanuel–Street confluence node (the
zig-zag critical pair with no convergent completion).  The capstone needs this either resolved or
permanently walled. -/
def fxOmega4_walkingAdjunctionCoherentPresentationWalledR2 : Bool := true

/-- ★ **The four op-dual-reachables are UNSHIPPED in Omega.**  `= true` records that the comonad,
idempotent comonad, KZ, and co-KZ are reachable from the shipped presentations by op-duality but not
shipped in the Omega lane this round (the Squier PRESENTATION does not auto-transport across op-duality the
way homology does — the critical-pair joins must be re-drawn). -/
def fxOmega4_squierFamilyOpDualReachableUnshippedR2 : Bool := true

/-- ★ **The multi-object walkers are OUTSIDE the decided-9.**  `= true` records that Brauer / Frobenius
(Amalgam / Brauer lanes) are walled for the single-mode `OmegaComputad` family pattern (`modeCarrier :=
Unit`): the family idiom does not encode multi-object presentations without a mode-carrier upgrade. -/
def fxOmega4_multiObjectWalkersOutsideDecidedNineR2 : Bool := true

/-- ★ **THE WP-SQUIER CAPSTONE IS NOT CLOSED (honest).**  `= false` records that the capstone (the
convergent-implies-coherent story for EVERY decided walker) is NOT closed by the r2 family round: four of
nine shipped, four op-dual-reachable-but-unshipped, one (the adjunction) genuinely walled.  The capstone
needs the walled adjunction resolved or PERMANENTLY walled, and the four op-dual reachables shipped or
waived.  Set `true` only when the whole decided-9 is decided or honestly walled. -/
def fxOmega4_squierCapstoneClosedR2 : Bool := false

/-! ## The r3 op-dual round — the two genuine op-transports shipped (WP-SQUIER r3, #2082)

★ **The op-dual round advances the census: the walking comonad and the idempotent comonad now have GENUINE
Omega-lane coherent presentations, transported generically from their shipped duals**
(`PresentationOpDualityWithId.lean`).  The r2 marker `fxOmega4_squierFamilyOpDualReachableUnshippedR2` recorded
that the four op-dual reachables were UNSHIPPED at r2; r3 SHIPS the two GENUINE ones (comonad, idempotent
comonad).  The other two (KZ, co-KZ) are FREE-RIDERS — not op-transports at all but the SAME presentation with
the directed rewrite order forgotten:

  * **walking KZ = monad (order forgotten).**  KZ's rewrite rules ARE the monad's; the KZ directed preorder
    (`KZTwoCellLE`, no `symm`) is extra structure the Squier-coherent fragment forgets.  So KZ's coherent
    presentation is ALREADY `monadWalkerCoherentPresentation` — reachable by forgetting the order, not by op.
  * **walking co-KZ = comonad (order forgotten).**  co-KZ = op(KZ) = op(monad) = comonad at the presentation
    level; ships IFF the comonad ships (same presentation).

So the honest count after r3 is SIX GENUINE Omega-lane coherent presentations (four r2 + comonad + idempotent
comonad), and EIGHT of nine presentation-covered when the two free-riders (KZ rides monad, co-KZ rides comonad)
are counted — matching the Homology lane's `walkersWithComputedHomologyCountAfterOpDuality = 8`, NAMED here,
not imported.  The sole residual is the walking adjunction (walled, below).

## The honest scope — PRESENTATION transport, NOT convergence transport

The r3 transport ships the coherent-presentation DATA (critical-pair rows, generating 3-cells, peak / valley
joins, per-pair resolutions, the least-congruence UP — every one a `SaturatedConvOverWithId` derivation
transported through `op`), NEVER convergence.  The reversed rules `t => t.t`, `e => e.e` are NON-TERMINATING
(identities grow), so the op-dual rewriting systems are NOT convergent.  The transport takes ZERO termination /
convergence input — exactly the H2-WALKERS precedent (there the HOMOLOGY transported under op-duality's
unimodular negation while convergence did not need to; here the coherent-presentation DATA transports while
convergence does not need to).  Recorded by `fxOmega4_squierOpDualPresentationNotConvergenceR3`. -/

/-- ★ **The two-genuine-op-duals statement (the r3 grounded census extension).**  A `Prop` conjunction of the
two GENUINE op-dual Omega-lane coherent presentations: the walking comonad (= op(monad), five pairs) and the
idempotent comonad (= op(idempotent semigroup), one pair), each transported generically from its shipped dual
through `opCriticalPairResolved`. -/
def SquierFamilyTwoGenuineOpDualsCoherentlyPresentedStatement : Prop :=
  ComonadWalkerCoherentPresentationStatement ∧
  IdempotentComonadWalkerCoherentPresentationStatement

/-- ★★ **THE GROUNDED TWO-GENUINE-OP-DUALS CENSUS (r3).**  Both genuine op-dual Omega-lane coherent
presentations assembled into ONE machine-checked datum — so the r3 op-dual advance is proof-carrying, not a
bare marker.  Each conjunct is the already-verified op-transported coherent presentation of its walker
(`comonadWalkerCoherentPresentation`, `idempotentComonadWalkerCoherentPresentation`). -/
theorem squierFamilyTwoGenuineOpDualsCoherentlyPresented :
    SquierFamilyTwoGenuineOpDualsCoherentlyPresentedStatement :=
  ⟨comonadWalkerCoherentPresentation, idempotentComonadWalkerCoherentPresentation⟩

/-- ★ **The six-genuine-of-nine statement (r3).**  The four r2 shipped presentations conjoined with the two
r3 genuine op-duals — the machine-checked content behind the six-genuine count. -/
def SquierFamilySixWalkersCoherentlyPresentedStatement : Prop :=
  SquierFamilyFourWalkersCoherentlyPresentedStatement ∧
  SquierFamilyTwoGenuineOpDualsCoherentlyPresentedStatement

/-- ★★ **THE GROUNDED SIX-GENUINE-OF-NINE CENSUS (r3).**  The four r2 shipped presentations AND the two r3
genuine op-duals, assembled into ONE machine-checked conjunction — so the six-genuine count is proof-carrying.
KZ and co-KZ additionally ride the monad / comonad presentations (free-riders, same presentation data), so
eight of nine are presentation-covered; the walking adjunction remains the sole walled residual. -/
theorem squierFamilySixWalkersCoherentlyPresented :
    SquierFamilySixWalkersCoherentlyPresentedStatement :=
  ⟨squierFamilyFourWalkersCoherentlyPresented, squierFamilyTwoGenuineOpDualsCoherentlyPresented⟩

/-- The six walkers with a GENUINE Omega-lane coherent presentation after r3 (four r2 shipped + the two r3
op-duals), enumerated. -/
def allSquierFamilyGenuinelyPresentedWalkersAfterR3 : List SquierFamilyWalker :=
  [.walkingInvolution, .walkingMonad, .walkingCyclicThree, .idempotentSemigroup,
    .walkingComonad, .idempotentComonad]

/-- ★ **The genuine-presentation count is exactly SIX after r3** — kernel-checked (`rfl`). -/
theorem squierFamilyGenuinelyPresentedWalkerCountIsSixAfterR3 :
    allSquierFamilyGenuinelyPresentedWalkersAfterR3.length = 6 := rfl

/-! ## The r3 census markers -/

/-- ★ **THE TWO GENUINE OP-DUALS SHIP IN THE CENSUS (r3).**  `= true` records that the walking comonad and
the idempotent comonad now have GENUINE Omega-lane coherent presentations
(`squierFamilyTwoGenuineOpDualsCoherentlyPresented`), machine-checked — a genuine advance over the r2 state
`fxOmega4_squierFamilyOpDualReachableUnshippedR2` (which recorded them as reachable-but-unshipped at r2). -/
def fxOmega4_squierFamilyTwoGenuineOpDualsShippedInCensusR3 : Bool := true

/-- ★ **EIGHT OF NINE PRESENTATION-COVERED (r3).**  `= true` records that eight of the decided-9 walkers are
presentation-covered after r3: SIX with a genuine Omega-lane coherent presentation
(`squierFamilyGenuinelyPresentedWalkerCountIsSixAfterR3`) plus TWO free-riders (KZ rides the monad
presentation, co-KZ rides the comonad presentation — same presentation data with the directed order
forgotten).  Matches the Homology lane's `walkersWithComputedHomologyCountAfterOpDuality = 8`, NAMED not
imported.  The sole residual is the walled walking adjunction. -/
def fxOmega4_squierFamilyPresentationCoveredEightOfNineR3 : Bool := true

/-- ★ **THE FREE-RIDER CAVEAT (honest).**  `= true` records that KZ and co-KZ are NOT independent op-transports:
KZ = monad and co-KZ = comonad at the presentation level (the directed KZ / co-KZ order is extra structure the
Squier-coherent fragment forgets), so only TWO of the four op-dual reachables (comonad, idempotent comonad) are
GENUINE op-transports; KZ / co-KZ ride the monad / comonad presentations.  Do not overclaim four independent
op-transports. -/
def fxOmega4_squierKZRidesMonadCoKZRidesComonadR3 : Bool := true

/-! ## The #2082 endgame ledger after r3 (B4 — what the capstone still owes)

★ **The capstone's presentation-census leg is complete (8 of 9 presentation-covered + 1 walled); its DEEP leg
is the OMEGA-5 remainder.**  After r3 the WP-SQUIER capstone (`fxOmega4_squierCapstoneClosedR3 = false`) still
owes exactly two walls — NEITHER closed by r3, both explicitly the OMEGA-5 handoff:

  1. **The adjunction wall (JAM).**  The sole non-census residual.  Goal: the walking adjunction
     `<L, R | eta : id => R.L, eps : L.R => id | triangles>` exhibited as a convergent Squier presentation with
     its critical pairs joined.  FALSE at this scope: the adjunction rewriting is NON-CONVERGENT — the
     Schanuel-Street zig-zag critical branching does not confluently join (the snake `eta` / `eps` triangle
     overlaps regenerate).  Blocking node: the Schanuel-Street confluence node (the zig-zag critical pair with
     no convergent completion).  The adjunction is essentially SELF-DUAL (op swaps `L <-> R`, `eta <-> eps` to
     an adjunction of the same walking shape), so op-duality yields NOTHING for it — it is walled either way.
     Recorded by `fxOmega4_squierCapstoneRemainingAdjunctionWallR3`.
  2. **The full-homotopy-basis wall (OMEGA-5 handoff).**  EVERY shipped and op-dual walker ships fragment scope
     only (`*FullHomotopyBasisReached = false` uniformly).  The full basis (every parallel 2-path pair
     3-cell-homotopic) needs the five normalizer obligations named in `CyclicThreeDemonstrator` /
     `IdempotentSemigroupDemonstrator`: (1) `TwoPath` NF-directed syntax; (2) a STRUCTURAL-FUEL `twoPathSize`
     measure (the load-bearing wall — must avoid `WellFounded.fix`, whose `propext` / `Quot.sound` leak is the
     Init-only wall); (3) completeness of the generating 3-cells (count certificate load-bearing at cyclic-3);
     (4) the ORTHOGONALITY 3-cells (UNSHIPPED — the concrete missing datum, the disjoint-redex commutation
     squares); (5) Newman-at-dim-3.  Recorded by `fxOmega4_squierCapstoneRemainingFullBasisNormalizerR3`.

Honest capstone state after r3: *"8 of 9 presentation-covered (6 genuine + 2 free-riders) + 1 permanently-open
adjunction; full homotopy basis + adjunction confluence remain open."*  The capstone is NOT closed. -/

/-- ★ **REMAINING WALL — the adjunction (r3).**  `= true` records that the walking adjunction is still the sole
non-census residual after r3: NON-CONVERGENT (Schanuel-Street zig-zag), and SELF-DUAL so op-duality yields
nothing.  Closes only by a decision / refutation of the adjunction confluence, or by accepting it as
permanently walled.  Blocking node: the Schanuel-Street confluence node. -/
def fxOmega4_squierCapstoneRemainingAdjunctionWallR3 : Bool := true

/-- ★ **REMAINING WALL — the full homotopy basis normalizer (r3, OMEGA-5 handoff).**  `= true` records that the
full homotopy basis for EVERY walker (shipped and op-dual) is still unreached: it needs the five normalizer
obligations (NF-directed 2-path syntax, structural-fuel `twoPathSize` avoiding `WellFounded.fix`, generating
3-cell completeness, the UNSHIPPED orthogonality 3-cells, Newman-at-dim-3).  The concrete missing datum is the
orthogonality 3-cells; the load-bearing wall is the structural-fuel measure. -/
def fxOmega4_squierCapstoneRemainingFullBasisNormalizerR3 : Bool := true

/-- ★ **THE WP-SQUIER CAPSTONE IS STILL NOT CLOSED (honest, r3).**  `= false` records that the capstone is NOT
closed after the r3 op-dual round: 8 of 9 are presentation-covered (six genuine Omega-lane presentations + KZ /
co-KZ free-riders), but the walking adjunction is walled (self-dual, op yields nothing) and EVERY walker's full
homotopy basis is unreached (the normalizer machine — obligations 1-5, orthogonality UNSHIPPED, structural-fuel
wall — is the OMEGA-5 remainder).  Set `true` only when the adjunction is decided or permanently walled AND the
full basis is reached. -/
def fxOmega4_squierCapstoneClosedR3 : Bool := false

/-! ## The WP-EQUIV extension — the two walking-equivalence walkers (additive, #2068)

★ **The census EXTENSION for the walking equivalence — ADDITIVE, the shipped decided-9 census UNTOUCHED.**
The walking equivalence is NOT one of the decided-9 (its BARE 2-cell word problem is the open winding
problem, `fxEquiv_bareEquivalenceParallelUniquenessOpen`), so its two walkers are recorded here as a SEPARATE
extension rather than grown into `allSquierFamilyDecidedWalkers` (whose count theorem
`squierFamilyDecidedWalkerCountIsNine` keeps its name and meaning).  Both walkers have SHIPPED Omega-lane
coherent presentations (`WalkingEquivalencePresentation.lean`): the walking equivalence (four iso-cancellation
rows) and the walking adjoint equivalence (+ two triangle rows).  This is the FIRST two-object Omega walker —
the genuine `modeCarrier := Bool` upgrade the r2 census's `fxOmega4_multiObjectWalkersOutsideDecidedNineR2`
flagged as needed.  The capstone marker `fxOmega4_squierCapstoneClosedR3` is NOT flipped. -/

/-- The two **walking-equivalence walkers** — the census extension (additive; NOT part of the decided-9). -/
inductive SquierFamilyEquivalenceWalker
  /-- The walking equivalence `<f, g | eta, etaInv, eps, epsInv | four iso-cancellations>`. -/
  | walkingEquivalence
  /-- The walking adjoint equivalence (+ two triangle rows). -/
  | walkingAdjointEquivalence

/-- The complete enumeration of the walking-equivalence walkers — TWO, listed. -/
def allSquierFamilyEquivalenceWalkers : List SquierFamilyEquivalenceWalker :=
  [.walkingEquivalence, .walkingAdjointEquivalence]

/-- ★ **The walking-equivalence walker count is exactly TWO** — kernel-checked (`rfl`). -/
theorem squierFamilyEquivalenceWalkerCountIsTwo : allSquierFamilyEquivalenceWalkers.length = 2 := rfl

/-- ★ **The equivalence-walker enumeration is EXHAUSTIVE** — both walkers appear. -/
theorem allSquierFamilyEquivalenceWalkersExhaustive :
    ∀ walker : SquierFamilyEquivalenceWalker, walker ∈ allSquierFamilyEquivalenceWalkers
  | .walkingEquivalence => List.Mem.head _
  | .walkingAdjointEquivalence => List.Mem.tail _ (List.Mem.head _)

/-- The coherent-presentation status of each equivalence walker — both SHIPPED in the Omega lane. -/
def squierFamilyEquivalenceStatus :
    SquierFamilyEquivalenceWalker → SquierFamilyCoherentPresentationStatus
  | .walkingEquivalence => .shippedOmegaLane
  | .walkingAdjointEquivalence => .shippedOmegaLane

/-- ★ **The two-equivalence-walkers-presented statement.**  A `Prop` conjunction of the two shipped Omega-lane
coherent presentations: the walking equivalence (four iso-cancellations) and the walking adjoint equivalence
(+ two triangles). -/
def SquierFamilyEquivalenceWalkersPresentedStatement : Prop :=
  WalkingEquivalenceCoherentPresentationStatement ∧
  WalkingAdjointEquivalenceCoherentPresentationStatement

/-- ★★ **THE GROUNDED TWO-EQUIVALENCE-WALKERS CENSUS (#2068).**  Both shipped Omega-lane coherent
presentations assembled into ONE machine-checked datum — so the census extension is proof-carrying, not a bare
tally.  Each conjunct is the already-verified coherent presentation of its walker
(`walkingEquivalenceCoherentPresentation`, `walkingAdjointEquivalenceCoherentPresentation`). -/
theorem squierFamilyEquivalenceWalkersPresented : SquierFamilyEquivalenceWalkersPresentedStatement :=
  ⟨walkingEquivalenceCoherentPresentation, walkingAdjointEquivalenceCoherentPresentation⟩

/-- ★ **THE TWO WALKING-EQUIVALENCE WALKERS ARE PRESENTED IN THE CENSUS (#2068).**  `= true` records that both
the walking equivalence and the walking adjoint equivalence have SHIPPED Omega-lane coherent presentations
(`squierFamilyEquivalenceWalkersPresented`), machine-checked — the WP-EQUIV r1 census tie-in, recorded
additively without touching the shipped decided-9. -/
def fxOmega4_walkingEquivalenceWalkersPresentedInCensus : Bool := true

/-- ★ **THE FIRST TWO-OBJECT OMEGA WALKER (census).**  `= true` records that the walking equivalence is the
first Omega walker outside the single-mode (`modeCarrier := Unit`) family pattern — the genuine
`modeCarrier := Bool` upgrade the r2 marker `fxOmega4_multiObjectWalkersOutsideDecidedNineR2` flagged as the
missing datum for multi-object walkers.  Now landed for the two-object equivalence. -/
def fxOmega4_walkingEquivalenceFirstTwoObjectOmegaWalkerInCensus : Bool := true

/-- ★ **WALL — the BARE walking-equivalence word problem is OPEN (census, #2068, honest).**  `= false` records
that the walking equivalence is NOT part of the DECIDED-9: its bare 2-cell parallel-uniqueness is the open
winding word problem (`fxEquiv_bareEquivalenceParallelUniquenessOpen`), so its walkers are a census EXTENSION,
not decided-9 members.  The ADJOINT walker's parallel-uniqueness is exercised (contractibility) but the full
quantified decision is the OMEGA-5 normalizer handoff. -/
def fxOmega4_bareWalkingEquivalenceWordProblemOpenInCensus : Bool := false

/-! ## The WP-FROBMONAD extension — the walking Frobenius monad (additive, #2070)

★ **The census EXTENSION for the walking Frobenius monad — ADDITIVE, the shipped decided-9 census and the
multi-object marker UNTOUCHED.**  The SINGLE-OBJECT walking Frobenius monad
`<s | mu, eta, delta, epsilon | monad + comonad + two Frobenius rows>` has a SHIPPED Omega-lane coherent
presentation (`FrobeniusMonadPresentation.lean`, twelve critical pairs).  It is NOT one of the decided-9
(its bare 2-cell word problem is walled at non-commutativity + 2Cob-genus,
`fxFrob_completenessWalledAtNonCommutativityAndGenus`), so it is recorded here as a SEPARATE extension
rather than grown into `allSquierFamilyDecidedWalkers` (whose count theorem
`squierFamilyDecidedWalkerCountIsNine` keeps its name and meaning).  The r2 marker
`fxOmega4_multiObjectWalkersOutsideDecidedNineR2` (which says Brauer / Frobenius are MULTI-object walkers)
is left UNTOUCHED — it is correct for the multi-object Frobenius PROP, but IMPRECISE for the single-object
Frobenius MONAD, so a NEW marker below records the distinction. -/

/-- The single **walking-Frobenius-monad walker** — the census extension (additive; NOT part of the
decided-9; DISTINCT from the multi-object Frobenius PROP). -/
inductive SquierFamilyFrobeniusWalker
  /-- The single-object walking Frobenius monad `<s | mu, eta, delta, epsilon>`. -/
  | walkingFrobeniusMonad

/-- The complete enumeration of the walking-Frobenius-monad walkers — ONE, listed. -/
def allSquierFamilyFrobeniusWalkers : List SquierFamilyFrobeniusWalker := [.walkingFrobeniusMonad]

/-- ★ **The walking-Frobenius-monad walker count is exactly ONE** — kernel-checked (`rfl`). -/
theorem squierFamilyFrobeniusWalkerCountIsOne : allSquierFamilyFrobeniusWalkers.length = 1 := rfl

/-- ★ **The Frobenius-walker enumeration is EXHAUSTIVE** — the single walker appears. -/
theorem allSquierFamilyFrobeniusWalkersExhaustive :
    ∀ walker : SquierFamilyFrobeniusWalker, walker ∈ allSquierFamilyFrobeniusWalkers
  | .walkingFrobeniusMonad => List.Mem.head _

/-- The coherent-presentation status of the Frobenius-monad walker — SHIPPED in the Omega lane. -/
def squierFamilyFrobeniusStatus :
    SquierFamilyFrobeniusWalker → SquierFamilyCoherentPresentationStatus
  | .walkingFrobeniusMonad => .shippedOmegaLane

/-- ★ **The walking-Frobenius-monad-presented statement.**  The shipped Omega-lane coherent presentation:
the twelve-critical-pair bundle (5 monad + 5 comonad + 2 Frobenius). -/
def SquierFamilyFrobeniusWalkerPresentedStatement : Prop :=
  FrobMonadWalkerCoherentPresentationStatement

/-- ★★ **THE GROUNDED WALKING-FROBENIUS-MONAD CENSUS (#2070).**  The shipped Omega-lane coherent presentation
assembled as one machine-checked datum — so the census extension is proof-carrying, not a bare tally.  The
conjunct is the already-verified coherent presentation of the walker
(`frobMonadWalkerCoherentPresentation`, all twelve critical pairs resolved modulo strict). -/
theorem squierFamilyFrobeniusWalkerPresented : SquierFamilyFrobeniusWalkerPresentedStatement :=
  frobMonadWalkerCoherentPresentation

/-- ★ **THE WALKING FROBENIUS MONAD IS PRESENTED IN THE CENSUS (#2070).**  `= true` records that the
single-object walking Frobenius monad has a SHIPPED Omega-lane coherent presentation
(`squierFamilyFrobeniusWalkerPresented`), machine-checked — the WP-FROBMONAD r1 census tie-in, recorded
additively without touching the shipped decided-9. -/
def fxOmega4_walkingFrobeniusMonadPresentedInCensus : Bool := true

/-- ★ **THE SINGLE-OBJECT FROBENIUS MONAD HAS AN OMEGA PRESENTATION (census, #2070).**  `= true` records the
distinction the r2 marker `fxOmega4_multiObjectWalkersOutsideDecidedNineR2` did NOT make: that marker is
correct for the MULTI-object Frobenius PROP (Brauer / 2Cob, still walled for the single-mode family), but the
SINGLE-object walking Frobenius MONAD is a DISTINCT walker that NOW has a single-mode (`modeCarrier := Unit`)
Omega presentation (four 2-cell generators, twelve critical pairs).  The multi-object marker is left
untouched; this records the single-object landing. -/
def fxOmega4_singleObjectFrobeniusMonadHasOmegaPresentation : Bool := true

/-- ★ **WALL — the bare Frobenius-monad DECISION stays walled (census, #2070, honest).**  `= false` records
that the single-object walking Frobenius monad is NOT part of the DECIDED-9: its full 2-cell word-problem
decision is walled at two named nodes — non-commutativity (the open `BRAUER-BREACH`) and 2Cob-genus
(`fxFrob_has2CobGenus = false`), the `TwoCategory/Frobenius/SpiderCompleteness` decision being for the
EXTRASPECIAL-COMMUTATIVE theory only (NAMED, not transferred).  The Omega r1 ships the coherent presentation
+ the weak four-count soundness invariant, not the decision. -/
def fxOmega4_bareFrobeniusMonadWordProblemWalledInCensus : Bool := false

/-! ## The WP-STRONG extension — the walking strong monad (additive, #2189)

★ **The census EXTENSION for the walking strong monad — ADDITIVE, the shipped decided-9 census and the
multi-object marker UNTOUCHED.**  The SINGLE-OBJECT walking strong monad
`<c, t | eta, mu, st : c.t => t.c | monad + two strength rows>` has a SHIPPED Omega-lane coherent
presentation (`WalkingStrongMonadPresentation.lean`, seven critical pairs — the walking distributive law
minus the c-side monad structure).  It is NOT one of the decided-9 (its full 2-cell word problem is walled
at the two-colour monotone-map model, the SAME node as the distributive law,
`fxStrong_fullTwoCellDecisionWalledAtTwoColourMonotoneMap`), so it is recorded here as a SEPARATE extension
rather than grown into `allSquierFamilyDecidedWalkers` (whose count theorem
`squierFamilyDecidedWalkerCountIsNine` keeps its name and meaning).  Its 1-cell word problem IS decided by
verbatim Parikh transport of the distributive law's (`strongMonadConv_iffSameCount`).  The r2 marker
`fxOmega4_multiObjectWalkersOutsideDecidedNineR2` is left UNTOUCHED — the strong monad is single-object and
fits the `modeCarrier := Unit` family pattern. -/

/-- The single **walking-strong-monad walker** — the census extension (additive; NOT part of the decided-9;
a SUB-presentation of the walking distributive law). -/
inductive SquierFamilyStrongWalker
  /-- The single-object walking strong monad `<c, t | eta, mu, st>`. -/
  | walkingStrongMonad

/-- The complete enumeration of the walking-strong-monad walkers — ONE, listed. -/
def allSquierFamilyStrongWalkers : List SquierFamilyStrongWalker := [.walkingStrongMonad]

/-- ★ **The walking-strong-monad walker count is exactly ONE** — kernel-checked (`rfl`). -/
theorem squierFamilyStrongWalkerCountIsOne : allSquierFamilyStrongWalkers.length = 1 := rfl

/-- ★ **The strong-walker enumeration is EXHAUSTIVE** — the single walker appears. -/
theorem allSquierFamilyStrongWalkersExhaustive :
    ∀ walker : SquierFamilyStrongWalker, walker ∈ allSquierFamilyStrongWalkers
  | .walkingStrongMonad => List.Mem.head _

/-- The coherent-presentation status of the strong-monad walker — SHIPPED in the Omega lane. -/
def squierFamilyStrongStatus :
    SquierFamilyStrongWalker → SquierFamilyCoherentPresentationStatus
  | .walkingStrongMonad => .shippedOmegaLane

/-- ★ **The walking-strong-monad-presented statement.**  The shipped Omega-lane coherent presentation: the
seven-critical-pair bundle (2 strength + 5 T-monad). -/
def SquierFamilyStrongWalkerPresentedStatement : Prop :=
  StrongMonadWalkerCoherentPresentationStatement

/-- ★★ **THE GROUNDED WALKING-STRONG-MONAD CENSUS (#2189).**  The shipped Omega-lane coherent presentation
assembled as one machine-checked datum — so the census extension is proof-carrying, not a bare tally.  The
conjunct is the already-verified coherent presentation of the walker
(`strongMonadWalkerCoherentPresentation`, all seven critical pairs resolved modulo strict). -/
theorem squierFamilyStrongWalkerPresented : SquierFamilyStrongWalkerPresentedStatement :=
  strongMonadWalkerCoherentPresentation

/-- ★ **THE WALKING STRONG MONAD IS PRESENTED IN THE CENSUS (#2189).**  `= true` records that the
single-object walking strong monad has a SHIPPED Omega-lane coherent presentation
(`squierFamilyStrongWalkerPresented`), machine-checked — the WP-STRONG r1 census tie-in, recorded
additively without touching the shipped decided-9. -/
def fxOmega4_walkingStrongMonadPresentedInCensus : Bool := true

/-- ★ **THE SINGLE-OBJECT STRONG MONAD IS A SUB-PRESENTATION OF THE DISTRIBUTIVE LAW (census, #2189).**
`= true` records that the walking strong monad is the walking distributive law minus the c-side monad
structure (`eta_s`, `mu_s`): five generator labels, seven critical pairs (the distributive law's fourteen
minus Beck-1, Beck-3, and the five S-monad rows), machine-checked as a count partition in the presentation
(`strongMonadKeptDropPartitionsDistLawFourteen`).  A distinct single-object walker fitting the
`modeCarrier := Unit` family pattern. -/
def fxOmega4_singleObjectStrongMonadHasOmegaPresentation : Bool := true

/-- ★ **WALL — the bare strong-monad 2-cell DECISION stays walled (census, #2189, honest).**  `= false`
records that the single-object walking strong monad is NOT part of the DECIDED-9: its full 2-cell
word-problem decision is walled at the two-colour monotone-map model (the SAME node as the distributive law,
`fxStrong_fullTwoCellDecisionWalledAtTwoColourMonotoneMap`).  Its 1-cell word problem IS decided by verbatim
Parikh transport (`strongMonadConv_iffSameCount`), and the coherent presentation ships, but not the full
2-cell decision. -/
def fxOmega4_bareStrongMonadTwoCellDecisionWalledInCensus : Bool := false

end FX1Poly.Polygraph.Omega
