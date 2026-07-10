import FX1Poly.Polygraph.Omega.InvolutionSquierBasis
import FX1Poly.Polygraph.Omega.MonadCoherentPresentation
import FX1Poly.Polygraph.Omega.CyclicThreeDemonstrator
import FX1Poly.Polygraph.Omega.IdempotentSemigroupDemonstrator

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

end FX1Poly.Polygraph.Omega
