import FX1Poly.Polygraph.Omega.BridgeDimTwo
import FX1Poly.Polygraph.Omega.CollapseDimOne

/-! # Polygraph/Omega/DesignLock — the OMEGA-1 architecture design lock (r1)

The decision record for the dimension-indexed carrier, mirroring `Table/DesignLock.lean`.  It cites the shipped
r1 pieces (`Omega/Carrier.lean`, `Omega/Congruence.lean`, `Omega/StrictAxioms.lean`, `Omega/BridgeDimTwo.lean`,
`Omega/CollapseDimOne.lean`) and ships one concrete typed anchor — the `OmegaCarrierDecision` classifier — plus
the r1-complete honesty marker.  No file outside `Omega/` is edited.

## The KEY DECISION — HYBRID, interface line `isStrongSteiner` (OMEGA-0 memo)

Not syntax-first, not arithmetic-first.  TWO primary carriers bridged by `linearize`:

  * **Above the line — syntax.**  `CellExpr n` (candidate ii, `Omega/Carrier.lean`) + `SaturatedConvOver n`
    (`Omega/Congruence.lean`); decision = per-presentation walker or honest wall.  This is what OMEGA-1 ships.
  * **Below the line — arithmetic.**  Steiner `List Int` chain tables (`Steiner/`, OMEGA-2); composition =
    truncated addition; word problem = `DecidableEq (List Int)`.
  * **The interface line — `isStrongSteiner : Computad n -> Bool`.**  It COINCIDES with the mathematical
    decidability boundary: strong-Steiner = decidable-by-arithmetic (Steiner math/0403237; AGOR 2204.12962);
    general presented = undecidable-in-general (Burroni TCS 1993).  Where arithmetic stops being available is
    exactly where the word problem stops being free.  (Deferred to OMEGA-2; recorded here as the lock.)

## The carrier decision — candidate (ii), extrinsic boundary (NOT the banned candidate i)

`CellExpr : Nat -> Type` is `Nat`-recursive over a PRIOR type: `CellExpr (n+1)` is built OVER `CellExpr n`, its
boundary a TOTAL STRUCTURAL FUNCTION, globularity EXTRINSIC.  This is the `RawTwoCellExpr` idiom lifted.  The
BANNED alternative (candidate i) indexes cells by a parallel boundary PAIR (`CellExpr : (n:Nat) -> CellExpr
(n-1) -> CellExpr (n-1) -> Type`), which fires the mutual-index / positivity minefield — absent everywhere on
disk, and confirmed hostile in r1 (even the extrinsic boundary FUNCTION needed the `PUnit`-motive total-match
trick to stay propext-clean; a partial match on the index leaks `propext` / `Quot.sound`).

## The falsifiability outcome (the prime directive held)

Specialised to `dim = 2`, the four one-hole congruence constructors (`vcompCongrLeft` / `vcompCongrRight` /
`whiskerLeftCongr` / `whiskerRightCongr`) reproduce the four shipped dim-2 constructors on the nose (see
`Omega/Congruence.lean`).  No parallel structure crept in.  The single honest divergence — no generic `ofFull`
— is bridged by firing `StrictAxiomRel` rows through `ofRelation` (r2 discharges `bridgeDimTwoHolds`).

## r1 scope boundary (from the OMEGA-0 memo FIRST BUILD ROUND)

SHIPPED: carrier + `cellSize` + total boundaries + globularity STATEMENT + structural `cellBeq`; generic
`SaturatedConvOver` + `recInto` + `IsSaturatedCongruence`; `StrictAxiomRel` + `freeStrictCongruence`; bridge /
collapse Prop STATEMENTS + the `realizePathCell` build map + non-vacuity evals + audit twins.  OUT: Steiner
`linearize` / soundness / completeness (OMEGA-2); the n=2 bridge PROOFS (r2); dim-3 congruence deciders;
grades; ps-contexts; pasting / subst; and deleting ANY dim-2 bespoke carrier — `RawTwoCellExpr` stays live and
is BRIDGED, never replaced.

## Honest r1 residuals (recorded, not hidden)

  * `IsGlobularCarrier` is STATED, not proven: the free `gen` constructor admits non-globular generators, so
    strict globularity holds only for globular computads (a `GlobularComputad` refinement, r2).
  * `cellBeq` is a `Bool` structural equality (propext-clean); promoting it to a `Prop`-valued `DecidableEq`
    needs `toSkeleton`-injectivity, the mechanical r2 follow-up.
  * `bridgeDimTwoHolds` / `dimOneCollapsesToPath` are forward-declared Props (r2 inhabits them).

Raw Lean 4 + Init; a docstring record plus one decidable-tag inductive, so every declaration is axiom-free.
Per-declaration `#assert_no_axioms` in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

/-! ## The carrier / decision registry anchor -/

/-- The **carrier-and-decision classifier** for OMEGA-1 — the strategy-key recording which encoding and which
side of the `isStrongSteiner` interface a construction lives on.  A genuine finite classifier (with a
distinctness smoke), the typed anchor of the design lock. -/
inductive OmegaCarrierDecision where
  /-- The syntax carrier `CellExpr n` — candidate (ii), extrinsic boundary, above the interface line. -/
  | extrinsicSyntaxCarrier
  /-- The banned globular-dependent encoding — candidate (i), boundary-pair index, mutual-index trap. -/
  | bannedGlobularDependent
  /-- The arithmetic carrier — Steiner `List Int` tables, below the interface line (OMEGA-2). -/
  | steinerArithmeticTable
  /-- The generic saturated congruence `SaturatedConvOver n` closing a law relation into a congruence. -/
  | saturatedCongruence
  /-- The `isStrongSteiner` interface line splitting the two carriers (OMEGA-2). -/
  | strongSteinerInterfaceLine
  deriving DecidableEq

/-- The chosen carrier is the extrinsic-syntax candidate (ii), NOT the banned globular-dependent candidate (i) —
a sanity check that the classifier separates the shipped choice from the rejected one. -/
theorem omegaCarrierDecision_chosen_ne_banned :
    OmegaCarrierDecision.extrinsicSyntaxCarrier ≠ OmegaCarrierDecision.bannedGlobularDependent := by decide

/-- The carrier OMEGA-1 ships — the extrinsic-syntax candidate (ii). -/
def omega1CarrierChoice : OmegaCarrierDecision := OmegaCarrierDecision.extrinsicSyntaxCarrier

/-! ## Honesty markers -/

/-- ★ **Honesty marker — OMEGA-1 r1 is COMPLETE.**  The dimension-indexed carrier (`CellExpr`, candidate ii,
extrinsic total boundaries, `cellSize`, structural `cellBeq`, globularity STATEMENT), the dimension-generic
saturated congruence (`SaturatedConvOver` with the four one-hole constructors reproducing the dim-2 four on the
nose, `recInto`, `IsSaturatedCongruence`), the strict-axiom row family (`StrictAxiomRel`,
`freeStrictCongruence`), and the n=2 bridge / n=1 collapse Prop STATEMENTS (`bridgeDimTwoHolds`,
`dimOneCollapsesToPath`, with the `realizePathCell` build map) all type-check zero-axiom.  Gated strictly on
what compiles: this marker imports every r1 piece.  `= true`. -/
def fxOmega_omega1R1Complete : Bool := true

/-- ★ **Honesty marker — the carrier is candidate (ii) and the interface line is `isStrongSteiner`.**  Records
the OMEGA-0 KEY DECISION in the repo: HYBRID architecture, extrinsic-syntax carrier above the line, Steiner
arithmetic below it, banned candidate (i).  `= true`. -/
def fxOmega_carrierIsExtrinsicCandidateTwo : Bool := true

/-! ## OMEGA-1 r2 — the four bricks + the ONE honest wall (B5 ledger)

The rung closes **complete-except-for-one-named-wall**.  Per-brick, strictly factual:

  * **B1 (n=1 collapse) — CLOSED, honestly.**  The UNCONDITIONAL `dimOneCollapsesToPath` is REFUTED
    (`dimOneCollapse_not_unconditional`, via the gen-atom difference-list invariant through `recInto` + a
    canonicity contradiction) — the extrinsic carrier admits ill-boundaried `gen` cells with no path preimage.
    The substantive UNCONDITIONAL content (homomorphism `realizePath_composePath_conv`, boundary read-off,
    `vcomp`-closure) ships alongside; the honest positive statement is the `GlobularComputad`-restricted collapse.

  * **B2 (n=2 bridge) — SIZE leg CLOSED, CONV leg WALLED (the one wall).**  `toCellDimTwo` maps the five
    `RawTwoCellExpr` generators to the five `CellExpr` generators on the nose (falsifiability: no extra
    generator), and `bridgeDimTwoForwardSize` PROVES size preservation.  The conv leg of `bridgeDimTwoHolds`
    (`TwoCellConv → freeStrictCongruence`) is the named wall: `freeStrictCongruence`'s four one-hole congruences
    (exactly the dim-2 four) are NOT a full congruence over the Omega carrier's EXPLICIT 1-cells, so `vcompIdLeft`
    needs an `id`-congruence it lacks.  `bridgeDimTwoHolds` keeps its name/meaning as the open statement.

  * **B3 (globularity) — CLOSED, softer than forecast.**  `globularLegs_of_isGlobularCell` PROVES globularity on
    the well-formed sub-carrier (`IsGlobularCell` = parallel generators + composable vcomps) by clean structural
    induction — NOT the forecast stratified-carriers wall.  The extrinsic `IsGlobularCarrier` stays stated.

  * **B4 (adequacy) — RESOLVED via DERIVED OPERATIONS.**  See `fxOmega_adequateByDerivedOperations`.

Only B2's conv leg is open; everything else is proven zero-axiom. -/

/-- ★ **Honesty marker — B1: the unconditional dim-1 collapse is REFUTED (closed honestly).** `= true`. -/
def fxOmega_dimOneCollapseRefuted : Bool := true

/-- ★ **Honesty marker — B2: the n=2 bridge SIZE leg is PROVEN (`bridgeDimTwoForwardSize`).** `= true`. -/
def fxOmega_bridgeDimTwoSizeLegProven : Bool := true

/-- ★ **Honesty marker — B2: the n=2 bridge CONV leg is OPEN (the ONE wall).**  `freeStrictCongruence` (four
one-hole congruences, matching dim-2) is not a full congruence over the Omega carrier's explicit 1-cells; the
`vcompIdLeft` row needs an `id`-congruence.  `= true` records the wall is present, not that the conv leg holds. -/
def fxOmega_bridgeDimTwoConvLegOpen : Bool := true

/-- ★ **Honesty marker — B3: globularity DISCHARGED on the well-formed sub-carrier
(`globularLegs_of_isGlobularCell`).** `= true`. -/
def fxOmega_globularityDischargedOnWellFormed : Bool := true

/-- ★ **Honesty marker — B4: the fixed-five carrier is ADEQUATE via DERIVED operations.**  The DERIVED-OPERATIONS
branch (recon verdict), NOT the memo's `2n` new composition constructors.  `godementComp` (`*_dim` Godement /
hcomp, the dim-2 `RawTwoCellExpr.hcomp` lifted) and `whiskerByLowerId` (`*_0` deep whisker via id-promotion) DEFINE
every codimension-`k` composite from `vcomp` / `whisker` / `id`, so the constructor COUNT is CONSTANT across
dimensions — strictly more faithful to "the dimension index is a parameter, never a reason for a parallel
structure" than a `*_k`-primitive-per-level set.  Congruence in the whiskered-CELL positions is FREE
(`whiskerByLowerId_congruence`).  The n=2 falsifiability RE-RUN holds: the four one-hole congruences reproduce the
dim-2 four (unchanged), `toCellDimTwo` maps the five generators — no parallel structure crept in.  `= true`. -/
def fxOmega_adequateByDerivedOperations : Bool := true

/-- ★ **Honesty marker — OMEGA-1 is COMPLETE-EXCEPT-FOR-ONE-WALL.**  `= false` (NOT fully complete): the ONE
open obligation is the B2 bridge conv leg (`fxOmega_bridgeDimTwoConvLegOpen`).  Every other r2 deliverable — the
n=1 refutation (B1), globularity on the well-formed sub-carrier (B3), and derived-operations adequacy (B4) — is
PROVEN zero-axiom.  Set `true` only when the conv leg is discharged (an `idCongr` + whisker-1-cell congruence
extension of `SaturatedConvOver`, or a normalising translation) in a follow-up. -/
def fxOmega_omega1Complete : Bool := false

/-! ## The OMEGA-2 handoff spec (B5)

OMEGA-2 (the Steiner crown) linearizes FROM this rung.  The map-out substrate is ALL shipped and clean:
`SaturatedConvOver.recInto` + `IsSaturatedCongruence` + `StrictAxiomRel` + `boundarySource` / `boundaryTarget`
(linearize's d⁻/d⁺) + `freeStrictCongruence` / `emptyPresentation`.  The generic invariant fold IS the shipped
eliminator.  Two SHAPES are recorded below so OMEGA-2 has exact targets; the Steiner substrate anchors + the two
recon API-drift corrections it must absorb follow.

### Steiner substrate anchors (recon-verified against `Steiner/`, with the two drift corrections)

  * `SteinerCell` (`Steiner/CellCoordinates.lean`) is a STRUCTURE `{ coordinates : CellVector }`,
    `CellVector := List Int` (abbrev) — NOT the memo's bare `= List Int`.  `linearize` produces the wrapper;
    `DecidableCellEq.lean` gives structural `DecidableEq` on it (propext-free).
  * **R1 (OMEGA-2 crux):** the shipped composition is `composeAtDimension (left right sharedBoundary : SteinerCell)
    : SteinerCell = x + y − sharedBoundary` — NOT the memo's `composeAt : Nat → SteinerCell → SteinerCell →
    Option SteinerCell`.  There is NO `Nat` arg, NO `Option`, and the shared boundary is an EXPLICIT argument whose
    computation from the augmented directed complex is DEFERRED.  So `T2.homomorphism`
    (`linearize (a *_k b) = compose k (lin a) (lin b)`) cannot even be STATED until `sharedBoundary` is derivable —
    the real OMEGA-2 crux the memo understated.
  * **R2 (structure drift):** there is NO dimension-indexed `Computad n`; the carrier is the FLAT `OmegaComputad`,
    and `Computad := ModeSignature` (flat abbrev).  `isStrongSteiner` / `suspend` must be FLAT
    (`OmegaComputad → Bool`), reading `genLabel` per dimension — NOT the memo's `Computad n → Bool`.
  * `sourceOfCell` / `targetOfCell` (d⁻/d⁺), `SteinerCell.HasDimensionShape` (the `isStrongSteiner` shape predicate
    layers on it), and `loopFreeOrderIsWellFounded` (`LoopFreeOrder.lean`, PRESENT and PROVEN by structural `Nat`
    induction, no `WellFounded.fix`) are the reconstruction well-order for excision-of-extremals.
  * `decideFreeConv a b := linearize a == linearize b` uses SteinerCell's STRUCTURAL `DecidableEq` — so OMEGA-2
    does NOT need `CellExpr`'s Prop-`DecidableEq`; the Bool-only `cellBeq` / `toSkeleton`-injectivity residual is
    OFF OMEGA-2's critical path. -/

/-- The OMEGA-2 **linearize-soundness SHAPE** — the exact target OMEGA-2 inhabits via the generic invariant fold
`SaturatedConvOver.recInto` at `inv := linearize`, `targetRel := fun a b => linearize a = linearize b`.  Parameterised
by the yet-to-be-defined `SteinerCellCarrier` and `linearize`; ships here as the handoff contract. -/
def OmegaTwoLinearizeSoundnessShape (computad : OmegaComputad) (SteinerCellCarrier : Type)
    (linearize : {dim : Nat} → CellExpr computad dim → SteinerCellCarrier) : Prop :=
  ∀ {dim : Nat} {cellAlpha cellBeta : CellExpr computad dim},
    SaturatedConvOver computad (StrictAxiomRel computad) cellAlpha cellBeta →
    linearize cellAlpha = linearize cellBeta

/-- The OMEGA-2 **interface-line SHAPE** — `isStrongSteiner` is a decidable `Bool` predicate on the FLAT
`OmegaComputad` (recon R2: a dimension-indexed `Computad n` is absent on disk).  Ships here as the signature
OMEGA-2 defines. -/
def OmegaTwoInterfaceLineShape : Type 1 := OmegaComputad → Bool

/-- ★ **Honesty marker — the OMEGA-2 handoff spec is RECORDED** (linearize-soundness shape, flat `isStrongSteiner`
signature, the Steiner substrate anchors, and the two recon API-drift corrections R1/R2).  `= true`. -/
def fxOmega_omegaTwoHandoffRecorded : Bool := true

end FX1Poly.Polygraph.Omega
