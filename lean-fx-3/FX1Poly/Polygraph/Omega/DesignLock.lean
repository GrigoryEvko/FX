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

end FX1Poly.Polygraph.Omega
