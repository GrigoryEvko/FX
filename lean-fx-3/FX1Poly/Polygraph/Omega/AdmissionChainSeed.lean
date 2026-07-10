import FX1Poly.Polygraph.Omega.PresentedKernelSeed

/-! # Polygraph/Omega/AdmissionChainSeed — the per-dimension admission chain (OMEGA-7 r1, B3)

★ **THE ADMISSION CHAIN SEED.**  OMEGA-7's grand tuple is "(signature, table2, table3, …) WITH per-dimension
admission": each dimension's table carries a DECIDABLE admissibility certificate, and admissibility ⟹ the
row's word problem is inherited-decidable with ZERO new call-site proofs.  This file seeds that per-dimension
admission structure over the shipped Omega carrier — the `AdmissionChainSeed = (dim : Nat) → AdmittedTableSeed`
family — turning the flat B2 tuple `PresentedKernel` into the runged kernel-as-value shape.

## The precedent (MODE-ADMIT, cited by name — recon JOB 3)

The admission gate exists ONE dimension up, at the mode-theory level, as the shipped MODE-ADMIT layer
(`Polygraph/TwoCategory/Amalgam/ModeAdmit.lean`):

  * `PresentationData` — a presentation-as-flat-data record with a structural `DecidableEq`;
  * `admitByName` — the by-name admission lookup;
  * `admitModeTheory` — returns `Option (DecidableSaturatedConvForRel …)`, a PACKAGED decider with zero
    call-site proof obligation (the "decidable admissibility ⟹ inherited decidable word problem, zero new
    proofs" payoff, #2214).

`AdmissionChainSeed` is the POLY-CAP lift of that gate to a per-dimension FAMILY (`Kernel := (n : Nat) →
AdmittedTable n`, memo T7.kernel-as-value): r1 SEEDS the shape (the admissibility flag as a `Bool`
certificate at each dimension) over the light `OmegaComputad` carrier; the r3 lift replaces the `Bool` flag
with the genuine `admitModeTheory`-style packaged decider (which needs the OMEGA-7 pasting engine to type the
rows' boundaries).

## What ships here (each machine-checked zero-axiom)

  * **`AdmittedTableSeed`** — a cell-relation row plus its decidable admissibility certificate (`Bool`).
  * **`AdmissionChainSeed`** — the per-dimension admission family `(dim : Nat) → AdmittedTableSeed`, the
    kernel-as-value shape.
  * **`presentedKernelAdmissionChain`** — the chain induced by a `PresentedKernel`: the tuple's rows tagged
    admissible exactly at the table2 / table3 slots (dimensions 2 and 3).
  * **`AdmissionInheritanceShape`** — the handoff signature the r3 gate fills: an admitted table's row plus
    its certificate, yielding an inherited word-problem decision (recorded as a `Type`, filled by
    `admitModeTheory` once the boundaries type).
  * **`demoAdmissionChain`** — the non-vacuous instance over the demo presented kernel; the two admitted
    slots CHECK admissible, the off-slots CHECK not-admissible, and the dim-3 admitted row FIRES on the
    OMEGA-4 interchange legs (a genuine 3-cell through the admission wrapper).

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

/-! ## The admitted table and the per-dimension chain -/

/-- An **admitted table (seed)** at one dimension — a cell-relation `row` plus its decidable admissibility
certificate `isAdmissible` (`Bool`).  The r1 `Bool` flag is the light stand-in for the MODE-ADMIT
`admitModeTheory` packaged decider; the r3 lift replaces it. -/
structure AdmittedTableSeed (computad : OmegaComputad) where
  /-- The generating cell rows at this dimension. -/
  row : CellRelOver computad
  /-- The decidable admissibility certificate (the MODE-ADMIT `admitModeTheory` shape, as a `Bool` seed). -/
  isAdmissible : Bool

/-- ★ **THE ADMISSION CHAIN — the per-dimension admitted-table family.**  `(dim : Nat) → AdmittedTableSeed`
is the POLY-CAP kernel-as-value shape: for every dimension, the table's rows AND its admissibility
certificate.  This is the runged form of the flat B2 `PresentedKernel` tuple — the "… with per-dimension
admission" of OMEGA-7's grand thesis. -/
def AdmissionChainSeed (computad : OmegaComputad) : Type :=
  (dim : Nat) → AdmittedTableSeed computad

/-- The **admission-inheritance handoff shape** — the signature the r3 gate fills: from an admitted table
(its row plus its `isAdmissible` certificate) produce the inherited word-problem decision.  Recorded here as
a `Type`; `admitModeTheory` (MODE-ADMIT) is the filler, available once the OMEGA-7 pasting engine types the
rows' boundaries. -/
def AdmissionInheritanceShape (computad : OmegaComputad) : Type :=
  AdmittedTableSeed computad → CellRelOver computad

/-! ## The chain induced by a presented kernel -/

/-- ★ The **admission chain of a presented kernel** — the B2 tuple's rows tagged with their admissibility
certificate: admissible exactly at the table2 (dim 2) and table3 (dim 3) slots, not admissible on the empty
off-slots.  This turns the flat `(signature, table2, table3)` tuple into the per-dimension admission family. -/
def presentedKernelAdmissionChain (kernel : PresentedKernel) :
    AdmissionChainSeed kernel.signature :=
  fun dim =>
    { row := presentedKernelRow kernel dim
      isAdmissible := dim == 2 || dim == 3 }

/-! ## The non-vacuous demo chain (admission through the OMEGA-4 dim-3 slot) -/

/-- The **demo admission chain** — the per-dimension admission family of the demo presented kernel. -/
def demoAdmissionChain : AdmissionChainSeed demoComputad :=
  presentedKernelAdmissionChain demoPresentedKernel

/-- Non-vacuity: the dim-3 slot (the OMEGA-4 critical-pair table) CHECKS admissible. -/
theorem demoAdmissionChain_dim3_isAdmissible :
    (demoAdmissionChain 3).isAdmissible = true := rfl

/-- ★ Non-vacuity: the admitted dim-3 row FIRES on the two OMEGA-4 interchange legs (its row is
definitionally `demoPresentedKernel.table3`, the critical-pair table) — the admission wrapper carries a
genuine 3-cell generator, not an empty slot. -/
theorem demoAdmissionChain_dim3_fires :
    (demoAdmissionChain 3).row interchangeCriticalRow.leftLeg interchangeCriticalRow.rightLeg :=
  CriticalPairRel.fire

/-- Off-slot honesty: a dimension with no generators (here dim 5) CHECKS not-admissible. -/
theorem demoAdmissionChain_offSlot_notAdmissible :
    (demoAdmissionChain 5).isAdmissible = false := rfl

end FX1Poly.Polygraph.Omega
