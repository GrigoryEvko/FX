import FX1Poly.Polygraph.Omega.AdmissionChainSeed
import FX1Poly.Polygraph.Omega.CohGateTyped

/-! # Polygraph/Omega/TypedKernelTuple — the kernel as a value tuple with TYPED per-dimension admission
    (OMEGA-7 r3, B1+B2)

★ **THE KERNEL-AS-VALUE TUPLE with genuine typed admission — the r3 close of the substitution=pasting
staircase.**  OMEGA-7's grand thesis is "the kernel = (signature, table2, table3, …) WITH per-dimension
admission".  r1 (`AdmissionChainSeed.lean`) seeded the SHAPE with a naked `Bool` certificate
(`AdmittedTableSeed.isAdmissible : Bool`); the r1 ledger flagged that a Bool flag "does not count" as a
seated decider.  r2 (`PsContextTyped.lean` / `CohGateTyped.lean`) shipped the exact gap the r1 jam named — the
TYPED telescope (`TeleType`, `teleTypeDim`, `psTypedCheck`, `telescopeWellFormed`) and the typed fullness
DECISION `cohFullnessCheck`.  This file consumes that r2 telescope surface to replace the naked `Bool` with a
GENUINE typed admissibility certificate, assembling the tuple `Kernel := (n : Nat) → AdmittedTable n` as a
machine-checked value over the demo kernel data.

## What the admission carries — the packaged decider, NOT a Bool (B1)

`AdmittedTable computad n` seats a per-dimension `row` on a `TeleType` boundary AT its dimension
(`boundaryDim : teleTypeDim boundary = n`), over a `psTypedCheck`-checked, `telescopeWellFormed` ps-context,
with admissibility DECIDED by `cohFullnessCheck` over the typed telescope (`fullnessOverPs = true`).  The
`fullnessOverPs` field is not a flag one asserts: it is a proof that the genuine fullness DECISION PROCEDURE
`cohFullnessCheck` evaluated to accept over the typed telescope — the r3 replacement for r1's
`AdmittedTableSeed.isAdmissible : Bool`.  The packaged-decider slot the CaTT/mode-theory admission fills is the
seed's `AdmissionInheritanceShape` (a `Type`, `AdmissionChainSeed.lean`), whose ω-word-problem filler is
MODE-ADMIT's `admitModeTheory` (`Amalgam/ModeAdmit.lean`) ONE dimension up — cited by name, NOT imported
(the layer rule + the cross-lane discipline forbid pulling the Amalgam lane's active surface).

## The tuple instantiation at the real kernel data (B2)

`demoTypedKernel : TypedKernel demoComputad := fun n => admittedTableAtDim … (presentedKernelRow
demoPresentedKernel n)` seats, at EVERY dimension `n`, the REAL kernel row `presentedKernelRow
demoPresentedKernel n` (= `StrictAxiomRel` table2 at dim 2, the OMEGA-4 interchange `criticalPairRel` table3
at dim 3, the empty row elsewhere) on the canonical dimension-`n` typed boundary `starTower n` over the
singleton object ps-context, with a genuine `cohFullnessCheck` admissibility proof.  The dimension `n` flows
UNIFORMLY into the boundary and the certificate — no dependent match on `n` in a return position, so the
tuple dodges the indexed-partial-match `propext` trap entirely.

HONESTY (state it, never over-claim):

  * The tuple seats each real row on the CANONICAL dimension-`n` boundary `starTower n` over the singleton
    object context, NOT on the row's own reconstructed pasting boundary — reconstructing each row's specific
    boundary is the type-respecting VALUATION `TeleVar(level) -> CellExpr` (the shared-variable term->cell
    action, `fxOmega7_fragmentTermToCellActionReached = false`), which stays open (r4 / Makkai-walled).  What
    is genuine here is: every slot carries a REAL generator row AND a genuine typed decision, no Bool flag.
  * `cohFullnessCheck` is the typed fullness gate; it is honestly the CaTT fullness side-condition decided
    over the telescope (support coverage + well-scopedness), slightly MORE permissive than strict CaTT type
    reconstruction (which needs the valuation).  The non-vacuity is the LOAD-BEARING rejection reused from r2:
    `interchangeMissingMiddleCoh` (the shared middle object omitted) is admitted by the r1 skeleton but
    REJECTED by this gate (`= false`, by `rfl`), so admissibility is not vacuously true.

## What ships here (each machine-checked zero-axiom)

  * **`AdmittedTable`** — the typed admitted table: a `row`, a `TeleType` boundary at its dimension, a typed
    checked well-formed ps-context, and the `cohFullnessCheck` admissibility proof.
  * **`TypedKernel`** — the kernel-as-value tuple `(n : Nat) → AdmittedTable n`.
  * **`starTower` / `teleTypeDim_starTower`** — the canonical dimension-`n` boundary and its dimension proof.
  * **`admittedTableAtDim`** — seat any row at dimension `n` on `starTower n` over the singleton context.
  * **`demoTypedKernel`** — the tuple over the demo kernel, real rows at every dimension.
  * **`typedKernelForget`** — the forgetful MAP `TypedKernel -> AdmissionChainSeed` (the r1 seed shape),
    identified through the shared `row` (`typedKernelForget_sharesRow`, by `rfl`) — an identification, NOT a
    variable-disjoint conjunction (the r2 honesty discipline).
  * **`demoTypedKernel_dim3_rowFires`** — the tuple's dim-3 slot carries the interchange 3-cell (fires on the
    two legs): a REAL dim-3 admitted row through the typed boundary.
  * **`demoDim3AdmittedTableFull`** — the interchange critical-pair row seated on its GENUINE
    horizontal-composite ps-context with a FULL support (the middle object covered) — the honest non-degenerate
    dim-3 witness.
  * **`interchangeMissingMiddle_notAdmitted`** — the LOAD-BEARING negative: the same boundary with the middle
    omitted is REJECTED by the admissibility gate (`cohFullnessCheck = false`).

Raw Lean 4 + Init, STRUCTURAL only, ASCII-only.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

/-! ## The typed admitted table (the r1 `Bool` seed upgraded to a typed decision) -/

/-- ★ **A typed admitted table at dimension `n`** — the r3 upgrade of `AdmittedTableSeed`.  A generating cell
`row` seated on a `TeleType` `boundary` AT its dimension (`boundaryDim : teleTypeDim boundary = n`), over a
`psTypedCheck`-checked, `telescopeWellFormed` ps-`context`, with admissibility DECIDED by `cohFullnessCheck`
over the typed telescope (`fullnessOverPs`).  `fullnessOverPs` is a genuine decision-procedure proof — the r3
replacement for r1's naked `AdmittedTableSeed.isAdmissible : Bool`.  The packaged ω-word-problem decider the
admission enables is the seed's `AdmissionInheritanceShape`, filled by MODE-ADMIT's `admitModeTheory` (cited,
not imported). -/
structure AdmittedTable (computad : OmegaComputad) (n : Nat) where
  /-- The generating cell rows at this dimension. -/
  row : CellRelOver computad
  /-- The boundary base type the row is seated on. -/
  boundary : TeleType
  /-- The boundary sits at this table's dimension (the row is seated on `TeleType` at `n`). -/
  boundaryDim : teleTypeDim boundary = n
  /-- The ps-context the boundary is typed over. -/
  context : PsContextRow
  /-- The context passes the TYPED ps-judgment (the r2 telescope surface consumed). -/
  contextTyped : psTypedCheck context = true
  /-- The elaborated telescope is well-formed (endpoints carry their base type, levels in scope). -/
  contextWellFormed : telescopeWellFormed (telescopeOf (elaboratePsContext context)) = true
  /-- The de Bruijn levels the source boundary uses. -/
  srcSupp : List Nat
  /-- The de Bruijn levels the target boundary uses. -/
  tgtSupp : List Nat
  /-- ★ Admissibility DECIDED — every variable of the ps-context is covered and the supports are in scope
  (`cohFullnessCheck` over the typed telescope evaluates to `true`).  The seated decider, not a `Bool` flag. -/
  fullnessOverPs :
    cohFullnessCheck (telescopeOf (elaboratePsContext context)) boundary srcSupp tgtSupp = true

/-- ★ **THE KERNEL AS A VALUE TUPLE** — `(n : Nat) -> AdmittedTable n`, the per-dimension admitted-table family
with genuine typed admission.  The r3 form of the runged kernel-as-value shape: every dimension's table, its
typed boundary, and its `cohFullnessCheck` admissibility certificate.  Replaces `AdmissionChainSeed`'s
`Bool`-certificate stub with the typed decision. -/
def TypedKernel (computad : OmegaComputad) : Type :=
  (n : Nat) → AdmittedTable computad n

/-! ## The canonical dimension-`n` boundary tower -/

/-- The **canonical dimension-`n` boundary** — an `n`-fold hom tower over the object type.  `starTower 0` is
`*`; `starTower (n+1)` is a hom over `starTower n` (its endpoints are the base object, irrelevant to fullness
coverage).  A total, structural, canonical boundary of any prescribed dimension. -/
def starTower : Nat → TeleType
  | 0 => TeleType.star
  | n + 1 => TeleType.arrow (starTower n) 0 0

/-- The **dimension of the canonical tower** is its index — the erasure the boundary is seated by.  Structural
induction on `n` (`star` is 0, each hom bumps the dimension by one). -/
theorem teleTypeDim_starTower : ∀ n : Nat, teleTypeDim (starTower n) = n
  | 0 => rfl
  | n + 1 => congrArg (· + 1) (teleTypeDim_starTower n)

/-! ## Seating a row at a dimension over the singleton object context -/

/-- ★ **Seat any row at dimension `n`** — the uniform admitted table: the `row` on the canonical dimension-`n`
boundary `starTower n` over the singleton object ps-context `[*]` (which types and is well-formed), with the
source/target supports `[0]` covering the single object level.  `n` flows uniformly into the boundary and the
dimension proof — no dependent match, so the propext trap is dodged. -/
def admittedTableAtDim (computad : OmegaComputad) (n : Nat) (row : CellRelOver computad) :
    AdmittedTable computad n where
  row := row
  boundary := starTower n
  boundaryDim := teleTypeDim_starTower n
  context := PsContextRow.start
  contextTyped := rfl
  contextWellFormed := rfl
  srcSupp := [0]
  tgtSupp := [0]
  fullnessOverPs := rfl

/-! ## The tuple over the demo kernel — real rows at every dimension -/

/-- ★ **THE DEMO TYPED KERNEL TUPLE** — the kernel-as-value tuple over the demo kernel data.  At every
dimension `n`, seats the REAL kernel row `presentedKernelRow demoPresentedKernel n` (`StrictAxiomRel` table2
at dim 2, the OMEGA-4 interchange `criticalPairRel` table3 at dim 3, the empty row elsewhere) on the canonical
typed boundary with a genuine `cohFullnessCheck` admissibility proof.  The tuple is LIVE with the real rows
AND the seated typed decider — the Bool seed is gone. -/
def demoTypedKernel : TypedKernel demoComputad :=
  fun n => admittedTableAtDim demoComputad n (presentedKernelRow demoPresentedKernel n)

/-- The tuple's dim-2 slot carries the strict-rewrite table2 — it FIRES on a real vcomp-associativity pair
(its row is definitionally `demoPresentedKernel.table2`, the `StrictAxiomRel` rewrite rows). -/
theorem demoTypedKernel_dim2_rowFires :
    (demoTypedKernel 2).row
      (CellExpr.vcomp (CellExpr.vcomp twoCellGen twoCellId) whiskerCell)
      (CellExpr.vcomp twoCellGen (CellExpr.vcomp twoCellId whiskerCell)) :=
  StrictAxiomRel.vcompAssoc twoCellGen twoCellId whiskerCell

/-- ★ **A REAL dim-3 admitted row through the typed boundary** — the tuple's dim-3 slot's row FIRES on the two
OMEGA-4 interchange legs (its row is definitionally `criticalPairRel interchangeCriticalRow`): the tuple's
dim-3 admission carries a genuine 3-cell generator, not an empty slot. -/
theorem demoTypedKernel_dim3_rowFires :
    (demoTypedKernel 3).row interchangeCriticalRow.leftLeg interchangeCriticalRow.rightLeg :=
  CriticalPairRel.fire

/-- ★ The tuple's dim-3 slot is ADMISSIBLE via the genuine typed decision (`cohFullnessCheck = true`, the
seated decider, not a Bool). -/
theorem demoTypedKernel_dim3_admissible :
    cohFullnessCheck (telescopeOf (elaboratePsContext (demoTypedKernel 3).context))
      (demoTypedKernel 3).boundary (demoTypedKernel 3).srcSupp (demoTypedKernel 3).tgtSupp = true :=
  (demoTypedKernel 3).fullnessOverPs

/-- ★ The tuple's dim-3 boundary genuinely sits at dimension 3 (`teleTypeDim boundary = 3`). -/
theorem demoTypedKernel_dim3_boundaryDim :
    teleTypeDim (demoTypedKernel 3).boundary = 3 :=
  (demoTypedKernel 3).boundaryDim

/-! ## The non-degenerate dim-3 witness — the real row over its GENUINE full boundary -/

/-- ★ **The interchange critical-pair row seated on its GENUINE ps-context with a FULL support.**  Over the
horizontal-composite ps-context `(x)(y)(z)(f,g,a)(h,k,b)` (9 typed entries, shared middle object `y` at level
1), the source support is the left half plus the middle `{x,y,f,g,a} = {0,1,2,3,4}` and the target support the
right half `{z,h,k,b} = {5,6,7,8}` — TOGETHER covering the whole context, so fullness HOLDS.  The `row` is the
real `criticalPairRel interchangeCriticalRow` (= `demoPresentedKernel.table3`): a non-degenerate dim-3 admitted
row over the row's own pasting-scheme context. -/
def demoDim3AdmittedTableFull : AdmittedTable demoComputad 3 where
  row := criticalPairRel interchangeCriticalRow
  boundary := starTower 3
  boundaryDim := teleTypeDim_starTower 3
  context := horizontalCompositePsContext
  contextTyped := horizontalCompositePsContext_psTyped
  contextWellFormed := rfl
  srcSupp := [0, 1, 2, 3, 4]
  tgtSupp := [5, 6, 7, 8]
  fullnessOverPs := rfl

/-- ★ Fullness HOLDS for the non-degenerate dim-3 witness (the middle object IS covered) — non-vacuity of the
typed admissibility over the row's genuine ps-context. -/
theorem demoDim3AdmittedTableFull_fullnessHolds :
    cohFullnessCheck (telescopeOf (elaboratePsContext demoDim3AdmittedTableFull.context))
      demoDim3AdmittedTableFull.boundary demoDim3AdmittedTableFull.srcSupp
      demoDim3AdmittedTableFull.tgtSupp = true :=
  demoDim3AdmittedTableFull.fullnessOverPs

/-- ★ The non-degenerate dim-3 row FIRES on the two interchange legs (the real critical-pair 3-cell). -/
theorem demoDim3AdmittedTableFull_rowFires :
    demoDim3AdmittedTableFull.row interchangeCriticalRow.leftLeg interchangeCriticalRow.rightLeg :=
  CriticalPairRel.fire

/-! ## The LOAD-BEARING negative — the admissibility gate genuinely rejects (typing is not vacuous) -/

/-- ★ **The admissibility gate REJECTS the interchange boundary with the shared middle omitted.**  Over the
same horizontal-composite ps-context, dropping the middle object `y` (level 1) from BOTH supports
(`srcSupp = {0,2,3,4}`, `tgtSupp = {5,6,7,8}`) makes `cohFullnessCheck` return `false` (by `rfl`, reused from
r2's `interchangeMissingMiddleCoh_fullnessFails`).  No `AdmittedTable` could carry this boundary — its
`fullnessOverPs` field is unfillable — so the typed admissibility is LOAD-BEARING, not vacuously true. -/
theorem interchangeMissingMiddle_notAdmitted :
    cohFullnessCheck (telescopeOf (elaboratePsContext interchangeMissingMiddleCoh.overRow))
      interchangeMissingMiddleCoh.base interchangeMissingMiddleCoh.srcSupp
      interchangeMissingMiddleCoh.tgtSupp = false :=
  interchangeMissingMiddleCoh_fullnessFails

/-! ## The forgetful map back to the r1 seed shape (identification through the shared row) -/

/-- ★ **The forgetful MAP** `TypedKernel -> AdmissionChainSeed` — projects each typed admitted table to the r1
seed row, marking it admissible (a typed table carries a genuine fullness proof, so its seed certificate is
`true`).  A genuine projection sharing the underlying `row` (`typedKernelForget_sharesRow`, by `rfl`), NOT a
variable-disjoint conjunction of "typed tuple AND r1 seed" — the r2 identification discipline. -/
def typedKernelForget {computad : OmegaComputad} (kernel : TypedKernel computad) :
    AdmissionChainSeed computad :=
  fun dim => { row := (kernel dim).row, isAdmissible := true }

/-- ★ The forgetful map shares the typed tuple's row at every dimension — the identification through the shared
`row` (definitional, witnessed pointwise by `Iff.rfl`), NOT a variable-disjoint conjunction. -/
theorem typedKernelForget_sharesRow {computad : OmegaComputad} (kernel : TypedKernel computad) (dim : Nat)
    {cellDim : Nat} (cellAlpha cellBeta : CellExpr computad cellDim) :
    (typedKernelForget kernel dim).row cellAlpha cellBeta ↔ (kernel dim).row cellAlpha cellBeta := Iff.rfl

/-- ★ Every slot of the forgetful seed is marked admissible (the typed tuple admits at every dimension). -/
theorem typedKernelForget_admissible {computad : OmegaComputad} (kernel : TypedKernel computad) (dim : Nat) :
    (typedKernelForget kernel dim).isAdmissible = true := rfl

end FX1Poly.Polygraph.Omega
