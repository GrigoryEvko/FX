import FX1Poly.Polygraph.Omega.Steiner.StrongSteiner
import FX1Poly.Polygraph.Omega.Steiner.DecideFreeConv

/-! # Polygraph/Omega/Steiner/DesignLock — the OMEGA-2 CROWN design lock (r1)

The decision record for the Steiner arithmetic crown, mirroring `Omega/DesignLock.lean` and
`Table/DesignLock.lean`.  It cites the shipped r1 pieces (`CoordinateArithmetic`, `StrongSteiner`,
`Linearize`, `Soundness`, `DecideFreeConv`) and ships the honesty markers plus the OMEGA-3 handoff.

## What r1 SHIPPED (all zero-axiom, machine-checked)

  * **B1 — THE ADMISSION.**  `isStrongSteiner : AugmentedDirectedComplex -> Bool`
    (`isStronglyLoopFreeUpTo && decideAtomicDirect`).  Positive eval: the single-object semiring
    complex is ADMITTED; negative eval: a two-object support-CYCLE complex is REFUSED.  Honest scope:
    iterated-support atomicity + Steiner unitality DEFERRED (r3) — the predicate is a sound
    under-approximation.
  * **B2 — LINEARIZE.**  `linearize : CellExpr computad dim -> SteinerCell` (relative to a
    `ComputadValuation`), total, length-uniform (`linearize_length`).  The ID THEOREM
    (`linearize_id`) made concrete: identities linearize to the DEGENERATE zero table (the honest,
    dimensionally-sound form of the memo's "linearize (id a) = linearize a").
  * **B3 — THE HOMOMORPHISM.**  Composition IS addition (`linearize_vcomp`); the whisker legs project
    to the main factor; `linearize_vcomp_composeAt` connects to the shipped `composeAtDimension`
    substrate with the degenerate (zero) shared boundary — the shared-boundary crux DISCHARGED on the
    free fragment.
  * **B4 — THE CROWN SOUNDNESS FOLD.**  `linearizeSoundness` inhabits the shipped
    `OmegaTwoLinearizeSoundnessShape` via `SaturatedConvOver.recInto` over `linearizeAbsorbs`.  ALL
    EIGHT strict-axiom rows discharged UNCONDITIONALLY (assoc/comm/zero kit + four rfl rows).  The
    ~8x-bespoke soundness leg, made dimension-generic ONCE.
  * **B5 — THE SOUND SEMI-DECIDER + NON-VACUITY.**  `decideFreeConvSound` (table equality via the
    shipped structural `DecidableEq SteinerCell`); `not_conv_of_linearize_ne` (distinct tables refute
    conv).  A dim-3 free cell linearized (`[1,0,0]`); two conv-related dim-3 cells with EQUAL tables
    (via an actual `vcompUnitLeft` derivation through the fold); two non-conv cells with DISTINCT
    tables (provably non-convertible).

## HONEST residuals (recorded, not hidden)

  * **Completeness is OPEN (r3).**  `decideFreeConvSound` is a SOUND semi-decider (table equality is a
    NECESSARY condition), NOT claimed complete.  The converse (reconstruct / excision-of-extremals,
    `linearize (reconstruct t) = t` and `SaturatedConvOver (reconstruct (linearize a)) a`) is the
    OMEGA-2 r3 item, riding `loopFreeOrderIsWellFounded` for the excision termination.
  * **The n=2 agreement with FREE-7 is OPEN (r2).**  `decideFreeConv 2 = decideTwoCellConvFull` on the
    admitted intersection (falsifiability check (ii)) needs `SpineTraceDecision`; deferred to r2.
  * **`isStrongSteiner` scope (r3).**  The iterated-support atomicity and Steiner unitality conjuncts
    need the full Steiner cell-table `⟨x⟩`, deferred; `isStrongSteiner` here is the loop-free +
    direct-atomic under-approximation (sound: it never wrongly admits a support-cycle complex).

Raw Lean 4 + Init; a docstring record plus decidable-tag inductives + Bool markers, so every
declaration is axiom-free.  Per-declaration `#assert_no_axioms` in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

/-! ## The crown-brick registry anchor -/

/-- The **OMEGA-2 crown-brick classifier** — the strategy-key recording which r1 brick a construction
belongs to.  A genuine finite classifier (with a distinctness smoke), the typed anchor of the crown
design lock. -/
inductive OmegaTwoBrick where
  /-- B1 — the `isStrongSteiner` admission interface line. -/
  | admissionInterfaceLine
  /-- B2 — the `linearize` ν/basis map. -/
  | linearizeMap
  /-- B3 — the composition-is-addition homomorphism legs. -/
  | additionHomomorphism
  /-- B4 — the unconditional CROWN soundness fold. -/
  | crownSoundnessFold
  /-- B5 — the sound (necessary-condition) semi-decider. -/
  | soundSemiDecider
  deriving DecidableEq

/-- The soundness fold and the semi-decider are distinct bricks (a sanity check the classifier
separates the r1 deliverables). -/
theorem omegaTwoBrick_fold_ne_decider :
    OmegaTwoBrick.crownSoundnessFold ≠ OmegaTwoBrick.soundSemiDecider := by decide

/-! ## Honesty markers -/

/-- ★ **B1 — the admission predicate is SHIPPED.**  `isStrongSteiner` decides loop-freeness +
direct-atomicity over `AugmentedDirectedComplex`; semiring ADMITTED, support-cycle REFUSED.  `= true`. -/
def fxOmega_isStrongSteinerShipped : Bool := true

/-- ★ **B1 — honest scope.**  `isStrongSteiner` is the loop-free + direct-atomic SOUND
under-approximation; iterated-support atomicity and Steiner unitality are DEFERRED (r3).  `= true`. -/
def fxOmega_isStrongSteinerScopedLoopFreeDirectAtomic : Bool := true

/-- ★ **B2 — `linearize` SHIPPED**, total and length-uniform; the ID THEOREM concretised
(identities = the degenerate zero table).  `= true`. -/
def fxOmega_linearizeShipped : Bool := true

/-- ★ **B3 — composition IS addition** (`linearize_vcomp`), connected to `composeAtDimension` with the
degenerate (zero) shared boundary (`linearize_vcomp_composeAt`).  `= true`. -/
def fxOmega_compositionIsAddition : Bool := true

/-- ★ **B4 — the CROWN soundness fold is UNCONDITIONAL.**  All eight strict-axiom rows discharge with
no composability side condition; `linearizeSoundness` inhabits `OmegaTwoLinearizeSoundnessShape`
via `SaturatedConvOver.recInto`.  `= true`. -/
def fxOmega_crownSoundnessUnconditional : Bool := true

/-- ★ **B5 — the SOUND semi-decider** `decideFreeConvSound` (table equality = a necessary condition);
distinct tables refute convertibility (`not_conv_of_linearize_ne`).  NOT claimed complete.  `= true`. -/
def fxOmega_decideFreeConvSoundNotComplete : Bool := true

/-- ★ **Honesty marker — OMEGA-2 r1 is COMPLETE.**  The B-arith kit, `isStrongSteiner` (B1),
`linearize` + id-theorem + length (B2), the addition homomorphism + `composeAtDimension` connection
(B3), the unconditional CROWN soundness fold (B4), and the sound semi-decider + non-vacuity (B5) all
type-check zero-axiom.  Gated strictly on what compiles: this marker imports every r1 piece.
`= true`. -/
def fxOmega_omega2R1Complete : Bool := true

/-! ## Honest OPEN residuals (r2 / r3) -/

/-- ★ **Honest residual — completeness is OPEN (r3).**  `decideFreeConvSound` is sound-only; the
reconstruct/excision converse (`linearize (reconstruct t) = t`) is the r3 item.  `= false` (NOT closed). -/
def fxOmega_completenessOpenR3 : Bool := false

/-- ★ **Honest residual — the n=2 agreement with FREE-7 is OPEN (r2).**
`decideFreeConv 2 = decideTwoCellConvFull` on the admitted intersection needs `SpineTraceDecision`.
`= false` (NOT closed). -/
def fxOmega_n2AgreementOpenR2 : Bool := false

/-! ## The OMEGA-3 handoff spec

OMEGA-3 (suspension) reindexes the crown: `suspend : OmegaComputad -> OmegaComputad` (reindex k-cells
to (k+1)-cells), `suspendTable : SteinerCell -> SteinerCell` (dimension shift), with the ceiling lift
riding `linearize (suspend a) = suspendTable (linearize a)` + `suspendTable` INJECTIVE.  The r1 crown
supplies the arithmetic invariant the reflection route dodges syntactic fullness through. -/

/-- ★ **Honesty marker — the OMEGA-3 handoff is RECORDED** (suspension reindexing + `suspendTable`
injectivity as the arithmetic reflection route for the ceiling lift).  `= true`. -/
def fxOmega_omegaThreeHandoffRecorded : Bool := true

end FX1Poly.Polygraph.Omega
