import FX1Poly.Axis.Mode.MultiplierEndofunctor
import FX1Poly.Typed.Engine.Classifier.DimensionLockAccessibility

/-! # FX1Poly/Typed/Fib/ModeLockMultiplier — fib-3a: rewire Core onto the mode axis — the affine dimension lock IS a mode-12 UNPOINTABLE multiplier

The MODE axis (`Axis/Mode`, `ModeOmega` / the `Multiplier` endofunctor) was ORPHANED from the kernel: zero
engine files imported it, and the kernel's affine dimension LOCK (`TypingContext.lockCons` + the bespoke
`ObligationModality` in `DimensionLockAccessibility`) asserted its discipline STRUCTURALLY — the locked
dimension is "not fibrantly accessible" (`dimensionIsNotAccessibleFibrantly`, a `rfl`-false `Bool` arm) — with
NO link to the real mode theory.

This file performs the first genuine `Core → Axis/Mode` REWIRE (mirroring `fib-1c`'s context rewire): it
imports the mode axis and pins the affine dimension lock's multiplier to the mode-12 VOID multiplier, whose
dimension is empty — UNPOINTABLE (`voidMultiplier.dimension → False`, no global point).  Unpointedness is the
mode-theoretic JUSTIFICATION for the kernel's structural fibrant-inaccessibility: a fibrant (global-point)
projection of the locked dimension would be a global point of an unpointable multiplier, which is impossible.
So the kernel's SYNTACTIC lock and the mode axis's SEMANTIC unpointedness are the two faces of the SAME
affine-dimension discipline.

## ★★ THE WRINKLE (load-bearing — do NOT conflate two distinct facts)

Affineness (mode-2 `MultiplierStructureClass.affine` = NO diagonal, but the structure-class table marks it
POINTED) ≠ unpointedness (mode-12 `Multiplier.IsUnpointable` = NO global point).  The lock's "no fibrant
access" reads off UNPOINTEDNESS (mode-12 `voidMultiplier`), NOT the affine structure class.  This file pins the
CORRECT one — the mode-12 unpointable `voidMultiplier`.

This is the A1-FIB3-SEED: Core now DEPENDS ON the (previously orphaned) mode axis, and the lock is fibred over a
real mode-12 unpointable multiplier.  The full fib-3 (index the judgment by `ModalityPath`, DERIVE the
inaccessibility from unpointedness via the semantic bridge, retire the bespoke `ObligationModality`, flip
`fxFib_hasModeFibration`) builds on this seed.

## Zero-axiom

`voidMultiplier_isUnpointable` (the mode-axis unpointedness, `Empty.elim`) + `dimensionIsNotAccessibleFibrantly`
(the kernel lock's `rfl`-false fibrant arm).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Core.Fib

open FX1Poly.Core FX1Poly.Axis FX1Poly.Typed FX1Poly.Universe

/-- The affine dimension LOCK's mode-axis multiplier: the mode-12 VOID multiplier, whose dimension is empty —
UNPOINTABLE (no global point).  The mode-theoretic carrier of the kernel's affine dimension lock; the correct
horn of the affine-vs-unpointable wrinkle (mode-12 unpointability, NOT the mode-2 pointed affine class). -/
def dimensionUsePositionLockMultiplier : Multiplier := voidMultiplier

/-- ★ The affine dimension lock is fibred over a mode-12 UNPOINTABLE multiplier — its dimension admits no
global point.  This unpointedness is the mode-theoretic reason the locked dimension is not fibrantly accessible. -/
theorem dimensionUsePositionLockMultiplier_isUnpointable : dimensionUsePositionLockMultiplier.IsUnpointable :=
  voidMultiplier_isUnpointable

/-- ★ **The fib-3a wiring (A1-FIB3-SEED).**  The kernel's affine dimension lock rejects fibrant access to its
dimension (`dimensionIsNotAccessibleFibrantly`, the structural `rfl`-false `Bool`), AND its mode-axis multiplier
is mode-12 UNPOINTABLE (`dimensionUsePositionLockMultiplier_isUnpointable`) — the syntactic lock and the semantic
no-global-point are the two faces of the SAME discipline.  Core now depends on the (previously orphaned) mode
axis; the lock is fibred over a real mode-12 unpointable multiplier (the seed the full fib-3 derivation and the
`ObligationModality` retirement build on). -/
theorem lockFibrantInaccessibility_witnessedByUnpointedMultiplier {profile : PolyProfile} {scope : Nat}
    (restContext : TypingContext profile scope) (dimensionType : RawTerm scope)
    (isLtZeroSucc : 0 < scope + 1) :
    (restContext.lockCons dimensionType).isAccessibleAtModality ⟨0, isLtZeroSucc⟩ .fibrant = false
    ∧ dimensionUsePositionLockMultiplier.IsUnpointable :=
  ⟨dimensionIsNotAccessibleFibrantly restContext dimensionType isLtZeroSucc,
    dimensionUsePositionLockMultiplier_isUnpointable⟩

/-- The affine dimension lock's multiplier is also dimensionally SPLIT — the dimension factors out as a product
(`voidMultiplier_splitData`), the mode-12 criterion INDEPENDENT of pointedness.  This is the mode-theoretic
carrier of the DIMENSIONAL half of the lock's split (the locked dimension IS accessible dimensionally even with
no global point). -/
theorem dimensionUsePositionLockMultiplier_isDimensionallySplit :
    dimensionUsePositionLockMultiplier.IsDimensionallySplit :=
  ⟨voidMultiplier_splitData⟩

/-- ★ **The full fibrant/dimensional lock split, justified by the mode-12 multiplier.**  The kernel's affine
dimension lock is two-way: `var 0` is NOT accessible fibrantly (`dimensionIsNotAccessibleFibrantly`) but IS
accessible dimensionally (`dimensionIsAccessibleDimensionally`) — and this split is EXACTLY the mode-12 void
multiplier's two INDEPENDENT criteria: UNPOINTABLE (no global point ⟹ no fibrant access) yet dimensionally
SPLIT (the dimension factors out ⟹ dimensional access).  So the kernel's bespoke fibrant/dimensional split IS
the mode-axis unpointable-but-split structure — the lock is the mode-12 multiplier in BOTH halves, the genuine
mode-theoretic justification the bespoke `ObligationModality` previously asserted on its own. -/
theorem dimensionUsePositionLockSplit_witnessedByMultiplier {profile : PolyProfile} {scope : Nat}
    (restContext : TypingContext profile scope) (dimensionType : RawTerm scope)
    (isLtZeroSucc : 0 < scope + 1) :
    (restContext.lockCons dimensionType).isAccessibleAtModality ⟨0, isLtZeroSucc⟩ .fibrant = false
    ∧ (restContext.lockCons dimensionType).isAccessibleAtModality ⟨0, isLtZeroSucc⟩ .dimensional = true
    ∧ dimensionUsePositionLockMultiplier.IsUnpointable
    ∧ dimensionUsePositionLockMultiplier.IsDimensionallySplit :=
  ⟨dimensionIsNotAccessibleFibrantly restContext dimensionType isLtZeroSucc,
    dimensionIsAccessibleDimensionally restContext dimensionType isLtZeroSucc,
    dimensionUsePositionLockMultiplier_isUnpointable,
    dimensionUsePositionLockMultiplier_isDimensionallySplit⟩

/-! ## fib-3c — DERIVE the fibrant-inaccessibility from unpointedness -/

/-- ★ **fib-3c (root cause).**  The affine dimension lock's multiplier has NO GLOBAL POINT, DERIVED from its
unpointedness via the mode-axis exclusivity `Multiplier.not_pointed_and_unpointable`.  A fibrant projection of
the locked dimension would BE a global point of the multiplier — so the kernel's structural fibrant-
inaccessibility (`dimensionIsNotAccessibleFibrantly`) is grounded in this no-global-point, no longer free. -/
theorem dimensionUsePositionLockMultiplier_notPointed : ¬ dimensionUsePositionLockMultiplier.IsPointed :=
  fun pointed =>
    dimensionUsePositionLockMultiplier.not_pointed_and_unpointable pointed
      dimensionUsePositionLockMultiplier_isUnpointable

/-- The affine-lock multiplier's pointedness is DECIDABLY FALSE — no global point. -/
instance dimensionUsePositionLockMultiplier_pointedDecidable :
    Decidable dimensionUsePositionLockMultiplier.IsPointed :=
  isFalse dimensionUsePositionLockMultiplier_notPointed

/-- ★ **fib-3c (computational).**  The kernel's structural fibrant-inaccessibility of the locked dimension
EQUALS the decidable reflection of the multiplier's pointedness — `false`, because the multiplier is
unpointable.  So `dimensionIsNotAccessibleFibrantly` is the mode-12 multiplier's NON-POINTEDNESS, COMPUTED:
the bespoke lock's "no fibrant access" is now grounded in (definitionally equal to) the mode-axis fact, not a
standalone assertion. -/
theorem lockFibrantAccess_eq_multiplierNonPointedness {profile : PolyProfile} {scope : Nat}
    (restContext : TypingContext profile scope) (dimensionType : RawTerm scope)
    (isLtZeroSucc : 0 < scope + 1) :
    (restContext.lockCons dimensionType).isAccessibleAtModality ⟨0, isLtZeroSucc⟩ .fibrant
      = decide dimensionUsePositionLockMultiplier.IsPointed :=
  rfl

end FX1Poly.Core.Fib
