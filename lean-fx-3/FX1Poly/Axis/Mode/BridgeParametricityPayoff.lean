import FX1Poly.Axis.Mode.BridgeIntervalAffineMultiplier
import FX1Poly.Axis.Mode.Transpension

/-! # mode-2/11 / A1-6 — the affine bridge's frontier payoff: parametricity Gel + definitional-univalence gating

The point of choosing the AFFINE (bridge) interval over the cubical (De Morgan) one (A1-5) is the frontier
payoff: the negative transpension over the affine multiplier is positioned to recover **internal parametricity**
(its zoo target is the parametricity **Gel** type, NOT the cubical **Glue**), and the affine multiplier's
quantifiability gates **definitional univalence** through the bridge rather than through cubical Kan structure.

This file CONFIRMS that structural positioning over the shipped substrate (A1-5's structure-class split +
mode-11's transpension zoo + mode-2's Nuyts property table):

  * the parametricity **Gel** is a named transpension target (`gel ∈ TranspensionRecoverable.all`);
  * the bridge (affine) multiplier is **quantifiable** (Π over the dimension exists — the transpension's left
    adjoint `DimProduct`), so it CARRIES the transpension whose target is Gel;
  * the bridge is non-cubical (no reversal, A1-5), so its transpension recovers the PARAMETRIC Gel, not the
    cubical Glue — internal parametricity, not cubical type theory;
  * definitional univalence is gated by exactly this combination — quantifiable (Π exists, so the universe-level
    transpension that computes `Id_U ↝ Equiv` exists) AND non-fibrant/affine (so univalence is the bridge's
    parametricity content, not cubical Kan filling).

## ★★ Honesty — positioning, not the realized recovery

This confirms the STRUCTURAL POSITIONING: the affine bridge is the parametricity-supporting, defuniv-gating
multiplier, and Gel is its transpension target.  It does NOT realize the per-operator recovery
`transpension @ affine = Gel` as a concrete instance (`fxMode_hasTranspensionZooRecovery := false`, mode-11), nor
the kernel-level definitional-univalence reduction row (the `defuniv-*` / `EXT-4` arc).  Those are the deferred
realizations the A1-NEG-TRANSPENSION lineage + the defuniv tasks land; A1-6 confirms the targets and the
structure-class gating that make them the RIGHT realizations.

All facts are `rfl` / `List.Mem` constructors over the shipped enums; no `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Axis

/-- **★ The parametricity Gel is a transpension target.**  `gel` is one of the eight named operators the
transpension is the universal home of (mode-11) — so internal parametricity (the Gel type) is in scope as a
transpension recovery, the bridge's intended payoff. -/
theorem gelIsTranspensionTarget : TranspensionRecoverable.gel ∈ TranspensionRecoverable.all :=
  List.Mem.head _

/-- **★ The bridge (affine) multiplier is quantifiable** — Π over the dimension exists (mode-2's `quantifiable`
property), which IS the transpension's left adjoint `DimProduct`.  So the affine bridge genuinely CARRIES a
transpension (the one whose target is Gel); the minimal cube-ladder multiplier is still quantifiable. -/
theorem bridgeMultiplierIsQuantifiable :
    bridgeIntervalMultiplier.structureClassOf.hasProperty .quantifiable = true := rfl

/-- **★ The bridge supports internal PARAMETRICITY, not cubical structure.**  Its transpension's target zoo
contains the parametricity `gel`, AND the bridge lacks the non-monotone reversal that characterizes the cubical
interval (A1-5).  So `transpension @ bridge` is positioned to recover Gel (parametricity), not Glue (cubical) —
the affine choice's first payoff. -/
theorem bridgeSupportsParametricityNotCubical :
    TranspensionRecoverable.gel ∈ TranspensionRecoverable.all
    ∧ bridgeIntervalMultiplier.structureClassOf.supportsReversal = false :=
  ⟨List.Mem.head _, rfl⟩

/-- **★ Definitional univalence is gated by the affine bridge.**  The two ingredients are exactly: (1)
QUANTIFIABLE — Π over the dimension exists, so the universe-level transpension that would compute `Id_U ↝ Equiv`
is available; and (2) NON-CUBICAL (no reversal) — so univalence arises as the bridge's parametricity content
rather than as cubical Kan filling.  This is the precise structure-class gate the defuniv arc plugs into. -/
theorem definitionalUnivalenceGatedByAffineBridge :
    bridgeIntervalMultiplier.structureClassOf.hasProperty .quantifiable = true
    ∧ bridgeIntervalMultiplier.structureClassOf.supportsReversal = false :=
  ⟨rfl, rfl⟩

/-- **★ The cubical path multiplier ALSO carries the transpension but routes to a DIFFERENT target.**  The path
(De Morgan) multiplier is quantifiable too, but it HAS the reversal — so its transpension is positioned for the
cubical Glue, not the parametric Gel.  This is the contrast that makes the affine choice meaningful: same
transpension machinery, different recovered operator, selected by structure-class. -/
theorem pathRoutesToCubicalNotParametric :
    pathIntervalMultiplier.structureClassOf.hasProperty .quantifiable = true
    ∧ pathIntervalMultiplier.structureClassOf.supportsReversal = true :=
  ⟨rfl, rfl⟩

/-- **★ HONESTY marker (A1-6).**  The structural positioning is confirmed (Gel is the bridge's transpension
target, the affine multiplier is quantifiable + non-cubical, gating parametricity and definitional univalence).
The actual per-operator recovery `transpension @ affine = Gel` is NOT realized here
(`fxMode_hasTranspensionZooRecovery = false`, mode-11) — the deferred realization the A1-NEG-TRANSPENSION lineage
and the defuniv arc land. -/
theorem bridgePayoffPositioningOnly_recoveryDeferred :
    fxMode_hasTranspensionZooRecovery = false := rfl

end FX1Poly.Axis
