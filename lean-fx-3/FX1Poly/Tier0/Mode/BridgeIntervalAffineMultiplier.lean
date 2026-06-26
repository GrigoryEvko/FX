import FX1Poly.Tier0.Mode.MultiplierStructureClass

/-! # mode-2 / A1-5 — the bridge (affine) vs path (cubical) interval, distinguished by structure-class

FX's dimension interval — the one `pathLam`/`pathApp` and the negative bridge `μ_affine◇→A` are built over — is
deliberately the **affine** multiplier (a fresh dimension with endpoints, NO diagonal / NO connections / NO
reversal), the BOTTOM of the mode-2 cube ladder.  It is NOT the CCHM / **De Morgan** cube interval that cubical
type theories use.  This file pins that design choice at the structure-class level and proves its load-bearing
consequence: because the bridge interval is affine, it lacks exactly the operators (the reversal `¬`, the
monotone connections `∧`/`∨`) whose presence makes a cube interval CUBICAL — which is precisely why FX's interval
stays PARAMETRIC and NON-FIBRANT (the design the A1 lineage / interval-non-fibrant work builds on), keeping
internal parametricity + definitional univalence rather than turning into cubical Kan structure.

  * `bridgeIntervalMultiplier` (`= affineInterval`) — FX's actual interval, the affine multiplier `μ_affine`
    is fibred over (mode-2 class `.affine`);
  * `pathIntervalMultiplier` (`= deMorganInterval`) — the CCHM cubical interval FX explicitly does NOT use, the
    full De Morgan cube (mode-2 class `.deMorgan`).

The split is contentful: `bridge ⊑ path` on the ladder (the affine interval is the WEAKER, more restrictive
multiplier), the two classes are distinct, and the bridge lacks the reversal the path has.  The bridge modality
itself is `μ_affine` (`Core/Fib/ModeAffineAdjunction`, A1-MODE-AFFINE); this file classifies the MULTIPLIER that
modality's dimension is built on.

## Honesty

This ships the STRUCTURE-CLASS distinction (the mode-2 substrate for the design choice).  The kernel-level
consequence — that the affine multiplier yields a genuinely NON-FIBRANT interval TYPE (so `pair (var 0) (var 0)`
under the lock is untypeable) — is the A1 / interval-non-fibrant arc (`DimensionLockAccessibility`,
A1-NEG-TRANSPENSION), not re-proved here.  All facts are `rfl` / clean `Nat` lemmas; no `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Tier0

/-- **★ FX's bridge interval multiplier** — the AFFINE interval `μ_affine` is fibred over: a fresh dimension with
endpoints and nothing else (no diagonal, no connections, no reversal).  The minimal transpension multiplier, the
bottom of the cube ladder. -/
def bridgeIntervalMultiplier : IntervalMultiplierName := .affineInterval

/-- **★ The path (cubical) interval multiplier FX does NOT use** — the De Morgan / CCHM cube, with the full
operator set (diagonal + monotone connections + the non-monotone reversal).  Named to make the rejected
alternative explicit: this is what FX's interval would be if it were cubical rather than parametric. -/
def pathIntervalMultiplier : IntervalMultiplierName := .deMorganInterval

/-- The bridge interval is the AFFINE structure class — the modality `μ_affine` is the affine modality precisely
because its multiplier is the affine interval. -/
theorem bridgeIntervalMultiplier_isAffine :
    bridgeIntervalMultiplier.structureClassOf = .affine := rfl

/-- The path interval is the DE MORGAN structure class — the full cubical cube. -/
theorem pathIntervalMultiplier_isDeMorgan :
    pathIntervalMultiplier.structureClassOf = .deMorgan := rfl

/-- **★ The defining distinction.**  The bridge (affine) interval does NOT support the non-monotone reversal `¬`,
whereas the path (De Morgan) interval does.  The reversal is the operator whose presence makes an interval
CUBICAL; its ABSENCE on the affine bridge is what keeps FX's interval parametric / non-fibrant. -/
theorem bridgeLacksReversal_pathHasReversal :
    bridgeIntervalMultiplier.structureClassOf.supportsReversal = false
    ∧ pathIntervalMultiplier.structureClassOf.supportsReversal = true :=
  ⟨rfl, rfl⟩

/-- The bridge interval also lacks the monotone connections `∧`/`∨` (it is below the Dedekind cube) — the second
cubical operator absent on the affine bridge. -/
theorem bridgeLacksConnections :
    bridgeIntervalMultiplier.structureClassOf.supportsConnections = false := rfl

/-- The bridge interval even lacks the diagonal / contraction (it is below the cartesian cube) — the affine
multiplier is the minimal one, carrying none of the three cubical operators. -/
theorem bridgeLacksDiagonal :
    bridgeIntervalMultiplier.structureClassOf.supportsDiagonal = false := rfl

/-- **★ The bridge REFINES the path** — the affine interval is the WEAKER (more restrictive) multiplier on the
cube ladder (`affine ⊑ deMorgan`, strength `0 ≤ 3`).  FX chooses the bottom of the ladder: the most restrictive
interval, which is exactly the one that preserves parametricity.  Proved by `Nat.zero_le` (propext-free). -/
theorem bridgeRefinesPath :
    bridgeIntervalMultiplier.structureClassOf.refines pathIntervalMultiplier.structureClassOf :=
  Nat.zero_le _

/-- **★ The bridge and path intervals are GENUINELY DISTINCT structure classes** — FX's affine interval is not
the cubical De Morgan interval.  Reuses the mode-2 non-degeneracy `affine_ne_deMorgan`. -/
theorem bridgeIntervalMultiplier_ne_pathIntervalMultiplier :
    bridgeIntervalMultiplier.structureClassOf ≠ pathIntervalMultiplier.structureClassOf :=
  affine_ne_deMorgan

/-- The path interval does NOT refine the bridge interval — the refinement is STRICT, so the cubical interval
genuinely carries structure (the reversal) the affine bridge does not.  The contentful half of the split. -/
theorem pathDoesNotRefineBridge :
    ¬ pathIntervalMultiplier.structureClassOf.refines bridgeIntervalMultiplier.structureClassOf :=
  deMorgan_not_refines_affine

end FX1Poly.Tier0
