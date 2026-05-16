import LeanFX2.Tools.DependencyAudit
import LeanFX2.Term.PreservesTerm

/-! # AuditConvTransB3cCubicalBeta — CONVTRANS-B.3c cubical β-rule lifts

Strict gate plus reviewer-facing audit for the **cubical β-rule
lift** family of CONVTRANS-A subject-reduction term construction
(CONVTRANS-B.3c, ticket #1731).  Third β/ι-rule sub-ticket
after B.3a (#1729) closed Π/Σ β-rules and B.3b (#1730) closed
closed-type ι-rules.

## Scope of B.3c

Four `RawStep.par.lift_full_*` lifts covering the cubical β/ι
family currently shippable at the typed kernel level:

| Lift | Host file | Source line | Coverage |
| --- | --- | --- | --- |
| `lift_full_pathApp` | `BetaCastWallDemolition.lean` | 136 | `betaPathApp` + `betaPathAppDeep` + `betaPathReflApp` + `pathAppCong` |
| `lift_full_glueIntro` | `TwoTyAtomsAndCong.lean` | 420 | `glueIntroCong` (value ctor, no β arm) |
| `lift_full_glueElim` | `TwoTyEliminators.lean` | 239 | `betaGlueElimIntro` + `betaGlueElimIntroDeep` + `glueElimCong` |
| `lift_full_hcomp_cong` | `TwoTyAtomsAndCong.lean` | 452 | `hcompCong` only (no Deep variant of `hcompBeta` exists at typed level) |

### Why these four

* **`lift_full_pathApp`** absorbs three typed β ctors plus cong:
  `betaPathApp` (shallow, `Reduction/ParRed/ParInductive.lean:843`),
  `betaPathReflApp` (constant-path β, line 889), and
  `betaPathAppDeep` (deep, line 1321).  Per `pathApp_inv`, both
  `betaPathApp` and `betaPathReflApp` route through the same
  "path develops to pathLam" disjunct, so the deep-arm body handles
  both rules via `Term.pathLamDestruct`.  Two-Ty existential
  absorbs the cast wall between the cong arm's `carrierType` and
  the β-deep arm's `Ty.subst0` target.

* **`lift_full_glueIntro`** is a Tier-2 cong-only lift (glueIntro
  is a value constructor — no β rule, no destructor).  Mirrors the
  pattern of `lift_full_pair` / `lift_full_recordIntro` for the
  value-constructor family.

* **`lift_full_glueElim`** absorbs the cong arm
  (`glueElimCong`), the shallow β `betaGlueElimIntro` (line 908),
  and the deep β `betaGlueElimIntroDeep` (line 1340) via
  `glueElim_inv` + `Term.glueIntroDestruct`.

* **`lift_full_hcomp_cong`** is a narrowed cong-only lift (note
  the explicit `_cong` suffix in the theorem name).  The β arm
  `hcompBeta` (typed, line 568) is a SHALLOW-ONLY ctor — the
  kernel ships no `Step.par.hcompBetaDeep` typed mirror.  The
  cong arm `Step.par.hcomp` (line 585) is fully covered.  Deep-β
  absorption is structurally blocked at the typed kernel (see
  Documented blockers below).

## Documented blockers — NOT in B.3c scope

Three full β-arm lifts CANNOT ship at the current typed kernel.
Each is a structural kernel gap, not a proof gap.

### `lift_full_transp` β-arm — blocked on `transpReflBetaDeep`

`Step.par.transpReflBeta` (`Reduction/ParRed/ParInductive.lean:535`)
fires only when the type path is syntactically pinned at
`RawTerm.pathLam typeRaw.weaken` (constant path).  Deep variant
(path reducing to a constant `pathLam` from a non-constant
path via inner par-reduction) is RAW-ONLY:
`RawStep.par.transpReflBetaDeep` (`Reduction/RawPar.lean:702`)
has no typed mirror.  Furthermore, `Term.transp` is
**type-changing** — `sourceType ≠ targetType` in general — so a
typed lift cannot reuse the two-Ty existential pattern; a target
Ty must come from the path-reduction premise itself.

Cross-references:
* Memory: `feedback_k1224_transp_hcomp_blocker.md` — "transp is
  type-changing (sourceType ≠ targetType); hcomp has no
  computational β rule (#1528 pending)"
* Tracker: #1949 D2.5.6-Blocker-B (typed `transpReflBetaDeep` +
  intrinsic source/target type indexing)
* Memory: `feedback_d255_eta_typed_kernel_correction_2026_05_16.md`
  — typed-eta redesign batch carries the coupled cubical-β
  cascade

The cong-only `lift_transp_cong` already ships under B.2e;
audit-gated there.

### `lift_full_hcomp` full β-arm — blocked on `hcompBetaDeep`

`Step.par.hcompBeta` (`Reduction/ParRed/ParInductive.lean:568`)
is shallow-only at the typed level.  Per the docstring at line
564-567: "Deep variant (sides develops to constant pathLam under
par reduction) remains raw-only via `RawStep.par.hcompBetaDeep`
per the `transpReflBetaDeep` precedent."  The raw-only
`hcompBetaDeep` (`Reduction/RawPar.lean:758`) has no typed
mirror because adding one requires the same cd-cascade extension
as `transpReflBetaDeep` plus a path-reduction premise discharge.

The cong-only `lift_full_hcomp_cong` covers all hcomp reductions
that do NOT fire the β rule (line 452, gate below).  Full β
absorption is deferred to the same kernel-extension batch as
`transpReflBetaDeep`.

### `lift_full_glueAtFace` — `betaGlueAtFace` is hypothetical

`Term.lean:366` documents a HYPOTHETICAL `betaGlueAtFace` rule
firing when `boundaryWitness = RawTerm.interval1`.  This rule is
NOT a real Term/Step.par ctor in the current kernel — it is a
docstring sketch reserved for D2.5.9-Lane-B's glue-at-face rep
discovery.  Until the rule lands, there is no β arm to lift
beyond `betaGlueElimIntro{,Deep}` (already covered by
`lift_full_glueElim`).

## Gap verification — typed cubical β-rule census

Investigation of `Reduction/ParRed/ParInductive.lean` (every
`| (transp|hcomp|betaPath|betaGlue) ...` ctor enumerated via
`rg "^  \\| (transp|hcomp|beta(Path|Glue))"`):

| Typed ctor | Line | Coverage |
| --- | --- | --- |
| `transp` | 495 | cong, covered by `lift_transp_cong` (B.2e) |
| `transpReflBeta` | 535 | β-shallow, NOT covered (kernel blocker, see above) |
| `hcompBeta` | 568 | β-shallow, NOT covered (kernel blocker, see above) |
| `hcomp` | 585 | cong, covered by `lift_full_hcomp_cong` (this audit) |
| `transpCong` | 695 | cong, covered by `lift_transp_cong` (B.2e) |
| `hcompCong` | 725 | cong, covered by `lift_full_hcomp_cong` (this audit) |
| `hcompPathCong` | 744 | cong, covered by `lift_full_hcomp_cong` (this audit) |
| `betaPathApp` | 843 | β-shallow, covered by `lift_full_pathApp` |
| `betaPathReflApp` | 889 | β-shallow, covered by `lift_full_pathApp` |
| `betaGlueElimIntro` | 908 | β-shallow, covered by `lift_full_glueElim` |
| `betaPathAppDeep` | 1321 | β-deep, covered by `lift_full_pathApp` |
| `betaGlueElimIntroDeep` | 1340 | β-deep, covered by `lift_full_glueElim` |

Raw-only ctors with no typed mirror (kernel-blocker family):
* `RawStep.par.transpReflBetaDeep` (`Reduction/RawPar.lean:702`)
* `RawStep.par.hcompBetaDeep` (`Reduction/RawPar.lean:758`)

These ARE discharged in the raw cd cascade (per
`Confluence/RawCdRename.lean:22`) and in the raw-typed-parity
strict-harness allowlist (per
`Tools/StrictHarness/Common.lean:1781,1875`).  The strict-parity
gate `#assert_raw_typed_parity` (`Tools/StrictHarness.lean`)
explicitly whitelists these two suffixes — preventing a false
parity violation while documenting the missing typed mirrors.

**No further cubical β-rule lift gaps exist at the typed level
beyond the three documented blockers above.**

## Cascade role

B.3c is the third β/ι-rule lift audit, completing the cubical
β-coverage modulo the three documented kernel-extension blockers.
Subsequent B.3.* tickets handle identity ι rules (#1732 B.3d:
`iotaIdJRefl`, `iotaIdStrictRecRefl`) and modal/HoTT-special β/ι
rules (#1733 B.3e).

## Why this audit lives under Smoke instead of Tools/AuditAll

Same reasoning as `AuditConvTransB3aPiSigmaBeta.lean` and
`AuditConvTransB3bIotaRules.lean`: `Term.PreservesTerm` is
reachable as a production module only through its smoke audits.
Co-location of `#print axioms` with the strict gates keeps the
reviewer-facing log adjacent.

The `#assert_no_axioms` strict gates fire under the
`LeanFX2Audit` target identically to gates in `Tools/AuditAll/`.

## Consolidation pattern

This audit reuses the structural template from
`AuditConvTransB3aPiSigmaBeta.lean` and
`AuditConvTransB3bIotaRules.lean`: pre-existing typed cubical
β/ι-rule lifts with one `#assert_no_axioms` strict gate per
lift, one `#print axioms` reviewer log per lift.  No new theorem
bodies shipped in this commit — the four cubical β-rule lifts
existed prior under Tier 2/3 eliminator coverage.  The new B.3c
banner certifies the cubical β-coverage as a coherent audit
family, with explicit blocker documentation for the three
kernel-blocked deferrals. -/

namespace LeanFX2.SmokeConvTransB3cCubicalBeta

/-! ## Strict gates — `#assert_no_axioms`

Build-failing under `LeanFX2Audit` if any of the four cubical
β-rule lifts ever reaches an axiom. -/

#assert_no_axioms LeanFX2.RawStep.par.lift_full_pathApp
#assert_no_axioms LeanFX2.RawStep.par.lift_full_glueIntro
#assert_no_axioms LeanFX2.RawStep.par.lift_full_glueElim
#assert_no_axioms LeanFX2.RawStep.par.lift_full_hcomp_cong

/-! ## Reviewer-facing log — `#print axioms`

Each invocation prints "does not depend on any axioms" alongside
the strict gates above. -/

#print axioms LeanFX2.RawStep.par.lift_full_pathApp
#print axioms LeanFX2.RawStep.par.lift_full_glueIntro
#print axioms LeanFX2.RawStep.par.lift_full_glueElim
#print axioms LeanFX2.RawStep.par.lift_full_hcomp_cong

end LeanFX2.SmokeConvTransB3cCubicalBeta
