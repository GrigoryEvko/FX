import LeanFX2.Tools.DependencyAudit
import LeanFX2.Term.PreservesTerm

/-! # AuditConvTransB3dJotaBeta — CONVTRANS-B.3d J-family β/ι-rule lifts

Strict gate plus reviewer-facing audit for the **J-family β/ι-rule
lift** sub-ticket of CONVTRANS-A subject-reduction term construction
(CONVTRANS-B.3d, ticket #1732).  Fourth β/ι-rule sub-ticket after
B.3a (#1729) closed Π/Σ β-rules, B.3b (#1730) closed closed-type ι
rules, and B.3c (#1731) closed cubical β-rules.

## Scope of B.3d

Three `RawStep.par.lift_full_*` lifts covering the identity-type
J-family β/ι rules currently shippable at the typed kernel level:

| Lift | Host file | Source line | Coverage |
| --- | --- | --- | --- |
| `lift_full_idJ` | `HeterogeneousElim.lean` | 110 | `iotaIdJRefl` + `iotaIdJReflDeep` + `idJ` cong |
| `lift_full_oeqJ` | `HeterogeneousElim.lean` | 170 | `oeqJCong` only (no β/ι rule at typed level) |
| `lift_full_idStrictRec` | `HeterogeneousElim.lean` | 234 | `iotaIdStrictRecRefl` + `iotaIdStrictRecReflDeep` + `idStrictRecCong` |

### Why these three

* **`lift_full_idJ`** absorbs two typed ι ctors plus cong:
  `iotaIdJRefl` (shallow, `Reduction/ParRed/ParInductive.lean:1256`)
  and `iotaIdJReflDeep` (deep, line 1578).  Per
  `RawStep.par.idJ_inv`, both rules route through the same "witness
  develops to `RawTerm.refl _`" disjunct, so the iota arm body
  handles both via `Term.idReflDestruct` plus HEq alignment to
  `Term.refl carrier endpoint` (Term.refl's typing forces
  `witnessRaw' = leftEndpoint = rightEndpoint`).  The
  motive-preserving target type `motiveType` lets the two-Ty
  existential collapse to a single Ty.

* **`lift_full_oeqJ`** is a **cong-only** lift.  `Term.oeqJ` exists
  as an eliminator over `Ty.oeq`, but the kernel ships **no typed
  ι rule** for it (no `iotaOeqJRefl`, no `iotaOeqJReflDeep`).  The
  raw side similarly has no `RawStep.par.iotaOeqJ*` ctor — see
  Gap verification below.  The cong-only lift uses
  `Step.par.oeqJCong` to track parallel reduction of the base case
  and witness sub-terms.  This is structurally analogous to
  `lift_full_hcomp_cong` (B.3c) — the eliminator exists but its
  β/ι rule is structurally absent from the kernel rather than
  conditionally deferred.

* **`lift_full_idStrictRec`** absorbs two typed ι ctors plus cong:
  `iotaIdStrictRecRefl` (shallow, line 1269) and
  `iotaIdStrictRecReflDeep` (deep, line 1594).  Mirrors
  `lift_full_idJ`'s structure with `Term.idStrictReflDestruct`
  + HEq alignment plus the `modeIsStrict` mode-restriction
  premise (`Ty.idStrict` only types under `mode = Mode.strict`).

## Documented blocker — NOT in B.3d scope

One full β-arm lift CANNOT ship at the current typed kernel.  This
is a structural kernel gap, not a proof gap.

### `lift_full_equivApply` β-arm — blocked on typed `uaBeta`

`RawStep.par.equivApply_inv` has THREE disjunctive arms:
* cong (covered by the B.2g `lift_uaToEquiv` companion + a cong
  arm on `equivApply` itself),
* `RawStep.par.uaBeta` shallow-β (`Reduction/RawPar.lean:1049`),
* `RawStep.par.uaBetaDeep` deep-β (`Reduction/RawPar.lean:1071`).

The raw `uaBeta`/`uaBetaDeep` rules fire when the equiv develops
to `RawTerm.uaToEquiv (RawTerm.oeqRefl _)` — a constant-equiv
β collapse from `equivApply (uaToEquiv (oeqRefl A)) value` to
`value` (modulo coercion of the carrier type).

**No typed mirror exists**.  Grep evidence:
* `rg -n '^  \| uaBeta' LeanFX2/Reduction/ParRed/ParInductive.lean`
  returns nothing.  The typed kernel ships `Step.par.equivApply`
  (cong over carrier+equiv+value) but no `Step.par.uaBeta` /
  `Step.par.uaBetaDeep` ctor.
* The B.2g deferral note (`AuditConvTransB2gTypeCodeHottCong.lean:
  72-78`) names this exact blocker: "*equivApply: ... defers to
  CONVTRANS-B.3 β-rule lifts (ticket #1729), which will ship
  `lift_full_equivApply` alongside `lift_full_app` / `lift_full_
  appPi` β-cascade machinery.*"

Shipping `lift_full_equivApply` requires extending the typed
kernel with `Step.par.uaBeta` (shallow) + `Step.par.uaBetaDeep`
(deep) ctors mirroring the raw rules, plus their
`#assert_raw_typed_parity` integration.  This is a kernel
extension batch, not a proof obligation discharge.

Cross-references:
* Tracker: #1571 D3.6-UA-BETA-INTERNAL — typed `Step.par.uaBeta`
  + `Step.par.uaBetaDeep` ctors as a coupled kernel extension.
* Tracker: #1572 D3.6-UA-BETA-SUBLEMMAS — supporting raw / typed
  inversion + parity-allowlist + cd cascade extensions for
  uaBeta.
* B.2g deferral note: `AuditConvTransB2gTypeCodeHottCong.lean:
  72-78` — original deferral cite under the cong-only audit.

## Gap verification — typed J-family β/ι-rule census

Investigation of `Reduction/ParRed/ParInductive.lean` (every
`| iota(IdJ|IdStrictRec|OeqJ)*` ctor enumerated via
`rg -n '^  \| (iotaIdJ|iotaIdStrictRec|iotaOeqJ|uaBeta)'
LeanFX2/Reduction/ParRed/ParInductive.lean`):

| Typed ctor | Line | Coverage |
| --- | --- | --- |
| `iotaIdJRefl` | 1256 | β-shallow, covered by `lift_full_idJ` |
| `iotaIdStrictRecRefl` | 1269 | β-shallow, covered by `lift_full_idStrictRec` |
| `iotaIdJReflDeep` | 1578 | β-deep, covered by `lift_full_idJ` |
| `iotaIdStrictRecReflDeep` | 1594 | β-deep, covered by `lift_full_idStrictRec` |

The same grep returns NO matches for `iotaOeqJ*` or `uaBeta*`
under `ParInductive.lean`, confirming:

* **`oeqJ` has no β/ι rule at the typed kernel level.**  Term.oeqJ
  exists as a constructor and `Step.par.oeqJCong` carries the cong
  rule, but no canonical β collapse rule fires.  This is consistent
  with the B.2c-family finding that the `Ty.oeq` heterogeneous
  identity does not admit a `Term.refl`-shape canonical form whose
  ι rule could fire — its left/right endpoints carry different
  types in general.  `lift_full_oeqJ` is correctly cong-only.

* **`uaBeta` is RAW-ONLY.**  Raw `RawStep.par.uaBeta`
  (`Reduction/RawPar.lean:1049`) and `RawStep.par.uaBetaDeep`
  (line 1071) ship at the raw layer but have no typed mirror,
  blocking `lift_full_equivApply` per the documented blocker
  above.  These ARE discharged in the raw cd cascade and in the
  raw-typed-parity strict-harness allowlist.

**Summary of J-family typed-level coverage:**

| Family | Typed ι ctors | Lift coverage | Status |
| --- | --- | --- | --- |
| `idJ` | 2 (shallow + deep `iotaIdJRefl{,Deep}`) | `lift_full_idJ` | full |
| `oeqJ` | 0 (no typed β/ι at all) | `lift_full_oeqJ` cong-only | full (structural) |
| `idStrictRec` | 2 (shallow + deep `iotaIdStrictRecRefl{,Deep}`) | `lift_full_idStrictRec` | full |
| `equivApply` | 0 (raw-only `uaBeta{,Deep}`) | DEFERRED | blocked on #1571/#1572 |

The kernel ships 2 + 0 + 2 = 4 J-family typed ι ctors, fully
absorbed by 2 of the 3 lifts (`lift_full_idJ` + `lift_full_idStrictRec`),
with the third lift (`lift_full_oeqJ`) being cong-only by kernel
design.

**No further J-family β/ι-rule lift gaps exist at the typed level
beyond the documented `equivApply` blocker above.**

## Cascade role

B.3d is the fourth β/ι-rule lift audit, completing the J-family
β/ι-coverage modulo the documented `uaBeta` kernel-extension
blocker.  Subsequent B.3.* tickets handle the LAST remaining
β/ι-rule families:

* **B.3e** (#1733) — modal/record/refine/codata β rules; the
  final β/ι-rule sub-ticket before the CONVTRANS-C/D chain lift
  + headline.

After B.3e the chain assembles via CONVTRANS-C (combined β-rule
+ cong sweep) → CONVTRANS-D (`Step.subjectReduction` headline).

## Why this audit lives under Smoke instead of Tools/AuditAll

Same reasoning as `AuditConvTransB3aPiSigmaBeta.lean`,
`AuditConvTransB3bIotaRules.lean`, and
`AuditConvTransB3cCubicalBeta.lean`: `Term.PreservesTerm` is
reachable as a production module only through its smoke audits.
Co-location of `#print axioms` with the strict gates keeps the
reviewer-facing log adjacent.

The `#assert_no_axioms` strict gates fire under the
`LeanFX2Audit` target identically to gates in `Tools/AuditAll/`.

## Consolidation pattern

This audit reuses the structural template from
`AuditConvTransB3cCubicalBeta.lean`: pre-existing typed J-family
β/ι-rule lifts with one `#assert_no_axioms` strict gate per lift,
one `#print axioms` reviewer log per lift.  No new theorem bodies
shipped in this commit — the three J-family lifts existed prior
under Tier 2/3 eliminator coverage in `HeterogeneousElim.lean`.
The new B.3d banner certifies the J-family β/ι-coverage as a
coherent audit family, with explicit blocker documentation for
the kernel-blocked `equivApply` deferral. -/

namespace LeanFX2.SmokeConvTransB3dJotaBeta

/-! ## Strict gates — `#assert_no_axioms`

Build-failing under `LeanFX2Audit` if any of the three J-family
β/ι-rule lifts ever reaches an axiom. -/

#assert_no_axioms LeanFX2.RawStep.par.lift_full_idJ
#assert_no_axioms LeanFX2.RawStep.par.lift_full_oeqJ
#assert_no_axioms LeanFX2.RawStep.par.lift_full_idStrictRec

/-! ## Reviewer-facing log — `#print axioms`

Each invocation prints "does not depend on any axioms" alongside
the strict gates above. -/

#print axioms LeanFX2.RawStep.par.lift_full_idJ
#print axioms LeanFX2.RawStep.par.lift_full_oeqJ
#print axioms LeanFX2.RawStep.par.lift_full_idStrictRec

end LeanFX2.SmokeConvTransB3dJotaBeta
