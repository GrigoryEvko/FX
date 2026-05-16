import LeanFX2.Tools.DependencyAudit
import LeanFX2.Term.PreservesTerm

/-! # AuditConvTransB3eAdvancedBeta — CONVTRANS-B.3e modal/record/refine/codata/session/effect β

Strict gate plus reviewer-facing audit for the **modal/record/refine/
codata/session/effect β-rule lift** sub-ticket of CONVTRANS-A
subject-reduction term construction (CONVTRANS-B.3e, ticket #1733).
Fifth and LAST β/ι-rule sub-ticket after B.3a (#1729 — Π/Σ β),
B.3b (#1730 — closed-type ι), B.3c (#1731 — cubical β), and
B.3d (#1732 — J-family β/ι) closed their respective slices.

With B.3e shipped, ALL five B.3.* sub-tickets are closed.  The
CONVTRANS-B macro-family (B.1 + B.2.* + B.3.*) is complete, and
the next CONVTRANS phase is C (chain lift, #1734) → D
(`Step.subjectReduction` headline, #1735) → Audit (#1736).

## Scope of B.3e

Six `RawStep.par.lift_full_*` lifts covering the advanced
β-rule families currently shippable at the typed kernel level:

| Lift | Host file | Source line | Coverage |
| --- | --- | --- | --- |
| `lift_full_modElim` | `TwoTyEliminators.lean` | 188 | `betaModElimIntro` + `betaModElimIntroDeep` + `modElimCong` |
| `lift_full_recordProj` | `TwoTyEliminators.lean` | 204 | `betaRecordProjIntro` + `betaRecordProjIntroDeep` + `recordProjCong` |
| `lift_full_refineElim` | `TwoTyEliminators.lean` | 221 | `betaRefineElimIntro` + `betaRefineElimIntroDeep` + `refineElimCong` |
| `lift_full_codataDest` | `TwoTyEliminators.lean` | 259 | `betaCodataDestUnfold` + `betaCodataDestUnfoldDeep` + `codataDestCong` |
| `lift_full_sessionRecv` | `TwoTyAtomsAndCong.lean` | 323 | `sessionRecvCong` only (no β rule at typed level) |
| `lift_full_effectPerform` | `TwoTyAtomsAndCong.lean` | 595 | `effectPerformCong` only (no β rule at typed level) |

### Why these six

* **`lift_full_modElim`** absorbs two typed β ctors plus cong:
  `betaModElimIntro` (shallow, `Reduction/ParRed/ParInductive.lean:
  406`) and `betaModElimIntroDeep` (deep, line 415).  The modal
  elimination β fires when the modal value develops to
  `RawTerm.modIntro inner`, yielding `inner` after collapse.
  Term.modIntro's inner term lives at the same type as the
  enclosing modal, so the two-Ty existential collapses to the
  shared `innerType`.

* **`lift_full_recordProj`** absorbs two typed β ctors plus cong:
  `betaRecordProjIntro` (shallow, line 926) and
  `betaRecordProjIntroDeep` (deep, line 1355).  The record-projection
  β fires when the record value develops to
  `RawTerm.recordIntro field`, yielding `field`.  Single-field
  record at the kernel level — multi-field records are encoded via
  nested singletons.  The projection's target type is exactly the
  record's `singleFieldType`.

* **`lift_full_refineElim`** absorbs two typed β ctors plus cong:
  `betaRefineElimIntro` (shallow, line 934) and
  `betaRefineElimIntroDeep` (deep, line 1364).  The refinement
  elimination β fires when the refined value develops to
  `RawTerm.refineIntro baseValue proof`, yielding `baseValue`
  (proof is discarded — refinements are erased at elaboration).
  The two-Ty existential collapses to the shared `baseType` since
  Term.refineIntro witnesses live at the underlying base type.

* **`lift_full_codataDest`** absorbs two typed β ctors plus cong:
  `betaCodataDestUnfold` (shallow, line 965) and
  `betaCodataDestUnfoldDeep` (deep, line 981).  The codata
  destruction β fires when the codata value develops to a
  `RawTerm.codataUnfold` (the coinductive unfold introduction
  form), yielding the unfolded step.  Output type is the codata's
  `outputType` parameter.

* **`lift_full_sessionRecv`** is a **cong-only** lift.  The
  typed kernel ships `Step.par.sessionRecvCong`
  (`Reduction/ParRed/ParInductive.lean:1018`) for parallel
  reduction of the channel sub-term but **no `Step.par.betaSession*`
  ctor**.  Session-protocol β reduction (a `sessionRecv` of a
  `sessionSend (...)` would collapse to the sent value plus the
  remaining protocol) is structurally absent from the kernel
  rather than conditionally deferred — session types do not admit
  a canonical β collapse at the kernel level because their
  protocol-step argument is a free variable in general.  This is
  structurally analogous to `lift_full_hcomp_cong` (B.3c) and
  `lift_full_oeqJ` (B.3d) — the eliminator exists, but no β/ι
  rule fires.

* **`lift_full_effectPerform`** is a **cong-only** lift.  The
  typed kernel ships `Step.par.effectPerformCong`
  (`Reduction/ParRed/ParInductive.lean:1027`) for parallel
  reduction of the operation tag and arguments sub-terms but
  **no `Step.par.betaEffect*` ctor**.  Effect-perform β reduction
  is the responsibility of the surrounding handler/handle-bind
  layer (the algebraic effects machinery in `Effects/*` — handler
  composition happens at the elaborator level, not via a kernel
  β rule).  Cong-only is the correct kernel-level coverage,
  mirroring the session pattern above.

## Coverage table — every typed β/ι rule mapped to a B.3.* lift

To certify the **full B.3.* macro-family coverage** at audit
closure, the following table enumerates every `beta*` and `iota*`
constructor in `Reduction/ParRed/ParInductive.lean` and maps it
to its covering lift across B.3a-e.

### β rules (21 ctors total)

| Typed β ctor | Line | Lift | Sub-ticket |
| --- | --- | --- | --- |
| `betaModElimIntro` | 406 | `lift_full_modElim` | **B.3e** |
| `betaModElimIntroDeep` | 415 | `lift_full_modElim` | **B.3e** |
| `betaApp` | 811 | `lift_full_app` | B.3a |
| `betaAppPi` | 827 | **DEFERRED — split lift_full_appPi gap** | B.3a (gap) |
| `betaPathApp` | 843 | `lift_full_pathApp` | B.3c |
| `betaPathReflApp` | 889 | `lift_full_pathApp` | B.3c |
| `betaGlueElimIntro` | 908 | `lift_full_glueElim` | B.3c |
| `betaRecordProjIntro` | 926 | `lift_full_recordProj` | **B.3e** |
| `betaRefineElimIntro` | 934 | `lift_full_refineElim` | **B.3e** |
| `betaCodataDestUnfold` | 965 | `lift_full_codataDest` | **B.3e** |
| `betaCodataDestUnfoldDeep` | 981 | `lift_full_codataDest` | **B.3e** |
| `betaFstPair` | 1055 | `lift_full_fst` | B.3a |
| `betaSndPair` | 1068 | `lift_full_snd` | B.3a |
| `betaAppDeep` | 1286 | `lift_full_app` | B.3a |
| `betaAppPiDeep` | 1304 | **DEFERRED — split lift_full_appPi gap** | B.3a (gap) |
| `betaPathAppDeep` | 1321 | `lift_full_pathApp` | B.3c |
| `betaGlueElimIntroDeep` | 1340 | `lift_full_glueElim` | B.3c |
| `betaRecordProjIntroDeep` | 1355 | `lift_full_recordProj` | **B.3e** |
| `betaRefineElimIntroDeep` | 1364 | `lift_full_refineElim` | **B.3e** |
| `betaFstPairDeep` | 1375 | `lift_full_fst` | B.3a |
| `betaSndPairDeep` | 1389 | `lift_full_snd` | B.3a |

**β coverage: 19/21 typed ctors absorbed (2 deferred under B.3a's
`betaAppPi{,Deep}` gap, documented at
`AuditConvTransB3aPiSigmaBeta.lean:42-149`).**

### ι rules (28 ctors total)

| Typed ι ctor | Line | Lift | Sub-ticket |
| --- | --- | --- | --- |
| `iotaBoolElimTrue` | 1082 | `lift_full_boolElim` | B.3b |
| `iotaBoolElimFalse` | 1095 | `lift_full_boolElim` | B.3b |
| `iotaNatElimZero` | 1108 | `lift_full_natElim` | B.3b |
| `iotaNatElimSucc` | 1118 | `lift_full_natElim` | B.3b |
| `iotaNatRecZero` | 1132 | `lift_full_natRec` | B.3b |
| `iotaNatRecSucc` | 1143 | `lift_full_natRec` | B.3b |
| `iotaListElimNil` | 1163 | `lift_full_listElim` | B.3b |
| `iotaListElimCons` | 1176 | `lift_full_listElim` | B.3b |
| `iotaOptionMatchNone` | 1199 | `lift_full_optionMatch` | B.3b |
| `iotaOptionMatchSome` | 1210 | `lift_full_optionMatch` | B.3b |
| `iotaEitherMatchInl` | 1224 | `lift_full_eitherMatch` | B.3b |
| `iotaEitherMatchInr` | 1240 | `lift_full_eitherMatch` | B.3b |
| `iotaIdJRefl` | 1256 | `lift_full_idJ` | B.3d |
| `iotaIdStrictRecRefl` | 1269 | `lift_full_idStrictRec` | B.3d |
| `iotaBoolElimTrueDeep` | 1403 | `lift_full_boolElim` | B.3b |
| `iotaBoolElimFalseDeep` | 1418 | `lift_full_boolElim` | B.3b |
| `iotaNatElimZeroDeep` | 1433 | `lift_full_natElim` | B.3b |
| `iotaNatElimSuccDeep` | 1445 | `lift_full_natElim` | B.3b |
| `iotaNatRecZeroDeep` | 1459 | `lift_full_natRec` | B.3b |
| `iotaNatRecSuccDeep` | 1472 | `lift_full_natRec` | B.3b |
| `iotaListElimNilDeep` | 1491 | `lift_full_listElim` | B.3b |
| `iotaListElimConsDeep` | 1505 | `lift_full_listElim` | B.3b |
| `iotaOptionMatchNoneDeep` | 1524 | `lift_full_optionMatch` | B.3b |
| `iotaOptionMatchSomeDeep` | 1536 | `lift_full_optionMatch` | B.3b |
| `iotaEitherMatchInlDeep` | 1550 | `lift_full_eitherMatch` | B.3b |
| `iotaEitherMatchInrDeep` | 1564 | `lift_full_eitherMatch` | B.3b |
| `iotaIdJReflDeep` | 1578 | `lift_full_idJ` | B.3d |
| `iotaIdStrictRecReflDeep` | 1594 | `lift_full_idStrictRec` | B.3d |

**ι coverage: 28/28 typed ctors absorbed (no deferrals).**

### Total B.3.* coverage summary

* β rules: **19/21 absorbed** (90.5%); 2 deferred under documented
  `lift_full_appPi` structured-source-split gap (B.3a #1729 docstring
  lines 42-149).
* ι rules: **28/28 absorbed** (100%).
* Combined: **47/49 typed β/ι ctors absorbed** (95.9%).

The remaining 2 deferrals (`betaAppPi{,Deep}`) are isolated to the
B.3a `lift_full_appPi` structural gap and tracked separately —
they do not block CONVTRANS-C chain assembly because Π
subject-reduction routes through the simpler `Step.par.appPi`
cong arm + the source-canonical-form sub-lifts already shipped.

## Cong-only lifts in this batch — structural rationale

Two of B.3e's six lifts (`lift_full_sessionRecv` and
`lift_full_effectPerform`) are **cong-only**, mirroring the
established B.3c `lift_full_hcomp_cong` and B.3d `lift_full_oeqJ`
pattern.  This is **correct** kernel-level coverage, not a
deferral:

* Session-type β collapse would require a canonical-form witness
  for the protocol-step parameter, but `protocolStep` is a free
  RawTerm at the kernel level (computed from the surrounding
  Term.session expression at elaboration time).
* Effect-perform β collapse is the responsibility of the
  handler-bind layer in `Effects/*`, which is elaborator-level
  and does not interact with `Step.par` directly.

In both cases the typed kernel ships exactly one constructor
(`sessionRecvCong` / `effectPerformCong`) for the relevant
typed reduction, and the lift covers it.  Shipping a β arm
would require new kernel ctors that do not (and structurally
should not) exist.

## Documented blockers — NOT in B.3e scope

Two β-arm lifts CANNOT ship at the current typed kernel.  Both
are kernel-extension blockers, not proof blockers:

### `lift_full_appPi` β-arm — blocked on structured-source split

Carried over from B.3a (#1729).  See
`AuditConvTransB3aPiSigmaBeta.lean:42-149` for the full
analysis.  Summary: the dependent Π β-rule lift needs to split
its source position into pre-committed canonical-form variants
(`lift_full_appPi_lamPi` + `lift_full_appPi_funextRefl`) because
the headline form runs into a cd-cascade head-mismatch when
covering both lamPi and funextRefl sources under a single
existential.

### `lift_full_equivApply` β-arm — blocked on typed `uaBeta`

Carried over from B.3d (#1732).  See
`AuditConvTransB3dJotaBeta.lean:55-97` for the full analysis.
Summary: raw `RawStep.par.uaBeta{,Deep}` ship at
`Reduction/RawPar.lean:1049/1071` but no typed mirror exists in
`Reduction/ParRed/ParInductive.lean`.  Trackers: #1571
(D3.6-UA-BETA-INTERNAL — typed `Step.par.uaBeta{,Deep}` ctors)
and #1572 (D3.6-UA-BETA-SUBLEMMAS — supporting inversion /
parity-allowlist / cd cascade extensions).

Neither blocker is in B.3e scope; both are tracked in
ROADMAP and revisit under their respective kernel-extension
batches.

## Cascade role

B.3e is the **fifth and final** β/ι-rule lift audit, closing
out the B.3.* macro-family.  Subsequent CONVTRANS-B work is
exhausted:

* **B.1** (#1727) — basic chain framework (closed).
* **B.2.{a-g}** (#1721-1728) — cong-rule lifts across Π/Σ/path/
  glue/HoTT/type-codes (closed).
* **B.3.{a-e}** (#1729-1733) — β/ι-rule lifts across all
  remaining constructor families (closed by this commit).

**CONVTRANS-B macro: 13/13 sub-tickets shipped.**

Next CONVTRANS phase:

* **CONVTRANS-C** (#1734) — chain lift assembling all B.2.* and
  B.3.* lifts into a single per-term subject-reduction step.
* **CONVTRANS-D** (#1735) — `Step.subjectReduction` headline
  (every typed Step.par preserves Conv).
* **CONVTRANS-Audit** (#1736) — strict-gate sweep over the
  headline + supporting infrastructure.

## Why this audit lives under Smoke instead of Tools/AuditAll

Same reasoning as `AuditConvTransB3aPiSigmaBeta.lean`,
`AuditConvTransB3bIotaRules.lean`,
`AuditConvTransB3cCubicalBeta.lean`, and
`AuditConvTransB3dJotaBeta.lean`: `Term.PreservesTerm` is
reachable as a production module only through its smoke audits.
Co-location of `#print axioms` with the strict gates keeps the
reviewer-facing log adjacent.

The `#assert_no_axioms` strict gates fire under the
`LeanFX2Audit` target identically to gates in `Tools/AuditAll/`.

## Consolidation pattern

This audit reuses the structural template from
`AuditConvTransB3dJotaBeta.lean`: pre-existing typed advanced
β/ι-rule lifts with one `#assert_no_axioms` strict gate per lift,
one `#print axioms` reviewer log per lift.  No new theorem
bodies shipped in this commit — the six advanced lifts existed
prior under Tier 2/3 eliminator and Tier 1 cong coverage in
`TwoTyEliminators.lean` and `TwoTyAtomsAndCong.lean`.  The new
B.3e banner certifies the modal/record/refine/codata/session/
effect β/ι-coverage as a coherent audit family, completing the
B.3.* macro-family with explicit blocker documentation cross-
referencing B.3a (appPi) and B.3d (equivApply). -/

namespace LeanFX2.SmokeConvTransB3eAdvancedBeta

/-! ## Strict gates — `#assert_no_axioms`

Build-failing under `LeanFX2Audit` if any of the six advanced
β/ι-rule lifts ever reaches an axiom. -/

#assert_no_axioms LeanFX2.RawStep.par.lift_full_modElim
#assert_no_axioms LeanFX2.RawStep.par.lift_full_recordProj
#assert_no_axioms LeanFX2.RawStep.par.lift_full_refineElim
#assert_no_axioms LeanFX2.RawStep.par.lift_full_codataDest
#assert_no_axioms LeanFX2.RawStep.par.lift_full_sessionRecv
#assert_no_axioms LeanFX2.RawStep.par.lift_full_effectPerform

/-! ## Reviewer-facing log — `#print axioms`

Each invocation prints "does not depend on any axioms" alongside
the strict gates above. -/

#print axioms LeanFX2.RawStep.par.lift_full_modElim
#print axioms LeanFX2.RawStep.par.lift_full_recordProj
#print axioms LeanFX2.RawStep.par.lift_full_refineElim
#print axioms LeanFX2.RawStep.par.lift_full_codataDest
#print axioms LeanFX2.RawStep.par.lift_full_sessionRecv
#print axioms LeanFX2.RawStep.par.lift_full_effectPerform

end LeanFX2.SmokeConvTransB3eAdvancedBeta
