import LeanFX2.Tools.DependencyAudit
import LeanFX2.Term.PreservesTerm

/-! # AuditConvTransB3bIotaRules — CONVTRANS-B.3b closed-type ι-rule lifts

Strict gate plus reviewer-facing audit for the **closed-type
eliminator ι-rule lift** family of CONVTRANS-A subject-reduction
term construction (CONVTRANS-B.3b, ticket #1730).  Second
β/ι-rule sub-ticket after B.3a (#1729) closed Π/Σ β-rules.

## Scope of B.3b

Six `RawStep.par.lift_full_*` theorems, one per closed-type
eliminator, each carrying both the cong arm AND the type-changing
ι-arms (where the scrutinee develops via `RawStep.par` *to* the
matching canonical introducer of the closed inductive — `boolTrue`
/ `boolFalse`, `natZero` / `natSucc`, `listNil` / `listCons`,
`optionNone` / `optionSome`, `eitherInl` / `eitherInr`).  Each lift
absorbs:

* The **cong arm** — scrutinee + branches all step via `RawStep.par`
  and reassemble through the same Term ctor.
* The **ι-arm pair** (one per canonical introducer) — scrutinee
  steps to a closed-type canonical, exposing the matching branch
  as the eliminator's result.  Both shallow `iota<X>` and deep
  `iota<X>Deep` typed Step.par ctors are absorbed under the
  single deep lift because the shallow form is a specialization
  of the deep form (scrutinee is already the canonical literal).

The two-Ty existential pattern from
`Term/PreservesTerm/BetaCastWallDemolition.lean`:

```
∃ (targetTy : Ty level scope) (targetTerm : Term context targetTy
    targetRaw),
  Step.par sourceTerm targetTerm
```

absorbs the cast wall between the cong-arm target Ty and each
ι-arm target Ty (branches inhabit `motiveType.subst0` /
`Ty.arrow` / etc. so the joint target Ty discharges via the
existential).

| Lift | Host file | Source line | ι-arms |
| --- | --- | --- | --- |
| `lift_full_boolElim` | `HeterogeneousElim.lean` | 290 | `iotaBoolElim{True,False}{,Deep}` |
| `lift_full_natElim` | `TwoTyEliminators.lean` | 28 | `iotaNatElim{Zero,Succ}{,Deep}` |
| `lift_full_natRec` | `TwoTyEliminators.lean` | 57 | `iotaNatRec{Zero,Succ}{,Deep}` |
| `lift_full_listElim` | `TwoTyEliminators.lean` | 89 | `iotaListElim{Nil,Cons}{,Deep}` |
| `lift_full_optionMatch` | `TwoTyEliminators.lean` | 124 | `iotaOptionMatch{None,Some}{,Deep}` |
| `lift_full_eitherMatch` | `TwoTyEliminators.lean` | 155 | `iotaEitherMatch{Inl,Inr}{,Deep}` |

These six lifts collectively cover **24 typed ι ctors** in
`Reduction/ParRed/ParInductive.lean`:

* 6 eliminators × 2 canonical introducers × 2 depth (shallow + deep)
* Shallow ctors: `iota{Bool,Nat,List,Option,Either}*` at lines
  1082, 1095, 1108, 1118, 1132, 1143, 1163, 1176, 1199, 1210,
  1224, 1240.
* Deep ctors: `iota{Bool,Nat,List,Option,Either}*Deep` at lines
  1403, 1418, 1433, 1445, 1459, 1472, 1491, 1505, 1524, 1536,
  1550, 1564.

## What this audit does NOT include

Two ι-rule families are explicitly OUT of B.3b scope:

* **Identity ι rules** (`iotaIdJRefl` line 1256, `iotaIdJReflDeep`
  line 1578; `iotaIdStrictRecRefl` line 1269, `iotaIdStrictRecRefl`
  Deep line 1594).  These belong to CONVTRANS-B.3d (identity-family
  ι rules) and are already shipped via `lift_full_idJ` and
  `lift_full_idStrictRec` in
  `Term/PreservesTerm/BetaCastWallDemolition.lean` — audit-gated
  under their own follow-up ticket (B.3d, #1732).

* **Cubical/HoTT ι rules** (transp/hcomp/glue/path-app
  reductions).  These belong to CONVTRANS-B.3c (cubical β/ι),
  ticket #1731.

## Gap verification

Investigation of `Reduction/ParRed/ParInductive.lean` (28 total
ι ctors): 12 shallow + 12 deep closed-type ctors are covered by
the 6 lifts above.  The remaining 4 ctors (idJ/idStrictRec ×
{shallow, deep}) are identity-family, properly excluded from B.3b.

**No closed-type ι-rule lift gaps remain.**

In particular, the Deep variants of each closed-type eliminator
have full coverage:

* `iotaBoolElim{True,False}Deep` (lines 1403/1418) → consumed
  inside `lift_full_boolElim` body via three-arm raw inversion
  (`HeterogeneousElim.lean:319-355`).
* `iotaNatElim{Zero,Succ}Deep` (lines 1433/1445) → consumed
  inside `lift_full_natElim` via `RawStep.par.lift_natElim`.
* `iotaNatRec{Zero,Succ}Deep` (lines 1459/1472) → consumed
  inside `lift_full_natRec` via `RawStep.par.lift_natRec`.
* `iotaListElim{Nil,Cons}Deep` (lines 1491/1505) → consumed
  inside `lift_full_listElim` via `RawStep.par.lift_listElim`.
* `iotaOptionMatch{None,Some}Deep` (lines 1524/1536) → consumed
  inside `lift_full_optionMatch` via `RawStep.par.lift_optionMatch`.
* `iotaEitherMatch{Inl,Inr}Deep` (lines 1550/1564) → consumed
  inside `lift_full_eitherMatch` via `RawStep.par.lift_eitherMatch`.

## Cascade role

B.3b is the second ι-rule lift audit, completing the closed-type
ι coverage.  Subsequent B.3.* tickets handle cubical β/ι rules
(transpReflBeta, hcompBeta, glueBeta, pathAppBeta — #1731 B.3c),
identity ι rules (`iotaIdJRefl`, `iotaIdStrictRecRefl` — #1732
B.3d), and modal/HoTT-special β/ι rules (#1733 B.3e).

## Why this audit lives under Smoke instead of Tools/AuditAll

Same reasoning as `AuditConvTransB3aPiSigmaBeta.lean` and the
prior B.2.* / B.3a audits: `Term.PreservesTerm` is reachable as
a production module only through its smoke audits.  Co-location
of `#print axioms` with the strict gates keeps the reviewer-
facing log adjacent.

The `#assert_no_axioms` strict gates fire under the
`LeanFX2Audit` target identically to gates in `Tools/AuditAll/`.

## Consolidation pattern

This audit reuses the structural template from
`AuditConvTransB3aPiSigmaBeta.lean`: pre-existing typed ι-rule
lifts with one `#assert_no_axioms` strict gate per lift, one
`#print axioms` reviewer log per lift.  No new theorem bodies
shipped in this commit — the six ι-rule lifts existed prior
under Tier 3 eliminator coverage.  The new B.3b banner certifies
the closed-type ι coverage as a coherent audit family. -/

namespace LeanFX2.SmokeConvTransB3bIotaRules

/-! ## Strict gates — `#assert_no_axioms`

Build-failing under `LeanFX2Audit` if any of the six closed-type
ι-rule lifts ever reaches an axiom. -/

#assert_no_axioms LeanFX2.RawStep.par.lift_full_boolElim
#assert_no_axioms LeanFX2.RawStep.par.lift_full_natElim
#assert_no_axioms LeanFX2.RawStep.par.lift_full_natRec
#assert_no_axioms LeanFX2.RawStep.par.lift_full_listElim
#assert_no_axioms LeanFX2.RawStep.par.lift_full_optionMatch
#assert_no_axioms LeanFX2.RawStep.par.lift_full_eitherMatch

/-! ## Reviewer-facing log — `#print axioms`

Each invocation prints "does not depend on any axioms" alongside
the strict gates above. -/

#print axioms LeanFX2.RawStep.par.lift_full_boolElim
#print axioms LeanFX2.RawStep.par.lift_full_natElim
#print axioms LeanFX2.RawStep.par.lift_full_natRec
#print axioms LeanFX2.RawStep.par.lift_full_listElim
#print axioms LeanFX2.RawStep.par.lift_full_optionMatch
#print axioms LeanFX2.RawStep.par.lift_full_eitherMatch

end LeanFX2.SmokeConvTransB3bIotaRules
