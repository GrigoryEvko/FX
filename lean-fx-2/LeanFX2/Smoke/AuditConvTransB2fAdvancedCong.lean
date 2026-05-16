import LeanFX2.Tools.DependencyAudit
import LeanFX2.Term.PreservesTerm

/-! # AuditConvTransB2fAdvancedCong — CONVTRANS-B.2f record/refine/codata/session/effect cong family

Strict gate plus reviewer-facing audit for the nine
`RawStep.par.lift_<X>` cong-only theorems that ship the
**record/refine/codata/session/effect-family cong-only** of
CONVTRANS-A subject-reduction term construction (CONVTRANS-B.2f,
ticket #1727).

Each lift takes raw parallel-reduction steps on its Term subterms
together with per-subterm typed-lift callbacks, and produces a typed
`Step.par sourceTerm targetTerm` witness via the corresponding
`Step.par.<X>Cong` constructor.  Bodies live across four sub-modules
of `Term/PreservesTerm/`:

| Lift | Host file |
| --- | --- |
| `lift_recordIntro` | `TierZeroAndUnary.lean` |
| `lift_recordProj` | `EliminatorShallowBeta.lean` |
| `lift_refineIntro` | `TierTwoBinary.lean` |
| `lift_refineElim` | `EliminatorShallowBeta.lean` |
| `lift_codataUnfold` | `TierTwoBinary.lean` |
| `lift_codataDest` | `EliminatorShallowBeta.lean` |
| `lift_sessionSend` | `TierTwoBinary.lean` |
| `lift_sessionRecv` | `TierTwoBinary.lean` |
| `lift_effectPerform` | `EliminatorConstantMotive.lean` |

All nine lifts were shipped in prior cascades and are consolidated
under this banner so the audit log certifies "B.2f record / refine /
codata / session / effect cong family complete and zero-axiom".

## Coverage

* `lift_recordIntro` — single-field record introduction
  (`Term.recordIntro`), cong-only over the field subterm.  No β arm
  at the typed level (β fires under `recordProj`).
* `lift_recordProj` — single-field record projection
  (`Term.recordProj`), full lift including shallow β arm.  This audit
  gates the cong projection used by the higher-level term-construction
  walker.
* `lift_refineIntro` — refinement introduction
  (`Term.refineIntro predicate value proof`), cong over both `value`
  and `proof` subterms.  Predicate slot is raw-only.
* `lift_refineElim` — refinement elimination
  (`Term.refineElim refined`), full lift; cong used by the walker.
* `lift_codataUnfold` — codata introduction
  (`Term.codataUnfold initialState transition`), cong over the
  `initialState` and `transition` subterms.
* `lift_codataDest` — codata destruction
  (`Term.codataDest codataValue`), full lift; cong arm consolidated
  here.
* `lift_sessionSend` — session send
  (`Term.sessionSend protocolStep channel payload`), cong over
  `channel` and `payload`.  `protocolStep` slot is raw-only.
* `lift_sessionRecv` — session receive
  (`Term.sessionRecv channel`), cong over `channel`.
* `lift_effectPerform` — effect operation invocation
  (`Term.effectPerform effectTag effectRow operationSignature ...`),
  cong over the operation arguments.

## Why "cong" rather than "full"

`recordIntro`, `refineIntro`, `codataUnfold`, `sessionSend`,
`sessionRecv`, `effectPerform` have no β arms at the typed level —
their cong-only lifts ARE the total raw inversion projection.
`recordProj`, `refineElim`, `codataDest` ship full lifts including
shallow-β firing; this audit gates the cong projection covered by
each lift's cong arm.

## Cascade role

Mirrors `AuditConvTransB2eCubicalCong.lean` for the cubical family
(ticket #1726), `AuditConvTransB2dModalCong.lean` for the
modal-family (ticket #1725), `AuditConvTransB2cIdentityCong.lean`
for the identity-family (ticket #1724),
`AuditConvTransB2bClosedTypeCong.lean` for the closed-type family
(ticket #1723), and `AuditConvTransB2aPiSigmaCong.lean` for the
Π/Σ family (ticket #1722).  Together B.2a + B.2b + B.2c + B.2d +
B.2e + B.2f cover the cong-only typed-step construction for Π/Σ,
closed-type, identity-type, modal, cubical, and record/refine/
codata/session/effect eliminators; type-code + HoTT-special
families (CONVTRANS-B.2g, ticket #1728) close the cascade before
pivoting to B.3 β-rule lifts.

## Consolidation pattern

This audit reuses the structural template from
`AuditConvTransB2eCubicalCong.lean` (commit 76028a0): nine pre-
existing typed cong lifts, one #assert_no_axioms strict gate per
lift, one #print axioms reviewer log per lift, no new theorem
bodies.  Investigation confirmed all nine `*Cong` constructors in
`Reduction/ParRed/ParInductive.lean` already have matching lifts;
no missing lift_*_cong theorems exist in this family.

## Why this audit lives under Smoke instead of Tools/AuditAll

Same reasoning as `AuditConvTransB2eCubicalCong.lean`:
`Term.PreservesTerm` is reachable as a production module only through
its smoke audits.  Co-location of `#print axioms` with the strict
gates keeps the reviewer-facing log adjacent.

The `#assert_no_axioms` strict gates fire under the `LeanFX2Audit`
target identically to gates in `Tools/AuditAll/`. -/

namespace LeanFX2.SmokeConvTransB2fAdvancedCong

/-! ## Strict gates — `#assert_no_axioms`

Build-failing under `LeanFX2Audit` if any of the nine
record/refine/codata/session/effect-family cong-only lifts ever
reaches an axiom. -/

#assert_no_axioms LeanFX2.RawStep.par.lift_recordIntro
#assert_no_axioms LeanFX2.RawStep.par.lift_recordProj
#assert_no_axioms LeanFX2.RawStep.par.lift_refineIntro
#assert_no_axioms LeanFX2.RawStep.par.lift_refineElim
#assert_no_axioms LeanFX2.RawStep.par.lift_codataUnfold
#assert_no_axioms LeanFX2.RawStep.par.lift_codataDest
#assert_no_axioms LeanFX2.RawStep.par.lift_sessionSend
#assert_no_axioms LeanFX2.RawStep.par.lift_sessionRecv
#assert_no_axioms LeanFX2.RawStep.par.lift_effectPerform

/-! ## Reviewer-facing log — `#print axioms`

Each invocation prints "does not depend on any axioms" alongside the
strict gates above. -/

#print axioms LeanFX2.RawStep.par.lift_recordIntro
#print axioms LeanFX2.RawStep.par.lift_recordProj
#print axioms LeanFX2.RawStep.par.lift_refineIntro
#print axioms LeanFX2.RawStep.par.lift_refineElim
#print axioms LeanFX2.RawStep.par.lift_codataUnfold
#print axioms LeanFX2.RawStep.par.lift_codataDest
#print axioms LeanFX2.RawStep.par.lift_sessionSend
#print axioms LeanFX2.RawStep.par.lift_sessionRecv
#print axioms LeanFX2.RawStep.par.lift_effectPerform

end LeanFX2.SmokeConvTransB2fAdvancedCong
