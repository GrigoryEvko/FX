import LeanFX2.Tools.DependencyAudit
import LeanFX2.Term.PreservesTerm

/-! # AuditConvTransB2eCubicalCong — CONVTRANS-B.2e cubical-family cong-only lift audit

Strict gate plus reviewer-facing audit for the ten
`RawStep.par.lift_<X>_cong` (or `lift_<X>`) theorems that ship the
**cubical-family cong-only** of CONVTRANS-A subject-reduction term
construction (CONVTRANS-B.2e, ticket #1726).

Each lift takes raw parallel-reduction steps on its Term subterms
together with per-subterm typed-lift callbacks, and produces a typed
`Step.par sourceTerm targetTerm` witness via the corresponding
`Step.par.<X>` (or `<X>Cong`) constructor.  Bodies live across four
sub-modules of `Term/PreservesTerm/`:

| Lift | Host file |
| --- | --- |
| `lift_pathLam` | `TierZeroAndUnary.lean` |
| `lift_intervalOpp` | `TierZeroAndUnary.lean` |
| `lift_pathApp_cong` | `EliminatorShallowBeta.lean` |
| `lift_transp_cong` | `EliminatorShallowBeta.lean` |
| `lift_glueElim` | `EliminatorShallowBeta.lean` |
| `lift_intervalMeet` | `TierTwoBinary.lean` |
| `lift_intervalJoin` | `TierTwoBinary.lean` |
| `lift_glueIntro` | `TierTwoBinary.lean` |
| `lift_hcomp_cong` | `TierTwoBinary.lean` |
| `lift_hcompPath_cong` | `EliminatorCubicalFamily.lean` |

The new entry in this batch is `lift_hcompPath_cong`; the other nine
lifts were shipped in prior cascades and are consolidated under this
banner so the audit log certifies "B.2e cubical cong family complete
and zero-axiom".

## Coverage

* `lift_pathLam` — path lambda (`Term.pathLam`), cong-only (no β
  arm at the typed level).
* `lift_intervalOpp` — interval negation (`Term.intervalOpp`).
* `lift_pathApp_cong` — path-app cong arm (β arms
  `betaPathApp` / `betaPathReflApp` live in a future full lift).
* `lift_transp_cong` — transp cong arm (β arms `transpReflBeta` /
  `uaBeta` / `transpCompose` and their Deep variants live in a
  future full lift; D3.6 cascade).
* `lift_glueElim` — glue elimination (full lift with β arm,
  shipped in the eliminator-shallow-β cascade).
* `lift_intervalMeet` — interval meet (`Term.intervalMeet`).
* `lift_intervalJoin` — interval join (`Term.intervalJoin`).
* `lift_glueIntro` — glue introduction (`Term.glueIntro`).
* `lift_hcomp_cong` — homogeneous composition cong arm (β arms
  `hcompBeta` / `hcompBetaDeep` are raw-only D2.5.2 ctors targeting
  the path-typed-sides representation; see `hcompPath` below).
* `lift_hcompPath_cong` — path-shaped homogeneous composition cong
  arm (`Term.hcompPath` redesign of `hcomp` per `Term.lean:472`).

## Why "cong" rather than "full"

`hcomp` / `hcompPath` typed β arms targeting the path-typed-sides
representation are pending; the D2.5.2 raw β rules `hcompBeta`
and `hcompBetaDeep` already land in `RawStep.par`, but the typed
mirrors (which would consume a typed pathLam witness on the sides
slot) wait on the Phase B cubical-β cascade.  Similarly, `transp`
and `pathApp` β arms require body-substitution casts deferred to
the `BetaCastWallDemolition` family.  `pathLam`, `intervalOpp`,
`intervalMeet`, `intervalJoin`, `glueIntro` have no β arms — their
cong-only lifts ARE the total raw inversion projection.
`glueElim` ships its full β-firing lift; this audit gates the
cong projection covered by `lift_glueElim`'s cong arm.

## Cascade role

Mirrors `AuditConvTransB2dModalCong.lean` for the modal-family
(ticket #1725), `AuditConvTransB2cIdentityCong.lean` for the
identity-family (ticket #1724), `AuditConvTransB2bClosedTypeCong.lean`
for the closed-type family (ticket #1723), and
`AuditConvTransB2aPiSigmaCong.lean` for the Π/Σ family
(ticket #1722).  Together B.2a + B.2b + B.2c + B.2d + B.2e cover
the cong-only typed-step construction for Π/Σ, closed-type,
identity-type, modal, and cubical eliminators; record/refine/codata/
session/effect families (CONVTRANS-B.2f, ticket #1727) follow next,
and type-code + HoTT-special families (CONVTRANS-B.2g, ticket #1728)
close the cascade.

## Why this audit lives under Smoke instead of Tools/AuditAll

Same reasoning as `AuditConvTransB2dModalCong.lean`:
`Term.PreservesTerm` is reachable as a production module only through
its smoke audits.  Co-location of `#print axioms` with the strict
gates keeps the reviewer-facing log adjacent.

The `#assert_no_axioms` strict gates fire under the `LeanFX2Audit`
target identically to gates in `Tools/AuditAll/`. -/

namespace LeanFX2.SmokeConvTransB2eCubicalCong

/-! ## Strict gates — `#assert_no_axioms`

Build-failing under `LeanFX2Audit` if any of the ten cubical-family
cong-only lifts ever reaches an axiom. -/

#assert_no_axioms LeanFX2.RawStep.par.lift_pathLam
#assert_no_axioms LeanFX2.RawStep.par.lift_intervalOpp
#assert_no_axioms LeanFX2.RawStep.par.lift_pathApp_cong
#assert_no_axioms LeanFX2.RawStep.par.lift_transp_cong
#assert_no_axioms LeanFX2.RawStep.par.lift_glueElim
#assert_no_axioms LeanFX2.RawStep.par.lift_intervalMeet
#assert_no_axioms LeanFX2.RawStep.par.lift_intervalJoin
#assert_no_axioms LeanFX2.RawStep.par.lift_glueIntro
#assert_no_axioms LeanFX2.RawStep.par.lift_hcomp_cong
#assert_no_axioms LeanFX2.RawStep.par.lift_hcompPath_cong

/-! ## Reviewer-facing log — `#print axioms`

Each invocation prints "does not depend on any axioms" alongside the
strict gates above. -/

#print axioms LeanFX2.RawStep.par.lift_pathLam
#print axioms LeanFX2.RawStep.par.lift_intervalOpp
#print axioms LeanFX2.RawStep.par.lift_pathApp_cong
#print axioms LeanFX2.RawStep.par.lift_transp_cong
#print axioms LeanFX2.RawStep.par.lift_glueElim
#print axioms LeanFX2.RawStep.par.lift_intervalMeet
#print axioms LeanFX2.RawStep.par.lift_intervalJoin
#print axioms LeanFX2.RawStep.par.lift_glueIntro
#print axioms LeanFX2.RawStep.par.lift_hcomp_cong
#print axioms LeanFX2.RawStep.par.lift_hcompPath_cong

end LeanFX2.SmokeConvTransB2eCubicalCong
