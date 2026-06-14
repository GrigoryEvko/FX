import FX1Poly.Typed.BridgeRelationalSconeIdentityPath
import FX1Poly.Typed.GradedIntroPremiseSpike
import FX1Poly.Tier0.Syntax.RawTermFreeVars
import FX1Poly.Tier0.Syntax.RawTermOccurrenceRename

/-! # FX1Poly/Typed/BridgeRelationalSconeAffineRole — the affine premise's semantic role (NATIVE-59)

The closing brick of the internal-parametricity model arc.  NATIVE-57 made the Bridge scone carry
the carrier relation; NATIVE-58 placed the reflexivity (identity-path) inhabitant on the diagonal.
This file pins WHAT THE AFFINE PREMISE DOES semantically — why the dimension binder's usage grade is
load-bearing for the relational interpretation, not decorative.

The dimension binder's affine premise is `gradedBinderChecks .one body`, i.e. the dimension variable
occurs `≤ 1` times in the body.  Its semantic role is a SEPARATION:

  * **count 0 (ghost-graded, the reflexivity bridge)** — the body is dimension-constant
    (`weaken carrierTerm`); BOTH endpoint substitutions collapse to `carrierTerm`
    (`reflexivityBridge_endpointBetaComputes`), so the bridge spans only the DIAGONAL `(t, t)` and
    the scone consults the carrier relation only reflexively (`R t t`, NATIVE-58).
  * **count 1 (genuinely affine, the identity path on the interval)** — the body USES its dimension
    (`var 0`); the two endpoints β-compute to the DISTINCT interval endpoints `interval0` /
    `interval1`, so the bridge spans an OFF-DIAGONAL pair and the scone consults the carrier relation
    relationally (`R interval0 interval1`, distinct).  This off-diagonal content is exactly what the
    affine budget — usage UP TO one, allowing one — buys.
  * **count ≥ 2 (rejected)** — the affine UPPER bound `≤ 1` refuses a body that duplicates its
    dimension.  Duplication is the unsound move that would let the two endpoints be forced equal
    (collapsing the relation back to the diagonal); the premise blocks it
    (`duplicatingBody_failsAffinePremise`).

So the usage grade is the relational rank knob: `0` = diagonal-only, `1` = full relational,
`≥ 2` = rejected.  Two FX dimensions (type × usage) are jointly load-bearing for one feature's
content — the design point recorded in `KernelParamSubstrateSurvey`.

  * `intervalZero_ne_intervalOne` — the endpoints of the affine identity path are distinct.
  * `affineIdentityPath_endpointZeroComputes` / `_endpointOneComputes` — they β-compute to the two
    distinct interval endpoints.
  * ★ `affineIdentityPath_sconeMemberOffDiagonal` — the affine identity path inhabits the OFF-diagonal
    scone pair `(interval0, interval1)` when the carrier relates them.
  * `affineBody_occurrenceCountIsOne` / `constantBody_occurrenceCountIsZero` — the grade facts.
  * ★ `duplicatingBody_failsAffinePremise` — count `≥ 2` is rejected (the soundness guard).
  * ★ `affinePremise_separatesDiagonalFromRelational` — the bundle: affine off-diagonal membership +
    distinct endpoints + the count-1 budget + the count-2 rejection.

Zero-axiom; gated in `FX1PolyAudit/AuditBridgeRelationalSconeAffineRole.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Modal
open StepStar

/-- The two endpoints of the affine identity path are DISTINCT (different interval generators) — so
the affine bridge genuinely spans an off-diagonal pair, unlike the diagonal reflexivity bridge. -/
theorem intervalZero_ne_intervalOne {scope : Nat} :
    (intervalZeroCell : RawTerm scope) ≠ intervalOneCell := by
  intro endpointsEqual
  have generatorsEqual : Generator.gen_interval0 = Generator.gen_interval1 :=
    congrArg RawTerm.rootGenerator endpointsEqual
  exact Generator.noConfusion generatorsEqual

/-- The affine identity path applied to the LEFT interval endpoint β-computes to `interval0`. -/
theorem affineIdentityPath_endpointZeroComputes {scope : Nat} :
    StepTable
      (pathAppCell (pathLamCell (variableCell ⟨0, Nat.succ_pos scope⟩))
        (intervalZeroCell (scope := scope)))
      intervalZeroCell :=
  StepTable.pathBetaFires (variableCell ⟨0, Nat.succ_pos scope⟩) intervalZeroCell

/-- The affine identity path applied to the RIGHT interval endpoint β-computes to `interval1`. -/
theorem affineIdentityPath_endpointOneComputes {scope : Nat} :
    StepTable
      (pathAppCell (pathLamCell (variableCell ⟨0, Nat.succ_pos scope⟩))
        (intervalOneCell (scope := scope)))
      intervalOneCell :=
  StepTable.pathBetaFires (variableCell ⟨0, Nat.succ_pos scope⟩) intervalOneCell

/-- ★ **Off-diagonal scone membership.**  When the carrier relation relates the DISTINCT interval
endpoints (`carrierRelation interval0 interval1`), the affine identity path `pathLam(var 0)` is a
member of the relational scone over the off-diagonal pair `(interval0, interval1)`.  This is the
relational content the affine budget (usage exactly one) makes available — unreachable by the
count-0 reflexivity bridge, whose endpoints are forced equal. -/
theorem affineIdentityPath_sconeMemberOffDiagonal {scope : Nat}
    {carrierRelation : BinaryCandidate scope}
    (offDiagonalRelated : carrierRelation intervalZeroCell intervalOneCell) :
    bridgeRelationalCandidate carrierRelation intervalZeroCell intervalOneCell
      (pathLamCell (variableCell ⟨0, Nat.succ_pos scope⟩)) :=
  bridgeRelationalCandidate.intro
    (pathLam_isStronglyNormalizing_of_body
      (IsStronglyNormalizing.ofIsStepNormalForm rfl))
    offDiagonalRelated

/-- The affine identity-path body `var 0` uses its dimension EXACTLY once (count `1`). -/
theorem affineBody_occurrenceCountIsOne {scope : Nat} :
    RawTerm.occurrenceCountAt (variableCell ⟨0, Nat.succ_pos scope⟩)
      ⟨0, Nat.succ_pos scope⟩ = 1 :=
  RawTerm.occurrenceCountAt_var_self ⟨0, Nat.succ_pos scope⟩

/-- The reflexivity-bridge body `weaken carrierTerm` is dimension-CONSTANT (count `0`, ghost-grade,
stronger than affine). -/
theorem constantBody_occurrenceCountIsZero {scope : Nat} (carrierTerm : RawTerm scope) :
    RawTerm.occurrenceCountAt (RawTerm.weaken carrierTerm) ⟨0, Nat.succ_pos scope⟩ = 0 :=
  RawTerm.occurrenceCountAt_weaken_zeroPosition carrierTerm

/-- ★ **The soundness guard: count `≥ 2` is rejected.**  Any body that uses its dimension variable
twice fails the affine premise `gradedBinderChecks .one` (`2 ≤ 1` is false) — the upper bound blocks
the duplication that would collapse the relational interpretation back to the diagonal. -/
theorem duplicatingBody_failsAffinePremise {scope : Nat} {body : RawTerm (scope + 1)}
    (duplicatesDimension :
      RawTerm.occurrenceCountAt body ⟨0, Nat.succ_pos scope⟩ = 2) :
    ¬ gradedBinderChecks UsageGrade.one body := by
  intro affineCheck
  have bound : RawTerm.occurrenceCountAt body ⟨0, Nat.succ_pos scope⟩ ≤ 1 := affineCheck
  rw [duplicatesDimension] at bound
  exact absurd bound (by decide)

/-- ★ **The semantic role of the affine premise, bundled.**  The affine (count-1) identity path
inhabits the OFF-diagonal scone pair `(interval0, interval1)` with DISTINCT endpoints, its body uses
the dimension exactly once, and any count-`≥ 2` body is rejected.  Together with NATIVE-58 (count-0
⟹ diagonal-only), this exhibits the usage grade as the relational-rank knob separating
diagonal-only from full-relational, with duplication soundly refused. -/
theorem affinePremise_separatesDiagonalFromRelational {scope : Nat}
    {carrierRelation : BinaryCandidate scope}
    (offDiagonalRelated : carrierRelation intervalZeroCell intervalOneCell) :
    bridgeRelationalCandidate carrierRelation intervalZeroCell intervalOneCell
        (pathLamCell (variableCell ⟨0, Nat.succ_pos scope⟩))
      ∧ (intervalZeroCell : RawTerm scope) ≠ intervalOneCell
      ∧ RawTerm.occurrenceCountAt (variableCell ⟨0, Nat.succ_pos scope⟩)
          ⟨0, Nat.succ_pos scope⟩ = 1
      ∧ ∀ body : RawTerm (scope + 1),
          RawTerm.occurrenceCountAt body ⟨0, Nat.succ_pos scope⟩ = 2 →
          ¬ gradedBinderChecks UsageGrade.one body :=
  ⟨affineIdentityPath_sconeMemberOffDiagonal offDiagonalRelated,
   intervalZero_ne_intervalOne,
   affineBody_occurrenceCountIsOne,
   fun _body duplicates => duplicatingBody_failsAffinePremise duplicates⟩

end FX1Poly.Typed
