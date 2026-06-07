import FX1Poly.Typed.HasTypeDescWeakening
import FX1Poly.Typed.HasTypeDescSubstitution
import FX1Poly.Typed.HasTypeDescStronglyNormalizing
import FX1Poly.Typed.HasTypeDescSubjectReduction
import FX1Poly.Typed.HasTypeDescPiWeakening
import FX1Poly.Typed.HasTypeDescPiSubstitution
import FX1Poly.Typed.OpenStronglyNormalizingUnconditional
import FX1Poly.Typed.SubjectReductionAtFormerGeneric
import FX1Poly.Typed.HasTypeDescPiSubjectReductionConvOfFormationArms

/-! # FX1Poly/Typed/MetatheoryParityLedger — PAR-1: formation↔grown reduction-metatheory parity

The kernel runs TWO typing engines (§ supersession): the FORMATION engine `HasTypeDesc` (var / conv /
universeFormation / generic `genFormation`, the table-driven type-FORMATION judgment) and the GROWN engine
`HasTypeDescPi` (`ofFormation` lift + `piIntro` / `piElim`, adding the binder INTRODUCTION and ELIMINATION
rules).  Each carries its own reduction metatheory.  This file is the honest, machine-anchored ledger of WHICH
metatheory holds on WHICH engine — and, crucially, where the two diverge.

## The honest parity picture (reduction-metatheory quartet)

| Property            | Formation `HasTypeDesc`            | Grown `HasTypeDescPi`                                   |
| ------------------- | ---------------------------------- | ------------------------------------------------------ |
| Weakening           | `renameRespectingContext` (uncond) | `renameRespectingContext` (uncond)                     |
| Substitution        | `substRespectingContext` (uncond)  | `substRespectingContext` (uncond)                      |
| Strong normalization| `isStronglyNormalizing` (uncond)   | `stronglyNormalizingOfWfContextDesc` (WF-ctx presup.)  |
| Subject reduction   | `subjectReduction` (uncond MASTER) | unconditional ARMS only; MASTER conditional on GCC-5   |

`MetatheoryProperty.parityStatus` records the three honest outcomes:

  * **`bothUnconditional`** — weakening, substitution: full parity, each engine has the theorem with no
    precondition.
  * **`grownNeedsWfContext`** — strong normalization: BOTH hold, but the grown one carries the well-formed-
    context presupposition (`WfContextDesc`).  This is a DECIDABLE presupposition (the honest precondition, not
    a blocker — the unqualified interface is unprovable because the var rule types in any context).
  * **`grownConditionalOnBundle`** — subject reduction: the formation MASTER is unconditional and cascade-free
    (`HasTypeDesc.subjectReduction` routes `genFormation` via the generic former arm); the grown engine has only
    the unconditional ARMS (`subjectReductionAtFormerGeneric` / `…AtConv` / `…AtOfFormation`).  Its MASTER
    dispatcher needs the piElim arm, which needs context-conversion of the function's exact Π classifier =
    "typing a Conv-equal type" = type-Conv-closure, circular with SR — the GCC-5 mutual fundamental-metatheory
    bundle (#842 / #845).  THIS is the precisely-scoped Milestone-A SR blocker.

The point the ledger makes auditable: the grown SN presupposition (`grownNeedsWfContext`) is a BENIGN decidable
precondition and is NOT the same thing as the grown SR being blocked (`grownConditionalOnBundle`) — the
discrimination theorems below prove the ledger keeps the benign presupposition and the real blocker distinct.

## Kernel-anchored, non-vacuous

Each both-engines (or unconditional-arm) claim is anchored `def parityAnchor_<prop>_<engine> := @<shippedDecl>`
(the §27.3-L3 cross-reference idiom): the file fails to compile if any anchored theorem is renamed/deleted, and
each anchor's `#assert_no_axioms` gate re-certifies that engine's proof is itself zero-axiom.  No unconditional
grown SR MASTER is anchored — because none exists; the ledger does not overstate.

## Zero-axiom verification

`MetatheoryProperty` / `EngineParityStatus` are plain enums (`parityStatus` a full-enumeration match);
the anchors are proof-term aliases of shipped zero-axiom theorems; the ledger facts are `rfl`; the
discriminations reduce the statuses then close by `EngineParityStatus.noConfusion`.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

/-- The core reduction-metatheory properties whose formation↔grown parity this ledger records. -/
inductive MetatheoryProperty where
  | weakening
  | substitution
  | strongNormalization
  | subjectReduction

/-- The three honest parity outcomes between the formation and grown engines. -/
inductive EngineParityStatus where
  /-- Both engines have the theorem with no precondition. -/
  | bothUnconditional
  /-- Both hold; the grown theorem carries the (decidable) well-formed-context presupposition. -/
  | grownNeedsWfContext
  /-- Formation unconditional; grown only as unconditional ARMS, its MASTER conditional on the GCC-5 bundle. -/
  | grownConditionalOnBundle
  deriving DecidableEq

/-- The parity status of each reduction-metatheory property (full enumeration, no wildcard). -/
def MetatheoryProperty.parityStatus : MetatheoryProperty → EngineParityStatus
  | .weakening => .bothUnconditional
  | .substitution => .bothUnconditional
  | .strongNormalization => .grownNeedsWfContext
  | .subjectReduction => .grownConditionalOnBundle

/-! ## Both-engines / unconditional-arm anchors (the teeth)

Each anchor binds the shipped proof term by reference; its gate re-certifies that engine's proof is
zero-axiom, and the file breaks if the theorem is renamed. -/

/-- Weakening, formation engine. -/
def parityAnchor_weakening_formation := @HasTypeDesc.renameRespectingContext
/-- Weakening, grown engine. -/
def parityAnchor_weakening_grown := @HasTypeDescPi.renameRespectingContext
/-- Substitution, formation engine. -/
def parityAnchor_substitution_formation := @HasTypeDesc.substRespectingContext
/-- Substitution, grown engine. -/
def parityAnchor_substitution_grown := @HasTypeDescPi.substRespectingContext
/-- Strong normalization, formation engine (unconditional). -/
def parityAnchor_strongNormalization_formation := @HasTypeDesc.isStronglyNormalizing
/-- Strong normalization, grown engine (over a well-formed context — the decidable presupposition). -/
def parityAnchor_strongNormalization_grown := @HasTypeDescPi.stronglyNormalizingOfWfContextDesc
/-- Subject reduction, formation engine — the UNCONDITIONAL master dispatcher (cascade-free via the generic
former arm). -/
def parityAnchor_subjectReduction_formation := @HasTypeDesc.subjectReduction
/-- Subject reduction, grown engine — the cascade-free generic FORMER arm (unconditional fragment). -/
def parityAnchor_subjectReduction_grownFormerArm := @HasTypeDescPi.subjectReductionAtFormerGeneric
/-- Subject reduction, grown engine — the conv arm (unconditional fragment). -/
def parityAnchor_subjectReduction_grownConvArm := @HasTypeDescPi.subjectReductionAtConv
/-- Subject reduction, grown engine — the ofFormation arm (unconditional fragment). -/
def parityAnchor_subjectReduction_grownOfFormationArm := @HasTypeDescPi.subjectReductionAtOfFormation

/-! ## Ledger facts -/

/-- Weakening is at FULL parity (both engines, unconditional). -/
theorem weakening_atFullParity :
    MetatheoryProperty.weakening.parityStatus = .bothUnconditional := rfl

/-- Substitution is at FULL parity (both engines, unconditional). -/
theorem substitution_atFullParity :
    MetatheoryProperty.substitution.parityStatus = .bothUnconditional := rfl

/-- Strong normalization holds on both engines; the grown one carries the (benign, decidable)
well-formed-context presupposition. -/
theorem strongNormalization_grownNeedsWfContext :
    MetatheoryProperty.strongNormalization.parityStatus = .grownNeedsWfContext := rfl

/-- Subject reduction is the ASYMMETRY: formation unconditional, grown master conditional on the GCC-5
mutual fundamental-metatheory bundle (#842 / #845) — the precisely-scoped Milestone-A SR blocker. -/
theorem subjectReduction_grownConditionalOnBundle :
    MetatheoryProperty.subjectReduction.parityStatus = .grownConditionalOnBundle := rfl

/-! ## Non-vacuity: the ledger genuinely discriminates -/

/-- The ledger separates full parity from the real blocker: weakening's status differs from subject
reduction's.  (A `passesReview = true`-style tautology guard: the status function is not constant.) -/
theorem parity_discriminates_weakening_vs_subjectReduction :
    MetatheoryProperty.weakening.parityStatus ≠ MetatheoryProperty.subjectReduction.parityStatus := by
  intro statusEq
  rw [weakening_atFullParity, subjectReduction_grownConditionalOnBundle] at statusEq
  exact EngineParityStatus.noConfusion statusEq

/-- **The honest distinction:** the grown SN's well-formed-context presupposition is NOT the GCC-5 blocker.
The ledger keeps `grownNeedsWfContext` (a benign decidable precondition) distinct from
`grownConditionalOnBundle` (the real SR blocker) — so "grown SN needs WF context" is never conflated with
"grown SR is blocked". -/
theorem parity_discriminates_strongNormalization_vs_subjectReduction :
    MetatheoryProperty.strongNormalization.parityStatus ≠
      MetatheoryProperty.subjectReduction.parityStatus := by
  intro statusEq
  rw [strongNormalization_grownNeedsWfContext, subjectReduction_grownConditionalOnBundle] at statusEq
  exact EngineParityStatus.noConfusion statusEq

end FX1Poly.Typed
