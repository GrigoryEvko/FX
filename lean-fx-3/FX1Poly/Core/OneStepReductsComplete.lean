import FX1Poly.Core.OneStepReducts
import FX1Poly.Core.StepStarConfluenceViaTable

/-! # FX1Poly/Core/OneStepReductsComplete
    — enumeration COMPLETENESS: every kernel Step is listed (COST-3 brick 3), TABLE-BACKED

The hard half of the reduct enumeration: every `Step` lands in `oneStepReducts`.  Since the
IOTA-T11 enumeration rebase this is ONE generic theorem instead of a 17-arm per-iota match: the
IOTA-T1 forward adequacy (`Step.toTableStep`) maps the bespoke step onto the canonical table,
and the generic table completeness (`oneStepReductsOverTable_complete`, certified by the
well-formedness pin `iotaRuleTable_isWf`) lists its reduct.  Adding an iota rule to the
kernel changes this file by NOTHING.

With brick 2's soundness this yields the CHARACTERIZATION `step_iff_mem_oneStepReducts`: the
computable enumeration decides exactly the `Step` relation — the substrate the worst-case
`costBound` folds over.

Zero-axiom; gated in `FX1PolyAudit/AuditTypedSubstVecCwR.lean`. -/

namespace FX1Poly.Core

open Foundation

/-! ## ★ Completeness — every Step is listed -/

/-- ★ **Enumeration completeness**: every `Step` reduct is listed — the bespoke step's
legacy-table image, listed by the generic table completeness under the legacy well-formedness
certificate. -/
theorem RawTerm.oneStepReducts_complete {scope : Nat} {term reduct : RawTerm scope}
    (bespokeStep : Step term reduct) :
    reduct ∈ RawTerm.oneStepReducts term :=
  oneStepReductsOverTable_complete iotaRuleTable_isWf bespokeStep.toTableStep

/-- Spine completeness: every children step is listed — the spine companion through the legacy
adequacy. -/
theorem RawTermChildren.oneStepChildrenReducts_complete {binderShifts : List Nat}
    {parentScope : Nat} {children steppedSpine : RawTermChildren binderShifts parentScope}
    (childrenStep : StepChildren children steppedSpine) :
    steppedSpine ∈ RawTermChildren.oneStepChildrenReducts children :=
  oneStepChildrenReductsOverTable_complete iotaRuleTable_isWf
    (StepChildren.toTableStepChildren childrenStep)

/-! ## ★ The characterization — the enumeration decides Step -/

/-- ★ **The enumeration characterizes one-step reduction**: a term steps to exactly the members
of its computable reduct list — soundness (brick 2) and completeness in one biconditional.  This
is the substrate the worst-case `costBound` folds over: the fold's recursive calls are justified
by soundness, and its bound covers EVERY strategy by completeness. -/
theorem RawTerm.step_iff_mem_oneStepReducts {scope : Nat}
    {term reduct : RawTerm scope} :
    Step term reduct ↔ reduct ∈ RawTerm.oneStepReducts term :=
  ⟨RawTerm.oneStepReducts_complete, RawTerm.oneStepReducts_sound term⟩

end FX1Poly.Core
