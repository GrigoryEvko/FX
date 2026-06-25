import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Metatheory.Canonicity.NatStructuredCandidate
import FX1Poly.Core.Metatheory.Canonicity.ListStructuredCandidate

/-! # FX1PolyAudit/Core/Metatheory/Canonicity/StructuredCandidates
    — zero-axiom gate for the open-scope Nat / List structural reducibility candidates (DEP-NAT/LIST-MODEL)

The open-scope structural candidates the dependent `natElim` / `natRec` / `listElim` reducibility arms pin
`natTypeCell` / `listTypeCell` to: the `IsNatStructured` / `IsListStructured` value predicates (closed under
the constructor at EVERY scope, unlike the scope-0-only `natSuccDataTaitMember` / `listConsDataTaitMember`),
their candidate / head-expansion-closure proofs, the backward predecessor / head-tail extraction stones, and
the trichotomy / confluence stones the outer structural recursion consumes.  The closed-collapse lemmas
(`natStructuredClosedReducesToNumeral` / `listStructuredClosedReducesToValue`) confirm each widening is
conservative for closed canonicity.  Split out of the recursive data-intro shard to keep each file under the
audit-shard eval ceiling.  Must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The OPEN-SCOPE nat structural candidate (NatStructuredCandidate.lean): the `IsNatStructured` value
-- predicate (`succ^k` of `zero` or a NORMAL neutral) whose `dataTaitCandidate` is closed under `natSucc` at
-- EVERY scope, unlike the scope-0-only `natSuccDataTaitMember` above (which rules the neutral disjunct out
-- with `IsNeutral.noClosed`).  The candidate the dependent `natElim` / `natRec` reducibility pins
-- `natTypeCell` to; `natStructuredClosedReducesToNumeral` confirms the widening is conservative for closed
-- canonicity (closed members are still exactly the numerals).
#assert_no_axioms FX1Poly.Core.isNatStructured_impliesStepNormalForm
#assert_no_axioms FX1Poly.Core.isNatValue_implies_isNatStructured
#assert_no_axioms FX1Poly.Core.isNatStructured_closed_isNatValue
#assert_no_axioms FX1Poly.Core.natStructuredCandidate_isReducibilityCandidate
#assert_no_axioms FX1Poly.Core.natStructuredCandidate_headExpansionClosed
#assert_no_axioms FX1Poly.Core.isNatValue_structuredMember
#assert_no_axioms FX1Poly.Core.natZeroStructuredMember
#assert_no_axioms FX1Poly.Core.natSuccStructuredMember
-- DEP-NAT-CORE: the BACKWARD predecessor-extraction stones the dependent recursive natElim member consumes —
-- a neutral head is never natSucc, the natSucc child reflects SN, IsNatStructured succ-inverts, and so the
-- structured-candidate natSucc cell's predecessor is itself a structured-candidate member.
#assert_no_axioms FX1Poly.Core.isNeutral_rootGenerator_ne_natSucc
#assert_no_axioms FX1Poly.Core.natSuccCell_predecessor_isStronglyNormalizing
#assert_no_axioms FX1Poly.Core.isNatStructured_succ_inversion
#assert_no_axioms FX1Poly.Core.natSuccStructuredMember_predecessor
-- DEP-NAT-CORE: the trichotomy/confluence stones the dependent recursive natElim member's outer structural
-- recursion + value-handler consume — the candidate-side value-head/neutral bridge, the structured-value
-- extraction starting the recursion, and the confluence corollary realigning a scrutinee reduct against the
-- structured value it reaches.
#assert_no_axioms FX1Poly.Core.eq_natZeroCell_of_rootGenerator
#assert_no_axioms FX1Poly.Core.exists_predecessor_of_rootGenerator_natSucc
#assert_no_axioms FX1Poly.Core.isNatStructured_valueHeadOrNeutral
#assert_no_axioms FX1Poly.Core.natStructuredMemberReachesStructuredValue
#assert_no_axioms FX1Poly.Core.stepStar_focus_reaches_normal_target
#assert_no_axioms FX1Poly.Core.natStructuredClosedReducesToNumeral

-- The OPEN-SCOPE list structural candidate (ListStructuredCandidate.lean, DEP-LIST-MODEL): the
-- `IsListStructured` value predicate (`nil`, a NORMAL neutral, or `cons` of a normal head onto a structured
-- tail) whose `dataTaitCandidate` is closed under `listCons` at EVERY scope — the BINARY recursive twin of
-- `IsNatStructured`, unlike the scope-0-only `listConsDataTaitMember` above (which rules the neutral-tail
-- disjunct out with `IsNeutral.noClosed`).  The candidate the model pins `listTypeCell` to; the closed
-- collapse `listStructuredClosedReducesToValue` confirms the widening is conservative for closed canonicity
-- (closed members are still exactly the strict list values).
#assert_no_axioms FX1Poly.Core.isListStructured_impliesStepNormalForm
#assert_no_axioms FX1Poly.Core.isListValue_implies_isListStructured
#assert_no_axioms FX1Poly.Core.isListStructured_closed_isListValue
#assert_no_axioms FX1Poly.Core.listStructuredCandidate_isReducibilityCandidate
#assert_no_axioms FX1Poly.Core.listStructuredCandidate_headExpansionClosed
#assert_no_axioms FX1Poly.Core.isListValue_structuredMember
#assert_no_axioms FX1Poly.Core.listNilStructuredMember
#assert_no_axioms FX1Poly.Core.listConsStructuredMember
#assert_no_axioms FX1Poly.Core.listStructuredClosedReducesToValue
-- DEP-LIST #1729 (sub-A): the eliminator-side stones the dependent listElim member consumes — the BINARY-cons
-- twins of the nat eliminator stones (two-child injection drilling, two-child SN reflection, the
-- both-children-normal lift for backward tail extraction).
#assert_no_axioms FX1Poly.Core.isNeutral_rootGenerator_ne_listCons
#assert_no_axioms FX1Poly.Core.eq_listNilCell_of_rootGenerator
#assert_no_axioms FX1Poly.Core.exists_head_tail_of_rootGenerator_listCons
#assert_no_axioms FX1Poly.Core.isListStructured_valueHeadOrNeutral
#assert_no_axioms FX1Poly.Core.listConsCell_head_isStronglyNormalizing
#assert_no_axioms FX1Poly.Core.listConsCell_tail_isStronglyNormalizing
#assert_no_axioms FX1Poly.Core.isListStructured_cons_inversion
#assert_no_axioms FX1Poly.Core.listConsStructuredMember_tail
#assert_no_axioms FX1Poly.Core.listStructuredMemberReachesStructuredValue

end FX1PolyAudit
