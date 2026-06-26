import FX1Poly.Typed.Metatheory.SubjectReduction.FormationObligationSize
import FX1Poly.Typed.Metatheory.SubjectReduction.UnionChildSubjectReductionBounded

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/FormationBoundedChildSubjectReduction
    — the formation gate runs on the FUEL-BOUNDED child-SR (SR-WF-TIEOFF step 3, formation)

`HasTypeUnionFormationCongruenceGate.lean` inhabits `UnionFormationCongruenceCloses` by building, INTERNALLY, the
per-obligation inline single-step-SR form

    `∀ obligation ∈ rule.obligations …, ∀ reduct, Step obligation.subject reduct → ∃ pinned, …`

from the UNIVERSAL `UnionChildSubjectReduction` premise (it applies `childSubjectReduction` to each obligation's
typing).  The SR-WF-TIEOFF needs that inline form from the FUEL-BOUNDED `UnionChildSubjectReductionBelow profile
cell.size` instead — because the well-founded recursion only supplies single-step SR for terms STRICTLY SMALLER
than the stepping cell.

This file ships exactly that bridge for the formation family: `formationGateInlineChildSubjectReductionOfBelow`
constructs the inline form from `UnionChildSubjectReductionBelow profile (mkGen generator payload children).size`.
It works because every formation obligation's subject is a structural child of the spine
(`formationRuleObligationSubjectSizeBound`), so `obligation.subject.size < children.size < cell.size` (the `mkGen`
size step `Nat.lt_succ_self`, `cell.size = children.size + 1` by `rfl`) — exactly the bound the fuel-bounded
predicate demands.  The formation gate's internal construction is then a drop-in: replace the universal
`childSubjectReduction (premisesHold …) stepReduct` with this bridge.

This is the FORMATION third of the bounded-gate refactor — the clean family (every obligation subject IS a child,
unlike `elim`'s `pathApp` carrier param, which is reconstructed from the typing, never steps in a congruence, and
so is carried over unchanged rather than re-typed).

## Zero-axiom

`formationRuleObligationSubjectSizeBound` (zero-axiom) + `Nat.lt_trans` + `Nat.lt_succ_self` + `Conv.sym`.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- ★ **The formation gate's inline child-SR, from the fuel-bounded predicate.**  Given the fuel-bounded
single-step SR at the stepping cell's size, every formation obligation's subject (a structural child, strictly
smaller than the cell) re-types after a single step at a `Conv`-equal classifier — the exact inline form the
formation congruence gate consumes, now sourced from `UnionChildSubjectReductionBelow` rather than the universal
`UnionChildSubjectReduction`.  The load-bearing bridge that lets the well-founded recursion (IH = SR below the
cell's size) discharge the formation gate. -/
theorem formationGateInlineChildSubjectReductionOfBelow {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} (generator : Generator) (payload : generator.payload scope)
    (children : RawTermChildren generator.binderShifts scope)
    (rule : FormationRule) (levels : List LevelExpr) (carrier : RawTerm scope)
    (level : LevelExpr) (flag : UniverseFlag)
    (premisesHold : ∀ obligation ∈ rule.obligations profile context children levels carrier level flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (childSubjectReductionBelow :
      UnionChildSubjectReductionBelow profile (RawTerm.mkGen generator payload children).size) :
    ∀ obligation ∈ rule.obligations profile context children levels carrier level flag,
      ∀ reduct : RawTerm obligation.scope, Step obligation.subject reduct →
        ∃ pinned : RawTerm obligation.scope,
          HasTypeUnion profile obligation.context reduct pinned ∧ Conv pinned obligation.classifier := by
  intro obligation obligationMem reduct stepReduct
  have subjectBelowChildren :
      obligation.subject.size < children.size :=
    formationRuleObligationSubjectSizeBound rule context carrier level flag children levels obligation obligationMem
  have subjectBelowCell :
      obligation.subject.size < (RawTerm.mkGen generator payload children).size :=
    Nat.lt_trans subjectBelowChildren (Nat.lt_succ_self children.size)
  have ⟨reductType, reductTyped, classifierConv⟩ :=
    childSubjectReductionBelow subjectBelowCell (premisesHold obligation obligationMem) stepReduct
  exact ⟨reductType, reductTyped, classifierConv.sym⟩

end FX1Poly.Typed
