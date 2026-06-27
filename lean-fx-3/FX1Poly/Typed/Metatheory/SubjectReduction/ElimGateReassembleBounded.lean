import FX1Poly.Typed.Metatheory.SubjectReduction.IntroObligationsDriftBounded
import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionCongruenceClosesGeneric

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/ElimGateReassembleBounded
    — SR-WF-TIEOFF (elim third): the FUEL-BOUNDED eliminator-congruence reassembly

The fuel-bounded twin of `elimGateRowReassemble` (`ElimGateReassemble.lean`).  Identical body — drive the
obligations forward across the arg step, rebuild the cell at the after-args via the native `elim` arm, post-compose
the output drift — but it consumes the FUEL-BOUNDED driver `premisesHoldUnderObligationsDriftBelow` (over
`ObligationsDriftBelow profile bound`) instead of the universal `premisesHoldUnderObligationsDrift`, so each
eliminator branch can feed the gate's `UnionChildSubjectReductionBelow profile (rule.memberCell scope args).size`
directly.

Recall the bounded driver discharges each obligation position WITHOUT folding child-SR along a multi-step classifier
chain: the clean arg positions via `SubjectDriftBelow` (single-step-below-bound subject, fixed classifier), the
`natElim`/`natRec` motive-in-context-head drift via `consContextHeadConv` (`convertHeadBinding` + direct
after-formedness), and the dependent recursors' MOTIVE-step branch positions via `consClassifierConv` (subject
fixed, classifier drifts via a `Conv`, `classifierFormedAfter` supplied DIRECTLY by the branch from the
type-formation-from-motive construction).

## Zero-axiom

`premisesHoldUnderObligationsDriftBelow` (the bounded driver) + the native `HasTypeUnion.elim` constructor.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **★ The fuel-bounded eliminator-congruence reassembly.**  Given the obligations held at `args`, the FUEL-BOUNDED
obligation drift `ObligationsDriftBelow profile bound` to `argsAfter`, and the output drift, the cell rebuilt at
`argsAfter` re-types at `outputType argsAfter` (`Conv`-equal to `outputType args`) — the bounded analogue of
`elimGateRowReassemble`, feeding the native `elim` constructor from `UnionChildSubjectReductionBelow profile
bound`. -/
theorem elimGateRowReassembleBounded {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    (generator : Generator) (rule : ElimRule)
    {args argsAfter : RawTermChildren rule.argShifts scope} (params : RawTermChildren rule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (isElim : elimRuleOf generator = some rule)
    (premisesHold : ∀ obligation ∈ rule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    {bound : Nat}
    (childSubjectReductionBelow : UnionChildSubjectReductionBelow profile bound)
    (drift : ObligationsDriftBelow profile bound
      (rule.obligations scope context args params level0 level1 flag)
      (rule.obligations scope context argsAfter params level0 level1 flag))
    (outputDrift : Conv (rule.outputType scope argsAfter params) (rule.outputType scope args params)) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context (rule.memberCell scope argsAfter) pinned ∧
      Conv pinned (rule.outputType scope args params) := by
  have premisesAfter := premisesHoldUnderObligationsDriftBelow drift childSubjectReductionBelow premisesHold
  exact ⟨rule.outputType scope argsAfter params,
    HasTypeUnion.elim context generator rule argsAfter params level0 level1 flag isElim premisesAfter,
    outputDrift⟩

end FX1Poly.Typed
