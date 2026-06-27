import FX1Poly.Typed.Metatheory.SubjectReduction.IntroObligationsDriftBounded
import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionCongruenceClosesGeneric

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/IntroGateReassembleBounded
    — SR-WF-TIEOFF (intro third): the FUEL-BOUNDED introducer-congruence reassembly

The fuel-bounded twin of `introGateRowReassemble` (`IntroGateReassemble.lean`).  Identical body — drive the
obligations forward across the arg step, rebuild the cell at the after-args via the native `intro` arm, post-compose
the output drift — but it consumes the FUEL-BOUNDED driver `premisesHoldUnderObligationsDriftBelow` (over
`ObligationsDriftBelow profile bound`) instead of the universal `premisesHoldUnderObligationsDrift`, so each
introducer branch can feed the gate's `UnionChildSubjectReductionBelow profile (rule.memberCell scope args).size`
directly (the stepping arg is a structural cell-child, strictly smaller than `memberCell.size`).

## Zero-axiom

`premisesHoldUnderObligationsDriftBelow` (the bounded driver) + the native `HasTypeUnion.intro` constructor.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **★ The fuel-bounded introducer-congruence reassembly.**  Given the obligations held at `args`, the
re-established side condition at `argsAfter`, the FUEL-BOUNDED obligation drift `ObligationsDriftBelow profile bound`
to `argsAfter`, and the output drift, the cell rebuilt at `argsAfter` re-types at `outputType argsAfter` (`Conv`-equal
to `outputType args`) — the bounded analogue of `introGateRowReassemble`, feeding the native `intro` constructor from
`UnionChildSubjectReductionBelow profile bound`. -/
theorem introGateRowReassembleBounded {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    (generator : Generator) (rule : IntroRule)
    {args argsAfter : RawTermChildren rule.argShifts scope} (params : RawTermChildren rule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (isIntro : introRuleOf generator = some rule)
    (premisesHold : ∀ obligation ∈ rule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    {bound : Nat}
    (childSubjectReductionBelow : UnionChildSubjectReductionBelow profile bound)
    (sideHoldsAfter : rule.sideCondition scope argsAfter)
    (drift : ObligationsDriftBelow profile bound
      (rule.obligations scope context args params level0 level1 flag)
      (rule.obligations scope context argsAfter params level0 level1 flag))
    (outputDrift : Conv (rule.outputType scope argsAfter params) (rule.outputType scope args params)) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context (rule.memberCell scope argsAfter) pinned ∧
      Conv pinned (rule.outputType scope args params) := by
  have premisesAfter := premisesHoldUnderObligationsDriftBelow drift childSubjectReductionBelow premisesHold
  exact ⟨rule.outputType scope argsAfter params,
    HasTypeUnion.intro context generator rule argsAfter params level0 level1 flag isIntro sideHoldsAfter
      premisesAfter,
    outputDrift⟩

end FX1Poly.Typed
