import FX1Poly.Typed.Metatheory.SubjectReduction.ElimObligationsDrift
import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionCongruenceClosesGeneric

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/IntroGateReassemble
    — SR-DSL-5: the GENERIC reassembly core of the INTRODUCER-congruence gate

The companion of `ElimGateReassemble.lean` for the `intro` arm.  The introducer-congruence gate
`UnionIntroCongruenceCloses` (HasTypeUnionCongruenceClosesGeneric.lean) re-types a stepped introducer cell.  Its
per-generator branches all share ONE reassembly: drive the obligations forward across the arg step
(`premisesHoldUnderObligationsDrift`, the SR-DSL-4 driver), rebuild the cell at the after-args via the native `intro`
arm, and post-compose the output drift.

The introducer arm differs from the eliminator arm in ONE field: `HasTypeUnion.intro` carries a `sideHolds :
rule.sideCondition scope args` (the load-bearing graded-binder usage discipline for `lam` / `pathLam`; `True` for the
data constructors).  So the reassembly takes the re-established `sideHoldsAfter : rule.sideCondition scope argsAfter`
as an explicit hypothesis — the per-row branch supplies it (`trivial` for the 15 data rows, `gradedBinderChecks`
preservation for the two graded binders).

The native `intro` arm's `isIntro` field is `fxTypingBundle.intro generator = some rule`, which is DEFINITIONALLY
the gate's `introRuleOf generator = some rule` (`fxTypingBundle.intro := introRuleOf`), so the gate's certificate
feeds it directly.

## Zero-axiom

`premisesHoldUnderObligationsDrift` (the SR-DSL-4 driver) + the native `HasTypeUnion.intro` constructor.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **★ The generic introducer-congruence reassembly.**  Given the obligations held at `args`, the re-established
side condition at `argsAfter`, the obligation drift to `argsAfter`, and the output drift `Conv (outputType argsAfter)
(outputType args)`, the cell rebuilt at `argsAfter` re-types at `outputType argsAfter`, which is `Conv`-equal to
`outputType args` — exactly the introducer gate's `∃ pinned, … ∧ Conv pinned (outputType args)` once the
per-generator branch identifies `rule.memberCell scope argsAfter` with its reformed `mkGen`.  The driver feeds the
native `intro` constructor directly. -/
theorem introGateRowReassemble {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    (generator : Generator) (rule : IntroRule)
    {args argsAfter : RawTermChildren rule.argShifts scope} (params : RawTermChildren rule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (isIntro : introRuleOf generator = some rule)
    (premisesHold : ∀ obligation ∈ rule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (childSubjectReduction : UnionChildSubjectReduction profile)
    (sideHoldsAfter : rule.sideCondition scope argsAfter)
    (drift : ObligationsDrift profile
      (rule.obligations scope context args params level0 level1 flag)
      (rule.obligations scope context argsAfter params level0 level1 flag))
    (outputDrift : Conv (rule.outputType scope argsAfter params) (rule.outputType scope args params)) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context (rule.memberCell scope argsAfter) pinned ∧
      Conv pinned (rule.outputType scope args params) := by
  have premisesAfter := premisesHoldUnderObligationsDrift drift childSubjectReduction premisesHold
  exact ⟨rule.outputType scope argsAfter params,
    HasTypeUnion.intro context generator rule argsAfter params level0 level1 flag isIntro sideHoldsAfter
      premisesAfter,
    outputDrift⟩

end FX1Poly.Typed
