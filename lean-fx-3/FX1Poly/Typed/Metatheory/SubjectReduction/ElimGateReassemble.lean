import FX1Poly.Typed.Metatheory.SubjectReduction.ElimObligationsDrift
import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionCongruenceClosesGeneric

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/ElimGateReassemble
    — SR-DSL-5: the GENERIC reassembly core of the eliminator-congruence gate

The eliminator-congruence gate `UnionElimCongruenceCloses` (HasTypeUnionCongruenceClosesGeneric.lean) re-types a
stepped eliminator cell.  Its per-generator branches all share ONE reassembly: drive the obligations forward across
the arg step, rebuild the cell at the after-args via the native `elim` arm, and post-compose the output drift.  This
file ships that core as a single generic lemma — the per-row work the gate dispatches to is then ONLY the row's
`ObligationsDrift` (the `*ObligationsDriftUnderArgStep` family) plus its one-line output drift.

`premisesHoldUnderObligationsDrift` produces EXACTLY the `∀ obligation ∈ rule.obligations … argsAfter …, HasType
Union …` shape that `HasTypeUnion.elim`'s `premisesHold` field consumes, so the rebuild is a direct constructor
application at `argsAfter`.  The native `elim` arm's `isElim` field is `fxTypingBundle.elim generator = some rule`,
which is DEFINITIONALLY the gate's `elimRuleOf generator = some rule` (`fxTypingBundle.elim := elimRuleOf`), so the
gate's certificate feeds it directly.

## Zero-axiom

`premisesHoldUnderObligationsDrift` (the SR-DSL-4 driver) + the native `HasTypeUnion.elim` constructor.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **★ The generic eliminator-congruence reassembly.**  Given the obligations held at `args`, the obligation drift
to `argsAfter` (a `*ObligationsDriftUnderArgStep` instance), and the output drift `Conv (outputType argsAfter)
(outputType args)`, the cell rebuilt at `argsAfter` re-types at `outputType argsAfter`, which is `Conv`-equal to
`outputType args` — exactly the eliminator gate's `∃ pinned, … ∧ Conv pinned (outputType args)` once the per-generator
branch rewrites `rule.memberCell scope argsAfter` to its reformed `mkGen`.  The driver feeds the native `elim`
constructor directly. -/
theorem elimGateRowReassemble {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    (generator : Generator) (rule : ElimRule)
    {args argsAfter : RawTermChildren rule.argShifts scope} (params : RawTermChildren rule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag)
    (isElim : elimRuleOf generator = some rule)
    (premisesHold : ∀ obligation ∈ rule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (childSubjectReduction : UnionChildSubjectReduction profile)
    (drift : ObligationsDrift profile
      (rule.obligations scope context args params level0 level1 flag)
      (rule.obligations scope context argsAfter params level0 level1 flag))
    (outputDrift : Conv (rule.outputType scope argsAfter params) (rule.outputType scope args params)) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context (rule.memberCell scope argsAfter) pinned ∧
      Conv pinned (rule.outputType scope args params) := by
  have premisesAfter := premisesHoldUnderObligationsDrift drift childSubjectReduction premisesHold
  exact ⟨rule.outputType scope argsAfter params,
    HasTypeUnion.elim context generator rule argsAfter params level0 level1 flag isElim premisesAfter,
    outputDrift⟩

end FX1Poly.Typed
