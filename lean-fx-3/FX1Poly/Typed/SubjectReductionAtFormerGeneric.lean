import FX1Poly.Typed.FormerStepInversionGeneric
import FX1Poly.Typed.HasTypeDescPi

/-! # FX1Poly/Typed/SubjectReductionAtFormerGeneric
    — the CASCADE-FREE generic former subject-reduction arm: ONE arm for the whole formation family (TG-2)

`HasTypeDescPiSubjectReductionFormerArms.lean` / `…InlineArms.lean` ship the FORMER subject-reduction routing
arms `subjectReductionAtPiFormer` / `subjectReductionAtSigmaFormer` / `subjectReductionPiFormerArm` /
`subjectReductionSigmaFormerArm` — each hard-coded to a SPECIFIC formation generator (`gen_piTyCode` /
`gen_sigmaTyCode`) via `Step.from_piTyCode` / `Step.from_sigmaTyCode` and the per-shape former congruences.  The
moment a new formation row lands (a data type code `listCode`/`optionCode`/…, a cubical former, a HIT code), the
SR dispatcher would need a NEW per-former arm — the cascade-death trap (polycell.md §3.16.19).

This file ships the table-generic successor: ONE former SR arm over `typingRuleDescOf`, with NO formation
generator named.

> `subjectReductionAtFormerGeneric` — for ANY `generator` with `typingRuleDescOf generator = some rule`, a step
> out of the genFormationPi-typed former `mkGen generator payload children` re-types at the SAME output
> `rule.outputType scope levels flag`, given the premise telescope's subject reduction.

## How it stays cascade-free

A former heads no root redex, so by `formerCellStepIsChildCongruence` (TG-1, itself enumeration-free) the step
is a child congruence `StepChildren children childrenAfter` with `target = mkGen generator payload childrenAfter`.
Re-typing the stepped premise telescope (`telescopeSR`, the mutual-partner `DescTelescopePi` subject reduction)
and reassembling via the GENERIC `HasTypeDescPi.genFormationPi` at the unchanged `rule.outputType` discharges the
goal.  Every step here is generic over the `typingRuleDescOf` table — adding a formation row is absorbed
zero-touch.  The `telescopeSR` premise is the genuine deferral: it is the grown telescope SR
(`DescTelescopePi.subjectReduction`, SRD-4), mutual with the master dispatcher, whose `here` (binding-head-steps)
case consumes the grown context-conversion (#814 pt2b / GCC) — exactly as the specific
`subjectReductionPiFormerArm` takes its `codomainReTyping` premise.  The master dispatcher (TG-3) supplies
`telescopeSR` via that mutual recursion and routes its `genFormationPi` case through this ONE generic arm.

## Zero-axiom verification

`formerCellStepIsChildCongruence` (TG-1) + `HasTypeDescPi.genFormationPi` (the engine's generic former arm).  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated
in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Cascade-free generic former subject reduction.**  A step out of a genFormationPi-typed former (ANY
formation generator) re-types at the same output `rule.outputType scope levels flag`, given the premise
telescope's subject reduction.  One arm for the whole `typingRuleDescOf` family — the table-generic successor to
the per-former `subjectReductionAtPiFormer` / `subjectReductionAtSigmaFormer`. -/
theorem HasTypeDescPi.subjectReductionAtFormerGeneric {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {generator : Generator} {payload : generator.payload scope}
    {children : RawTermChildren generator.binderShifts scope}
    {levels : List LevelExpr} {flag : UniverseFlag} {rule : TypingRuleDesc}
    {target : RawTerm scope}
    (isFormation : typingRuleDescOf generator = some rule)
    (step : Step (.mkGen generator payload children) target)
    (telescopeSR : ∀ {childrenAfter : RawTermChildren generator.binderShifts scope},
      StepChildren children childrenAfter →
        DescTelescopePi profile (currentDepth := 0) context levels flag childrenAfter) :
    HasTypeDescPi profile context target (rule.outputType scope levels flag) := by
  obtain ⟨childrenAfter, targetEq, stepChildren⟩ := formerCellStepIsChildCongruence isFormation step
  subst targetEq
  exact HasTypeDescPi.genFormationPi context generator payload childrenAfter levels flag rule isFormation
    (telescopeSR stepChildren)

end FX1Poly.Typed
