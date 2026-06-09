import FX1Poly.Typed.DenoteKeyedLevelIrrelevance

/-! # FX1Poly/Typed/DenoteKeyedReducibleTypeLevelLift
    — the SINGLE-level reducibility lift backbone (the genFormationPi child-lift engine; toward SN-043/#752)

The genFormationPi arm (`fundamentalTypeFormerAtDenote`) consumes the former reducible at its DECODED level —
a single level.  Its telescope children, however, arrive reducible at THEIR OWN decoded levels, which are
strictly lower (a former's components live in universes strictly below the former's).  Bridging the children up
to the former's level is the genFormationPi integration's central move: the **child-LIFT**.

This file ships the lift's inductive backbone.  Contrast the all-level backbone
`IsReducibleTypeAtAllDenoteLevels.ofReducibleTypeStepDenote` (DenoteKeyedLevelIrrelevance), which produces
reducibility at EVERY level from one step — and whose `piType` arm is genuinely unachievable for threshold-drift
composite-domain Π (the Π fails BELOW threshold, where the domain candidate is the vacuous everything-predicate
and the codomain premise must hold for arbitrary garbage members).  `reducibleTypeLevelLift` produces
reducibility at a SINGLE fixed `highLevel` instead.  Its `piType` arm is therefore tractable: it needs the
domain member-stable only between the two concrete levels (`highLevel` and the `lowerAt` family's level), which
holds above threshold — NOT across all levels.  This is the route correction recorded for #752 crystallised into
reusable infrastructure: the single-level route is tractable exactly where the all-level backbone is not.

`reducibleTypeLevelLift`: from a `ReducibleTypeStepDenote env lowerAt typeCode candidate` step (typically at
`lowerAt = denoteBelowFamily env lowLevel`, i.e. the child reducible at its own decoded level) produce
`IsReducibleTypeAtDenote env highLevel typeCode` (the child reducible at the former's higher decoded level).  The
four non-Π arms discharge constructively:

  * `whnfExpand` — head-expand the lifted reduct (the inductive hypothesis supplies the reduct at `highLevel`);
  * `neutral` — the strong-normalization candidate references neither the lower family nor the level, free at any
    level;
  * `universeCode` — `universeCode_isReducibleAtDenote`, the anti-vacuity that makes universe codes reducible at
    EVERY level;
  * `ofPointwiseIff` — the inductive hypothesis is on the same `typeCode`, level-agnostic motive.

The lone `piType` arm is isolated as the `piArmLift` hypothesis — the genuine member-stability residual, exactly
parallel to how `ofReducibleTypeStepDenote` isolates its own `piArm`.  Discharging `piArmLift` reduces to
`piFormerReducibleAtLevel env highLevel` (DenoteKeyedPiFormerAtLevel) with the codomain inductive hypothesis
bridged across the two levels by domain member-stability — the above-threshold uniform candidate
(`uniformDomainPi_memberStableAboveThreshold`, shipped) supplying that bridge.

## Zero-axiom verification

A single `induction` on the step functor with four constructive arms and one isolated hypothesis; the arms reuse
`universeCode_isReducibleAtDenote` and the `neutral`/`whnfExpand` constructors only.  No `funext`, no recursion
beyond the structural induction.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or
`omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **The single-level reducibility lift backbone.**  A `ReducibleTypeStepDenote env lowerAt` step yields
reducibility at a single fixed `highLevel` — the four non-Π arms (`whnfExpand` / `neutral` / `universeCode` /
`ofPointwiseIff`) discharged, the `piType` arm isolated as `piArmLift`.  The genFormationPi child-lift engine:
instantiated at `lowerAt = denoteBelowFamily env lowLevel`, it lifts a telescope child reducible at its own
decoded level to the former's higher decoded level.  Unlike the all-level
`IsReducibleTypeAtAllDenoteLevels.ofReducibleTypeStepDenote`, the single fixed `highLevel` makes `piArmLift` the
tractable member-stability bridge (above threshold) rather than the unachievable all-level gate. -/
theorem reducibleTypeLevelLift {scope : Nat} {env : Nat → Nat}
    {lowerAt : Nat → RawTerm scope → (RawTerm scope → Prop) → Prop} (highLevel : Nat)
    (piArmLift : ∀ {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
        {domainCandidate : RawTerm scope → Prop}
        (codomainCandidate : RawTerm scope → (RawTerm scope → Prop)),
        ReducibleTypeStepDenote env lowerAt domainCode domainCandidate →
        (∀ argument : RawTerm scope, domainCandidate argument →
          ReducibleTypeStepDenote env lowerAt (RawTerm.subst0 codomainCode argument)
            (codomainCandidate argument)) →
        IsReducibleTypeAtDenote env highLevel domainCode →
        (∀ argument : RawTerm scope, domainCandidate argument →
          IsReducibleTypeAtDenote env highLevel (RawTerm.subst0 codomainCode argument)) →
        IsReducibleTypeAtDenote env highLevel
          (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))))
    {typeCode : RawTerm scope} {candidate : RawTerm scope → Prop}
    (reducible : ReducibleTypeStepDenote env lowerAt typeCode candidate) :
    IsReducibleTypeAtDenote env highLevel typeCode := by
  induction reducible with
  | whnfExpand weakHeadStep _reductReducible reductInductiveHypothesis =>
      obtain ⟨reductCandidate, reductReducibleAtHigh⟩ := reductInductiveHypothesis
      exact ⟨reductCandidate, ReducibleTypeStepDenote.whnfExpand weakHeadStep reductReducibleAtHigh⟩
  | neutral noWeakHeadStep notPiType notUniverse notEmpty =>
      exact ⟨IsStronglyNormalizing,
        ReducibleTypeStepDenote.neutral noWeakHeadStep notPiType notUniverse notEmpty⟩
  | @piType domainCode codomainCode domainCandidate codomainCandidate domainReducible
      codomainReducible domainInductiveHypothesis codomainInductiveHypothesis =>
      exact piArmLift codomainCandidate domainReducible codomainReducible
        domainInductiveHypothesis codomainInductiveHypothesis
  | universeCode levelExpr flag =>
      exact universeCode_isReducibleAtDenote env highLevel levelExpr flag
  | dataEmpty =>
      exact ⟨emptyTaitCandidate, ReducibleTypeStepDenote.dataEmpty⟩
  | ofPointwiseIff _innerReducible _pointwiseIff innerInductiveHypothesis =>
      exact innerInductiveHypothesis

end FX1Poly.Typed
