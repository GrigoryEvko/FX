import FX1Poly.Typed.Metatheory.Denote.Core.DenoteKeyedUniformReducible
import FX1Poly.Typed.Metatheory.Denote.Pi.DenoteKeyedUniformPiAboveThreshold

/-! # FX1Poly/Typed/DenoteKeyedUniformDependentPiArm
    — the DEPENDENT composite piArm in the uniform motive, sum-threshold form (toward SN-043/#752)

`DenoteKeyedUniformReducible.UniformlyReducibleAboveDenote.nonDependentArrow` discharged the uniform-motive
piArm for a CONSTANT codomain (`domainCode → codomainBase`): the codomain `weaken codomainBase` substitutes to
the level-independent `codomainBase`, so a single codomain threshold suffices and the Π threshold is the sum
`domThreshold + codomainThreshold`.  `DenoteKeyedUniformPiAboveThreshold.uniformDomainPi_hasUniformCandidate
AboveThreshold` handled a DEPENDENT codomain but at ONE shared threshold for both components.

This file ships the genuine join: the DEPENDENT composite piArm in the `UniformlyReducibleAboveDenote` motive
with SEPARATE domain / codomain thresholds combined by the zero-axiom sum technique.  The codomain candidate is
a per-argument function `codomainCandidate : argument ↦ (term ↦ Prop)` reducible above its OWN threshold,
UNIFORMLY in the argument (one codomain threshold, one codomain candidate function for all domain members) —
exactly the shape the constant case generalizes.  The result is packaged as `UniformlyReducibleAboveDenote env
(Π domainCode codomainCode)`, so it plugs directly into the `UniformlyReducibleAboveDenote.\
ofReducibleTypeStepDenote` backbone's `piType` arm.

## What this closes, and what it does NOT

This closes the composite piArm MODULO a UNIFORM-IN-ARGUMENT codomain: given the codomain reducible above one
threshold with one candidate function across all domain members, the dependent Π is uniformly reducible above
the sum threshold, and its members are stable there.  The constant-codomain `nonDependentArrow` and the
shared-threshold `uniformDomainPi_hasUniformCandidateAboveThreshold` are now both instances (constant codomain
candidate / equal thresholds).

It does NOT solve the residual `∀ argument, ∃ threshold` → `∃ threshold, ∀ argument` swap: the
`ofReducibleTypeStepDenote` backbone supplies the codomain inductive hypothesis as
`∀ argument, domainCandidate argument → UniformlyReducibleAboveDenote env (subst0 codomainCode argument)` — a
per-argument EXISTENTIAL threshold and candidate.  Collapsing those into the single uniform-in-argument codomain
this arm consumes is the genuine threshold-swap (`DenoteKeyedUniformReducible`'s documented deep residual): in
general different arguments yield different existential thresholds with no uniform bound.  The structural reason
a uniform bound EXISTS (a former's codomain has a fixed universe level independent of the substituted term, so
its threshold is the codomain's decoded level — SN-003 `ClassifierLevelMeasure`) is not exposed by the bare
`UniformlyReducibleAboveDenote` IH; supplying it is the canonical-threshold motive strengthening (the
ValidTyping-derivation-indexed route).  This arm is the precise reduction TARGET of that strengthening: once the
codomain is uniform-in-argument, the dependent Π closes here with no further work.

## Zero-axiom verification

`dependentPi_reducibleAboveSumThreshold` is one `ReducibleTypeStepDenote.piType` per above-sum-threshold level
(the candidate fixed, level-independent), with the two component thresholds weakened through the sum by
`Nat.le_add_right` / `Nat.le_add_left` + `Nat.lt_of_le_of_lt` (NOT `Nat.max` / `Nat.le_max_*`, which leak
`propext` in this Init-only setting — the exact gotcha the shipped `nonDependentArrow` records).
`dependentPiArm` packages it existentially; `dependentPi_memberStableAboveSumThreshold` applies
`uniformType_memberStableAboveThreshold` to the fixed candidate.  No `induction`, no `funext`.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **The dependent composite Π is reducible with a FIXED candidate above the sum threshold.**  Given the domain
reducible with one candidate above `domainThreshold` and the codomain reducible with one candidate FUNCTION
(uniform in the argument) above `codomainThreshold`, `Π domainCode codomainCode` is reducible at every level
strictly above `domainThreshold + codomainThreshold` with the FIXED `piType` candidate.  The dependent
generalization of the constant-codomain `nonDependentArrow`: the codomain candidate now varies with the domain
argument, but a single codomain threshold still bounds them all, so the sum threshold dominates both components
and the candidate is level-independent above it.  Each above-sum-threshold level weakens to both component
thresholds by `Nat.le_add_right` / `Nat.le_add_left`. -/
theorem dependentPi_reducibleAboveSumThreshold {scope : Nat} (env : Nat → Nat)
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (domainThreshold : Nat) (domainCandidate : RawTerm scope → Prop)
    (domainReducible : ∀ level : Nat, domainThreshold < level →
      ReducibleTypeAtDenote env level domainCode domainCandidate)
    (codomainThreshold : Nat) (codomainCandidate : RawTerm scope → (RawTerm scope → Prop))
    (codomainReducible : ∀ level : Nat, codomainThreshold < level → ∀ argument : RawTerm scope,
      domainCandidate argument →
      ReducibleTypeAtDenote env level (RawTerm.subst0 codomainCode argument)
        (codomainCandidate argument)) :
    ∀ level : Nat, domainThreshold + codomainThreshold < level →
      ReducibleTypeAtDenote env level
        (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil)))
        (fun functionTerm => ∀ argument : RawTerm scope, domainCandidate argument →
          codomainCandidate argument
            (.mkGen .gen_app () (.childCons functionTerm (.childCons argument .childNil)))) :=
  fun level levelAboveSum =>
    ReducibleTypeStepDenote.piType codomainCandidate
      (domainReducible level
        (Nat.lt_of_le_of_lt (Nat.le_add_right domainThreshold codomainThreshold) levelAboveSum))
      (fun argument argumentInDomain =>
        codomainReducible level
          (Nat.lt_of_le_of_lt (Nat.le_add_left codomainThreshold domainThreshold) levelAboveSum)
          argument argumentInDomain)

/-- **The dependent composite piArm in the uniform motive (sum-threshold form).**  From a domain reducible with
one candidate above `domainThreshold` and a codomain reducible with one candidate function (uniform in the
argument) above `codomainThreshold`, the dependent `Π domainCode codomainCode` is `UniformlyReducibleAboveDenote`
— uniformly reducible above the sum threshold with the fixed `piType` candidate.  Packages
`dependentPi_reducibleAboveSumThreshold` into the `∃ threshold candidate` motive, so it slots directly into the
`UniformlyReducibleAboveDenote.ofReducibleTypeStepDenote` backbone's `piType` arm — once the backbone's
per-argument codomain IH is collapsed to the uniform-in-argument codomain this consumes (the threshold-swap, the
sole remaining residual; see the module header).  Strictly generalizes `nonDependentArrow` (constant codomain
candidate) and the shared-threshold `uniformDomainPi_hasUniformCandidateAboveThreshold` (equal thresholds). -/
theorem UniformlyReducibleAboveDenote.dependentPiArm {scope : Nat} (env : Nat → Nat)
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (domainThreshold : Nat) (domainCandidate : RawTerm scope → Prop)
    (domainReducible : ∀ level : Nat, domainThreshold < level →
      ReducibleTypeAtDenote env level domainCode domainCandidate)
    (codomainThreshold : Nat) (codomainCandidate : RawTerm scope → (RawTerm scope → Prop))
    (codomainReducible : ∀ level : Nat, codomainThreshold < level → ∀ argument : RawTerm scope,
      domainCandidate argument →
      ReducibleTypeAtDenote env level (RawTerm.subst0 codomainCode argument)
        (codomainCandidate argument)) :
    UniformlyReducibleAboveDenote env
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))) :=
  ⟨domainThreshold + codomainThreshold,
    (fun functionTerm => ∀ argument : RawTerm scope, domainCandidate argument →
      codomainCandidate argument
        (.mkGen .gen_app () (.childCons functionTerm (.childCons argument .childNil)))),
    dependentPi_reducibleAboveSumThreshold env domainThreshold domainCandidate domainReducible
      codomainThreshold codomainCandidate codomainReducible⟩

/-- **The dependent composite Π is member-stable above the sum threshold.**  Since the dependent Π has one fixed
candidate at every level above `domainThreshold + codomainThreshold`
(`dependentPi_reducibleAboveSumThreshold`), a denote-reducible member at one above-sum-threshold level is a
member at every above-sum-threshold level (`uniformType_memberStableAboveThreshold`).  This is the
member-stability HALF of the joint (reducibility ∧ member-stability) composite step: combined with
`dependentPi_reducibleAboveSumThreshold` it gives the dependent Π's full joint above-threshold property — the
recursive heart the eventual #752 assembly consumes for the composite arm, now over SEPARATE component
thresholds. -/
theorem dependentPi_memberStableAboveSumThreshold {scope : Nat} (env : Nat → Nat)
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (domainThreshold : Nat) (domainCandidate : RawTerm scope → Prop)
    (domainReducible : ∀ level : Nat, domainThreshold < level →
      ReducibleTypeAtDenote env level domainCode domainCandidate)
    (codomainThreshold : Nat) (codomainCandidate : RawTerm scope → (RawTerm scope → Prop))
    (codomainReducible : ∀ level : Nat, codomainThreshold < level → ∀ argument : RawTerm scope,
      domainCandidate argument →
      ReducibleTypeAtDenote env level (RawTerm.subst0 codomainCode argument)
        (codomainCandidate argument))
    {term : RawTerm scope} {sourceLevel : Nat}
    (sourceAbove : domainThreshold + codomainThreshold < sourceLevel)
    (memberAtSource : IsReducibleMemberAtDenote env sourceLevel
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))) term)
    (targetLevel : Nat) (targetAbove : domainThreshold + codomainThreshold < targetLevel) :
    IsReducibleMemberAtDenote env targetLevel
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))) term :=
  uniformType_memberStableAboveThreshold env (domainThreshold + codomainThreshold)
    (dependentPi_reducibleAboveSumThreshold env domainThreshold domainCandidate domainReducible
      codomainThreshold codomainCandidate codomainReducible)
    sourceAbove memberAtSource targetLevel targetAbove

end FX1Poly.Typed
