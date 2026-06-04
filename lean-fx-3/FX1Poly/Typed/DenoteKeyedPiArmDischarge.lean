import FX1Poly.Typed.DenoteKeyedPiFormerAtLevel
import FX1Poly.Typed.DenoteKeyedReducibleTypeLevelLift
import FX1Poly.Typed.DenoteKeyedUniformPiAboveThreshold

/-! # FX1Poly/Typed/DenoteKeyedPiArmDischarge
    — discharging `reducibleTypeLevelLift`'s `piArmLift` hypothesis, case by case (toward SN-043/#752)

`reducibleTypeLevelLift` (DenoteKeyedReducibleTypeLevelLift) lifts a reducibility derivation from `lowerAt` to a
single fixed `highLevel`, with the `piType` arm isolated as the `piArmLift` hypothesis.  To make the child-lift
unconditional, `piArmLift` must be discharged for every domain shape the induction can encounter: neutral
(type-variable / stuck), universe code, and threshold-drift composite.  This file accrues those discharges.  The
split is NOT free-vs-deep as one might first guess — it is FREE (neutral only) vs ABOVE-THRESHOLD (universe AND
composite).  A neutral type's strong-normalization candidate is level-independent, so the neutral case lifts
unconditionally.  A universe code, by contrast, is a reducible TYPE at every level but its MEMBER candidate goes
VACUOUS below its decoded level (`IsStronglyNormalizing ∧ False`), so the universe case — exactly like the
composite — needs the threshold conditions.  In the genFormationPi context those hold by construction (a former's
components live strictly below its own decoded level).

`neutralDomainPiArmLift`: the NEUTRAL-domain case.  When the Π's domain is neutral (weak-head-normal, non-Π,
non-universe — a context type variable or a stuck application), the lift's `piType` conclusion holds:

  * the domain is reducible at `highLevel` for FREE via the `neutral` constructor (its strong-normalization
    candidate references neither `lowerAt` nor the level);
  * the member-stability bridge — needed because the codomain hypothesis is keyed on the lower `domainCandidate`
    while `piFormerReducibleAtLevel`'s codomain premise is keyed on the canonical highLevel member-predicate —
    pivots through `candidateIffStronglyNormalizing` at BOTH levels.  For a neutral type EVERY candidate is
    pointwise-iff `IsStronglyNormalizing` (`ReducibleTypeStepDenote.candidateIffStronglyNormalizing`), so a
    member at `highLevel` is `IsStronglyNormalizing`, which the lower `domainReducible`'s own
    `candidateIffStronglyNormalizing` converts back into `domainCandidate` membership.  `IsStronglyNormalizing`
    is the common, fully level-irrelevant pivot.

## Zero-axiom verification

`piFormerReducibleAtLevel` applied to the `neutral` constructor and a codomain premise whose only nontrivial step
is two `candidateIffStronglyNormalizing` rewrites (`.mp` then `.mpr`) through the SN pivot.  No `induction`, no
`funext`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **The neutral-domain discharge of `reducibleTypeLevelLift`'s `piArmLift`.**  For a neutral domain, the Π
former is reducible at `highLevel`: the domain is reducible there for free (the `neutral` constructor), and the
member-stability bridge from the canonical highLevel member-predicate back to the lower `domainCandidate` pivots
through `candidateIffStronglyNormalizing` at both levels (member → `IsStronglyNormalizing` → `domainCandidate`).
The first of the three `piArmLift` domain-shape cases (neutral / universe / composite); combined with the
universe and composite cases it makes the single-level child-lift unconditional on a neutral spine. -/
theorem neutralDomainPiArmLift {scope : Nat} {env : Nat → Nat} (highLevel : Nat)
    {lowerAt : Nat → RawTerm scope → (RawTerm scope → Prop) → Prop}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainCandidate : RawTerm scope → Prop}
    (noWeakHeadStep : ∀ reduct : RawTerm scope, ¬ WeakHeadStep domainCode reduct)
    (notPiType : domainCode.rootGenerator ≠ Generator.gen_piTyCode)
    (notUniverse : domainCode.rootGenerator ≠ Generator.gen_universeCode)
    (domainReducible : ReducibleTypeStepDenote env lowerAt domainCode domainCandidate)
    (codomainLiftedPerMember : ∀ argument : RawTerm scope, domainCandidate argument →
      IsReducibleTypeAtDenote env highLevel (RawTerm.subst0 codomainCode argument)) :
    IsReducibleTypeAtDenote env highLevel
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))) :=
  piFormerReducibleAtLevel env highLevel
    ⟨IsStronglyNormalizing, ReducibleTypeStepDenote.neutral noWeakHeadStep notPiType notUniverse⟩
    (fun argument argumentMember =>
      let ⟨_memberCandidate, memberCandidateReducible, argumentInMemberCandidate⟩ := argumentMember
      have argumentStronglyNormalizing : IsStronglyNormalizing argument :=
        (memberCandidateReducible.candidateIffStronglyNormalizing
          noWeakHeadStep notPiType notUniverse argument).mp argumentInMemberCandidate
      have argumentInDomainCandidate : domainCandidate argument :=
        (domainReducible.candidateIffStronglyNormalizing
          noWeakHeadStep notPiType notUniverse argument).mpr argumentStronglyNormalizing
      codomainLiftedPerMember argument argumentInDomainCandidate)

/-- **The universe-domain (above-threshold) discharge of `reducibleTypeLevelLift`'s `piArmLift`.**  For a
universe-code domain `Type@levelExpr`, the Π former is reducible at `highLevel` — PROVIDED the universe's decoded
level sits strictly below BOTH the lower family level and `highLevel` (`domainBelowLow`, `domainBelowHigh`).  The
domain is reducible at `highLevel` for free (`universeDomainPiFormerReducibleAtLevel` via
`universeCode_isReducibleAtDenote`); the member-stability bridge pins both candidates to the denote-keyed universe
predicate (`candidateIffUniverse` at each level), then collapses BOTH below-family universe predicates to the
single fixed decode-at-`denote levelExpr env` set via coherence (`denoteBelowFamily_eq_reducible`, applicable
exactly because of the two threshold conditions).

The threshold conditions are ESSENTIAL, not bureaucratic: below its decoded level a universe code's member
candidate is `IsStronglyNormalizing ∧ False` — the EMPTY predicate (the `denoteBelowFamily` index runs off the
end).  So `Type@e` is a reducible TYPE at every level (anti-vacuity, `universeCode_isReducibleAtDenote`) but its
MEMBER candidate goes vacuous below threshold — the threshold-drift obstruction in its sharpest form.  The
universe-domain case is therefore the ABOVE-THRESHOLD case, NOT unconditionally free (contrast the neutral case,
whose SN candidate never goes vacuous).  In the genFormationPi context the conditions hold by construction: a
former's universe-code components live strictly below the former's own decoded level.  The second of the three
`piArmLift` shape cases (neutral / universe / composite). -/
theorem universeDomainPiArmLift {scope : Nat} {env : Nat → Nat} (lowLevel highLevel : Nat)
    (levelExpr : LevelExpr) (flag : UniverseFlag) {codomainCode : RawTerm (scope + 1)}
    {domainCandidate : RawTerm scope → Prop}
    (domainBelowLow : LevelExpr.denote levelExpr env < lowLevel)
    (domainBelowHigh : LevelExpr.denote levelExpr env < highLevel)
    (domainStep : ReducibleTypeStepDenote env (denoteBelowFamily env lowLevel)
      (.mkGen .gen_universeCode (levelExpr, flag) .childNil) domainCandidate)
    (codomainLiftedPerMember : ∀ argument : RawTerm scope, domainCandidate argument →
      IsReducibleTypeAtDenote env highLevel (RawTerm.subst0 codomainCode argument)) :
    IsReducibleTypeAtDenote env highLevel
      (.mkGen .gen_piTyCode ()
        (.childCons (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
          (.childCons codomainCode .childNil))) := by
  have lowCollapse : denoteBelowFamily (scope := scope) env lowLevel (LevelExpr.denote levelExpr env)
      = ReducibleTypeAtDenote env (LevelExpr.denote levelExpr env) :=
    denoteBelowFamily_eq_reducible (scope := scope) env lowLevel (LevelExpr.denote levelExpr env) domainBelowLow
  have highCollapse : denoteBelowFamily (scope := scope) env highLevel (LevelExpr.denote levelExpr env)
      = ReducibleTypeAtDenote env (LevelExpr.denote levelExpr env) :=
    denoteBelowFamily_eq_reducible (scope := scope) env highLevel (LevelExpr.denote levelExpr env) domainBelowHigh
  have predicateBridge : ∀ argument : RawTerm scope,
      universeDenotePredicate env (denoteBelowFamily env highLevel) levelExpr argument →
      universeDenotePredicate env (denoteBelowFamily env lowLevel) levelExpr argument := by
    intro argument memberHigh
    obtain ⟨stronglyNormalizing, candidateAtDenote, reducibleAtDenote⟩ := memberHigh
    refine ⟨stronglyNormalizing, candidateAtDenote, ?_⟩
    rw [lowCollapse]
    rw [highCollapse] at reducibleAtDenote
    exact reducibleAtDenote
  exact universeDomainPiFormerReducibleAtLevel env highLevel levelExpr flag
    (fun argument argumentMember => by
      obtain ⟨memberCandidate, memberCandidateReducible, argumentInMemberCandidate⟩ := argumentMember
      have argumentInHighPredicate :
          universeDenotePredicate env (denoteBelowFamily env highLevel) levelExpr argument :=
        (memberCandidateReducible.candidateIffUniverse rfl argument).mp argumentInMemberCandidate
      have argumentInDomainCandidate : domainCandidate argument :=
        (domainStep.candidateIffUniverse rfl argument).mpr
          (predicateBridge argument argumentInHighPredicate)
      exact codomainLiftedPerMember argument argumentInDomainCandidate)

/-- **The GENERAL above-threshold discharge — the shape-independent engine.**  For ANY domain reducible with one
fixed candidate `domainCandidate` at every level strictly above `threshold`, the Π former is reducible at
`highLevel` (itself above the threshold).  The member-stability bridge — converting a canonical highLevel member
back to `domainCandidate` membership — is just `ReducibleTypeAtDenote.deterministic` AT THE SINGLE `highLevel`:
both the member's candidate and the uniform candidate live at `highLevel`, so determinism aligns them with NO
cross-level transport.  That collapse of the cross-level bridge to one-level determinism is the decisive
simplification: the lift's `piArmLift` already supplies the domain reducible at `highLevel`, so the only residual
is pinning the member's candidate to `domainCandidate`, which determinism does at `highLevel` alone.

This subsumes the universe and neutral special cases (each is "establish the shape's uniformity, apply this") and
is exactly the form the composite case needs.  The three `piArmLift` shape discharges are now uniformly: NEUTRAL
(uniform at every level with the SN candidate), UNIVERSE (uniform above its decoded level), COMPOSITE (uniform
above its components' threshold). -/
theorem aboveThresholdDomainPiArmLift {scope : Nat} {env : Nat → Nat} (threshold highLevel : Nat)
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainCandidate : RawTerm scope → Prop}
    (highAbove : threshold < highLevel)
    (domainUniform : ∀ level : Nat, threshold < level →
      ReducibleTypeAtDenote env level domainCode domainCandidate)
    (codomainLiftedPerMember : ∀ argument : RawTerm scope, domainCandidate argument →
      IsReducibleTypeAtDenote env highLevel (RawTerm.subst0 codomainCode argument)) :
    IsReducibleTypeAtDenote env highLevel
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))) :=
  piFormerReducibleAtLevel env highLevel
    ⟨domainCandidate, domainUniform highLevel highAbove⟩
    (fun argument argumentMember => by
      obtain ⟨memberCandidate, memberCandidateReducible, argumentInMemberCandidate⟩ := argumentMember
      have argumentInDomainCandidate : domainCandidate argument :=
        (ReducibleTypeAtDenote.deterministic memberCandidateReducible
          (domainUniform highLevel highAbove) argument).mp argumentInMemberCandidate
      exact codomainLiftedPerMember argument argumentInDomainCandidate)

/-- **The composite-domain (above-threshold) discharge — case 3/3.**  When the Π's domain is itself a composite
`Π innerDomain innerCodomain` whose components are uniform above the threshold, the inner Π has a fixed `piType`
candidate above the threshold (`uniformDomainPi_hasUniformCandidateAboveThreshold`), so it feeds the general
`aboveThresholdDomainPiArmLift` engine directly.  This is the lone deep #672 / SN-001 obstruction — a composite
domain like `Type@0 → Type@0` whose candidate drifts below threshold — now closed ABOVE the threshold, which is
all the genFormationPi arm needs (a former's decoded level sits above its components' thresholds).  The third and
last of the three `piArmLift` domain-shape cases; with neutral and universe it makes the single-level child-lift's
`piArmLift` dischargeable on every domain shape (each above its own threshold). -/
theorem compositeDomainPiArmLift {scope : Nat} {env : Nat → Nat} (threshold highLevel : Nat)
    {innerDomain : RawTerm scope} {innerCodomain : RawTerm (scope + 1)} {codomainCode : RawTerm (scope + 1)}
    (innerDomainCandidate : RawTerm scope → Prop)
    (innerCodomainCandidate : RawTerm scope → (RawTerm scope → Prop))
    (highAbove : threshold < highLevel)
    (innerDomainUniform : ∀ level : Nat, threshold < level →
      ReducibleTypeAtDenote env level innerDomain innerDomainCandidate)
    (innerCodomainUniform : ∀ level : Nat, threshold < level → ∀ argument : RawTerm scope,
      innerDomainCandidate argument →
      ReducibleTypeAtDenote env level (RawTerm.subst0 innerCodomain argument)
        (innerCodomainCandidate argument))
    (codomainLiftedPerMember : ∀ functionTerm : RawTerm scope,
      (∀ argument : RawTerm scope, innerDomainCandidate argument →
        innerCodomainCandidate argument
          (.mkGen .gen_app () (.childCons functionTerm (.childCons argument .childNil)))) →
      IsReducibleTypeAtDenote env highLevel (RawTerm.subst0 codomainCode functionTerm)) :
    IsReducibleTypeAtDenote env highLevel
      (.mkGen .gen_piTyCode ()
        (.childCons (.mkGen .gen_piTyCode () (.childCons innerDomain (.childCons innerCodomain .childNil)))
          (.childCons codomainCode .childNil))) :=
  aboveThresholdDomainPiArmLift threshold highLevel highAbove
    (uniformDomainPi_hasUniformCandidateAboveThreshold env threshold innerDomainCandidate innerDomainUniform
      innerCodomainCandidate innerCodomainUniform)
    codomainLiftedPerMember

end FX1Poly.Typed
