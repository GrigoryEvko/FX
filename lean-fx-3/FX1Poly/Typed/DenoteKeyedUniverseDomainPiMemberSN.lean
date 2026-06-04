import FX1Poly.Typed.DenoteKeyedUniverseDomainPi
import FX1Poly.Typed.HasType
import FX1Poly.Core.DependentArrowReducibilityCandidate
import FX1Poly.Core.StratifiedReducibleTypeCandidate
import FX1Poly.Core.StrongNormalizationLeaves

/-! # FX1Poly/Typed/DenoteKeyedUniverseDomainPiMemberSN
    — SN-D7: member strong-normalization for the universe-domain Π fragment over the denote relation

`DenoteKeyedUniverseDomainPi.lean` ships the TYPE-level half of the universe-domain Π `piArm`: the dependent
universe-domain Π `Π (X : Type@e). C[X]` is reducible-as-a-type at every denote level
(`universeDomainPi_reducibleAtEveryDenoteLevel`) and its members are level-stable
(`universeDomainPi_memberStableAcrossDenoteLevels`).  What it does NOT supply is the MEMBER-level
strong-normalization payoff: that a reducible member of that Π is strongly normalizing.  This file adds it —
SN-D7, the "early win that de-risks SN-D5".

## Why this is unblocked where SN-043 is not

The full unconditional SN-043 is obstructed at the cumulativity transport (`DenoteKeyedCumulativityObstruction.
lean`): a gap-universe domain Π is reducible at a low level VACUOUSLY but at a high level with real codomain
data, and no across-level transport manufactures the missing codomain data.  THIS file sidesteps that
entirely: it fixes ONE ambient level strictly above the domain's decoded level `denote levelExpr env` and
never transports across levels.  At that single fixed level the universe candidate of `Type@e` is a genuine
Girard reducibility candidate (the bounded interface legs `denoteBelowFamily_forwardStep` +
`denoteBelowFamily_neutralInclusion_of_lt` both hold because `denote e env < level`), and the dependent-arrow
construction (`isDependentArrowReducibleStepDenote_isReducibilityCandidate`) lifts that to a reducibility
candidate for the whole Π — whose `stronglyNormalizing` field IS member-SN.

The codomain side is taken as a hypothesis, exactly the shape `universeDomainPi_reducibleAtEveryDenoteLevel`
already consumes (the codomain is reducible, and its candidate is itself a reducibility candidate, under each
`Type@e`-member).  The domain inhabitant the dependent-arrow CR1 needs is supplied concretely: a universe code
`Type@0` is a `Type@e`-member at any level (it is strongly normalizing and reducible-as-a-type at every level,
`universeCode_isReducibleAtDenote`).

## What lands here (both zero-axiom)

  * `universeDomainPiCandidateIsReducibilityCandidate` — the dependent-arrow candidate of the universe-domain
    Π is a Girard reducibility candidate at any level strictly above `denote levelExpr env`.  The new core
    content: domain candidate from the bounded universe legs, domain inhabitant `Type@0`, codomain from the
    hypotheses, assembled through the shipped denote dependent-arrow CR1.
  * `universeDomainPiMemberStronglyNormalizing` — SN-D7 proper: a reducible member of `Π (X : Type@e). C[X]`
    (at a level above `denote e`) is strongly normalizing.  The member's candidate agrees with the
    dependent-arrow candidate by `ReducibleTypeAtDenote.deterministic`, and the latter's `stronglyNormalizing`
    field discharges SN.

This isolates the residual SN-043 obstruction to ESTABLISHING the codomain reducibility uniformly across
levels (the cumulativity transport), demonstrating that the universe-domain Π fragment's member-SN follows
cleanly once that single ingredient is in hand at one level — no member of the fragment is the obstacle.

## Zero-axiom verification

Both theorems compose shipped zero-axiom machinery: `ReducibleTypeStep.universeCandidateIsReducibilityCandidate`
(the universe CR over the bounded legs), `isDependentArrowReducibleStepDenote_isReducibilityCandidate` (the
denote dependent-arrow CR1), `ReducibleTypeStepDenote.piType` / `.universeCode` (the formers),
`ReducibleTypeAtDenote.deterministic` (candidate alignment), `denoteBelowFamily_eq_reducible` (coherence), and
`universeCode_isStronglyNormalizing`.  No `induction`, no `funext`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **The universe-domain Π's dependent-arrow candidate is a Girard reducibility candidate** (at any ambient
level strictly above the domain's decoded level `denote levelExpr env`).  The domain candidate is the denote
universe candidate of `Type@levelExpr`, itself a reducibility candidate via
`ReducibleTypeStep.universeCandidateIsReducibilityCandidate` over the bounded `denoteBelowFamily` legs (the
`< level` bound holds by `levelAbove`).  The domain inhabitant the dependent-arrow CR1 requires is supplied
concretely by the universe code `Type@0` (strongly normalizing + reducible-as-a-type at the decoded level via
coherence + `.universeCode`).  The codomain side is the hypothesis pair the type-level
`universeDomainPi_reducibleAtEveryDenoteLevel` already consumes.  Sidesteps the cumulativity obstruction by
fixing one level — no across-level transport. -/
theorem universeDomainPiCandidateIsReducibilityCandidate {scope : Nat} (env : Nat → Nat) (level : Nat)
    (levelExpr : LevelExpr) {codomainCode : RawTerm (scope + 1)}
    (codomainCandidate : RawTerm scope → (RawTerm scope → Prop))
    (levelAbove : LevelExpr.denote levelExpr env < level)
    (codomainCandidateHood : ∀ argument : RawTerm scope,
      universeDenotePredicate env (denoteBelowFamily env level) levelExpr argument →
        IsReducibilityCandidate (codomainCandidate argument))
    (codomainReducible : ∀ argument : RawTerm scope,
      universeDenotePredicate env (denoteBelowFamily env level) levelExpr argument →
        ReducibleTypeAtDenote env level (RawTerm.subst0 codomainCode argument)
          (codomainCandidate argument)) :
    IsReducibilityCandidate
      (IsDependentArrowReducible (universeDenotePredicate env (denoteBelowFamily env level) levelExpr)
        codomainCandidate) := by
  have domainCandidate :
      IsReducibilityCandidate (universeDenotePredicate env (denoteBelowFamily env level) levelExpr) :=
    ReducibleTypeStep.universeCandidateIsReducibilityCandidate
      (scope := scope)
      (lowerReducible := denoteBelowFamily env level (LevelExpr.denote levelExpr env))
      (fun member step =>
        denoteBelowFamily_forwardStep env level (LevelExpr.denote levelExpr env) member step)
      (fun neutral reductsReducible =>
        denoteBelowFamily_neutralInclusion_of_lt env level (LevelExpr.denote levelExpr env) levelAbove
          neutral reductsReducible)
  have witnessReducible :
      universeDenotePredicate env (denoteBelowFamily env level) levelExpr
        (universeCodeCell (scope := scope) LevelExpr.lzero UniverseFlag.standard) := by
    refine ⟨universeCode_isStronglyNormalizing (LevelExpr.lzero, UniverseFlag.standard), ?_⟩
    rw [denoteBelowFamily_eq_reducible env level (LevelExpr.denote levelExpr env) levelAbove]
    exact ⟨_, ReducibleTypeStepDenote.universeCode LevelExpr.lzero UniverseFlag.standard⟩
  exact isDependentArrowReducibleStepDenote_isReducibilityCandidate
    domainCandidate codomainCandidateHood codomainReducible _ witnessReducible

/-- **SN-D7: a reducible member of the universe-domain Π is strongly normalizing.**  Given the codomain
reducibility hypotheses (the same the type-level `universeDomainPi_reducibleAtEveryDenoteLevel` consumes), every
reducible member of `Π (X : Type@e). C[X]` at an ambient level above `denote e` is strongly normalizing.  The
member's reducible-type witness has a candidate that agrees pointwise with the dependent-arrow candidate by
`ReducibleTypeAtDenote.deterministic`, so the member lies in the dependent-arrow candidate, whose
`stronglyNormalizing` field (from `universeDomainPiCandidateIsReducibilityCandidate`) discharges SN.  The
member-level half of the universe-domain Π `piArm`, complementing the shipped type-level half — and the early
win that de-risks the full SN-D5 induction. -/
theorem universeDomainPiMemberStronglyNormalizing {scope : Nat} (env : Nat → Nat) (level : Nat)
    (levelExpr : LevelExpr) (flag : UniverseFlag) {codomainCode : RawTerm (scope + 1)}
    (codomainCandidate : RawTerm scope → (RawTerm scope → Prop))
    (levelAbove : LevelExpr.denote levelExpr env < level)
    (codomainCandidateHood : ∀ argument : RawTerm scope,
      universeDenotePredicate env (denoteBelowFamily env level) levelExpr argument →
        IsReducibilityCandidate (codomainCandidate argument))
    (codomainReducible : ∀ argument : RawTerm scope,
      universeDenotePredicate env (denoteBelowFamily env level) levelExpr argument →
        ReducibleTypeAtDenote env level (RawTerm.subst0 codomainCode argument)
          (codomainCandidate argument))
    {functionTerm : RawTerm scope}
    (member : IsReducibleMemberAtDenote env level
      (piTyCodeCell (universeCodeCell levelExpr flag) codomainCode) functionTerm) :
    IsStronglyNormalizing functionTerm := by
  obtain ⟨candidate, typeReducible, memberInCandidate⟩ := member
  have arrowReducible :
      ReducibleTypeAtDenote env level
        (piTyCodeCell (universeCodeCell levelExpr flag) codomainCode)
        (IsDependentArrowReducible (universeDenotePredicate env (denoteBelowFamily env level) levelExpr)
          codomainCandidate) :=
    ReducibleTypeStepDenote.piType codomainCandidate
      (ReducibleTypeStepDenote.universeCode levelExpr flag)
      (fun argument argumentInDomain => codomainReducible argument argumentInDomain)
  have candidatesAgree := ReducibleTypeAtDenote.deterministic typeReducible arrowReducible
  exact (universeDomainPiCandidateIsReducibilityCandidate env level levelExpr codomainCandidate
    levelAbove codomainCandidateHood codomainReducible).stronglyNormalizing
    ((candidatesAgree functionTerm).mp memberInCandidate)

end FX1Poly.Typed
