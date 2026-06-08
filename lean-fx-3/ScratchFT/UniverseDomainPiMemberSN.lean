import FX1Poly.Typed.DenoteKeyedUniverseDomainPi
import FX1Poly.Typed.HasType
import FX1Poly.Core.DependentArrowReducibilityCandidate
import FX1Poly.Core.StratifiedReducibleTypeCandidate
import FX1Poly.Core.StrongNormalizationLeaves

/-! Scratch probe for SN-D7 (#746): denote member-SN for the universe-domain Π fragment.

The type-level half (`universeDomainPi_reducibleAtEveryDenoteLevel`) is shipped.  The missing half is
MEMBER-SN: a reducible member of `Π (X : Type@e). C[X]` is strongly normalizing.  This sidesteps the
cumulativity obstruction by fixing ONE level above `denote e` — no cross-level transport. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- The universe-domain Π's dependent-arrow candidate is a Girard reducibility candidate (at any level
strictly above `denote levelExpr env`). -/
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
reducibility hypotheses (the same the type-level `universeDomainPi_reducibleAtEveryDenoteLevel` consumes),
every reducible member of `Π (X : Type@e). C[X]` at a level above `denote e` is SN. -/
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

#print axioms FX1Poly.Typed.universeDomainPiCandidateIsReducibilityCandidate
#print axioms FX1Poly.Typed.universeDomainPiMemberStronglyNormalizing
