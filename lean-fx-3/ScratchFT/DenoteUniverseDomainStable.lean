import FX1Poly.Typed.DenoteKeyedReducibility
import FX1Poly.Typed.ClassifierLevelMeasure

/-! Scratch: the conceptual heart of why the denote-keyed model closes the universe-domain piArm that the
external-Nat-fuel model could NOT.  The fuel frontier note (ReducibleTypeAtAllLevelsInduction.lean §"Why the
piArm is a genuine fixpoint") says: universe membership at fuel k admits every code reducible-at-(k-1), so the
candidates at successive levels genuinely DIFFER, and no finite-fuel induction bridges 0↔1.

In the denote model, `universeMembership_levelIrrelevant` says the `Type@e` candidate is the FIXED
decode-at-`denote e env` set at EVERY ambient level above `denote e env`.  So:

  (1) the universe-domain candidate does NOT drift across levels (the exact negation of the fuel obstruction);
  (2) therefore one fixed candidate witnesses reducibility of `Type@e` simultaneously at all sufficiently-high
      ambient levels — the uniform domain candidate a level-stable piArm needs. -/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **Universe-domain candidate stability (the negation of the fuel obstruction).**  A single fixed candidate —
the decode-at-`denote levelExpr env` set — is the candidate of `Type@levelExpr` at EVERY ambient level strictly
above `denote levelExpr env`.  Where the external-fuel model has genuinely different universe candidates at
successive levels (so no `0↔1` bridge exists), the denote model decodes at the fixed classifier level, so the
candidate is literally level-invariant.  Both witnesses are one `universeMembership_levelIrrelevant`. -/
theorem universeDomainCandidate_levelStable {scope : Nat} (env : Nat → Nat) (level1 level2 : Nat)
    (levelExpr : LevelExpr) (flag : UniverseFlag)
    (above1 : LevelExpr.denote levelExpr env < level1)
    (above2 : LevelExpr.denote levelExpr env < level2) :
    ∃ candidate : RawTerm scope → Prop,
      ReducibleTypeAtDenote env level1
        (.mkGen .gen_universeCode (levelExpr, flag) .childNil) candidate ∧
      ReducibleTypeAtDenote env level2
        (.mkGen .gen_universeCode (levelExpr, flag) .childNil) candidate := by
  refine ⟨fun member => IsStronglyNormalizing member ∧
      IsReducibleTypeAtDenote env (LevelExpr.denote levelExpr env) member, ?_, ?_⟩
  · exact universeMembership_levelIrrelevant env level1 levelExpr flag above1
  · exact universeMembership_levelIrrelevant env level2 levelExpr flag above2

/-- **The denote-keyed universe-domain Π, reducible at every level above `denote levelExpr env`, with a
UNIFORM codomain candidate.**  This is the precise content the external-fuel `piArm` could not reach: the
dependent universe-domain Π `Π (X : Type@e). C[X]` is reducible-as-a-type at every ambient level above the
domain's decoded level `denote levelExpr env`, using ONE codomain-candidate function across all those levels.

Why this works here and not in the fuel model: the domain candidate is the level-stable fixed decode-set
(`universeMembership_levelIrrelevant`), so a SINGLE codomain obligation — the codomain reducible under that
fixed domain membership — discharges the `piType` constructor at every level simultaneously.  No
member-extension across levels is needed (the fuel obstruction), because the domain candidate never drifts. -/
theorem universeDomainPi_reducibleAtAllDenoteLevels {scope : Nat} (env : Nat → Nat)
    (levelExpr : LevelExpr) (flag : UniverseFlag) {codomainCode : RawTerm (scope + 1)}
    (codomainCandidate : RawTerm scope → (RawTerm scope → Prop))
    (codomainReducible : ∀ (level : Nat), LevelExpr.denote levelExpr env < level →
      ∀ argument : RawTerm scope,
        (IsStronglyNormalizing argument ∧
          IsReducibleTypeAtDenote env (LevelExpr.denote levelExpr env) argument) →
          ReducibleTypeAtDenote env level (RawTerm.subst0 codomainCode argument)
            (codomainCandidate argument)) :
    ∀ (level : Nat), LevelExpr.denote levelExpr env < level →
      IsReducibleTypeAtDenote env level
        (.mkGen .gen_piTyCode () (.childCons (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
          (.childCons codomainCode .childNil))) := by
  intro level hlevel
  exact ⟨_, ReducibleTypeStepDenote.piType codomainCandidate
    (universeMembership_levelIrrelevant env level levelExpr flag hlevel)
    (fun argument hArg => codomainReducible level hlevel argument hArg)⟩

end FX1Poly.Typed

#print axioms FX1Poly.Typed.universeDomainCandidate_levelStable
#print axioms FX1Poly.Typed.universeDomainPi_reducibleAtAllDenoteLevels
