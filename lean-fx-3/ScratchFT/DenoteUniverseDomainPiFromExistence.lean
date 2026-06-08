import FX1Poly.Typed.DenoteKeyedLevelIrrelevance
import FX1Poly.Typed.DenoteKeyedCanonicalMemberCandidate

/-! Scratch: universe-domain Π-formation FROM CODOMAIN EXISTENCE — the impredicative case completing the
from-existence piArm family. `Π (X : Type@e). C[X]` is denote-reducible-at-all-levels given the codomain
reducible-at-all-levels (existence) for every universe member `X` (an SN type reducible at the decoded level
`denote e env`). At each ambient level: above the threshold `denote e env`, the universe candidate's family
equals the relation at `denote e env` (so the universe membership IS the codomain-existence gate); at/below the
threshold the universe candidate is empty (codomain arm vacuous). Choice-free: canonical codomain candidate. -/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe
open StepStar

theorem universeDomainPi_reducibleFromCodomainExistence {scope : Nat} (env : Nat → Nat)
    (levelExpr : LevelExpr) (flag : UniverseFlag) {codomainCode : RawTerm (scope + 1)}
    (codomainExistence : ∀ argument : RawTerm scope,
      (IsStronglyNormalizing argument ∧ IsReducibleTypeAtDenote env (LevelExpr.denote levelExpr env) argument) →
      IsReducibleTypeAtAllDenoteLevels env (RawTerm.subst0 codomainCode argument)) :
    IsReducibleTypeAtAllDenoteLevels env
      (.mkGen .gen_piTyCode ()
        (.childCons (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
          (.childCons codomainCode .childNil))) := by
  intro level
  refine ⟨_, ReducibleTypeStepDenote.piType
    (fun argument => IsReducibleMemberAtDenote env level (RawTerm.subst0 codomainCode argument))
    (ReducibleTypeStepDenote.universeCode levelExpr flag) (fun argument argumentInUniverse => ?_)⟩
  obtain ⟨argumentStronglyNormalizing, candidate, argumentInFamily⟩ := argumentInUniverse
  rcases Nat.lt_or_ge (LevelExpr.denote levelExpr env) level with above | below
  · rw [denoteBelowFamily_eq_reducible env level (LevelExpr.denote levelExpr env) above] at argumentInFamily
    exact (codomainExistence argument
      ⟨argumentStronglyNormalizing, candidate, argumentInFamily⟩ level).reducibleMemberCandidate
  · rw [denoteBelowFamily_eq_empty_of_ge env level (LevelExpr.denote levelExpr env) below] at argumentInFamily
    exact argumentInFamily.elim

end FX1Poly.Typed

#print axioms FX1Poly.Typed.universeDomainPi_reducibleFromCodomainExistence
