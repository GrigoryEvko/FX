import FX1Poly.Typed.DenoteKeyedReducibility
import FX1Poly.Typed.HasType

/-! Scratch probe: PIN the denote-keyed TYPE-reducibility cumulativity obstruction.

At a low level `lowLevel ≤ denote gapLevel env`, the universe code `Type@gapLevel` has an EMPTY member
candidate (the below-family is empty at index ≥ lowLevel). So a Π whose domain is `Type@gapLevel` is
reducible-as-type at `lowLevel` for ANY codomain whatsoever — the codomain obligation is vacuous (no
domain member to feed it). This is the concrete witness that low-level reducibility of a gap-universe-domain
Π carries NO information about its codomain, hence CANNOT be lifted to a higher level (where the domain
gains members and the codomain genuinely matters). The lift `reducible at L1 → reducible at L2` for L1 ≤ L2
is therefore obstructed by exactly such terms — which arise as semantic domain-members (args) during the
genFormationPi non-uniform cumulativity, since reducibility does NOT bound universes. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

theorem gapUniverseDomainPiVacuouslyReducibleAtLowLevel {scope : Nat} (env : Nat → Nat)
    (lowLevel : Nat) (gapLevel : LevelExpr) (flag : UniverseFlag)
    (codomain : RawTerm (scope + 1))
    (gapAtOrAboveLow : lowLevel ≤ LevelExpr.denote gapLevel env) :
    IsReducibleTypeAtDenote env lowLevel
      (piTyCodeCell (universeCodeCell gapLevel flag) codomain) := by
  refine ⟨_, ReducibleTypeStepDenote.piType
    (fun _argument => IsStronglyNormalizing)
    (ReducibleTypeStepDenote.universeCode gapLevel flag)
    (fun argument argumentInDomain => ?_)⟩
  obtain ⟨_strongNormalizing, candidate, member⟩ := argumentInDomain
  rw [denoteBelowFamily_eq_empty_of_ge env lowLevel (LevelExpr.denote gapLevel env) gapAtOrAboveLow] at member
  exact absurd member id

#print axioms gapUniverseDomainPiVacuouslyReducibleAtLowLevel

end FX1Poly.Typed
