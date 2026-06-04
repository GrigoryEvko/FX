import FX1Poly.Typed.DenoteKeyedBoundedGenFormationPiArm
import FX1Poly.Typed.FormerOutputLevelBounds

/-! # FX1Poly/Typed/BoundedDomainInhabitant
    — the last two genFormationPi recursor-arm prerequisites: the output `belowBound` and the domain inhabitant

The bounded `genFormationPi` recursor arm assembles `fundamentalGenFormationPiAtBoundedSucc` from the telescope
projection (`twoChildMembers`).  Two small facts remain before the assembly:

  * `levelMax_lt` — the former's decoded output level `levelMax (denote domainLevel env) (denote codomainLevel
    env)` is below the bound when BOTH child levels are (each `belowBound` from gate-extraction).  This is the
    `belowBound` premise of `fundamentalGenFormationPiAtBoundedSucc` at the output level.
  * `variableZeroMemberOfBoundedUniverseMember` — to discharge `codomainSN` via
    `codomainOpenStronglyNormalizing_ofBoundedFilledMember`, the codomain telescope must be instantiated at SOME
    bound-reducible argument of the domain at `argLevel`.  The variable-0 neutral cell is always available: the
    domain (a universe member, decoded to a reducible TYPE at its own level by
    `universeMemberReducibleAsTypeAtDecodedLevelBounded`, then lifted to `argLevel` by free bounded cumulativity
    `isReducibleBounded_cumulative`) is a reducibility candidate, and any candidate contains the variable-0 cell
    (`IsReducibilityCandidate.containsVariable` — the CR3 neutral leaf, the same fresh-variable mining the denote
    `piFormerOfChildMemberships` performs).

## Zero-axiom verification

`levelMax_lt` matches on the (necessarily successor) bound and routes through `LevelExpr.levelMax_le`
(`Nat.lt_succ_iff` / `Nat.lt_succ_of_le`); `variableZeroMemberOfBoundedUniverseMember` is the decode + cumulative
lift + `containsVariable` projection, packaged as the member existential.  No `funext`.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega` (checked: depends on no axioms).
Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation
open StepStar

/-- **The former output level is below the bound.**  When both child levels are below `bound`, their `levelMax`
(the Π/Σ decoded output level) is too — the `belowBound` premise of `fundamentalGenFormationPiAtBoundedSucc` at
the output universe. -/
theorem levelMax_lt {valueA valueB bound : Nat} (ha : valueA < bound) (hb : valueB < bound) :
    LevelExpr.levelMax valueA valueB < bound := by
  match bound with
  | 0 => exact absurd ha (Nat.not_lt_zero _)
  | bound + 1 =>
      exact Nat.lt_succ_of_le
        (LevelExpr.levelMax_le valueA valueB bound (Nat.lt_succ_iff.mp ha) (Nat.lt_succ_iff.mp hb))

/-- **The variable-0 neutral inhabits the bounded domain candidate at the output level.**  From the domain's
universe membership at `bound` (decoded level below `bound`, and at or below the output `argLevel`), the variable-0
cell `gen_var ⟨0, _⟩` is a bound-reducible member of the domain at `argLevel`: decode the universe member to a
reducible TYPE at its own decoded level, lift to `argLevel` by free bounded cumulativity, then the candidate
contains the variable cell (`IsReducibilityCandidate.containsVariable`).  Supplies the domain argument the
`genFormationPi` arm instantiates the codomain telescope at to discharge `codomainSN`. -/
theorem variableZeroMemberOfBoundedUniverseMember {scope : Nat} {env : Nat → Nat} {bound argLevel : Nat}
    {domainLevel : LevelExpr} {flag : UniverseFlag} {domainTerm : RawTerm (scope + 1)}
    (domainMember : IsReducibleMemberAtBounded env bound (universeCodeCell domainLevel flag) domainTerm)
    (decodedBelowBound : LevelExpr.denote domainLevel env < bound)
    (decodedBelowArgLevel : LevelExpr.denote domainLevel env ≤ argLevel) :
    IsReducibleMemberAtBounded env argLevel domainTerm
      (.mkGen .gen_var ⟨0, Nat.succ_pos scope⟩ .childNil) := by
  have domainAtDecoded :=
    universeMemberReducibleAsTypeAtDecodedLevelBounded domainMember decodedBelowBound
  have domainAtArgLevel := isReducibleBounded_cumulative domainAtDecoded decodedBelowArgLevel
  obtain ⟨candidate, candidateReducible⟩ := domainAtArgLevel
  exact ⟨candidate, candidateReducible,
    candidateReducible.isReducibilityCandidate.containsVariable ⟨0, Nat.succ_pos scope⟩⟩

end FX1Poly.Typed
