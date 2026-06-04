import FX1Poly.Typed.BoundedUniverseInversion
import FX1Poly.Typed.DenoteKeyedBoundedGenFormationPiArm
import FX1Poly.Typed.BoundedGrownFundamental

/-! # FX1Poly/Typed/BoundedBindingTypeReducible
    — a universe-typed subject is bound-reducible-as-type under a reducible env (OB-2b, toward OPEN SN-043)

`HasTypeDescPi.subjectReducibleAsTypeUnderEnv`: if `bindingType` is typed at a universe code
`Type@levelExpr` (a grown derivation), and a closing substitution `substitution` is a bound-reducible
environment for the context at `bound` (with a `BoundExceedsPi` budget for the derivation at the SAME `bound`),
then `subst substitution bindingType` is bound-reducible-as-type at `bound`.

This is the TYPE-side per-step lemma the reducible-closing-environment builder (`reducibleEnvOfWfContext`,
OB-3/OB-4) cons-feeds at every context position — the companion to OB-1 (`IsReducibleMemberAtBounded.ofVariable`,
the variable-membership leaf).  Together they discharge the `OpenStronglyNormalizing.lean` residual toward
unconditional open SN-043 (#546).

## The five-step assembly (all shipped pieces + OB-2a)

  1. `HasTypeDescPi.fundamentalAtBoundedSucc` (BFT-12c) on the derivation + budget + env gives a bound-reducible
     MEMBER of `subst substitution (universeCodeCell levelExpr flag)`.
  2. `subst_universeCodeCell` fixes the closed classifier to `Type@levelExpr` (universe codes have no free vars).
  3. `belowBound_of_reducibleUniverse` (OB-2a) recovers the gate `denote levelExpr env < bound` from the member's
     universe candidate.
  4. `universeMemberReducibleAsTypeAtDecodedLevelBounded` (the decode) turns the universe member into a
     bound-reducible TYPE at the DECODED level `denote levelExpr env`.
  5. `isReducibleBounded_cumulative` lifts that from the decoded level up to the uniform `bound`
     (`denote levelExpr env ≤ bound` from the gate).

The budget is taken as a HYPOTHESIS (rather than produced by `existsBound` here) precisely so the global bound
coordination — choosing one `bound` exceeding the main derivation AND every context-entry derivation — lives in
the telescope induction (OB-3/OB-4), where it belongs.

## Zero-axiom verification

A linear composition of shipped zero-axiom results (FT + decode + cumulativity) with the OB-2a inversion and one
`subst_universeCodeCell` rewrite.  Checked to depend on NO axioms.  No `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation
open StepStar

/-- **OB-2b: a universe-typed subject is bound-reducible-as-type under a reducible env.**  Given a grown
derivation typing `bindingType` at `Type@levelExpr`, a `BoundExceedsPi` budget for it at `bound`, and a
bound-reducible closing environment for the context at `bound`, the substituted `bindingType` is
bound-reducible-as-type at `bound`.  FT → `subst_universeCodeCell` → OB-2a gate → decode → cumulativity.  The
type-side leaf the reducible-closing-environment builder (`reducibleEnvOfWfContext`) cons-feeds. -/
theorem HasTypeDescPi.subjectReducibleAsTypeUnderEnv {profile : PolyProfile} {scope targetScope : Nat}
    {env : Nat → Nat} {bound : Nat} {restContext : TypingContext profile scope}
    {bindingType : RawTerm scope} {levelExpr : LevelExpr} {flag : UniverseFlag}
    (descPiDeriv : HasTypeDescPi profile restContext bindingType (universeCodeCell levelExpr flag))
    (budget : BoundExceedsPi env bound descPiDeriv)
    {substitution : RawTermSubst scope (targetScope + 1)}
    (envReducible : ReducibleEnvAtBounded env bound restContext substitution) :
    IsReducibleTypeAtBounded env bound (RawTerm.subst substitution bindingType) := by
  have member := HasTypeDescPi.fundamentalAtBoundedSucc env bound descPiDeriv budget substitution envReducible
  rw [subst_universeCodeCell] at member
  obtain ⟨candidate, candidateReducible, candidateMember⟩ := member
  have belowBound := belowBound_of_reducibleUniverse candidateReducible
  exact isReducibleBounded_cumulative
    (universeMemberReducibleAsTypeAtDecodedLevelBounded
      ⟨candidate, candidateReducible, candidateMember⟩ belowBound)
    (Nat.le_of_lt belowBound)

end FX1Poly.Typed
