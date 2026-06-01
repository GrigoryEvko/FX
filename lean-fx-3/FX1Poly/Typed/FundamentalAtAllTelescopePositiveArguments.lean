import FX1Poly.Typed.FundamentalAtAllTelescope
import FX1Poly.Typed.FundamentalAtAllPositiveArguments

/-! # FX1Poly/Typed/FundamentalAtAllTelescopePositiveArguments
    — telescope-cons assembly from all-positive fresh arguments

The formation-fragment fundamental theorem's premise telescope crosses a binder: after the head child is
read, the tail is checked under a substitution extended by an arbitrary reducible argument for that head.
An ordinary all-level recursive premise for the tail needs the extended environment
`ReducibleEnvAtAllLevels.cons`, which in turn needs the fresh argument at every positive member level.

This file factors the exact bridge:

* first, a raw premise saying each one-level head member extends to all-positive head membership; and
* second, the candidate-companion form that derives that extension from an all-level head candidate.

No theorem here manufactures that companion for universe domains.  Universe domains remain the hard Tarski
case: membership in `Type@u` at one fuel decodes only one lower reducible-type level.  These lemmas are the
non-recursive telescope wiring used once a proof-relevant/Kripke type companion supplies the argument
strengthening.

## Zero-axiom verification

Both proofs are direct compositions of `fundamentalTelescopeConsAtAll`,
`HasAllPositiveReducibleCandidateUnderAllLevelSubstitution.memberExtendsToAllPositive`, and the supplied
tail premise.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Telescope cons from all-positive argument strengthening.**  The head child is read from its all-level
fundamental result as usual.  For the tail, any one-level head member is first strengthened to all-positive
head membership, then the caller's all-positive tail premise runs under that stronger argument. -/
theorem fundamentalTelescopeConsAtAllFromAllPositiveArgumentPremises {profile : PolyProfile}
    {baseScope targetScope currentDepth count : Nat}
    {context : TypingContext profile (baseScope + currentDepth)}
    {head : RawTerm (baseScope + currentDepth)}
    {restLevels : List LevelExpr} {flag : UniverseFlag}
    {rest : RawTermChildren (consecutiveShifts (currentDepth + 1) count) baseScope}
    {headLevel : LevelExpr}
    {substitution : RawTermSubst (baseScope + currentDepth) (targetScope + 1)}
    (reducibleEnv : ReducibleEnvAtAllLevels context substitution)
    (headFundamental : FundamentalConclusionAtAll context head (universeCodeCell headLevel flag))
    (headMemberExtendsToAllPositive :
      ∀ {memberLevel : Nat} (argument : RawTerm (targetScope + 1)),
        IsReducibleMemberAt memberLevel (RawTerm.subst substitution head) argument →
          IsReducibleMemberAtAllPositiveLevels (RawTerm.subst substitution head) argument)
    (tailReducibleAtAllPositiveArgument :
      ∀ (argument : RawTerm (targetScope + 1)),
        IsReducibleMemberAtAllPositiveLevels (RawTerm.subst substitution head) argument →
          TelescopeReducible flag (currentDepth + 1) count
            (RawTermSubst.cons argument substitution) restLevels rest) :
    TelescopeReducible flag currentDepth (count + 1) substitution (headLevel :: restLevels)
      (.childCons head rest) :=
  fundamentalTelescopeConsAtAll reducibleEnv headFundamental
    (fun argument argumentMember =>
      tailReducibleAtAllPositiveArgument argument
        (headMemberExtendsToAllPositive argument argumentMember))

/-- **Telescope cons from an all-level head-candidate companion.**  The all-level candidate companion says
the substituted head denotes `IsReducibleMemberAtAllPositiveLevels` at every fuel.  Candidate determinism
therefore upgrades any one-level head member to all-positive membership, which is exactly the premise needed
by `fundamentalTelescopeConsAtAllFromAllPositiveArgumentPremises`. -/
theorem fundamentalTelescopeConsAtAllFromAllLevelHeadCandidateCompanion {profile : PolyProfile}
    {baseScope targetScope currentDepth count : Nat}
    {context : TypingContext profile (baseScope + currentDepth)}
    {head : RawTerm (baseScope + currentDepth)}
    {restLevels : List LevelExpr} {flag : UniverseFlag}
    {rest : RawTermChildren (consecutiveShifts (currentDepth + 1) count) baseScope}
    {headLevel : LevelExpr}
    {substitution : RawTermSubst (baseScope + currentDepth) (targetScope + 1)}
    (reducibleEnv : ReducibleEnvAtAllLevels context substitution)
    (headFundamental : FundamentalConclusionAtAll context head (universeCodeCell headLevel flag))
    (headHasAllPositiveCandidate :
      HasAllPositiveReducibleCandidateUnderAllLevelSubstitution context head)
    (tailReducibleAtAllPositiveArgument :
      ∀ (argument : RawTerm (targetScope + 1)),
        IsReducibleMemberAtAllPositiveLevels (RawTerm.subst substitution head) argument →
          TelescopeReducible flag (currentDepth + 1) count
            (RawTermSubst.cons argument substitution) restLevels rest) :
    TelescopeReducible flag currentDepth (count + 1) substitution (headLevel :: restLevels)
      (.childCons head rest) :=
  fundamentalTelescopeConsAtAllFromAllPositiveArgumentPremises reducibleEnv headFundamental
    (fun {_memberLevel} argument argumentMember => by
      obtain ⟨headCandidate, headReducible, argumentInHeadCandidate⟩ := argumentMember
      exact HasAllPositiveReducibleCandidateAt.memberExtendsToAllPositive
        (headHasAllPositiveCandidate substitution reducibleEnv _memberLevel)
        headReducible argumentInHeadCandidate)
    tailReducibleAtAllPositiveArgument

end FX1Poly.Typed
