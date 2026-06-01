import FX1Poly.Typed.FundamentalAtAllTelescopePositiveArguments
import FX1Poly.Typed.FundamentalWithTypeValueCandidates

/-! # FX1Poly/Typed/FundamentalAtAllPositiveMemberExtension
    -- binder and telescope bridges from positive-member extension

The all-level dependent fundamental theorem cannot obtain an all-positive binder argument from a bare
`FundamentalConclusionAtAll` result alone.  A type in a universe gives strong normalization plus all-level
type reducibility; turning a one-level member of that type into a member at every positive fuel is exactly
the positive-member-extension/type-value-completion principle.

This file commits to that discharge route explicitly.  It packages the reusable bridges that binder and
telescope arms consume once `HasPositiveMemberExtensionForStronglyNormalizingAllLevelTypes` is available:

* type-in-universe fundamentals yield positive-fuel all-positive candidates;
* positive-fuel members of such types extend to all positive fuels;
* all-level environments can be extended from one positive member by first strengthening it; and
* telescope cons can split the fuel-zero branch from the positive branch, avoiding the unsound claim that
  positive-member extension says anything at fuel zero.

## Zero-axiom verification

The proofs are projections through the already-gated Tarski decode/extraction theorem and the equivalence
between positive-member extension and type-value candidates.  The telescope bridge is a single `Nat` split
on the supplied member level.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Positive candidates from a type-in-universe fundamental result.**  Under positive-member extension, a
fundamental theorem result for `typeCode : Type@levelExpr` exposes `typeCode`'s all-positive member
predicate as the reducible candidate at every positive fuel after any closing all-level substitution. -/
theorem FundamentalConclusionAtAll.typeInUniverse_hasPositiveCandidateOfPositiveMemberExtension
    {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    {typeCode : RawTerm scope} {levelExpr : LevelExpr} {flag : UniverseFlag}
    (positiveMemberExtension :
      HasPositiveMemberExtensionForStronglyNormalizingAllLevelTypes)
    (typeFundamental :
      FundamentalConclusionAtAll context typeCode (universeCodeCell levelExpr flag)) :
    ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
      (_env : ReducibleEnvAtAllLevels context substitution) (predLevel : Nat),
      HasAllPositiveReducibleCandidateAt (predLevel + 1)
        (RawTerm.subst substitution typeCode) := by
  intro _targetScope substitution env predLevel
  have typeData :=
    FundamentalConclusionAtAll.typeInUniverse_hasStrongNormalizationAndAllLevelReducibility
      typeFundamental substitution env
  exact positiveMemberExtension.toAllReducibleTypesHaveTypeValueCandidates
    typeData.1 typeData.2 predLevel

/-- **Positive-fuel members under a type-in-universe fundamental result extend to all positive fuels.**
This is the member-level form consumed by binder arms: a decoded argument at the exact positive level where
the semantic rule obtained it is strengthened to the all-positive argument required by
`ReducibleEnvAtAllLevels.cons`. -/
theorem FundamentalConclusionAtAll.typeInUniverse_positiveMemberExtendsToAllPositiveOfPositiveMemberExtension
    {profile : PolyProfile} {scope targetScope : Nat}
    {context : TypingContext profile scope}
    {typeCode : RawTerm scope} {levelExpr : LevelExpr} {flag : UniverseFlag}
    {argument : RawTerm (targetScope + 1)} {memberPredLevel : Nat}
    (positiveMemberExtension :
      HasPositiveMemberExtensionForStronglyNormalizingAllLevelTypes)
    (typeFundamental :
      FundamentalConclusionAtAll context typeCode (universeCodeCell levelExpr flag))
    (substitution : RawTermSubst scope (targetScope + 1))
    (env : ReducibleEnvAtAllLevels context substitution)
    (argumentMember :
      IsReducibleMemberAt (memberPredLevel + 1) (RawTerm.subst substitution typeCode) argument) :
    IsReducibleMemberAtAllPositiveLevels (RawTerm.subst substitution typeCode) argument :=
  IsReducibleMemberAt.extendsToAllPositiveOfAllPositiveCandidate
    (FundamentalConclusionAtAll.typeInUniverse_hasPositiveCandidateOfPositiveMemberExtension
      positiveMemberExtension typeFundamental substitution env memberPredLevel)
    argumentMember

/-- **Extend an all-level environment from one positive member under a type-in-universe head.**  The head
argument is supplied at one positive member level; positive-member extension strengthens it to all positive
levels, and then `ReducibleEnvAtAllLevels.cons` installs it as the fresh binding. -/
theorem ReducibleEnvAtAllLevels.consArgumentAtPositiveMemberLevelOfHeadFundamental
    {profile : PolyProfile} {scope targetScope : Nat}
    {context : TypingContext profile scope}
    {bindingType : RawTerm scope} {levelExpr : LevelExpr} {flag : UniverseFlag}
    {substitution : RawTermSubst scope (targetScope + 1)}
    {argument : RawTerm (targetScope + 1)} {memberPredLevel : Nat}
    (positiveMemberExtension :
      HasPositiveMemberExtensionForStronglyNormalizingAllLevelTypes)
    (env : ReducibleEnvAtAllLevels context substitution)
    (bindingTypeFundamental :
      FundamentalConclusionAtAll context bindingType (universeCodeCell levelExpr flag))
    (argumentMember :
      IsReducibleMemberAt (memberPredLevel + 1)
        (RawTerm.subst substitution bindingType) argument) :
    ReducibleEnvAtAllLevels (context.cons bindingType)
      (RawTermSubst.cons argument substitution) :=
  ReducibleEnvAtAllLevels.cons env
    (FundamentalConclusionAtAll.typeInUniverse_positiveMemberExtendsToAllPositiveOfPositiveMemberExtension
      positiveMemberExtension bindingTypeFundamental substitution env argumentMember)

/-- **Telescope cons through positive-member extension with an explicit fuel-zero branch.**  The telescope
tail is asked for every `memberLevel`.  Positive-member extension covers only the positive levels
`memberPredLevel + 1`; therefore this bridge keeps the fuel-zero tail premise explicit and uses
positive-member extension exactly on the successor branch.  This is the sound recursor-facing shape for the
formation telescope: no hidden level irrelevance, and no false claim that universe/type-value completion
acts at fuel zero. -/
theorem fundamentalTelescopeConsAtAllFromPositiveMemberExtensionAndZeroMemberTail
    {profile : PolyProfile} {baseScope targetScope currentDepth count : Nat}
    {context : TypingContext profile (baseScope + currentDepth)}
    {head : RawTerm (baseScope + currentDepth)}
    {restLevels : List LevelExpr} {flag : UniverseFlag}
    {rest : RawTermChildren (consecutiveShifts (currentDepth + 1) count) baseScope}
    {headLevel : LevelExpr}
    {substitution : RawTermSubst (baseScope + currentDepth) (targetScope + 1)}
    (positiveMemberExtension :
      HasPositiveMemberExtensionForStronglyNormalizingAllLevelTypes)
    (env : ReducibleEnvAtAllLevels context substitution)
    (headFundamental :
      FundamentalConclusionAtAll context head (universeCodeCell headLevel flag))
    (tailReducibleAtZero :
      ∀ argument : RawTerm (targetScope + 1),
        IsReducibleMemberAt 0 (RawTerm.subst substitution head) argument →
          TelescopeReducible flag (currentDepth + 1) count
            (RawTermSubst.cons argument substitution) restLevels rest)
    (tailReducibleAtAllPositiveArgument :
      ∀ argument : RawTerm (targetScope + 1),
        IsReducibleMemberAtAllPositiveLevels (RawTerm.subst substitution head) argument →
          TelescopeReducible flag (currentDepth + 1) count
            (RawTermSubst.cons argument substitution) restLevels rest) :
    TelescopeReducible flag currentDepth (count + 1) substitution (headLevel :: restLevels)
      (.childCons head rest) :=
  fundamentalTelescopeConsAtAll env headFundamental
    (fun {memberLevel} argument argumentMember => by
      cases memberLevel with
      | zero =>
          exact tailReducibleAtZero argument argumentMember
      | succ memberPredLevel =>
          exact tailReducibleAtAllPositiveArgument argument
            (FundamentalConclusionAtAll.typeInUniverse_positiveMemberExtendsToAllPositiveOfPositiveMemberExtension
              positiveMemberExtension headFundamental substitution env argumentMember))

end FX1Poly.Typed
