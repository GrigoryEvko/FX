import FX1Poly.Typed.ReducibleEnvAtAllLevelsWithPositiveTypeCandidates
import FX1Poly.Typed.HasTypeSubstitution

/-! # FX1Poly/Typed/ReducibleEnvAtAllLevelsWithTypeValueCandidates
    -- strengthened all-level environments for type-valued variables

`ReducibleEnvAtAllLevelsWithPositiveTypeCandidates` records positive-fuel candidate companions for the
LOOKED-UP binding types.  That is enough for ordinary binders once the domain is known as a type, but the
two-part dependent fundamental theorem also has a type-variable arm: when a variable's substituted lookup
classifier is a universe code, the substituted variable itself is a type value and must expose the
all-positive member predicate as a candidate.

This file packages exactly that additional proof-relevant data.  The universe test is intentionally stated
AFTER substitution:

  `RawTerm.subst substitution (context.lookup index) = universeCodeCell levelExpr flag`.

That form is stable under binder extension.  At successor variables, `lookup_cons_succ` plus
`RawTerm.weaken_subst_cons` rewrites the extended lookup back to the tail lookup, so the tail witness applies
without any unsafe syntactic "rename reflects universe" lemma.  At variable zero, the caller supplies the
fresh head's type-value candidate when the substituted binding type is a universe.

This is not a level-irrelevance theorem.  It is the honest extra semantic payload needed by type variables
in the strengthened fundamental-theorem motive.

## Zero-axiom verification

All proofs are conjunction projections or the same propext-free de Bruijn split used by the reducible
environment lemmas.  The only rewrites are `subst_variableCell`, `TypingContext.lookup_cons_zero`,
`TypingContext.lookup_cons_succ`, and `RawTerm.weaken_subst_cons`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Foundation FX1Poly.Universe

/-- A strengthened closing environment carrying:

* ordinary all-level variable membership;
* positive-fuel candidate companions for looked-up binding types; and
* positive-fuel candidate companions for substituted VARIABLE VALUES whenever their substituted lookup
  classifier is a universe code.

The last projection is the type-variable payload consumed by the two-part dependent fundamental theorem. -/
def ReducibleEnvAtAllLevelsWithTypeValueCandidates
    {profile : PolyProfile} {scope targetScope : Nat}
    (context : TypingContext profile scope)
    (substitution : RawTermSubst scope targetScope) : Prop :=
  ReducibleEnvAtAllLevelsWithPositiveTypeCandidates context substitution ∧
    ∀ (index : Fin scope) {levelExpr : LevelExpr} {flag : UniverseFlag},
      RawTerm.subst substitution (context.lookup index) = universeCodeCell levelExpr flag →
        ∀ predLevel : Nat,
          HasAllPositiveReducibleCandidateAt (predLevel + 1)
            (RawTerm.subst substitution (variableCell index))

/-- Forget the type-value payload and keep the existing positive-candidate environment. -/
theorem ReducibleEnvAtAllLevelsWithTypeValueCandidates.toPositiveTypeCandidates
    {profile : PolyProfile} {scope targetScope : Nat}
    {context : TypingContext profile scope} {substitution : RawTermSubst scope targetScope}
    (envWithTypeValueCandidates :
      ReducibleEnvAtAllLevelsWithTypeValueCandidates context substitution) :
    ReducibleEnvAtAllLevelsWithPositiveTypeCandidates context substitution :=
  envWithTypeValueCandidates.1

/-- Forget down to the ordinary all-level reducible environment. -/
theorem ReducibleEnvAtAllLevelsWithTypeValueCandidates.toAllLevels
    {profile : PolyProfile} {scope targetScope : Nat}
    {context : TypingContext profile scope} {substitution : RawTermSubst scope targetScope}
    (envWithTypeValueCandidates :
      ReducibleEnvAtAllLevelsWithTypeValueCandidates context substitution) :
    ReducibleEnvAtAllLevels context substitution :=
  envWithTypeValueCandidates.toPositiveTypeCandidates.toAllLevels

/-- Project the positive-fuel candidate companion for a looked-up binding type. -/
theorem ReducibleEnvAtAllLevelsWithTypeValueCandidates.lookupPositiveCandidate
    {profile : PolyProfile} {scope targetScope : Nat}
    {context : TypingContext profile scope} {substitution : RawTermSubst scope targetScope}
    (envWithTypeValueCandidates :
      ReducibleEnvAtAllLevelsWithTypeValueCandidates context substitution)
    (index : Fin scope) (predLevel : Nat) :
    HasAllPositiveReducibleCandidateAt (predLevel + 1)
      (RawTerm.subst substitution (context.lookup index)) :=
  envWithTypeValueCandidates.toPositiveTypeCandidates.lookupPositiveCandidate index predLevel

/-- Project the type-variable payload: if the substituted classifier of a variable is a universe code, then
the substituted variable value has the positive-fuel all-positive candidate companion. -/
theorem ReducibleEnvAtAllLevelsWithTypeValueCandidates.lookupTypeValuePositiveCandidate
    {profile : PolyProfile} {scope targetScope : Nat}
    {context : TypingContext profile scope} {substitution : RawTermSubst scope targetScope}
    (envWithTypeValueCandidates :
      ReducibleEnvAtAllLevelsWithTypeValueCandidates context substitution)
    (index : Fin scope) {levelExpr : LevelExpr} {flag : UniverseFlag}
    (lookupSubstIsUniverse :
      RawTerm.subst substitution (context.lookup index) = universeCodeCell levelExpr flag)
    (predLevel : Nat) :
    HasAllPositiveReducibleCandidateAt (predLevel + 1)
      (RawTerm.subst substitution (variableCell index)) :=
  envWithTypeValueCandidates.2 index lookupSubstIsUniverse predLevel

/-- The empty context has the strengthened environment vacuously. -/
theorem ReducibleEnvAtAllLevelsWithTypeValueCandidates.empty
    {profile : PolyProfile} {targetScope : Nat}
    (substitution : RawTermSubst 0 targetScope) :
    ReducibleEnvAtAllLevelsWithTypeValueCandidates
      (TypingContext.empty : TypingContext profile 0) substitution :=
  ⟨ReducibleEnvAtAllLevelsWithPositiveTypeCandidates.empty substitution, fun index => index.elim0⟩

/-- Extend the strengthened environment through a binder.  In addition to the ordinary all-positive head
membership and the binding-type positive candidate, the caller supplies the head VALUE's positive candidate
whenever the substituted binding type is a universe.  This is precisely the data required for variable zero
to be usable as a type variable under the binder; successor variables recurse into the tail environment
after `weaken_subst_cons` cancels the context lookup weakening. -/
theorem ReducibleEnvAtAllLevelsWithTypeValueCandidates.cons
    {profile : PolyProfile} {scope targetScope : Nat}
    {context : TypingContext profile scope} {bindingType : RawTerm scope}
    {tailSubstitution : RawTermSubst scope targetScope} {headTerm : RawTerm targetScope}
    (tailEnvWithTypeValueCandidates :
      ReducibleEnvAtAllLevelsWithTypeValueCandidates context tailSubstitution)
    (headReducibleAtAllPositiveLevels :
      IsReducibleMemberAtAllPositiveLevels (RawTerm.subst tailSubstitution bindingType) headTerm)
    (headTypeHasPositiveCandidate :
      ∀ predLevel : Nat,
        HasAllPositiveReducibleCandidateAt (predLevel + 1)
          (RawTerm.subst tailSubstitution bindingType))
    (headValueHasPositiveCandidateWhenBindingIsUniverse :
      ∀ {levelExpr : LevelExpr} {flag : UniverseFlag},
        RawTerm.subst tailSubstitution bindingType = universeCodeCell levelExpr flag →
          ∀ predLevel : Nat,
            HasAllPositiveReducibleCandidateAt (predLevel + 1) headTerm) :
    ReducibleEnvAtAllLevelsWithTypeValueCandidates (context.cons bindingType)
      (RawTermSubst.cons headTerm tailSubstitution) := by
  constructor
  · exact ReducibleEnvAtAllLevelsWithPositiveTypeCandidates.cons
      tailEnvWithTypeValueCandidates.toPositiveTypeCandidates
      headReducibleAtAllPositiveLevels headTypeHasPositiveCandidate
  · intro index levelExpr flag lookupSubstIsUniverse predLevel
    match index with
    | ⟨0, isLtZeroSucc⟩ =>
        rw [subst_variableCell]
        apply headValueHasPositiveCandidateWhenBindingIsUniverse
        rw [TypingContext.lookup_cons_zero context bindingType isLtZeroSucc,
          RawTerm.weaken_subst_cons bindingType headTerm tailSubstitution] at lookupSubstIsUniverse
        exact lookupSubstIsUniverse
    | ⟨position + 1, isLtSuccSucc⟩ =>
        rw [subst_variableCell]
        rw [TypingContext.lookup_cons_succ context bindingType position isLtSuccSucc,
          RawTerm.weaken_subst_cons
            (context.lookup ⟨position, Nat.lt_of_succ_lt_succ isLtSuccSucc⟩)
            headTerm tailSubstitution] at lookupSubstIsUniverse
        exact tailEnvWithTypeValueCandidates.lookupTypeValuePositiveCandidate
          ⟨position, Nat.lt_of_succ_lt_succ isLtSuccSucc⟩ lookupSubstIsUniverse predLevel

end FX1Poly.Typed
