import FX1Poly.Typed.ReducibleEnvAtAllLevels
import FX1Poly.Typed.FundamentalAtAllPositiveArguments

/-! # FX1Poly/Typed/ReducibleEnvAtAllLevelsWithPositiveTypeCandidates
    — proof-relevant all-level environments carrying positive type-candidate companions

The all-level environment `ReducibleEnvAtAllLevels` is exactly the right shape for the dependent
fundamental theorem's `var` arm: every variable is available at every positive fuel level.  Dependent binder
arms need one more piece of proof-relevant information: when a context binding is used as a domain, the
substituted binding type must expose the all-positive member predicate as a reducible candidate at positive
fuel levels.  That is the companion used by the all-positive argument bridges in
`FundamentalAtAllPositiveArguments`.

This file packages that pair as a strengthened reducible environment:

* ordinary all-level membership for variables; and
* positive-fuel all-positive candidate witnesses for the substituted lookup type of every variable.

The key operation is `cons`: extending the environment requires the fresh head term as an all-positive member
of the new binding type and a positive-fuel candidate companion for that binding type.  Variable zero then
uses the head companion after the standard `lookup_cons_zero` / `weaken_subst_cons` rewrite; successor
variables use the tail companion after the corresponding successor rewrite.

This is intentionally a proof-relevant environment layer, not a level-irrelevance theorem.  It records the
extra semantic data the binder route actually needs, without claiming that arbitrary reducibility candidates
can be transported across fuel levels.

## Zero-axiom verification

All declarations are conjunction projections or the same `Fin` index split used by `ReducibleEnvAt.cons`.
The only rewrites are `TypingContext.lookup_cons_zero`, `TypingContext.lookup_cons_succ`, and
`RawTerm.weaken_subst_cons`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or
`omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Foundation

/-- A proof-relevant all-level reducible environment carrying the positive-fuel type-candidate companion
for every looked-up binding type.  The first projection is the ordinary all-level environment.  The second
projection says that each substituted lookup type denotes `IsReducibleMemberAtAllPositiveLevels` as a
candidate at every positive fuel level. -/
def ReducibleEnvAtAllLevelsWithPositiveTypeCandidates {profile : PolyProfile} {scope targetScope : Nat}
    (context : TypingContext profile scope)
    (substitution : RawTermSubst scope targetScope) : Prop :=
  ReducibleEnvAtAllLevels context substitution ∧
    ∀ (index : Fin scope) (predLevel : Nat),
      HasAllPositiveReducibleCandidateAt (predLevel + 1)
        (RawTerm.subst substitution (context.lookup index))

/-- Project the ordinary all-level reducible environment from the strengthened proof-relevant environment. -/
theorem ReducibleEnvAtAllLevelsWithPositiveTypeCandidates.toAllLevels
    {profile : PolyProfile} {scope targetScope : Nat}
    {context : TypingContext profile scope} {substitution : RawTermSubst scope targetScope}
    (envWithCandidates :
      ReducibleEnvAtAllLevelsWithPositiveTypeCandidates context substitution) :
    ReducibleEnvAtAllLevels context substitution :=
  envWithCandidates.1

/-- Project the positive-fuel all-positive candidate witness for a looked-up binding type. -/
theorem ReducibleEnvAtAllLevelsWithPositiveTypeCandidates.lookupPositiveCandidate
    {profile : PolyProfile} {scope targetScope : Nat}
    {context : TypingContext profile scope} {substitution : RawTermSubst scope targetScope}
    (envWithCandidates :
      ReducibleEnvAtAllLevelsWithPositiveTypeCandidates context substitution)
    (index : Fin scope) (predLevel : Nat) :
    HasAllPositiveReducibleCandidateAt (predLevel + 1)
      (RawTerm.subst substitution (context.lookup index)) :=
  envWithCandidates.2 index predLevel

/-- The empty context has a strengthened environment vacuously: there are no variables whose binding types
need candidate companions. -/
theorem ReducibleEnvAtAllLevelsWithPositiveTypeCandidates.empty
    {profile : PolyProfile} {targetScope : Nat}
    (substitution : RawTermSubst 0 targetScope) :
    ReducibleEnvAtAllLevelsWithPositiveTypeCandidates
      (TypingContext.empty : TypingContext profile 0) substitution :=
  ⟨ReducibleEnvAtAllLevels.empty substitution, fun index => index.elim0⟩

/-- Extend a strengthened all-level environment through a binder.  The tail supplies all ordinary variables
and their positive-fuel type-candidate companions.  The fresh head must be an all-positive member of the new
binding type, so the ordinary all-level environment extends; and the binding type itself must have the
positive-fuel all-positive candidate companion, so variable zero's lookup companion extends. -/
theorem ReducibleEnvAtAllLevelsWithPositiveTypeCandidates.cons
    {profile : PolyProfile} {scope targetScope : Nat}
    {context : TypingContext profile scope} {bindingType : RawTerm scope}
    {tailSubstitution : RawTermSubst scope targetScope} {headTerm : RawTerm targetScope}
    (tailEnvWithCandidates :
      ReducibleEnvAtAllLevelsWithPositiveTypeCandidates context tailSubstitution)
    (headReducibleAtAllPositiveLevels :
      IsReducibleMemberAtAllPositiveLevels (RawTerm.subst tailSubstitution bindingType) headTerm)
    (headTypeHasPositiveCandidate :
      ∀ predLevel : Nat,
        HasAllPositiveReducibleCandidateAt (predLevel + 1)
          (RawTerm.subst tailSubstitution bindingType)) :
    ReducibleEnvAtAllLevelsWithPositiveTypeCandidates (context.cons bindingType)
      (RawTermSubst.cons headTerm tailSubstitution) := by
  constructor
  · exact ReducibleEnvAtAllLevels.cons
      tailEnvWithCandidates.toAllLevels headReducibleAtAllPositiveLevels
  · intro index predLevel
    match index with
    | ⟨0, isLtZeroSucc⟩ =>
        rw [TypingContext.lookup_cons_zero context bindingType isLtZeroSucc,
          RawTerm.weaken_subst_cons bindingType headTerm tailSubstitution]
        exact headTypeHasPositiveCandidate predLevel
    | ⟨position + 1, isLtSuccSucc⟩ =>
        rw [TypingContext.lookup_cons_succ context bindingType position isLtSuccSucc,
          RawTerm.weaken_subst_cons
            (context.lookup ⟨position, Nat.lt_of_succ_lt_succ isLtSuccSucc⟩)
            headTerm tailSubstitution]
        exact tailEnvWithCandidates.lookupPositiveCandidate
          ⟨position, Nat.lt_of_succ_lt_succ isLtSuccSucc⟩ predLevel

end FX1Poly.Typed
