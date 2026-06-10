import FX1Poly.Typed.DenoteKeyedFundamentalMotive
import FX1Poly.Typed.DenoteKeyedAbstractionUnderSubst
import FX1Poly.Typed.DenoteKeyedCanonicalMemberCandidate
import FX1Poly.Typed.HasTypeDescPi

/-! # FX1Poly/Typed/DenoteKeyedFundamentalPiIntro
    — the denote fundamental theorem's Π-INTRODUCTION (λ) dispatcher arm — THE BINDER CRUX (SN-D5c; toward SN-043)

The arm for the `HasTypeDescPi.piIntro` constructor, the case the per-level route WALLED on (the binder env-cons
coordination): from the domain, codomain, and body fundamental-theorem data, conclude the fundamental-theorem
conclusion of `λ body` at `Π domainCode codomainCode`.

THE KEY MOVE that makes the binder coordination clean — the CANONICAL member predicate as candidate.  Take
BOTH the domain candidate and (per argument) the codomain candidate to be the canonical member predicate
`IsReducibleMemberAtDenote env level (subst …)` (the type's own candidate, `reducibleMemberCandidate`).  Two
payoffs collapse the crux:
  * the env-cons argument-membership is DIRECT — `domainCandidate argument` IS
    `IsReducibleMemberAtDenote env level (subst σ domainCode) argument`, exactly the `headReducible` premise
    `ReducibleEnvAtDenote.cons` wants, so threading the binder environment needs no repackaging;
  * `bodyReducible` is DIRECT — the codomain candidate `IsReducibleMemberAtDenote env level (subst (cons arg σ)
    codomainCode)` is precisely the body IH `bodyConclusion`'s output type at the cons-extended substitution and
    environment, so no `deterministic` alignment is needed.

The actual reducibility content is supplied as clean caller premises (the SN-D5 wiring discharges them):
`domainReducibleAtLevel` / `codomainReducibleAtLevel` are the A2-bridge-applied domain / codomain IHs
(`universeMemberReducibleAtLevel`, the universe-membership→ambient-level reducibility bridge, applied to the
`piIntro` constructor's domain/codomain universe-membership IHs); `domainArgumentsSN` is denote CR1 (members of
the domain candidate are strongly normalizing); the body IH is the direct `bodyConclusion`.  So this arm is
UNCONDITIONAL given those three reducibility/SN premises — the genuinely-new content is the canonical-candidate
threading plus `abstractionMemberUnderClosingSubstitution` (SN-D3) and `ReducibleEnvAtDenote.cons`.

## Zero-axiom verification

`intro` the substitution / environment, then one `abstractionMemberUnderClosingSubstitution` with the domain and
codomain candidates pinned to the canonical member predicate, the domain/codomain reducibilities supplied via
`reducibleMemberCandidate`, domain CR1 from the premise, and the body membership from `bodyConclusion` on the
`ReducibleEnvAtDenote.cons`-extended environment.  No induction, no `funext`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation
open StepStar

/-- **The denote `piIntro` (λ) fundamental-theorem arm — the binder crux.**  Given the domain reducible at the
ambient level under every closing substitution, the domain candidate's members strongly normalizing (denote
CR1), the codomain reducible at the ambient level under every closing substitution extended by a domain member,
and the body's fundamental-theorem conclusion under the extended context, `λ body` satisfies the
fundamental-theorem conclusion at `Π domainCode codomainCode`.  The domain/codomain candidates are the canonical
member predicate, making the binder environment threading (`ReducibleEnvAtDenote.cons`) and the body membership
both direct; the assembly is `abstractionMemberUnderClosingSubstitution`.  The reducibility premises are the
A2-bridge-applied IHs and CR1 (the wiring supplies them); the body conclusion is the direct body IH. -/
theorem fundamentalPiIntroAtDenote {profile : PolyProfile} {scope : Nat} (env : Nat → Nat) (level : Nat)
    (context : TypingContext profile scope)
    {domainCode : RawTerm scope} {codomainCode body : RawTerm (scope + 1)}
    (domainReducibleAtLevel : ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtDenote env level context substitution →
        IsReducibleTypeAtDenote env level (RawTerm.subst substitution domainCode))
    (domainCodeStronglyNormalizing :
        ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtDenote env level context substitution →
        IsStronglyNormalizing (RawTerm.subst substitution domainCode))
    (domainArgumentsSN : ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtDenote env level context substitution →
        ∀ argument : RawTerm targetScope,
          IsReducibleMemberAtDenote env level (RawTerm.subst substitution domainCode) argument →
          IsStronglyNormalizing argument)
    (codomainReducibleAtLevel : ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtDenote env level context substitution →
        ∀ argument : RawTerm targetScope,
          IsReducibleMemberAtDenote env level (RawTerm.subst substitution domainCode) argument →
          IsReducibleTypeAtDenote env level
            (RawTerm.subst (RawTermSubst.cons argument substitution) codomainCode))
    (bodyConclusion :
        FundamentalConclusionAtDenote env level (context.cons domainCode) body codomainCode) :
    FundamentalConclusionAtDenote env level context (lamCell domainCode body)
      (piTyCodeCell domainCode codomainCode) := by
  intro _targetScope substitution envReducible
  exact abstractionMemberUnderClosingSubstitution
    (domainCandidate := IsReducibleMemberAtDenote env level (RawTerm.subst substitution domainCode))
    (codomainCandidate := fun argument =>
      IsReducibleMemberAtDenote env level
        (RawTerm.subst (RawTermSubst.cons argument substitution) codomainCode))
    env level
    (domainReducibleAtLevel substitution envReducible).reducibleMemberCandidate
    (domainCodeStronglyNormalizing substitution envReducible)
    (fun argument argumentMember =>
      (codomainReducibleAtLevel substitution envReducible argument argumentMember).reducibleMemberCandidate)
    (domainArgumentsSN substitution envReducible)
    (fun argument argumentMember =>
      bodyConclusion (RawTermSubst.cons argument substitution)
        (ReducibleEnvAtDenote.cons envReducible argumentMember))

end FX1Poly.Typed
