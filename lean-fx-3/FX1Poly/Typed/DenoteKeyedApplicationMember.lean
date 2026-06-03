import FX1Poly.Typed.DenoteKeyedReducibility
import FX1Poly.Core.RawTermSubst0Commute

/-! # FX1Poly/Typed/DenoteKeyedApplicationMember
    — the denote fundamental theorem's Π-ELIMINATION (application) member arm

The first MEMBER-level fundamental-theorem arm over the denote relation (the type-formation arms live in
`DenoteKeyedPiFormationFromExistence` / `…UnderSubst`).  It is the computational heart of the elimination rule:
if `functionTerm` is a denote-reducible member of `Π domainCode codomainCode` and `argumentTerm` is a
denote-reducible member of `domainCode`, then the application `app functionTerm argumentTerm` is a
denote-reducible member of the substituted codomain `subst0 codomainCode argumentTerm`.

It reads DIRECTLY off the `piType` candidate, with no backward-closure and no new machinery: by construction a
member of `Π A B` is a function whose application to any domain member lands in the codomain candidate (the
`piType` candidate is `fun f => ∀ arg, domainCandidate arg → codomainCandidate arg (app f arg)`).
`piTypeInversion` recovers the domain/codomain candidates and that application-form `PointwiseIff`;
`deterministic` aligns the argument's own candidate with the Π's domain candidate so the argument membership
feeds the function's per-argument obligation; the result is exactly membership of `app f arg` in the codomain
candidate at `arg`, which `piTypeInversion` certifies as the candidate of `subst0 codomainCode argumentTerm`.

## Zero-axiom verification

`obtain` destructuring of the two members and `piTypeInversion`, then `deterministic`/`PointwiseIff` `.mp`
transports and a final anonymous-constructor witness — no tactic recursion, no `funext`.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- **The denote Π-elimination (application) member arm.**  A denote-reducible member of `Π domainCode
codomainCode` applied to a denote-reducible member of `domainCode` is a denote-reducible member of
`subst0 codomainCode argumentTerm`.  Direct from the `piType` candidate via `piTypeInversion` (recovering the
domain/codomain candidates and the application-form `PointwiseIff`) and `deterministic` (aligning the
argument's candidate with the domain candidate). -/
theorem applicationMemberAtDenote {scope : Nat} (env : Nat → Nat) (level : Nat)
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {functionTerm argumentTerm : RawTerm scope}
    (functionMember : IsReducibleMemberAtDenote env level
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))) functionTerm)
    (argumentMember : IsReducibleMemberAtDenote env level domainCode argumentTerm) :
    IsReducibleMemberAtDenote env level (RawTerm.subst0 codomainCode argumentTerm)
      (.mkGen .gen_app () (.childCons functionTerm (.childCons argumentTerm .childNil))) := by
  obtain ⟨_piCandidate, piReducible, functionInPi⟩ := functionMember
  obtain ⟨domainCandidate, codomainCandidate, domainReducible, codomainReducible, piCandidateIff⟩ :=
    piReducible.piTypeInversion
  have functionApplies := (piCandidateIff functionTerm).mp functionInPi
  obtain ⟨argumentCandidate, argumentReducible, argumentInCandidate⟩ := argumentMember
  have argumentInDomain : domainCandidate argumentTerm :=
    (ReducibleTypeAtDenote.deterministic argumentReducible domainReducible argumentTerm).mp
      argumentInCandidate
  exact ⟨codomainCandidate argumentTerm, codomainReducible argumentTerm argumentInDomain,
    functionApplies argumentTerm argumentInDomain⟩

/-- **The denote Π-elimination member arm under a closing substitution (the fundamental-theorem shape).**  From
a denote-reducible member of the substituted Π `subst σ (Π domainCode codomainCode)` and a denote-reducible
member of the substituted domain `subst σ domainCode`, the substituted application `subst σ (app functionTerm
argumentTerm)` is a denote-reducible member of the substituted dependent codomain `subst σ (subst0 codomainCode
argumentTerm)`.  The `subst` distributes over the app and Π cells definitionally; the dependent result type
commutes by `RawTerm.subst0_subst_commute` (`subst σ (subst0 B a) = subst0 (subst (lift σ) B) (subst σ a)`) into
exactly the shape `applicationMemberAtDenote` produces.  This is the FT's elimination case under the closing
substitution. -/
theorem applicationMemberUnderClosingSubstitution {scope targetScope : Nat} (env : Nat → Nat) (level : Nat)
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {functionTerm argumentTerm : RawTerm scope} {substitution : RawTermSubst scope targetScope}
    (functionMember : IsReducibleMemberAtDenote env level
      (RawTerm.subst substitution
        (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))))
      (RawTerm.subst substitution functionTerm))
    (argumentMember : IsReducibleMemberAtDenote env level
      (RawTerm.subst substitution domainCode) (RawTerm.subst substitution argumentTerm)) :
    IsReducibleMemberAtDenote env level
      (RawTerm.subst substitution (RawTerm.subst0 codomainCode argumentTerm))
      (RawTerm.subst substitution
        (.mkGen .gen_app () (.childCons functionTerm (.childCons argumentTerm .childNil)))) := by
  rw [RawTerm.subst0_subst_commute codomainCode argumentTerm substitution]
  exact applicationMemberAtDenote env level functionMember argumentMember

end FX1Poly.Typed
