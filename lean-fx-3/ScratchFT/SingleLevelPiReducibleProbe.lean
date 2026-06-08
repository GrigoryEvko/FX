import FX1Poly.Typed.DenoteKeyedGeneralDomainPiArm

/-! Scratch probe: the SINGLE-LEVEL Π type-reducibility assembly — `IsReducibleTypeAtDenote env L (Π D C)` from
    component reducibility AT L, via canonical member-predicates. Single level ⟹ NO all-levels low-level drift.
    This is the building block for discharging genFormationPi's `piReducibleAsType` (at the decoded output level)
    directly, sidestepping the all-levels #752 piArm. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

theorem piReducibleAtLevelFromComponents {scope : Nat} (env : Nat → Nat) (level : Nat)
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (domainReducible : IsReducibleTypeAtDenote env level domainCode)
    (codomainReducible : ∀ argument : RawTerm scope,
        IsReducibleMemberAtDenote env level domainCode argument →
        IsReducibleTypeAtDenote env level (RawTerm.subst0 codomainCode argument)) :
    IsReducibleTypeAtDenote env level
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))) :=
  ⟨_, ReducibleTypeStepDenote.piType
    (fun argument => IsReducibleMemberAtDenote env level (RawTerm.subst0 codomainCode argument))
    domainReducible.reducibleMemberCandidate
    (fun argument argumentInDomain =>
      (codomainReducible argument argumentInDomain).reducibleMemberCandidate)⟩

/-- A universe MEMBER of `Type@levelExpr` is reducible-as-TYPE at the DECODED level `denote levelExpr env`
    directly — no all-levels lift, no piArm.  This is the bridge's first half (`universeMemberReducibleAtLevel`
    extracts exactly this before over-generalizing to all levels). Drift-free: works for ANY `X` (including
    composite-universe Π), since it only decodes membership at the single decoded level. -/
theorem universeMemberReducibleAsTypeAtDecodedLevel {scope : Nat} {env : Nat → Nat} {level : Nat}
    {levelExpr : LevelExpr} {flag : UniverseFlag} {typeCode : RawTerm scope}
    (memberOfUniverse : IsReducibleMemberAtDenote env level
      (.mkGen .gen_universeCode (levelExpr, flag) .childNil) typeCode)
    (levelAbove : LevelExpr.denote levelExpr env < level) :
    IsReducibleTypeAtDenote env (LevelExpr.denote levelExpr env) typeCode := by
  obtain ⟨candidate, reducibleUniverse, candidateMember⟩ := memberOfUniverse
  have candidateIff := ReducibleTypeStepDenote.candidateIffUniverse reducibleUniverse
    (levelExpr := levelExpr) (flag := flag) rfl
  obtain ⟨_strongNormalizing, decodeCandidate, denoteReducible⟩ := (candidateIff typeCode).mp candidateMember
  rw [denoteBelowFamily_eq_reducible env level (LevelExpr.denote levelExpr env) levelAbove]
    at denoteReducible
  exact ⟨decodeCandidate, denoteReducible⟩

#print axioms piReducibleAtLevelFromComponents
#print axioms universeMemberReducibleAsTypeAtDecodedLevel

end FX1Poly.Typed
