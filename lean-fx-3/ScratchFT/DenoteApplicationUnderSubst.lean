import FX1Poly.Typed.DenoteKeyedApplicationMember
import FX1Poly.Core.RawTermSubst0Commute

/-! Scratch: the denote Π-ELIMINATION member arm UNDER A CLOSING SUBSTITUTION (FT-shape of applicationMember).
subst distributes over the app + Π cells by rfl; the result type subst σ (subst0 B a) commutes to
subst0 (subst (lift σ) B) (subst σ a) by subst0_subst_commute, matching applicationMemberAtDenote's output. -/

namespace FX1Poly.Typed
open FX1Poly.Core

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

#print axioms FX1Poly.Typed.applicationMemberUnderClosingSubstitution
