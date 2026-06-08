import FX1Poly.Typed.DenoteKeyedFundamentalMotive
import FX1Poly.Core.RawTermSubstIdentity

/-! Scratch (route-E / SN-D6 precursor): the closed-term reducibility corollary of the denote FT motive.
At the EMPTY context, the FT conclusion instantiated at the IDENTITY substitution + the empty environment
(`ReducibleEnvAtDenote.empty`) gives — after the identity-substitution cancellation `subst identity t = t` —
the closed subject as a denote-reducible MEMBER of the closed classifier. This is the step from the (eventual)
closed-term FT conclusion to closed-term reducibility, which composed with CR1 yields closed-term SN = SN-043. -/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

theorem closedMemberAtDenote {profile : PolyProfile} (env : Nat → Nat) (level : Nat)
    {subject classifier : RawTerm 0}
    (conclusion : FundamentalConclusionAtDenote env level
      (TypingContext.empty : TypingContext profile 0) subject classifier) :
    IsReducibleMemberAtDenote env level classifier subject := by
  have member := conclusion RawTermSubst.identity
    (ReducibleEnvAtDenote.empty (profile := profile) RawTermSubst.identity)
  rw [RawTerm.subst_identity_apply, RawTerm.subst_identity_apply] at member
  exact member

end FX1Poly.Typed

#print axioms FX1Poly.Typed.closedMemberAtDenote
