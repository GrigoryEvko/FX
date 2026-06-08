import FX1Poly.Typed.DenoteKeyedFundamentalMotive
import FX1Poly.Typed.DenoteKeyedApplicationMember
import FX1Poly.Typed.HasTypeDescPi

/-! Scratch SN-D5b: the FT piElim (application) arm over the denote motive.  Cleanest dispatcher arm — composes
the shipped `applicationMemberUnderClosingSubstitution` with both sub-IHs at the SAME ambient `level`, no
level-bridge / no universe-membership extraction (unlike conv). functionConclusion gives a member of the Π type,
argumentConclusion a member of the domain; the application is a member of the substituted dependent codomain. -/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

theorem fundamentalPiElimAtDenote {profile : PolyProfile} {scope : Nat} (env : Nat → Nat) (level : Nat)
    (context : TypingContext profile scope)
    {functionTerm argument domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (functionConclusion :
      FundamentalConclusionAtDenote env level context functionTerm
        (piTyCodeCell domainCode codomainCode))
    (argumentConclusion :
      FundamentalConclusionAtDenote env level context argument domainCode) :
    FundamentalConclusionAtDenote env level context (appCell functionTerm argument)
      (RawTerm.subst0 codomainCode argument) := by
  intro targetScope substitution envReducible
  exact applicationMemberUnderClosingSubstitution env level
    (functionConclusion substitution envReducible)
    (argumentConclusion substitution envReducible)

end FX1Poly.Typed

#print axioms FX1Poly.Typed.fundamentalPiElimAtDenote
