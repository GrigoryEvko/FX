import FX1Poly.Typed.DenoteKeyedFundamentalMotive
import FX1Poly.Typed.DenoteKeyedApplicationMember
import FX1Poly.Typed.HasTypeDescPi

/-! # FX1Poly/Typed/DenoteKeyedFundamentalPiElim
    — the denote fundamental theorem's Π-ELIMINATION (application) dispatcher arm (SN-D5b; toward SN-043/#672)

The first RECURSIVE-arm dispatcher of the denote fundamental theorem (the leaf arms — var, universeFormation —
shipped in `DenoteKeyedFundamentalMotive`, SN-D4).  This is the arm for the `HasTypeDescPi.piElim` constructor:
from the fundamental-theorem conclusions of the function and the argument, conclude the fundamental-theorem
conclusion of the application.

It is the LOWEST-RISK recursive arm — a direct composition of the shipped
`applicationMemberUnderClosingSubstitution` (the FT-shaped Π-elimination member arm) with both sub-conclusions
applied to the SAME closing substitution and the SAME denote-reducible environment, ALL at one uniform ambient
`level`.  No level-bridge, no universe-membership extraction (unlike the conv arm, which needs the target type's
reducibility at the ambient level out of a universe membership at the decoded level).  The function conclusion
delivers a member of the Π type `subst σ (piTyCodeCell domainCode codomainCode)`; the argument conclusion a
member of `subst σ domainCode`; `applicationMemberUnderClosingSubstitution` lands the application in the
substituted dependent codomain `subst σ (subst0 codomainCode argument)` — exactly the `piElim` constructor's
output classifier.

## Zero-axiom verification

`intro` the substitution / environment, then one `applicationMemberUnderClosingSubstitution` fed the two
sub-conclusions instantiated at that substitution and environment.  No induction (the recursion is the FT's, this
is just the arm), no `funext`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or
`omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **The denote `piElim` (application) fundamental-theorem arm.**  Given the fundamental-theorem conclusions of
the function (a member of `Π domainCode codomainCode`) and the argument (a member of `domainCode`), the
application `appCell functionTerm argument` satisfies the fundamental-theorem conclusion at the substituted
dependent codomain `subst0 codomainCode argument`.  A direct composition of
`applicationMemberUnderClosingSubstitution` with both sub-conclusions at the same closing substitution,
environment, and uniform ambient `level` — no level-bridge needed. -/
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
  intro _targetScope substitution envReducible
  exact applicationMemberUnderClosingSubstitution env level
    (functionConclusion substitution envReducible)
    (argumentConclusion substitution envReducible)

end FX1Poly.Typed
