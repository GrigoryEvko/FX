import FX1Poly.Typed.HasTypeDescPiFormationCodomainReTyping
import FX1Poly.Typed.HasTypeDescPiFormerCongruence

/-! # FX1Poly/Typed/HasTypeDescPiFormerStepDomainFormationCodomain
    — the unconditional former-DOMAIN subject reduction for a FORMATION codomain (toward SN-055)

The former-domain SR congruence `HasTypeDescPi.congPiDomain` / `congSigmaDomain` is conditional on a
`codomainReTyping` (the deferred grown context-conversion).  For the COMMON case — a Π/Σ-former whose codomain
is a FORMATION type — `HasTypeDescPiFormationCodomainReTyping.formationCodomainReTyping` discharges that
re-typing UNCONDITIONALLY.  This file COMPLETES the former-domain SR for that case: given the stepped domain's
typing and the codomain's FORMATION typing, the former with the stepped domain types at the canonical formation
output `Type@(lmax domainLevel codomainLevel)`.

It is the directly-usable rebuild the SR dispatcher's former-domain case will invoke for formation codomains:
`{pi,sigma}FormationViaGenArm` reassembles the former from the stepped domain and the re-typed codomain, with no
appeal to the multi-fire mutual bundle.  The dispatcher converts the result to the former's original classifier
via the `Conv` that `invertPiTyCode` returns (the classifier is `Conv` to this canonical universe code).

## Zero-axiom verification

A direct `{pi,sigma}FormationViaGenArm` applied to the stepped domain + `formationCodomainReTyping`.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **Former-domain SR for a Π-former with a FORMATION codomain.**  When a Π-former's domain steps
`domainCode ⤳ domainCode'` (so `Conv domainCode domainCode'`, and the stepped domain re-types at the same
universe via `domainStepped`), and the codomain is FORMATION-typed at a universe, the former with the stepped
domain types at the canonical output `Type@(lmax domainLevel codomainLevel)` — UNCONDITIONALLY (no grown
context-conversion bundle), by reassembling through `piFormationViaGenArm` + `formationCodomainReTyping`. -/
theorem HasTypeDescPi.piFormerStepDomainFormationCodomain {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode domainCode' : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainLevel codomainLevel : LevelExpr} {flag : UniverseFlag}
    (domainStepped : HasTypeDescPi profile context domainCode' (universeCodeCell domainLevel flag))
    (codomainFormationTyped :
      HasTypeDesc profile (context.cons domainCode) codomainCode
        (universeCodeCell codomainLevel flag))
    (convDomains : Conv domainCode domainCode') :
    HasTypeDescPi profile context (piTyCodeCell domainCode' codomainCode)
      (universeCodeCell (LevelExpr.lmax domainLevel codomainLevel) flag) :=
  HasTypeDescPi.piFormationViaGenArm context domainCode' codomainCode domainLevel codomainLevel
    flag domainStepped
    (HasTypeDescPi.formationCodomainReTyping codomainFormationTyped convDomains)

/-- **Former-domain SR for a Σ-former with a FORMATION codomain** — the Σ dual of
`piFormerStepDomainFormationCodomain`, via `sigmaFormationViaGenArm`. -/
theorem HasTypeDescPi.sigmaFormerStepDomainFormationCodomain {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode domainCode' : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainLevel codomainLevel : LevelExpr} {flag : UniverseFlag}
    (domainStepped : HasTypeDescPi profile context domainCode' (universeCodeCell domainLevel flag))
    (codomainFormationTyped :
      HasTypeDesc profile (context.cons domainCode) codomainCode
        (universeCodeCell codomainLevel flag))
    (convDomains : Conv domainCode domainCode') :
    HasTypeDescPi profile context (sigmaTyCodeCell domainCode' codomainCode)
      (universeCodeCell (LevelExpr.lmax domainLevel codomainLevel) flag) :=
  HasTypeDescPi.sigmaFormationViaGenArm context domainCode' codomainCode domainLevel codomainLevel
    flag domainStepped
    (HasTypeDescPi.formationCodomainReTyping codomainFormationTyped convDomains)

end FX1Poly.Typed
