import FX1Poly.Typed.HasTypeDescPiContextConversion
import FX1Poly.Core.ConvSubstRename
import FX1Poly.Core.RawConfluence

/-! # FX1Poly/Typed/HasTypeDescPiFormationCodomainReTyping
    — re-typing a FORMATION codomain under a `Conv`-stepped domain (the dischargeable half of the
      former-domain SR `codomainReTyping`, toward SN-055)

The former-DOMAIN subject-reduction congruence (`HasTypeDescPi.congPiDomain` / `congSigmaDomain`) takes a
`codomainReTyping` hypothesis: when a Π/Σ-former's domain steps `domain ⤳ domain'`, the codomain — typed under
`cons domain` — must be re-typed under `cons domain'`.  That re-typing is the grown context-conversion (#814),
whose full form is part of the mutual fundamental-metatheory bundle (a multi-fire development) — EXCEPT for the
COMMON case where the codomain is a FORMATION type (a variable, a universe code, or a former over formation
children).  For a formation codomain the part-2a `HasTypeDescPi.convContextOfFormation` discharges it
UNCONDITIONALLY, with no appeal to the deferred grown core.

This file ships exactly that discharge: given the codomain's FORMATION typing at a universe code and the
domains' `Conv` (which a `Step domain domain'` supplies), re-type the codomain under the stepped domain.  It is
the directly-usable form the SR dispatcher's former-domain case will consume for formation codomains, isolating
the residual to the genuinely grown-codomain case (a type-level application/λ in the codomain).

## Recipe (SR-free, the part-2a unblocker)

Build the pointwise context-`Conv` between `cons domain` and `cons domain'`: at index `0` the (weakened)
entries are `domain` / `domain'`, related by `Conv.rename weaken convDomains`; at successors the entries are
identical (`Conv.refl`).  Feed that to `convContextOfFormation` (the formation typing context-converts to a
`Conv`-equal classifier under `cons domain'`), then `convBackToUniverseCode` pins the classifier back to the
original universe code.

## Zero-axiom verification

`convContextOfFormation` + `convBackToUniverseCode` + `Conv.rename` / `Conv.refl` + the `lookup_cons_*`
definitional unfolders.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **Re-type a FORMATION codomain under a `Conv`-stepped domain.**  If `codomainCode` is FORMATION-typed at a
universe code under `cons domainCode`, and `domainCode` is `Conv`-equal to `domainCode'` (as a domain step
supplies), then `codomainCode` is grown-typed at the SAME universe code under `cons domainCode'`.  This
discharges the `codomainReTyping` hypothesis of `congPiDomain` / `congSigmaDomain` for the common
formation-codomain case, unconditionally — the deferred grown context-conversion (#814) is needed only when the
codomain is itself a grown type. -/
theorem HasTypeDescPi.formationCodomainReTyping {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode domainCode' : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {codomainLevel : LevelExpr} {codomainFlag : UniverseFlag}
    (codomainFormationTyped :
      HasTypeDesc profile (context.cons domainCode) codomainCode
        (universeCodeCell codomainLevel codomainFlag))
    (convDomains : Conv domainCode domainCode') :
    HasTypeDescPi profile (context.cons domainCode') codomainCode
      (universeCodeCell codomainLevel codomainFlag) := by
  have contextConv : ∀ index : Fin (scope + 1),
      Conv ((context.cons domainCode).lookup index)
           ((context.cons domainCode').lookup index) := by
    intro index
    rcases index with ⟨value, isLt⟩
    cases value with
    | zero =>
        rw [TypingContext.lookup_cons_zero, TypingContext.lookup_cons_zero]
        exact Conv.rename RawRenaming.weaken convDomains
    | succ k =>
        rw [TypingContext.lookup_cons_succ, TypingContext.lookup_cons_succ]
        exact Conv.refl _
  obtain ⟨convertedClassifier, classifierConverts, codomainUnderTarget⟩ :=
    HasTypeDescPi.convContextOfFormation codomainFormationTyped (context.cons domainCode') contextConv
  exact HasTypeDescPi.convBackToUniverseCode codomainUnderTarget classifierConverts

end FX1Poly.Typed
