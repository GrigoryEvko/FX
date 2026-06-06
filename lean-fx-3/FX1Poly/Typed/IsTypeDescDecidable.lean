import FX1Poly.Typed.IsTypeDescRigidity
import FX1Poly.Typed.WfContextDescUniqueness
import FX1Poly.Typed.UniverseCodeConversion
import FX1Poly.Typed.UniverseCodeShape
import FX1Poly.Typed.SigmaCodeShape

/-! # FX1Poly/Typed/IsTypeDescDecidable
    — concrete-children former-code inversions for the formation engine (off old `HasType`)

This file once carried the bespoke `IsTypeDesc.decideWithWitness` / `IsTypeDesc.decidableOfWellFormed`
type-hood decider — a `RawTerm.size` recursion with HAND-WRITTEN Π / Σ branches plus a
`typingRuleDescOf_isPiOrSigma` enumeration `else`.  That cascade decider has been RETIRED in favour of the
fully cascade-free structural-mutual decider `IsTypeDesc.decideTypeGeneric`
(`IsTypeDescDecidableGeneric.lean`), which absorbs any future formation row zero-touch.

What remains here are the two CONCRETE-CHILDREN former-code inversions — `WfContext`-free, keeping the
`domainCode` / `codomainCode` concrete (unlike the generic `DescTelescope.twoChildComponents` and the generic
`HasTypeDesc.inversionFormerWithConvGeneric`, which existentially repack the children).  They state the clean
metatheory fact that a typed `piTyCodeCell` / `sigmaTyCodeCell` has both children typed at universe codes at a
shared flag, and are retained as a reusable inversion API for the dependent type-formers.

## Zero-axiom verification

Each inversion destructs the native `HasTypeDesc.inversionPiCode` / `inversionSigmaCode` telescope over the
concrete two-child spine: the child index pins each `cons` head to the concrete child and refutes the closing
`nil` arms definitionally (the propext-clean discipline of `twoChildComponents`).  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Concrete-children inversion for a Π-type code.**  A `piTyCodeCell domainCode codomainCode` typed by the
formation engine has its two children typed at universe codes — `domainCode` at `Type@(domainLevel, flag)` in
`context`, `codomainCode` at `Type@(codomainLevel, flag)` under the domain binder — at a SHARED `flag`.  Unlike
the generic `DescTelescope.twoChildComponents` (which existentially repacks the children), this keeps
`domainCode` / `codomainCode` concrete.

Destructs the `HasTypeDesc.inversionPiCode` telescope over the concrete `binderShape domainCode codomainCode`
spine: each `cons` head is pinned to the concrete child by the `RawTermChildren` index, and the closing `nil`
is forced, so the nested `cases` is propext-clean (same discipline as `twoChildComponents`). -/
theorem HasTypeDesc.inversionPiCodeChildren {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)} {classifier : RawTerm scope}
    (typed : HasTypeDesc profile context (piTyCodeCell domainCode codomainCode) classifier) :
    ∃ (domainLevel codomainLevel : LevelExpr) (flag : UniverseFlag),
      HasTypeDesc profile context domainCode (universeCodeCell domainLevel flag)
        ∧ HasTypeDesc profile (context.cons domainCode) codomainCode
            (universeCodeCell codomainLevel flag) := by
  obtain ⟨_levels, flag, telescope⟩ := HasTypeDesc.inversionPiCode typed
  cases telescope with
  | cons _context _head domainLevel _restLevels _flag _rest domainTyped restTelescope =>
      cases restTelescope with
      | cons _context2 _head2 codomainLevel _restLevels2 _flag2 _rest2 codomainTyped _tailTelescope =>
          exact ⟨domainLevel, codomainLevel, flag, domainTyped, codomainTyped⟩

/-- **Concrete-children inversion for a Σ-type code** — the Σ mirror of `inversionPiCodeChildren`, over
`HasTypeDesc.inversionSigmaCode` and the `sigmaTyCodeCell` spine.  Identical recipe; only the former changes. -/
theorem HasTypeDesc.inversionSigmaCodeChildren {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)} {classifier : RawTerm scope}
    (typed : HasTypeDesc profile context (sigmaTyCodeCell domainCode codomainCode) classifier) :
    ∃ (domainLevel codomainLevel : LevelExpr) (flag : UniverseFlag),
      HasTypeDesc profile context domainCode (universeCodeCell domainLevel flag)
        ∧ HasTypeDesc profile (context.cons domainCode) codomainCode
            (universeCodeCell codomainLevel flag) := by
  obtain ⟨_levels, flag, telescope⟩ := HasTypeDesc.inversionSigmaCode typed
  cases telescope with
  | cons _context _head domainLevel _restLevels _flag _rest domainTyped restTelescope =>
      cases restTelescope with
      | cons _context2 _head2 codomainLevel _restLevels2 _flag2 _rest2 codomainTyped _tailTelescope =>
          exact ⟨domainLevel, codomainLevel, flag, domainTyped, codomainTyped⟩

end FX1Poly.Typed
