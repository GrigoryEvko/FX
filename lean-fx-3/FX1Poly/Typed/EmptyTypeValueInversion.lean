import FX1Poly.Typed.HasTypeDescPiLamInversion
import FX1Poly.Typed.HasTypeDescPiFormerInversion
import FX1Poly.Typed.HasTypeDescPiUniverseCodeInversion
import FX1Poly.Typed.EmptyTypeCodeConvRigidity

/-! # FX1Poly/Typed/EmptyTypeValueInversion — no canonical VALUE is typed at the empty type, SN-FREE.

The grown engine `HasTypeDescPi` introduces exactly three canonical values: a λ (`piIntro`, classified
by a Π-code), a Π-type former, and a Σ-type former (`genFormationPi`, classified by a universe code).
This file proves NONE of them can be typed at `emptyTypeCell`: peeling the `conv` rule, a λ's classifier
is `Conv` a Π-code and a former's classifier is `Conv` a universe code, and neither is `Conv`-equal to
`emptyTypeCell` (`EmptyTypeCodeConvRigidity`).

These are the VALUE-CASE inversions of the consistency argument: combined with strong normalization and
subject reduction (the SR dispatcher, SN-055), a closed term of the empty type would reduce to a closed
value of the empty type — which this file rules out.  Banked SN-free ahead of the SR dispatcher, exactly
as `ConvCodeInjectivity` banked the Π/Σ rigidity.  The typing-layer companion to the reducibility-side
`emptyHasNoClosedMember` (#680) and the `Conv`-layer rigidity (`Conv.piTyCode_not_emptyTypeCode` etc.).

## Zero-axiom

`HasTypeDescPi.invertLam` / `invertPiTyCode` / `invertSigmaTyCode` (the shipped grown inversions) +
`Conv.sym` + the `EmptyTypeCodeConvRigidity` disjointness lemmas.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Audit-gated.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **A λ is never typed at the empty type.**  `invertLam` exposes the λ's classifier as `Conv` a Π-code;
`Conv.piTyCode_not_emptyTypeCode` refutes that against `emptyTypeCell`.  No well-formedness needed (the λ
inversion is context-free). -/
theorem HasTypeDescPi.lambdaNotTypedAtEmptyType {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {body : RawTerm (scope + 1)}
    (typed : HasTypeDescPi profile context (lamCell body) (emptyTypeCell (scope := scope))) :
    False := by
  obtain ⟨_domainCode, _codomainCode, _domainLevel, _codomainLevel, _flag,
      convToPiCode, _domainTyped, _codomainTyped, _bodyTyped⟩ := HasTypeDescPi.invertLam typed
  exact Conv.piTyCode_not_emptyTypeCode convToPiCode.sym

/-- **A Π-type former is never typed at the empty type.**  `invertPiTyCode` exposes the former's
classifier as `Conv` a universe code; `Conv.universeCode_not_emptyTypeCode` refutes that against
`emptyTypeCell`.  Requires `WfContext` (the former inversion's well-formedness premise). -/
theorem HasTypeDescPi.piFormerNotTypedAtEmptyType {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (typed :
      HasTypeDescPi profile context (piTyCodeCell domainCode codomainCode)
        (emptyTypeCell (scope := scope)))
    (wellFormed : WfContext context) :
    False := by
  obtain ⟨_domainLevel, _codomainLevel, _flag, _domainTyped, _codomainTyped, convToUniverseCode⟩ :=
    HasTypeDescPi.invertPiTyCode typed
  exact Conv.universeCode_not_emptyTypeCode convToUniverseCode.sym

/-- **A Σ-type former is never typed at the empty type** — the Σ dual of
`HasTypeDescPi.piFormerNotTypedAtEmptyType`. -/
theorem HasTypeDescPi.sigmaFormerNotTypedAtEmptyType {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (typed :
      HasTypeDescPi profile context (sigmaTyCodeCell domainCode codomainCode)
        (emptyTypeCell (scope := scope)))
    (wellFormed : WfContext context) :
    False := by
  obtain ⟨_domainLevel, _codomainLevel, _flag, _domainTyped, _codomainTyped, convToUniverseCode⟩ :=
    HasTypeDescPi.invertSigmaTyCode typed
  exact Conv.universeCode_not_emptyTypeCode convToUniverseCode.sym

/-- **A universe code is never typed at the empty type** — completing the value-case family.  A universe
code `Type@(e, flag)`'s classifier is `Conv` the next universe `Type@(lsucc e, flag)`
(`HasTypeDescPi.inversionUniverseCode`), which is not `Conv`-equal to `emptyTypeCell`.  With λ / Π-former /
Σ-former / universe-code covered, NO canonical value the grown engine types is typed at the empty type. -/
theorem HasTypeDescPi.universeCodeNotTypedAtEmptyType {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {levelExpr : LevelExpr} {flag : UniverseFlag}
    (typed :
      HasTypeDescPi profile context (universeCodeCell levelExpr flag)
        (emptyTypeCell (scope := scope)))
    (wellFormed : WfContext context) :
    False :=
  Conv.universeCode_not_emptyTypeCode
    (HasTypeDescPi.inversionUniverseCode typed wellFormed).sym

end FX1Poly.Typed
