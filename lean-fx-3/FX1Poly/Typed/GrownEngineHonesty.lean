import FX1Poly.Typed.HasTypeDescPiLamInversion
import FX1Poly.Typed.HasTypeDescPiFormerInversion
import FX1Poly.Typed.ConvCodeInjectivity
import FX1Poly.Typed.WfContextDescPi

/-! # FX1Poly/Typed/GrownEngineHonesty
    — 0-FP honesty for the GROWN engine `HasTypeDescPi` (a λ inhabits ONLY a Π type; a type code inhabits ONLY a
    universe)

0-FP honesty for the GROWN engine `HasTypeDescPi` — the engine carrying piIntro/piElim where SN/SR/consistency
live.  This file pins the SHAPE of a classifier from the shape of its subject, rejecting the cross-shape
mismatches structurally.  These are the §1.4 "a function is not a type, a type is not a function"
impossibilities, made precise at the grown engine.

  * `lam_notTypedAtUniverseCode` / `…AtSigmaTyCode` / `…AtVariableCell` — a `lamCell body` (a function value) is
    NEVER typed at a universe code, a Σ-type code, or a variable.  `HasTypeDescPi.invertLam` forces its
    classifier `Conv` to a Π-code `piTyCodeCell …`; the conv-rigidity family
    (`Conv.piTyCode_not_universeCode` / `…_sigmaTyCode` / `…_variableCell`) refutes each non-Π classifier.  So a
    λ inhabits ONLY a Π type — it is not a type (`Type@e`), not a pair-typed thing (`Σ`), not a stuck variable.
  * `piTyCode_notTypedAtPiTyCode` / `sigmaTyCode_notTypedAtPiTyCode` — a Π/Σ-type CODE (a type, an inhabitant of
    some universe) is NEVER typed at a Π type.  `HasTypeDescPi.invertPiTyCode` / `invertSigmaTyCode` force its
    classifier `Conv` to a universe code; `Conv.piTyCode_not_universeCode` refutes a Π-type classifier.  So a
    type code inhabits ONLY a universe — a type is not classified by a function type.

These hold because `conv` uses symmetric `Conv` (no `≤`-cumulativity yet):
a subject's classifier is pinned to its exact shape up to conversion, and the conv-rigidity family makes the
distinct type-code/universe/variable shapes pairwise non-convertible.

## Zero-axiom verification

Each rejection is one grown inversion (`invertLam` / `invertPiTyCode` / `invertSigmaTyCode`) feeding the
`Conv`-witness to a conv-rigidity lemma (with `Conv.sym` to orient the λ cases).  The `invertPiTyCode` /
`invertSigmaTyCode` type-code rejections carry the grown well-formedness `WfContextDescPi` as a shape decoration
(the honesty is over well-formed contexts).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Grown 0-FP: a λ is never typed at a universe code.**  A `lamCell body` inhabits a Π type, not `Type@e` —
`HasTypeDescPi.invertLam` forces its classifier `Conv` to a Π-code, refuted against the universe code by
`Conv.piTyCode_not_universeCode`. -/
theorem lam_notTypedAtUniverseCode {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {body : RawTerm (scope + 1)}
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    ¬ HasTypeDescPi profile context (lamCell body) (universeCodeCell levelExpr flag) := by
  intro typed
  obtain ⟨_domainCode, _codomainCode, _domainLevel, _codomainLevel, _flag, conv, _, _, _⟩ :=
    HasTypeDescPi.invertLam typed
  exact Conv.piTyCode_not_universeCode conv.sym

/-- **Grown 0-FP: a λ is never typed at a Σ-type code** (lambdas inhabit Π, not Σ). -/
theorem lam_notTypedAtSigmaTyCode {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {body : RawTerm (scope + 1)}
    (sigmaDomain : RawTerm scope) (sigmaCodomain : RawTerm (scope + 1)) :
    ¬ HasTypeDescPi profile context (lamCell body) (sigmaTyCodeCell sigmaDomain sigmaCodomain) := by
  intro typed
  obtain ⟨_domainCode, _codomainCode, _domainLevel, _codomainLevel, _flag, conv, _, _, _⟩ :=
    HasTypeDescPi.invertLam typed
  exact Conv.piTyCode_not_sigmaTyCode conv.sym

/-- **Grown 0-FP: a λ is never typed at a variable** (a Π type is a `piTyCodeCell`, never a stuck variable). -/
theorem lam_notTypedAtVariableCell {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {body : RawTerm (scope + 1)}
    (index : Fin scope) :
    ¬ HasTypeDescPi profile context (lamCell body) (variableCell index) := by
  intro typed
  obtain ⟨_domainCode, _codomainCode, _domainLevel, _codomainLevel, _flag, conv, _, _, _⟩ :=
    HasTypeDescPi.invertLam typed
  exact Conv.piTyCode_not_variableCell conv.sym

/-- **Grown 0-FP: a Π-type code is never typed at a Π type.**  A `piTyCodeCell` is a TYPE (an inhabitant of some
universe), not a function — `HasTypeDescPi.invertPiTyCode` forces its classifier `Conv` to a universe code,
refuted against a Π-type classifier by `Conv.piTyCode_not_universeCode`. -/
theorem piTyCode_notTypedAtPiTyCode {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (classifierDomain : RawTerm scope) (classifierCodomain : RawTerm (scope + 1))
    (_contextWellFormed : WfContextDescPi context) :
    ¬ HasTypeDescPi profile context (piTyCodeCell domainCode codomainCode)
        (piTyCodeCell classifierDomain classifierCodomain) := by
  intro typed
  obtain ⟨_domainLevel, _codomainLevel, _flag, _, _, conv⟩ :=
    HasTypeDescPi.invertPiTyCode typed
  exact Conv.piTyCode_not_universeCode conv

/-- **Grown 0-FP: a Σ-type code is never typed at a Π type** (the Σ dual of `piTyCode_notTypedAtPiTyCode`; a
type code inhabits a universe, not a function type). -/
theorem sigmaTyCode_notTypedAtPiTyCode {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (classifierDomain : RawTerm scope) (classifierCodomain : RawTerm (scope + 1))
    (_contextWellFormed : WfContextDescPi context) :
    ¬ HasTypeDescPi profile context (sigmaTyCodeCell domainCode codomainCode)
        (piTyCodeCell classifierDomain classifierCodomain) := by
  intro typed
  obtain ⟨_domainLevel, _codomainLevel, _flag, _, _, conv⟩ :=
    HasTypeDescPi.invertSigmaTyCode typed
  exact Conv.piTyCode_not_universeCode conv

end FX1Poly.Typed
