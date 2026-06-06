import FX1Poly.Typed.HasTypeDescPiFormerInversion
import FX1Poly.Typed.UniverseCodeConversion

/-! # FX1Poly/Typed/GrownFormerFormationStrictness
    — the GROWN engine's dependent formers live ABOVE the bottom universe (five-layer-defense L1, 0-FP)

`FormerFormationStrictness` proved the Π/Σ-formation rules are level-tight for the FORMATION engine `HasType`
(`closedPi_notTypedAtZero` etc.).  This file lifts the dependent-former level-strictness to the LIVE grown engine
`HasTypeDescPi`, the companion to `GrownUniverseFormationStrictness` (grown universe strictness) — together they
make the grown engine's whole formation family (universe + Π + Σ) level-strict.

The grown engine carries a SHARPER tool than the formation engine: `HasTypeDescPi.invertPiTyCode` /
`invertSigmaTyCode` EXTRACT the component levels existentially and report the classifier as
`Conv`-equal to `Type@(lmaxAll [domainLevel, codomainLevel])`.  Since `lmaxAll [a, b]` reduces definitionally to
`LevelExpr.lmax a b` (an `lmax`-headed level, never `lzero`), a grown Π/Σ-type code is NEVER classified by the
bottom universe `Type@0` — in ANY context, with ANY components.  This is strictly STRONGER than the formation
engine's closed `closedPi_notTypedAtZero` (which fixes the components to `Type@0` in the empty context): the grown
rejection discards the component typings entirely and refutes the level equation structurally.

  * `HasTypeDescPi.piTyCode_notTypedAtZero` — a Π-type code is NOT grown-typed at `Type@0` at any context with any
    components.  Inverting the (hypothetical) typing exposes the classifier as `Conv` to `Type@(lmax dL cL)`;
    `universeCodeCell_inj_of_conv` reads off `lzero = lmax dL cL`, refuted by `LevelExpr.noConfusion`.
  * `HasTypeDescPi.sigmaTyCode_notTypedAtZero` — the Σ dual.

This holds because the grown `conv` arm uses symmetric `Conv` (structural NF equality on universe codes), not a
`≤`-cumulativity, so a dependent type code does not descend to the bottom universe.  When cumulativity lands
(`@[cumulUpMarker]`, M43), the statement becomes a `≤`-bounded floor.

## Zero-axiom verification

Each rejection inverts the typing with `HasTypeDescPi.invertPiTyCode` / `invertSigmaTyCode` (validity-backed,
zero-axiom), reads off the level equality with `universeCodeCell_inj_of_conv` (confluence + cell injectivity), and
refutes the `lzero = lmax _ _` clash with `LevelExpr.noConfusion` (distinct constructors — `lmaxAll [a, b]` is
definitionally `lmax a b`).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`
(verified by `#print axioms` in scratch before landing).  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **A grown Π-type code is never classified by the bottom universe `Type@0`.**  In any well-formed context, with
ANY domain/codomain codes, `piTyCodeCell domainCode codomainCode` is NOT grown-typed at `universeCodeCell lzero
flag`.  The grown `invertPiTyCode` exposes the true classifier as `Conv` to `Type@(lmax dL cL)`
(`lmaxAll [dL, cL]` reduces to `lmax dL cL`); `universeCodeCell_inj_of_conv` forces `lzero = lmax dL cL`, refuted
structurally by `LevelExpr.noConfusion`.  Strictly stronger than the formation-engine `closedPi_notTypedAtZero`
(any context, any components, no level-pinning). -/
theorem HasTypeDescPi.piTyCode_notTypedAtZero {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (_contextWellFormed : WfContext context)
    (domainCode : RawTerm scope) (codomainCode : RawTerm (scope + 1)) (flag : UniverseFlag) :
    ¬ HasTypeDescPi profile context (piTyCodeCell domainCode codomainCode)
        (universeCodeCell LevelExpr.lzero flag) := by
  intro typed
  obtain ⟨domainLevel, codomainLevel, _convFlag, _domainTyped, _codomainTyped, conv⟩ :=
    HasTypeDescPi.invertPiTyCode typed
  have levelEq : (LevelExpr.lzero : LevelExpr) = LevelExpr.lmax domainLevel codomainLevel :=
    (universeCodeCell_inj_of_conv conv).1
  exact LevelExpr.noConfusion levelEq

/-- **A grown Σ-type code is never classified by the bottom universe `Type@0`** — the Σ dual of
`piTyCode_notTypedAtZero`, via `invertSigmaTyCode`.  Completes the grown dependent-former level-strictness
(Π + Σ), the companion to the grown universe strictness. -/
theorem HasTypeDescPi.sigmaTyCode_notTypedAtZero {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (_contextWellFormed : WfContext context)
    (domainCode : RawTerm scope) (codomainCode : RawTerm (scope + 1)) (flag : UniverseFlag) :
    ¬ HasTypeDescPi profile context (sigmaTyCodeCell domainCode codomainCode)
        (universeCodeCell LevelExpr.lzero flag) := by
  intro typed
  obtain ⟨domainLevel, codomainLevel, _convFlag, _domainTyped, _codomainTyped, conv⟩ :=
    HasTypeDescPi.invertSigmaTyCode typed
  have levelEq : (LevelExpr.lzero : LevelExpr) = LevelExpr.lmax domainLevel codomainLevel :=
    (universeCodeCell_inj_of_conv conv).1
  exact LevelExpr.noConfusion levelEq

end FX1Poly.Typed
