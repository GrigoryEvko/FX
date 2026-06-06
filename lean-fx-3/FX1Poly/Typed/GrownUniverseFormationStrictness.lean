import FX1Poly.Typed.HasTypeDescPiUniverseCodeInversion
import FX1Poly.Typed.UniverseCodeConversion
import FX1Poly.Typed.WfContextDescPi

/-! # FX1Poly/Typed/GrownUniverseFormationStrictness
    — the GROWN engine is LEVEL-TIGHT: no Type-in-Type (five-layer-defense L1, §27.2/§1.4)

The universe rule is level-tight for the GROWN engine `HasTypeDescPi` — the one carrying the `piIntro` /
`piElim` arms through which a `Type:Type` paradox would actually encode a fixpoint.  This file establishes the
level-strictness corpus on `HasTypeDescPi`, so the §1.4 / §27.2 "Type:Type / Girard's-paradox structurally
impossible" claim holds for the engine that matters.

The grown engine has its own universe-code inversion `HasTypeDescPi.inversionUniverseCode` (any classifier of
`Type@e` is `Conv` to `Type@(e+1)`); composed with `universeCodeCell_inj_of_conv` (convertible universe codes have
syntactically equal levels) and the predicativity guards `LevelExpr.ne_lsucc_self` / `ne_lsuccLsucc_self`, it
rejects every level mismatch in the grown engine exactly as the formation engine does.

  * `HasTypeDescPi.universeCode_notTypedAtSelf` — **no Type-in-Type.**  `Type@e` is NOT
    grown-typed at `Type@e` at ANY level in ANY well-formed context.  A self-classified universe forces
    `e = lsucc e`, refuted by `LevelExpr.ne_lsucc_self`.  The headline §1.4 Girard rejection for `HasTypeDescPi`.
  * `HasTypeDescPi.universeCode_notTypedAboveSuccessor` — **no level inflation.**  `Type@e` is NOT grown-typed at
    `Type@(e+2)` — only at `Type@(e+1)`.  Forces `lsucc (lsucc e) = lsucc e`.
  * `HasTypeDescPi.universeCode_notTypedBelowSuccessor` — **no level deflation.**  `Type@(e+1)` is NOT grown-typed
    at `Type@e` — only at `Type@(e+2)`.  Forces `e = lsucc (lsucc e)`, refuted by `ne_lsuccLsucc_self`.

This holds because the grown `conv` arm uses symmetric `Conv`, not a
`≤`-cumulativity, so a universe code neither climbs nor descends.  When cumulativity lands
(`@[cumulUpMarker]`), the over-shoot rejection becomes a `≤`-bounded statement.

## Zero-axiom verification

Each rejection inverts the (hypothetical) grown typing with `HasTypeDescPi.inversionUniverseCode` (validity-backed,
zero-axiom), reads off the level equality with `universeCodeCell_inj_of_conv` (confluence + cell injectivity), and
refutes it with the size-free predicativity guards `LevelExpr.ne_lsucc_self` / `ne_lsuccLsucc_self`.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega` (verified by `#print axioms` in scratch
before landing).  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **No Type-in-Type for the grown engine.**  `Type@e` is NOT grown-typed at `Type@e` at ANY level
in ANY well-formed context — the universe sits strictly above itself everywhere.  The §1.4 "Type:Type / Girard's
paradox structurally impossible" claim for `HasTypeDescPi` (the all-context form is
`universeCode_notTypedAtSelf_general`): a self-classified universe forces `e = lsucc e`, refuted by the
predicativity guard `LevelExpr.ne_lsucc_self`. -/
theorem HasTypeDescPi.universeCode_notTypedAtSelf {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (_contextWellFormed : WfContextDescPi context)
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    ¬ HasTypeDescPi profile context (universeCodeCell levelExpr flag)
        (universeCodeCell levelExpr flag) := by
  intro typed
  have conv : Conv (universeCodeCell levelExpr flag : RawTerm scope)
      (universeCodeCell levelExpr.lsucc flag) :=
    HasTypeDescPi.inversionUniverseCode typed
  exact absurd (universeCodeCell_inj_of_conv conv).1 (LevelExpr.ne_lsucc_self levelExpr)

/-- **No level inflation for the grown engine.**  `Type@e` is NOT grown-typed at `Type@(e+2)` at ANY level in ANY
well-formed context — only at `Type@(e+1)`.  The inversion forces `lsucc (lsucc e) = lsucc e`, refuted by
`LevelExpr.ne_lsucc_self` at `lsucc e`. -/
theorem HasTypeDescPi.universeCode_notTypedAboveSuccessor {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (_contextWellFormed : WfContextDescPi context)
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    ¬ HasTypeDescPi profile context (universeCodeCell levelExpr flag)
        (universeCodeCell levelExpr.lsucc.lsucc flag) := by
  intro typed
  have conv : Conv (universeCodeCell levelExpr.lsucc.lsucc flag : RawTerm scope)
      (universeCodeCell levelExpr.lsucc flag) :=
    HasTypeDescPi.inversionUniverseCode typed
  exact absurd (universeCodeCell_inj_of_conv conv).1 (LevelExpr.ne_lsucc_self levelExpr.lsucc).symm

/-- **No level deflation for the grown engine.**  `Type@(e+1)` is NOT grown-typed at `Type@e` at ANY level in ANY
well-formed context — only at `Type@(e+2)`.  Inverting the subject `Type@(e+1)` forces its classifier `Type@e` to
convert to `Type@(e+2)`, i.e. `e = lsucc (lsucc e)`, refuted by the double-successor predicativity guard
`LevelExpr.ne_lsuccLsucc_self`.  Completes the grown level-strictness corpus (self / above / below), parallel to
the formation engine's. -/
theorem HasTypeDescPi.universeCode_notTypedBelowSuccessor {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (_contextWellFormed : WfContextDescPi context)
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    ¬ HasTypeDescPi profile context (universeCodeCell levelExpr.lsucc flag)
        (universeCodeCell levelExpr flag) := by
  intro typed
  have conv : Conv (universeCodeCell levelExpr flag : RawTerm scope)
      (universeCodeCell levelExpr.lsucc.lsucc flag) :=
    HasTypeDescPi.inversionUniverseCode typed
  exact absurd (universeCodeCell_inj_of_conv conv).1 (LevelExpr.ne_lsuccLsucc_self levelExpr)

end FX1Poly.Typed
