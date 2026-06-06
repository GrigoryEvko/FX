import FX1Poly.Typed.HasTypeDescPiUniverseCodeInversion
import FX1Poly.Typed.UniverseCodeConversion
import FX1Poly.Typed.ClassifierLevelMeasure

/-! # FX1Poly/Typed/GrownNoTypeInType
    — the grown engine is PREDICATIVE: no universe is a member of itself (§27.2 / SN-140 L1)

`Type : Type` (Girard's paradox) is the canonical type-theory unsoundness — a universe that contains
itself collapses the hierarchy and makes every type inhabited (fx_design §27.2 catalogs it among the
known-unsoundness corpus that the five-layer defense rejects, §27.3 L1).  FX is predicative: the
universe-formation rule sends `Type@(e, flag)` to `Type@(e+1, flag)`, strictly one level up.  This file
ships the metatheoretic GUARANTEE that the grown engine actually rejects `Type : Type` — not merely that
the formation rule moves up a level, but that NO derivation by ANY route (formation, conversion,
elimination) can type a universe code at itself.

## The witnesses (a coherent predicativity mini-corpus)

* `HasTypeDescPi.universeClassifierLevelIsSucc` — the full predicativity inversion: if `Type@(e, flag)` is
  grown-typed at another universe code `Type@(e', flag')`, then `e' = e+1 ∧ flag' = flag`.  The classifier
  level is FORCED to the successor — never `e` itself, never lower.
* `HasTypeDescPi.noUniverseInItself` — the §27.2 Girard rejection: `Type@(e, flag) : Type@(e, flag)` is
  underivable in any well-formed context.  Specialises the inversion at `e' = e`, refuted by the
  predicativity guard `LevelExpr.ne_lsucc_self` (`e ≠ e+1`).
* `HasTypeDescPi.noClosedUniverseInItself` — the closed corollary at `Γ = .empty`
  (`WfContext.emptyIsWellFormed`), the concrete permanent regression witness.

## Why this is non-vacuous

The guarantee is against the WHOLE grown engine, not the formation rule alone: it routes through
`HasTypeDescPi.inversionUniverseCode` (the grown universe-code inversion, which inverts ANY derivation of a
universe code — including `conv` re-classifications — back to the successor universe).  So `Type@e` cannot
sneak a self-typing through conversion either.  The §27.3 L1 discipline: every cataloged unsoundness
becomes a permanent rejected test; this is the `Type : Type` entry for the grown engine.

## Zero-axiom verification

Three-step assembly of shipped, gated lemmas: `inversionUniverseCode` (the grown universe inversion) +
`universeCodeCell_inj_of_conv` (a Conv between universe codes forces level + flag equality) +
`LevelExpr.ne_lsucc_self` (predicativity: `e ≠ e+1`).  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Predicativity inversion.**  If the universe code `Type@(e, flag)` is grown-typed at another universe
code `Type@(e', flag')` (in a well-formed context), the classifier level is forced to the successor:
`e' = e+1 ∧ flag' = flag`.  The classifier of a universe is never the universe itself, never lower —
the grown engine is strictly predicative.  Composes the grown universe inversion with universe-code
injectivity-under-Conv. -/
theorem HasTypeDescPi.universeClassifierLevelIsSucc {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {levelExpr classifierLevel : LevelExpr} {flag classifierFlag : UniverseFlag}
    (typed : HasTypeDescPi profile context (universeCodeCell levelExpr flag)
      (universeCodeCell classifierLevel classifierFlag))
    (wellFormed : WfContext context) :
    classifierLevel = levelExpr.lsucc ∧ classifierFlag = flag :=
  universeCodeCell_inj_of_conv (typed.inversionUniverseCode wellFormed)

/-- **★ No `Type : Type` (§27.2 Girard rejection).**  No universe code is grown-typed at ITSELF, in any
well-formed context: `HasTypeDescPi Γ (universeCodeCell e flag) (universeCodeCell e flag) → False`.  The
predicativity inversion forces the self-classifier level to be `e+1`, refuted by `e ≠ e+1`.  The grown
engine rejects the precondition of Girard's paradox by ANY derivation route, not the formation rule alone
(the inversion covers conversion re-classifications). -/
theorem HasTypeDescPi.noUniverseInItself {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {levelExpr : LevelExpr} {flag : UniverseFlag}
    (typed : HasTypeDescPi profile context (universeCodeCell levelExpr flag)
      (universeCodeCell levelExpr flag))
    (wellFormed : WfContext context) :
    False :=
  LevelExpr.ne_lsucc_self levelExpr (typed.universeClassifierLevelIsSucc wellFormed).1

/-- **No `Type : Type` at the empty context** — the closed permanent regression witness, specialising
`noUniverseInItself` at `Γ = .empty` via `WfContext.emptyIsWellFormed`. -/
theorem HasTypeDescPi.noClosedUniverseInItself {profile : PolyProfile}
    {levelExpr : LevelExpr} {flag : UniverseFlag}
    (typed : HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0)
      (universeCodeCell levelExpr flag) (universeCodeCell levelExpr flag)) :
    False :=
  HasTypeDescPi.noUniverseInItself typed WfContext.emptyIsWellFormed

/-- **The universe hierarchy is SEMANTICALLY strict.**  If `Type@(e, flag)` is grown-typed at another
universe code `Type@(e', flag')`, then `e` denotes to a STRICTLY SMALLER level than `e'`, in every level
environment: `denote e env < denote e' env`.  The semantic predicativity — a universe genuinely sits below
its own classifier universe (no level cycle, no fixpoint).  Strengthens the syntactic
`universeClassifierLevelIsSucc` (`e' = e+1`) to the semantic order via `denote_lt_lsucc` (the SN-003
predicative-decrease fact `denote e env < denote (e+1) env`).  `noUniverseInItself` is the degenerate
`e' = e` case (a level cannot be `< itself`). -/
theorem HasTypeDescPi.universeStrictlyBelowClassifierLevel {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {levelExpr classifierLevel : LevelExpr} {flag classifierFlag : UniverseFlag} (env : Nat → Nat)
    (typed : HasTypeDescPi profile context (universeCodeCell levelExpr flag)
      (universeCodeCell classifierLevel classifierFlag))
    (wellFormed : WfContext context) :
    LevelExpr.denote levelExpr env < LevelExpr.denote classifierLevel env := by
  rw [(typed.universeClassifierLevelIsSucc wellFormed).1]
  exact denote_lt_lsucc levelExpr env

end FX1Poly.Typed
