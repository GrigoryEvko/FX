import FX1Poly.Typed.HasTypeDescPiUniverseCodeInversion
import FX1Poly.Typed.UniverseCodeConversion

/-! # FX1Poly/Typed/GrownUniverseConsistency
    — universe consistency for the GROWN engine `HasTypeDescPi`: no `Type : Type`, no inflation, no deflation,
      flag rigidity (SN-140 L1, the §27.2 Girard's-paradox known-unsoundness witness at the grown engine)

`UniverseFormationStrictness` pinned the level-strictness corpus (`universeCode_notTypedAtSelf_general` /
`…AboveSuccessor_general` / `…BelowSuccessor_general`) for the FORMATION engine `HasType`.  This file is the
GROWN-engine (`HasTypeDescPi` — the engine carrying piIntro/piElim, where SN/SR/consistency live) parity twin
plus a novel flag-rigidity probe: the predicative universe discipline holds structurally at the engine the
kernel's metatheory actually runs on.  These are the §11.8.2 universe-consistency guarantees — no `Type : Type`,
hence no Girard paradox at the universe level (§27.2 "Dependent type (Type:Type / Girard's paradox)").

Each rejection reads off the single shipped grown inversion `HasTypeDescPi.inversionUniverseCode`: a universe
code `Type@(e, flag)` receives ONLY classifiers `Conv`-equal to its strict predicative successor
`Type@(lsucc e, flag)`.  `universeCodeCell_inj_of_conv` (confluence + cell injectivity, no SN premise) collapses
that `Conv` to level + flag equality; the predicativity guards `LevelExpr.ne_lsucc_self` (`e ≠ lsucc e`) and
`LevelExpr.ne_lsuccLsucc_self` (`e ≠ lsucc (lsucc e)`) refute the level mis-classifications, and the flag
component refutes the flag mismatch.  The universe rule's `conv` uses symmetric `Conv`, not `≤`-cumulativity,
so a grown universe code neither climbs nor descends nor changes flag.

  * `grownUniverseCode_notTypedAtSelf` — **no `Type : Type`.**  `Type@(e, f)` is NOT classified by itself: that
    would force `e = lsucc e` (`ne_lsucc_self`).  The headline universe-consistency / no-Girard guarantee.
  * `grownUniverseCode_notTypedAboveSuccessor` — **no inflation.**  `Type@(e, f)` is NOT classified by
    `Type@(lsucc (lsucc e), f)` (two levels up): that would force `lsucc (lsucc e) = lsucc e` (`ne_lsucc_self` at
    `lsucc e`).  A universe never floats above its unique successor classifier.
  * `grownUniverseCode_notTypedBelowSuccessor` — **no deflation.**  The successor universe `Type@(lsucc e, f)`
    is NOT classified by the base `Type@(e, f)`: that would force `e = lsucc (lsucc e)` (`ne_lsuccLsucc_self`).
    A universe never sinks into a strictly-lower one.
  * `grownUniverseCode_notTypedAtFlagMismatchedSuccessor` — **flag rigidity** (novel; no formation twin).  When
    `f1 ≠ f2`, `Type@(e, f1)` is NOT classified by the flag-mismatched successor `Type@(lsucc e, f2)`: universe
    formation preserves the admission FLAG, so `universeCodeCell_inj_of_conv` exposes `f2 = f1`, refuting `f1 ≠ f2`.

The well-formed context is `inversionUniverseCode`'s presupposition; the empty context
(`WfContext.emptyIsWellFormed`) already instantiates it, so each probe is NON-vacuous.  Together with
`GrownEngineHonesty` (a λ inhabits only Π; a type code only a universe) this completes the grown engine's 0-FP
shape/level/flag discipline, in parity with the formation engine's.

## Zero-axiom verification

Each rejection is one `inversionUniverseCode` feeding its `Conv` witness to `universeCodeCell_inj_of_conv`, then
a predicativity guard (`ne_lsucc_self` / `ne_lsuccLsucc_self`) or the flag component via `absurd`.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Grown no-`Type : Type` (the Girard's-paradox rejection).**  A universe code `Type@(e, flag)` is never
classified by itself in the grown engine — `inversionUniverseCode` forces any classifier `Conv`-equal to its
strict predicative successor `Type@(lsucc e, flag)`, so self-classification forces `e = lsucc e`, refuted by
`ne_lsucc_self`.  The grown twin of `universeCode_notTypedAtSelf_general`. -/
theorem grownUniverseCode_notTypedAtSelf {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} (_contextWellFormed : WfContext context)
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    ¬ HasTypeDescPi profile context (universeCodeCell levelExpr flag)
        (universeCodeCell levelExpr flag) := by
  intro typed
  have conv : Conv (universeCodeCell levelExpr flag : RawTerm scope)
      (universeCodeCell levelExpr.lsucc flag) :=
    HasTypeDescPi.inversionUniverseCode typed
  exact absurd (universeCodeCell_inj_of_conv conv).1 (LevelExpr.ne_lsucc_self levelExpr)

/-- **Grown no-inflation.**  `Type@(e, flag)` is NOT classified by `Type@(lsucc (lsucc e), flag)` (two predicative
levels up) — only by `Type@(lsucc e, flag)`.  The inversion forces `lsucc (lsucc e) = lsucc e`, refuted by
`ne_lsucc_self` at `lsucc e`.  The grown twin of `universeCode_notTypedAboveSuccessor_general`. -/
theorem grownUniverseCode_notTypedAboveSuccessor {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} (_contextWellFormed : WfContext context)
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    ¬ HasTypeDescPi profile context (universeCodeCell levelExpr flag)
        (universeCodeCell levelExpr.lsucc.lsucc flag) := by
  intro typed
  have conv : Conv (universeCodeCell levelExpr.lsucc.lsucc flag : RawTerm scope)
      (universeCodeCell levelExpr.lsucc flag) :=
    HasTypeDescPi.inversionUniverseCode typed
  exact absurd (universeCodeCell_inj_of_conv conv).1 (LevelExpr.ne_lsucc_self levelExpr.lsucc).symm

/-- **Grown no-deflation.**  The successor universe `Type@(lsucc e, flag)` is NOT classified by the base
universe `Type@(e, flag)` — the base sits two predicative levels below its true classifier
`Type@(lsucc (lsucc e), flag)`.  The inversion forces `e = lsucc (lsucc e)`, refuted by `ne_lsuccLsucc_self`.
A universe never sinks into a strictly-lower one.  The grown twin of
`universeCode_notTypedBelowSuccessor_general`. -/
theorem grownUniverseCode_notTypedBelowSuccessor {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} (_contextWellFormed : WfContext context)
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    ¬ HasTypeDescPi profile context (universeCodeCell levelExpr.lsucc flag)
        (universeCodeCell levelExpr flag) := by
  intro typed
  have conv : Conv (universeCodeCell levelExpr flag : RawTerm scope)
      (universeCodeCell levelExpr.lsucc.lsucc flag) :=
    HasTypeDescPi.inversionUniverseCode typed
  exact absurd (universeCodeCell_inj_of_conv conv).1 (LevelExpr.ne_lsuccLsucc_self levelExpr)

/-- **Grown universe-flag rigidity** (novel — no formation twin).  When the admission flags differ
(`subjectFlag ≠ classifierFlag`), `Type@(e, subjectFlag)` is NEVER classified by the flag-mismatched successor
`Type@(lsucc e, classifierFlag)`.  Universe formation preserves the flag, so the true successor classifier
carries `subjectFlag`; `inversionUniverseCode` forces the received classifier `Conv`-equal to
`Type@(lsucc e, subjectFlag)`, and `universeCodeCell_inj_of_conv` exposes `classifierFlag = subjectFlag`,
refuting the disequality. -/
theorem grownUniverseCode_notTypedAtFlagMismatchedSuccessor {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} (_contextWellFormed : WfContext context)
    (levelExpr : LevelExpr) (subjectFlag classifierFlag : UniverseFlag)
    (flagsDiffer : subjectFlag ≠ classifierFlag) :
    ¬ HasTypeDescPi profile context (universeCodeCell levelExpr subjectFlag)
        (universeCodeCell levelExpr.lsucc classifierFlag) := by
  intro typed
  have conv : Conv (universeCodeCell levelExpr.lsucc classifierFlag : RawTerm scope)
      (universeCodeCell levelExpr.lsucc subjectFlag) :=
    HasTypeDescPi.inversionUniverseCode typed
  exact absurd (universeCodeCell_inj_of_conv conv).2.symm flagsDiffer

end FX1Poly.Typed
