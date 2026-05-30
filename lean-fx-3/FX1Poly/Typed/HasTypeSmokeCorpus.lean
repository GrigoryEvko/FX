import FX1Poly.Typed.HasTypeDecidable

/-! # FX1Poly/Typed/HasTypeSmokeCorpus
    — non-vacuity / regression witnesses for the typed-checking deciders

The decision procedures `IsType.decidableOfWellFormed` (#303) and
`HasType.decidableOfWellFormed` (#461) are sound and complete *by construction*
(a `Decidable` carries its proof or refutation).  What that does NOT establish on
its own is *discrimination*: a decider that answered `isFalse` on every input
would also be "sound+complete" vacuously.  This corpus is the regression net that
pins discrimination — concrete cells where the typing relation genuinely holds AND
concrete cells where it genuinely fails, one per outcome branch of the deciders:

* `gen_universeCode` accepted — `corpus_universeCode_typedBySucc` (a universe code
  is typed by its successor universe);
* `gen_var` accepted — `corpus_variable_typedByLookup` (variable 0 is typed by its
  looked-up classifier, in a context binding a universe code);
* outer reject — `corpus_unitCell_rejected` (the unit cell, head `gen_unit`, is
  typed by nothing) — cf. the pre-existing `appUnitUnit_hasNoTyping` for `gen_app`;
* `gen_universeCode` reject with wrong classifier —
  `corpus_universeCode_notTypedByUnit` (a universe code is NOT typed by the unit
  cell — the highest-value witness, distinguishing classifier-discrimination from
  subject-head discrimination).

A λ/app arm (#444) breaks the leaf-only invariant these rest on; this corpus then
flags any decider whose verdicts silently change.

## Zero-axiom verification

Positives are the `var` / `universeFormation` rules directly; negatives route
through the classifier-equality characterization + `Generator.noConfusion` on a
head-generator mismatch (the same propext-free pattern as `appUnitUnit_hasNoTyping`).
Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- Head generator of the unit cell — mirror of
`headGenerator_{variableCell,universeCodeCell}`, `scope` pinned so `rfl` reduces
the matcher. -/
theorem headGenerator_unitCell {scope : Nat} :
    RawTerm.headGenerator (unitCell : RawTerm scope) = Generator.gen_unit :=
  rfl

/-- POSITIVE (`gen_universeCode` accepted): a universe code is typed by its
successor universe — the `universeFormation` rule. -/
theorem corpus_universeCode_typedBySucc {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (levelExpr : LevelExpr)
    (flag : UniverseFlag) :
    HasType profile context (universeCodeCell levelExpr flag)
      (universeCodeCell levelExpr.lsucc flag) :=
  HasType.universeFormation context levelExpr flag

/-- POSITIVE (`gen_var` accepted): a variable cell is typed by its looked-up
classifier — the `var` rule.  Stated over an arbitrary `index` rather than a
concrete `Fin` numeral: `(0 : Fin (n+1))` via `OfNat` pulls `propext` through
Fin's `Nat.mod_lt` / `NeZero` machinery (cf. the Fin-elimination axiom trap), so
a numeral would taint the witness; the general form covers the same decider
branch axiom-cleanly. -/
theorem corpus_variable_typedByLookup {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (index : Fin scope) :
    HasType profile context (variableCell index) (context.lookup index) :=
  HasType.var context index

/-- NEGATIVE (outer reject): the unit cell — head `gen_unit`, neither a variable
nor a universe code — has no typing derivation under any classifier. -/
theorem corpus_unitCell_rejected {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope} :
    ¬ HasType profile context unitCell classifier :=
  HasType.not_of_headGenerator
    (by rw [headGenerator_unitCell]; exact fun headEq => Generator.noConfusion headEq)
    (by rw [headGenerator_unitCell]; exact fun headEq => Generator.noConfusion headEq)

/-- NEGATIVE (`gen_universeCode` reject, wrong classifier): a universe code is NOT
typed by the unit cell — its unique classifier is the successor universe
(head `gen_universeCode`), which differs from the unit cell's `gen_unit`. -/
theorem corpus_universeCode_notTypedByUnit {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} (wellFormed : WfContext context)
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    ¬ HasType profile context (universeCodeCell levelExpr flag) unitCell := by
  intro typed
  have classifierEqualsSucc :
      (unitCell : RawTerm scope) = universeCodeCell levelExpr.lsucc flag :=
    (HasType.universeCodeCell_iff_classifierEqSucc wellFormed levelExpr flag
      unitCell).mp typed
  have headsAgree :
      RawTerm.headGenerator (unitCell : RawTerm scope)
        = RawTerm.headGenerator (universeCodeCell levelExpr.lsucc flag) :=
    congrArg RawTerm.headGenerator classifierEqualsSucc
  rw [headGenerator_unitCell, headGenerator_universeCodeCell] at headsAgree
  exact Generator.noConfusion headsAgree

end FX1Poly.Typed
