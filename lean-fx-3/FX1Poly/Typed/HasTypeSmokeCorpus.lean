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
  cell — distinguishing classifier-discrimination from subject-head discrimination);
* NO-TYPE-IN-TYPE — `probe_universe_Type_in_Type_rejected` (#442): a universe
  code is NOT classified by itself (`Type@(e,f) : Type@(e,f)` rejected), the
  headline predicativity / no-Girard guarantee — the highest-value witness.

This corpus flags any decider whose verdicts silently change.

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

/-- NO-TYPE-IN-TYPE honesty probe (#442): a universe code is NOT classified
by ITSELF.  `Type@(e, f)` inhabits `Type@(lsucc e, f)` — its strict predicative
successor — and nothing else (the `universeFormation` rule's classifier is fixed
one level up); so `Type@(e, f) : Type@(e, f)` is rejected.  This is the headline
universe-consistency guarantee: no `Type : Type`, hence no Girard paradox at the
universe level (§11.8.2 gap #1).  Were it to hold, the classifier-equality
characterization would force `e = lsucc e` (`universeCodeCell_inj`), refuted by
`LevelExpr.ne_lsucc_self`.  The well-formed context is the iff lemma's premise;
the empty context (`WfContext.emptyIsWellFormed`) already instantiates it, so the
probe is non-vacuous. -/
theorem probe_universe_Type_in_Type_rejected {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} (wellFormed : WfContext context)
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    ¬ HasType profile context (universeCodeCell levelExpr flag)
        (universeCodeCell levelExpr flag) := by
  intro typed
  have classifierEqualsSucc :
      (universeCodeCell levelExpr flag : RawTerm scope)
        = universeCodeCell levelExpr.lsucc flag :=
    (HasType.universeCodeCell_iff_classifierEqSucc wellFormed levelExpr flag
      (universeCodeCell levelExpr flag)).mp typed
  exact LevelExpr.ne_lsucc_self levelExpr
    (universeCodeCell_inj classifierEqualsSucc).1

end FX1Poly.Typed
