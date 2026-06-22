import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BaseTypeFormationArm
import FX1Poly.Typed.Metatheory.Reducibility.Bounded.FlatFormationFamilyArm
import FX1Poly.Typed.Metatheory.Reducibility.Bounded.CumulativeFormationFamilyArm
import FX1Poly.Typed.Metatheory.Reducibility.Bounded.TermIndexedFormationRows

/-! # FX1Poly/Typed/UnionFormationFundamental
    — the native `formationFundamental` premise discharged at the formation table (TYTAB-4 step 4)

`HasTypeUnionOver.fundamentalAtBoundedSuccFromTableArms` (`BoundedUnionFundamental.lean`) takes three explicit
table-arm FT premises (`formationFundamental` / `introFundamental` / `elimFundamental`).  This file discharges
the FIRST — the `formationFundamental` premise — for ANY generator whose formation rule comes from
`formationRuleOf` (the `fxTypingBundle.formation` table).

## The four-family `cases FormationRule` assembly

`formationRuleOf` tags every formation generator with one of the four `FormationRule` families, each of which
now has a per-family arm dispatcher (each in turn dispatching its own generators to the shipped per-generator
rows):

  * `.baseType` → `fundamentalBaseTypeRowAtBoundedSucc` (bool / empty / nat / unit / interval);
  * `.flat` → `fundamentalFlatFormationRowAtBoundedSucc` (product / sum / either / arrow / equiv + ʃ / ♭ / ♯);
  * `.termIndexed` → `fundamentalTermIndexedFormationRowAtBoundedSucc` (Id / Bridge);
  * `.cumulative` → `fundamentalCumulativeFormationRowAtBoundedSucc` (Π / Σ / List / Option).

The arms were stated so the `cases rule` dispatch is mechanical: each family arm takes the obligation premise
over `(FormationRule.X rule).obligations …` and concludes at `(FormationRule.X rule).outputType …` — EXACTLY
the glue's hypothesis and goal once `cases rule` substitutes the family constructor.  The four reverse
extractions (`formationRuleOf_X_inv`) re-expose the underlying sub-table hit each arm keys on; `boundPositive`
and the `levels`-tail bound come off the non-empty `level :: levels` gate; the `.cumulative` arm's
`isNotNullary` (the `gen_unitCode` exclusion) follows because `formationRuleOf .gen_unitCode` is the
`.baseType` row, not `.cumulative`.

This is the native (table-driven) analogue of the grown formation engine's
`HasTypeDesc.fundamentalAtBoundedSucc` — but assembled from per-family table rows rather than a
`BoundExceeds`-budget recursion, so a future formation row (a `ProfileExtension` type-former) extends one
family arm with no change here.

## Zero-axiom verification

`cases FormationRule` (4 arms) + the four reverse extractions + elementary `Nat`/`List.Mem` bound arithmetic
+ each family arm (themselves zero-axiom).  No new members, no induction.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The native `formationFundamental` premise (TYTAB-4 step 4).**  Every generator carrying a
`formationRuleOf` formation rule makes `mkGen generator payload children` a bound-reducible member of the
rule's output universe, given the per-level bounds (the non-empty `level :: levels` gate) and the child
obligation IHs.  The four-family `cases FormationRule` assembly: each arm re-exposes its sub-table hit
(`formationRuleOf_X_inv`) and feeds the shipped per-family arm, whose obligation premise / output match the
glue's by construction.  Discharges the `formationFundamental` argument of
`HasTypeUnionOver.fundamentalAtBoundedSuccFromTableArms` for any `fxTypingBundle`-style formation table. -/
theorem fundamentalFormationRowAtBoundedSucc {profile : PolyProfile} (env : Nat → Nat) (bound : Nat)
    {scope : Nat} {context : TypingContext profile scope} {generator : Generator}
    {payload : generator.payload scope} {children : RawTermChildren generator.binderShifts scope}
    {rule : FormationRule} {levels : List LevelExpr} {carrier : RawTerm scope} {level : LevelExpr}
    {flag : UniverseFlag}
    (isFormation : formationRuleOf generator = some rule)
    (levelsBelowBound : ∀ levelExpr, levelExpr ∈ level :: levels → LevelExpr.denote levelExpr env < bound)
    (obligationsFundamental : ∀ obligation,
        obligation ∈ rule.obligations profile context children levels carrier level flag →
        FundamentalConclusionAtBoundedSucc env bound obligation.context obligation.subject
          obligation.classifier) :
    FundamentalConclusionAtBoundedSucc env bound context (RawTerm.mkGen generator payload children)
      (rule.outputType scope levels level flag) := by
  have boundPositive : 0 < bound :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) (levelsBelowBound level (List.Mem.head _))
  have tailBelowBound : ∀ levelExpr, levelExpr ∈ levels → LevelExpr.denote levelExpr env < bound :=
    fun levelExpr levelMem => levelsBelowBound levelExpr (List.Mem.tail _ levelMem)
  intro targetScope substitution envReducible
  cases rule with
  | baseType baseRule =>
      exact fundamentalBaseTypeRowAtBoundedSucc env bound context
        (formationRuleOf_baseType_inv isFormation) boundPositive substitution envReducible
  | flat flatRule =>
      exact fundamentalFlatFormationRowAtBoundedSucc env bound context
        (formationRuleOf_flat_inv isFormation) tailBelowBound boundPositive obligationsFundamental
        substitution envReducible
  | termIndexed termRule =>
      exact fundamentalTermIndexedFormationRowAtBoundedSucc env bound context
        (formationRuleOf_termIndexed_inv isFormation) obligationsFundamental
        substitution envReducible
  | cumulative cumRule =>
      have isNotNullary : generator ≠ Generator.gen_unitCode := by
        intro isUnit
        subst isUnit
        injection isFormation with ruleEq
        injection ruleEq
      exact fundamentalCumulativeFormationRowAtBoundedSucc env bound context
        (formationRuleOf_cumulative_inv isFormation) isNotNullary tailBelowBound boundPositive
        obligationsFundamental substitution envReducible

end FX1Poly.Typed
