import FX1Poly.Typed.Metatheory.Reducibility.Bounded.CumulativeFormationRows
import FX1Poly.Typed.Metatheory.Reducibility.Bounded.CumulativeElementFormationRows

/-! # FX1Poly/Typed/CumulativeFormationFamilyArm
    — the cumulative formation FT family-arm dispatcher (TYTAB-4 step 4)

The cumulative formation sub-family has four NON-nullary generators across two shipped row files:

  * binder-shape dependent formers (`CumulativeFormationRows`): `gen_piTyCode` (Π) / `gen_sigmaTyCode` (Σ) —
    two children `[domain, codomain]` at shifts `[0, 1]`, the codomain typed in the domain-extended context
    (the binder-crossing obligation);
  * element-shape formers (`CumulativeElementFormationRows`): `gen_listCode` / `gen_optionCode` — one child
    `[element]` at shift `[0]`.

All four per-generator rows share the SAME interface (`levelsBelowBound` + `boundPositive` +
`obligationsFundamental` over `cumulativeFormationObligations`, output `universeFormerOutput scope levels
flag`), so this arm is a uniform four-way `by_cases` dispatch keyed on `typingRuleDescOf` — the analogue of
`fundamentalBaseTypeRowAtBoundedSucc` / `fundamentalFlatFormationRowAtBoundedSucc` /
`fundamentalTermIndexedFormationRowAtBoundedSucc`.  The `.cumulative` arm of the eventual `cases FormationRule`
assembly.

## The nullary `gen_unitCode` exclusion

`typingRuleDescOf` covers FIVE generators — the four dependent formers above PLUS the nullary `gen_unitCode`.
But `gen_unitCode` ALSO carries a `baseTypeRuleDescOf` row, which `formationRuleOf` tries FIRST, so
`formationRuleOf .gen_unitCode = some (.baseType …)`, never `.cumulative` — the eventual glue's `.cumulative`
arm is never reached at `gen_unitCode`.  This arm therefore takes `isNotNullary : generator ≠ gen_unitCode`
(exactly the hypothesis `formationRuleOf_cumulative` demands) and dispatches the four dependent formers; the
none-case `if_neg` cascade includes the unit branch via `isNotNullary`, mirroring
`formationRuleOf_cumulative`'s own exfalso branch.

The obligation premise is stated over `(FormationRule.cumulative cumRule).obligations …`, which reduces by the
`.cumulative` arm of `FormationRule.obligations` to `cumulativeFormationObligations profile context flag
children levels` (the `carrier` / `level` args inert) — defeq to each row's premise.  The output
`(FormationRule.cumulative cumRule).outputType scope levels level flag` reduces (after pinning
`cumRule = { outputType := universeFormerOutput }`) to `universeFormerOutput scope levels flag`.

## Zero-axiom verification

Four `by_cases` each pinning `cumRule` via a per-generator `rfl` metadata lemma (`typingRuleDescOf_X`) +
`Option.some.inj`, routing to the shipped row; the none-case is the `typingRuleDescOf` if-chain `if_neg`
cascade (the four formers + the nullary `isNotNullary`) + `contradiction`.  No new members, no induction.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The cumulative formation FT family arm (TYTAB-4 step 4).**  A NON-nullary generator carrying a cumulative
table row (`typingRuleDescOf generator = some cumRule`, `generator ≠ gen_unitCode`) makes `mkGen generator
payload children` a bound-reducible member of the rule's output universe under any closing substitution, given
the per-level bounds, `0 < bound`, and the child obligation IHs.  Dispatches the four dependent formers
(`gen_piTyCode` / `gen_sigmaTyCode` binder-shape, `gen_listCode` / `gen_optionCode` element-shape) to their
per-generator rows; the nullary `gen_unitCode` is excluded by hypothesis (it routes through the base-type
arm).  The cumulative sub-family of the native `formationFundamental` premise — the `.cumulative` arm of the
eventual `cases FormationRule` assembly. -/
theorem fundamentalCumulativeFormationRowAtBoundedSucc {profile : PolyProfile} (env : Nat → Nat) (bound : Nat)
    {scope : Nat} (context : TypingContext profile scope)
    {generator : Generator} {payload : generator.payload scope}
    {children : RawTermChildren generator.binderShifts scope}
    {cumRule : TypingRuleDesc} {levels : List LevelExpr} {carrier : RawTerm scope}
    {level : LevelExpr} {flag : UniverseFlag}
    (isCumulative : typingRuleDescOf generator = some cumRule)
    (isNotNullary : generator ≠ .gen_unitCode)
    (levelsBelowBound : ∀ levelExpr, levelExpr ∈ levels → LevelExpr.denote levelExpr env < bound)
    (boundPositive : 0 < bound)
    (obligationsFundamental : ∀ obligation,
        obligation ∈ (FormationRule.cumulative cumRule).obligations
          profile context children levels carrier level flag →
        FundamentalConclusionAtBoundedSucc env bound obligation.context obligation.subject
          obligation.classifier) :
    FundamentalConclusionAtBoundedSucc env bound context (RawTerm.mkGen generator payload children)
      ((FormationRule.cumulative cumRule).outputType scope levels level flag) := by
  by_cases isPi : generator = .gen_piTyCode
  · subst isPi
    obtain rfl : cumRule = { outputType := universeFormerOutput } :=
      Option.some.inj (isCumulative.symm.trans typingRuleDescOf_piTyCode)
    exact fundamentalCumulativePiRowAtBoundedSucc env bound context
      levelsBelowBound boundPositive obligationsFundamental
  · by_cases isSigma : generator = .gen_sigmaTyCode
    · subst isSigma
      obtain rfl : cumRule = { outputType := universeFormerOutput } :=
        Option.some.inj (isCumulative.symm.trans typingRuleDescOf_sigmaTyCode)
      exact fundamentalCumulativeSigmaRowAtBoundedSucc env bound context
        levelsBelowBound boundPositive obligationsFundamental
    · by_cases isList : generator = .gen_listCode
      · subst isList
        obtain rfl : cumRule = { outputType := universeFormerOutput } :=
          Option.some.inj (isCumulative.symm.trans typingRuleDescOf_listCode)
        exact fundamentalCumulativeListRowAtBoundedSucc env bound context
          levelsBelowBound boundPositive obligationsFundamental
      · by_cases isOption : generator = .gen_optionCode
        · subst isOption
          obtain rfl : cumRule = { outputType := universeFormerOutput } :=
            Option.some.inj (isCumulative.symm.trans typingRuleDescOf_optionCode)
          exact fundamentalCumulativeOptionRowAtBoundedSucc env bound context
            levelsBelowBound boundPositive obligationsFundamental
        · exfalso
          dsimp only [typingRuleDescOf] at isCumulative
          rw [if_neg isPi, if_neg isSigma, if_neg isList, if_neg isOption, if_neg isNotNullary]
            at isCumulative
          contradiction

end FX1Poly.Typed
