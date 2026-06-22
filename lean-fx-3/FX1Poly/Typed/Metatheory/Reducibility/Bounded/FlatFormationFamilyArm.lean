import FX1Poly.Typed.Metatheory.Reducibility.Bounded.CarrierAwareFlatFormationRows
import FX1Poly.Typed.Metatheory.Reducibility.Bounded.ContentFreeFlatFormationRows
import FX1Poly.Typed.Metatheory.Reducibility.Bounded.ModalityFlatFormationRows

/-! # FX1Poly/Typed/FlatFormationFamilyArm
    — the flat formation FT family-arm dispatcher (TYTAB-4 step 4)

The flat formation sub-family has EIGHT generators across three shipped row files:

  * carrier-aware data codes (`CarrierAwareFlatFormationRows`): `gen_productCode` / `gen_eitherCode` /
    `gen_equivCode` — both children typed at the context, the cell reducible-as-type via the carrier-aware
    builder;
  * content-free data codes (`ContentFreeFlatFormationRows`): `gen_arrowCode` / `gen_sumCode` — same shape,
    content-free reducibility;
  * cohesion modalities (`ModalityFlatFormationRows`): `gen_shapeModality` (ʃ) / `gen_flatModality` (♭) /
    `gen_sharpModality` (♯) — one-child level-preserving formers, the `neutral` arm.

Every one of the eight per-generator rows shares the SAME interface (`levelsBelowBound` + `boundPositive` +
`obligationsFundamental` over `flatFormationObligations`, output `universeFormerOutput scope levels flag`), so
this arm is a uniform eight-way `by_cases` dispatch keyed on `flatTypingRuleDescOf` — the analogue of
`fundamentalBaseTypeRowAtBoundedSucc` (base-type family) and
`fundamentalTermIndexedFormationRowAtBoundedSucc` (term-indexed family).  A non-flat generator is impossible
(`flatTypingRuleDescOf … = none`).  The `.flat` arm of the eventual `cases FormationRule` assembly that
discharges the native `formationFundamental` premise.

The obligation premise is stated over `(FormationRule.flat flatRule).obligations …`, which reduces by the
`.flat` arm of `FormationRule.obligations` to `flatFormationObligations profile context flag children levels`
(the `carrier` / `level` args inert) — defeq to each row's premise, so each row consumes it directly.  The
output `(FormationRule.flat flatRule).outputType scope levels level flag` reduces (after pinning
`flatRule = { outputType := universeFormerOutput }` from the table metadata) to `universeFormerOutput scope
levels flag`, each row's conclusion.

## Zero-axiom verification

Eight `by_cases` (`DecidableEq Generator`) each pinning `flatRule` via a per-generator `rfl` metadata lemma
(`flatTypingRuleDescOf_X`) + `Option.some.inj`, routing to the shipped row; the none-case is the if-chain
`if_neg` cascade + `contradiction`.  No new members, no induction.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The flat formation FT family arm (TYTAB-4 step 4).**  A generator carrying a flat table row
(`flatTypingRuleDescOf generator = some flatRule`) makes `mkGen generator payload children` a bound-reducible
member of the rule's output universe under any closing substitution, given the per-level bounds, `0 < bound`,
and the child obligation IHs.  Dispatches the eight flat formers (the `flatTypingRuleDescOf` if-chain order:
product / sum / either / arrow / equiv / shape / flat / sharp) to their per-generator rows; a non-flat
generator is impossible.  The flat sub-family of the native `formationFundamental` premise — the `.flat` arm of
the eventual `cases FormationRule` assembly. -/
theorem fundamentalFlatFormationRowAtBoundedSucc {profile : PolyProfile} (env : Nat → Nat) (bound : Nat)
    {scope : Nat} (context : TypingContext profile scope)
    {generator : Generator} {payload : generator.payload scope}
    {children : RawTermChildren generator.binderShifts scope}
    {flatRule : TypingRuleDesc} {levels : List LevelExpr} {carrier : RawTerm scope}
    {level : LevelExpr} {flag : UniverseFlag}
    (isFlat : flatTypingRuleDescOf generator = some flatRule)
    (levelsBelowBound : ∀ levelExpr, levelExpr ∈ levels → LevelExpr.denote levelExpr env < bound)
    (boundPositive : 0 < bound)
    (obligationsFundamental : ∀ obligation,
        obligation ∈ (FormationRule.flat flatRule).obligations
          profile context children levels carrier level flag →
        FundamentalConclusionAtBoundedSucc env bound obligation.context obligation.subject
          obligation.classifier) :
    FundamentalConclusionAtBoundedSucc env bound context (RawTerm.mkGen generator payload children)
      ((FormationRule.flat flatRule).outputType scope levels level flag) := by
  by_cases isProduct : generator = .gen_productCode
  · subst isProduct
    obtain rfl : flatRule = { outputType := universeFormerOutput } :=
      Option.some.inj (isFlat.symm.trans flatTypingRuleDescOf_productCode)
    exact fundamentalProductFormationRowAtBoundedSucc env bound context
      levelsBelowBound boundPositive obligationsFundamental
  · by_cases isSum : generator = .gen_sumCode
    · subst isSum
      obtain rfl : flatRule = { outputType := universeFormerOutput } :=
        Option.some.inj (isFlat.symm.trans flatTypingRuleDescOf_sumCode)
      exact fundamentalSumFormationRowAtBoundedSucc env bound context
        levelsBelowBound boundPositive obligationsFundamental
    · by_cases isEither : generator = .gen_eitherCode
      · subst isEither
        obtain rfl : flatRule = { outputType := universeFormerOutput } :=
          Option.some.inj (isFlat.symm.trans flatTypingRuleDescOf_eitherCode)
        exact fundamentalEitherFormationRowAtBoundedSucc env bound context
          levelsBelowBound boundPositive obligationsFundamental
      · by_cases isArrow : generator = .gen_arrowCode
        · subst isArrow
          obtain rfl : flatRule = { outputType := universeFormerOutput } :=
            Option.some.inj (isFlat.symm.trans flatTypingRuleDescOf_arrowCode)
          exact fundamentalArrowFormationRowAtBoundedSucc env bound context
            levelsBelowBound boundPositive obligationsFundamental
        · by_cases isEquiv : generator = .gen_equivCode
          · subst isEquiv
            obtain rfl : flatRule = { outputType := universeFormerOutput } :=
              Option.some.inj (isFlat.symm.trans flatTypingRuleDescOf_equivCode)
            exact fundamentalEquivFormationRowAtBoundedSucc env bound context
              levelsBelowBound boundPositive obligationsFundamental
          · by_cases isShape : generator = .gen_shapeModality
            · subst isShape
              obtain rfl : flatRule = { outputType := universeFormerOutput } :=
                Option.some.inj (isFlat.symm.trans flatTypingRuleDescOf_shapeModality)
              exact fundamentalShapeModalityFormationRowAtBoundedSucc env bound context
                levelsBelowBound boundPositive obligationsFundamental
            · by_cases isFlatMod : generator = .gen_flatModality
              · subst isFlatMod
                obtain rfl : flatRule = { outputType := universeFormerOutput } :=
                  Option.some.inj (isFlat.symm.trans flatTypingRuleDescOf_flatModality)
                exact fundamentalFlatModalityFormationRowAtBoundedSucc env bound context
                  levelsBelowBound boundPositive obligationsFundamental
              · by_cases isSharp : generator = .gen_sharpModality
                · subst isSharp
                  obtain rfl : flatRule = { outputType := universeFormerOutput } :=
                    Option.some.inj (isFlat.symm.trans flatTypingRuleDescOf_sharpModality)
                  exact fundamentalSharpModalityFormationRowAtBoundedSucc env bound context
                    levelsBelowBound boundPositive obligationsFundamental
                · exfalso
                  dsimp only [flatTypingRuleDescOf] at isFlat
                  rw [if_neg isProduct, if_neg isSum, if_neg isEither, if_neg isArrow, if_neg isEquiv,
                    if_neg isShape, if_neg isFlatMod, if_neg isSharp] at isFlat
                  contradiction

end FX1Poly.Typed
