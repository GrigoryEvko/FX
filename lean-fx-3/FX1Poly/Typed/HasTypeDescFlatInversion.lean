import FX1Poly.Typed.HasTypeDescFlat

/-! # FX1Poly/Typed/HasTypeDescFlatInversion
    — inversion metatheory for the flat-former typing judgment (first #935 increment)

`HasTypeDescFlat` (the standalone flat-former engine, #934) types the non-dependent `[0,0]` type-code formers.
Its metatheory now needs the same inversion the formation / grown engines have: from a `HasTypeDescFlat`
derivation, recover the premise telescope (and hence the children's typings) and the output classifier.  This
file supplies it — the flat twin of `HasTypeDesc.inversionListCode` / `inversionPiCodeWithConv`.

Because `HasTypeDescFlat` has exactly ONE constructor (`flatFormation`), the generic inversion is a single-arm
`cases` that simply returns the constructor's fields.  The per-former corollary then projects the
`FlatDescTelescope` premise through `FlatDescTelescope.twoChildComponents` to recover BOTH children's typings,
and pins the classifier to the `universeFormerOutput` shape via the `flatTypingRuleDescOf` row.

## Zero-axiom verification

`inversion` is a single-arm `cases` + `exact`.  `inversionProductCodeComponents` cases the derivation (the
subject `mkGen gen_productCode ()` forces the generator), projects the two-child flat telescope
(`twoChildComponents` — the shipped single-live-`cons`-then-`nil` projection, no `propext`/`Quot.sound`), pins
`rule = { outputType := universeFormerOutput }` from the table row (`Option.some.inj`), and closes the classifier
shape by `rw` + `rfl` (the structure projection + `universeFormerOutput` unfold are definitional).  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Generic flat-former inversion.**  A `HasTypeDescFlat` derivation recovers its sole constructor's fields:
the generator (a flat former, witnessed by `flatTypingRuleDescOf generator = some rule`), the payload/children,
the levels/flag, the subject as a `mkGen` cell, the classifier as the rule's `outputType`, and the
`FlatDescTelescope` premise.  Single-arm `cases` over the one-constructor judgment. -/
theorem HasTypeDescFlat.inversion {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject reachedClassifier : RawTerm scope}
    (derivation : HasTypeDescFlat profile context subject reachedClassifier) :
    ∃ (generator : Generator) (payload : generator.payload scope)
      (children : RawTermChildren generator.binderShifts scope) (levels : List LevelExpr)
      (flag : UniverseFlag) (rule : TypingRuleDesc),
      flatTypingRuleDescOf generator = some rule ∧
      subject = .mkGen generator payload children ∧
      reachedClassifier = rule.outputType scope levels flag ∧
      FlatDescTelescope profile context flag levels children := by
  cases derivation with
  | flatFormation generator payload children levels flag rule isFlat premise =>
      exact ⟨generator, payload, children, levels, flag, rule, isFlat, rfl, rfl, premise⟩

/-- **`productCode` component inversion.**  A typed `product children` cell recovers both children's typings at
their universe codes AND the classifier shape `Type@(lmax [firstLevel, secondLevel])` — the flat-former twin of
`HasTypeDesc.inversionListCode`.  Casing the derivation forces the generator to `gen_productCode`; the
`FlatDescTelescope.twoChildComponents` projection recovers the two child typings under the SAME base context
(the non-dependent former shape), and the `gen_productCode` row pins the output universe. -/
theorem HasTypeDescFlat.inversionProductCodeComponents {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {children : RawTermChildren [0, 0] scope}
    {reachedClassifier : RawTerm scope}
    (derivation : HasTypeDescFlat profile context
      (.mkGen .gen_productCode () children) reachedClassifier) :
    ∃ (firstChild secondChild : RawTerm scope) (firstLevel secondLevel : LevelExpr)
      (flag : UniverseFlag),
      HasTypeDesc profile context firstChild (universeCodeCell firstLevel flag) ∧
      HasTypeDesc profile context secondChild (universeCodeCell secondLevel flag) ∧
      reachedClassifier = universeCodeCell (lmaxAll [firstLevel, secondLevel]) flag := by
  cases derivation with
  | flatFormation _generator _payload _children levels flag rule isFlat premise =>
      obtain ⟨firstChild, secondChild, firstLevel, secondLevel, levelsEq, firstTyped, secondTyped⟩ :=
        premise.twoChildComponents
      refine ⟨firstChild, secondChild, firstLevel, secondLevel, flag, firstTyped, secondTyped, ?_⟩
      have ruleEq : rule = { outputType := universeFormerOutput } :=
        Option.some.inj (isFlat.symm.trans flatTypingRuleDescOf_productCode)
      rw [ruleEq, levelsEq]
      rfl

end FX1Poly.Typed
