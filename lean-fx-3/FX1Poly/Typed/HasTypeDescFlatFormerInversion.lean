import FX1Poly.Typed.HasTypeDescFlat
import FX1Poly.Typed.HasTypeDescFormerTelescopeInversion

/-! # FX1Poly/Typed/HasTypeDescFlatFormerInversion
    — the propext-free generic flat-former inversion (telescope + classifier Conv)

The flat twin of `HasTypeDesc.inversionFormerWithConvGeneric` (aliased `HasTypeDesc.ln`): a flat-typed cell
yields BOTH the children `FlatDescTelescope` AND the classifier `Conv` to the canonical universe code, at
CONSISTENT `levels`/`flag` (both read off the SAME `flatFormation` arm).  This is the substrate the flat
uniqueness headline (`HasTypeDescFlat.uniquenessNative`, #940) consumes — two separate existential inversions
would NOT guarantee the consistency `uniquenessAgree` needs.

## Why a dedicated inversion (the propext discipline)

Naively casing/injecting the raw `subject = mkGen generator payload children` on a VARIABLE generator drills the
dependent `mkGen` indices (payload/children `HEq`) and leaks `propext` (the childcons-injection-drilling area).
`inversionFormerWithConv` is propext-free by the same "cracked-wall" idiom the formation engine uses: it aligns
the generator FIRST via `congrArg RawTerm.headGenerator subjectEq` (a clean projection `Eq`) + `subst`, THEN
`injection` + `subst_vars` on the now-aligned cell.  It takes `subjectEq` as a hypothesis (rather than deriving
it), so the caller supplies the alignment.

## Zero-axiom verification

`flatFormerBinderShifts` is a five-way `by_cases` over the flat formers (each `binderShifts = [0,0]` by `rfl`;
the non-former branch `exfalso` via `unfold` + `if_neg` chain + `contradiction`).  `inversionFormerWithConv`
is a single-arm `cases derivation` (free subject — no concrete-`mkGen` index unification) + the
`congrArg headGenerator` / `subst` / `injection` / `subst_vars` cracked-wall idiom +
`flatFormationRuleIsUniverseFormer` + `Conv.refl`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **A flat former has binderShifts `[0, 0]`** (the non-dependent two-child shape).  Five-way `by_cases` over the
flat formers; the substrate for level-list-length / non-emptiness arguments over flat telescopes. -/
theorem flatFormerBinderShifts {generator : Generator} {rule : TypingRuleDesc}
    (isFlatFormation : flatTypingRuleDescOf generator = some rule) :
    generator.binderShifts = [0, 0] := by
  by_cases hProduct : generator = .gen_productCode
  · subst hProduct; rfl
  · by_cases hSum : generator = .gen_sumCode
    · subst hSum; rfl
    · by_cases hEither : generator = .gen_eitherCode
      · subst hEither; rfl
      · by_cases hArrow : generator = .gen_arrowCode
        · subst hArrow; rfl
        · by_cases hEquiv : generator = .gen_equivCode
          · subst hEquiv; rfl
          · exfalso
            dsimp only [flatTypingRuleDescOf] at isFlatFormation
            rw [if_neg hProduct, if_neg hSum, if_neg hEither, if_neg hArrow, if_neg hEquiv]
              at isFlatFormation
            contradiction

/-- **Generic flat-former inversion (telescope + classifier Conv).**  The propext-free flat twin of
`HasTypeDesc.inversionFormerWithConvGeneric` (`HasTypeDesc.ln`): a flat-typed cell yields BOTH the children
`FlatDescTelescope` AND the classifier `Conv` to the canonical universe code, at CONSISTENT `levels`/`flag`.
Aligns the generator via `congrArg RawTerm.headGenerator subjectEq` + `subst` BEFORE the `injection`, so the
dependent-`mkGen` drill never exposes the `propext`-leaking raw injection. -/
theorem HasTypeDescFlat.inversionFormerWithConv {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject reachedClassifier : RawTerm scope}
    (derivation : HasTypeDescFlat profile context subject reachedClassifier)
    {generator : Generator} {rule : TypingRuleDesc}
    (isFlatFormation : flatTypingRuleDescOf generator = some rule)
    {payload : generator.payload scope} {children : RawTermChildren generator.binderShifts scope}
    (subjectEq : subject = RawTerm.mkGen generator payload children) :
    ∃ (levels : List LevelExpr) (flag : UniverseFlag),
      FlatDescTelescope profile context flag levels children ∧
      Conv reachedClassifier (universeCodeCell (lmaxAll levels) flag) := by
  cases derivation with
  | flatFormation armGenerator armPayload armChildren armLevels armFlag armRule armIsFlat armPremise =>
      have generatorAgree : armGenerator = generator :=
        congrArg RawTerm.headGenerator subjectEq
      subst generatorAgree
      obtain rfl : armRule = { outputType := universeFormerOutput } :=
        flatFormationRuleIsUniverseFormer armIsFlat
      injection subjectEq
      subst_vars
      exact ⟨armLevels, armFlag, armPremise, Conv.refl _⟩

end FX1Poly.Typed
