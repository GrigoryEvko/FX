import FX1Poly.Typed.HasTypeDescPiAppInversion
import FX1Poly.Typed.TypedFragmentAcyclicity

/-! # FX1Poly/Typed/ClassifierRespectsConvRefuted — `classifierRespectsConv` (the VAL-1 GCC-5 reduction
    target) is FALSE; the GCC-5 piElim arm cannot route through it.

`PiElimUpToClassifierConv` (VAL-1, `#1039`) reduced the GCC-5 entangled crux (the grown context-conversion
`piElim` arm, `#842`) to a single property,

  `classifierRespectsConv : IsTypeDescPi Γ A → Conv A B → IsTypeDescPi Γ B`   (type-Conv-closure)

and VAL-2 (`#1040`) was scheduled to prove it.  **This file proves `classifierRespectsConv` is FALSE.**  So
VAL-2 as planned is impossible — one cannot prove a false lemma — and the route plan's "GCC-5 = ONE lemma"
characterization is incorrect.  GCC-5 must instead be discharged a different way (see the redirect below).

## The counterexample

  * `A = Type@0` — a type (`IsTypeDescPi`, classified by `Type@1`);
  * `B = (λ_. Type@0) Ω` — the application of the constant-`Type@0` function to `Ω = (λx. x x)(λx. x x)`.

`B ↝ A`: the lambda's body `Type@0` has no bound occurrence, so β DISCARDS `Ω` and `B` steps straight to
`Type@0 = A`.  Hence `Conv A B`.  Yet `B` is NOT a type — indeed it is UNTYPABLE.  The only rule that types an
application is `piElim`, and `invertApp` shows a typing of `B` would type its ARGUMENT `Ω` at the function's
domain.  But `Ω` is untypable (`omegaCombinator_notClosedWellTyped`, `#958`: were `Ω` typed it would be
strongly normalizing by SN-043, but it β-self-loops).  So `IsTypeDescPi Γ B` is false while `IsTypeDescPi Γ A`
and `Conv A B` both hold — refuting `classifierRespectsConv`.

## Why this happens — the deep finding

The grown typing rules require EVERY subterm to be typed, INCLUDING a subterm a reduction later discards.
`piElim` types `f a` only with `a` typed at the domain, even when `f` ignores its argument.  So a β-redex that
discards an untypable argument is itself untypable, yet is convertible to its (well-typed) contractum.
**Therefore grown well-typedness — equivalently `IsTypeDescPi` — is NOT `Conv`-invariant.**  Any GCC-5 attack
that needs `IsType` transported across a bare `Conv` (forgetting the source derivation) is doomed.

## The GCC-5 redirect

The ACTUAL `piElim` arm (`HasTypeDescPiContextConversionConditional`'s `piElimArm`) does NOT have a bare
`Conv functionType (piTyCode D C)` — it has the ORIGINAL source derivation `fn : piTyCodeCell D C`, whose
components `D` / `C` are GENUINELY typed (by `inversionPiCodeComponentsUnconditional` / validity).  So
`piTyCode D C` is a type in the SOURCE context, and the arm should context-convert THAT formation (the
genFormationPi context-conversion, GCC-4) — never the lossy `classifierRespectsConv`.  VAL-1's abstraction
discarded the source derivation and so landed on the false `classifierRespectsConv`; the correct reduction
keeps it.  (The remaining difficulty is that the source-validity formation is not a structural SUBDERIVATION
of the application, so its context-conversion needs its own well-founded handling — the genuine GCC-5 residual,
now correctly located.)

## Zero-axiom

`Step.beta` + `HasTypeDescPi.invertApp` + `omegaCombinator_notClosedWellTyped` + the universe-formation rule +
`Conv.fromStepStar`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Gated per-declaration in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe StepStar

/-- The good type `A = Type@0`. -/
abbrev classifierConvCounterexampleType : RawTerm 0 :=
  universeCodeCell LevelExpr.lzero UniverseFlag.standard

/-- The bad term `B = (λ_. Type@0) Ω` — a β-redex whose lambda discards its (untypable) argument. -/
abbrev classifierConvCounterexampleRedex : RawTerm 0 :=
  appCell (lamCell (universeCodeCell LevelExpr.lzero UniverseFlag.standard)) omegaCombinator

/-- `B ↝ A`: the β-redex discards `Ω` (the body `Type@0` has no `var 0`), stepping to `Type@0`. -/
theorem classifierConvCounterexampleRedex_stepsToType :
    Step classifierConvCounterexampleRedex classifierConvCounterexampleType :=
  Step.beta

/-- `A = Type@0` IS a type (classified by `Type@1` via the universe-formation rule). -/
theorem classifierConvCounterexampleType_isType {profile : PolyProfile} :
    IsTypeDescPi profile TypingContext.empty classifierConvCounterexampleType :=
  ⟨LevelExpr.lzero.lsucc, UniverseFlag.standard,
   HasTypeDescPi.ofFormation (HasTypeDesc.universeFormation TypingContext.empty LevelExpr.lzero
     UniverseFlag.standard)⟩

/-- `B = (λ.Type@0) Ω` is NOT a type — a typing of `B` would, by `invertApp`, type its argument `Ω` at the
function's domain, contradicting `omegaCombinator_notClosedWellTyped` (`Ω` has no closed type). -/
theorem classifierConvCounterexampleRedex_notType {profile : PolyProfile} :
    ¬ IsTypeDescPi profile TypingContext.empty classifierConvCounterexampleRedex := by
  rintro ⟨_level, _flag, typed⟩
  obtain ⟨domainCode, _codomainCode, _functionTyped, omegaTyped, _conv⟩ :=
    HasTypeDescPi.invertApp typed
  exact omegaCombinator_notClosedWellTyped ⟨domainCode, omegaTyped⟩

/-- ★ **`classifierRespectsConv` is FALSE.**  There exist a type `A` and a `Conv`-equal `B` that is NOT a type
(`A = Type@0`, `B = (λ.Type@0) Ω`).  So the VAL-1 GCC-5 reduction target cannot be proven; GCC-5 must keep the
source Π-type derivation rather than reduce to a bare `Conv functionType (piTyCode D C)`.  Equivalently: grown
`IsTypeDescPi` is NOT `Conv`-invariant. -/
theorem classifierRespectsConv_isFalse {profile : PolyProfile} :
    ¬ (∀ {typeLeft typeRight : RawTerm 0},
        IsTypeDescPi profile TypingContext.empty typeLeft → Conv typeLeft typeRight →
          IsTypeDescPi profile TypingContext.empty typeRight) := by
  intro classifierRespectsConv
  exact classifierConvCounterexampleRedex_notType
    (classifierRespectsConv classifierConvCounterexampleType_isType
      (Conv.fromStepStar (StepStar.single classifierConvCounterexampleRedex_stepsToType)).sym)

end FX1Poly.Typed
