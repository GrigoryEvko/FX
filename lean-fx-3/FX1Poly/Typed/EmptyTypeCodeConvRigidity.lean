import FX1Poly.Typed.ConvCodeInjectivity
import FX1Poly.Typed.HasTypeDescSubjectReduction

/-! # FX1Poly/Typed/EmptyTypeCodeConvRigidity — `emptyTypeCell` is a DISTINCT type former
    (Conv-rigidity: never convertible to Π / Σ / a universe), proved SN-FREE.

`ConvCodeInjectivity` proves the dependent type formers are pairwise non-convertible (Π ≠ Σ,
Π ≠ universe, Σ ≠ universe).  `emptyTypeCell` (`gen_emptyCode`, the nullary data-type code substrate,
#808) is a FOURTH distinct type former: this file proves it is never `Conv`-equal to a Π-code, a
Σ-code, or a universe code.

## Why this is SN-free (the crack, reused)

`Conv` is `StepStar.Join`.  `emptyTypeCell` admits NO `Step` at all (`Step.no_step_from_emptyCode`: a
nullary leaf heads no β/ι and its child spine is empty), so a `StepStar` out of it is reflexive
(`StepStar.eq_of_noStep`).  A Π/Σ-code's head is `StepStar`-stable (`shapeStable_{pi,sigma}TyCode`),
and a universe code is likewise a step normal form (`noStep_universeCode`).  So the common reduct of
any such conversion is forced to be BOTH `gen_emptyCode` and the other former's generator —
contradicting `Generator.noConfusion`.  No confluence, no strong normalization.

## What these are for

The type-code RIGIDITY ingredients the consistency / canonicity inversion consumes: a closed value's
natural classifier is a Π-type (a λ) or a universe code (a type former), and neither is `Conv`-equal
to `emptyTypeCell` — so no closed value can be typed at the empty type.  The `Conv`-side companion to
the reducibility-side empty candidate (`emptyHasNoClosedMember`, #680).

## Zero-axiom

`Step.no_step_from_emptyCode` + `StepStar.eq_of_noStep` + `StepStar.shapeStable_{pi,sigma}TyCode` +
`StepStar.noStep_universeCode` + `congrArg RawTerm.headGenerator` + `Generator.noConfusion`.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Audit-gated.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **A Π-code is never convertible to the empty-type code.**  Both legs of the conversion land on a
shared common reduct, forced to be both a `piTyCodeCell` (head-stability) and `emptyTypeCell` (the
empty code is a step normal form) — distinct generators. -/
theorem Conv.piTyCode_not_emptyTypeCode {scope : Nat}
    {piDomain : RawTerm scope} {piCodomain : RawTerm (scope + 1)}
    (convertibility :
      Conv (piTyCodeCell piDomain piCodomain) (emptyTypeCell (scope := scope))) :
    False := by
  obtain ⟨_commonReduct, leftChain, rightChain⟩ := convertibility
  obtain ⟨_, _, leftCommonEq, _, _⟩ := StepStar.shapeStable_piTyCode leftChain
  have rightCommonEq :=
    StepStar.eq_of_noStep (fun _reduct step => Step.no_step_from_emptyCode step) rightChain
  rw [leftCommonEq] at rightCommonEq
  exact Generator.noConfusion
    (congrArg RawTerm.headGenerator rightCommonEq :
      Generator.gen_piTyCode = Generator.gen_emptyCode)

/-- **A Σ-code is never convertible to the empty-type code** — the Σ dual of
`Conv.piTyCode_not_emptyTypeCode`. -/
theorem Conv.sigmaTyCode_not_emptyTypeCode {scope : Nat}
    {sigmaDomain : RawTerm scope} {sigmaCodomain : RawTerm (scope + 1)}
    (convertibility :
      Conv (sigmaTyCodeCell sigmaDomain sigmaCodomain) (emptyTypeCell (scope := scope))) :
    False := by
  obtain ⟨_commonReduct, leftChain, rightChain⟩ := convertibility
  obtain ⟨_, _, leftCommonEq, _, _⟩ := StepStar.shapeStable_sigmaTyCode leftChain
  have rightCommonEq :=
    StepStar.eq_of_noStep (fun _reduct step => Step.no_step_from_emptyCode step) rightChain
  rw [leftCommonEq] at rightCommonEq
  exact Generator.noConfusion
    (congrArg RawTerm.headGenerator rightCommonEq :
      Generator.gen_sigmaTyCode = Generator.gen_emptyCode)

/-- **A universe code is never convertible to the empty-type code.**  Both `universeCodeCell` and
`emptyTypeCell` are step normal forms, so the common reduct equals each — forcing
`gen_universeCode = gen_emptyCode`. -/
theorem Conv.universeCode_not_emptyTypeCode {scope : Nat}
    {levelExpr : LevelExpr} {flag : UniverseFlag}
    (convertibility :
      Conv (universeCodeCell levelExpr flag) (emptyTypeCell (scope := scope))) :
    False := by
  obtain ⟨_commonReduct, leftChain, rightChain⟩ := convertibility
  have leftCommonEq :=
    StepStar.eq_of_noStep
      (fun _reduct step => StepStar.noStep_universeCode (levelExpr, flag) step) leftChain
  have rightCommonEq :=
    StepStar.eq_of_noStep (fun _reduct step => Step.no_step_from_emptyCode step) rightChain
  rw [leftCommonEq] at rightCommonEq
  exact Generator.noConfusion
    (congrArg RawTerm.headGenerator rightCommonEq :
      Generator.gen_universeCode = Generator.gen_emptyCode)

end FX1Poly.Typed
