import FX1Poly.Typed.GrownRigidityCanonicity
import FX1Poly.Typed.ConvBoolCodeRigidity

/-! # FX1Poly/Typed/ClosedNatCanonicity — the Nat operational-value vocabulary + natCode rigidities

Originally SN-048's closed Nat canonicity via the syntactic route over the standalone nat-intro engine.
NATIVE-42 retired the zoo-premised statements (`subjectIsNatNumeral` / `standaloneNatCanonicalForms` /
`closedNatCanonicalForms` — their live restatement is the DEEP union theorem
`HasTypeUnion.closedNormalNatNumeral` in `NatNumeralUnionCanonicity`, the Milestone-A Nat pillar);
what remains here is the zoo-free substrate both that theorem and the eliminator-computing canonicity
lane consume:

  * **`IsNatNumeral`** — the closed-numeral predicate: `natZero` is one, `natSucc(p)` is one if `p` is.
    The "is a value" target for Nat canonicity (a recursive family — Nat has infinitely many numerals,
    unlike bool's two).  Consumed by NatElim/ListElim/MatchElim ComputingCanonicity + the deep union
    numeral extraction.
  * **`Conv.natTypeCell_not_piTyCode` / `_not_sigmaTyCode` / `_not_universeCode`** — the cross-former
    rigidities (mirroring `ConvBoolCodeRigidity`): `natTypeCell` is a no-step leaf (`isStepNormalForm`
    by `rfl`), so a shared `Conv` reduct would carry both `gen_natCode` and the former's head —
    `Generator.noConfusion`.

## Zero-axiom verification

The rigidities are `StepStar.eq_of_noStep` + `rfl` normality + the shipped `StepStar.shapeStable_*` /
`noStep_universeCode` + `Generator.noConfusion`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **A closed nat numeral**: `natZero`, or `natSucc(p)` for a numeral `p`.  The recursive "is a value"
predicate for Nat canonicity — Nat has infinitely many numerals (unlike bool's two), so the value target is an
inductive family, not a finite disjunction. -/
inductive IsNatNumeral {scope : Nat} : RawTerm scope → Prop where
  | zero : IsNatNumeral natZeroCell
  | succ {predecessor : RawTerm scope} :
      IsNatNumeral predecessor → IsNatNumeral (natSuccCell predecessor)

/-- **`natCode` is never convertible to a Π-code.**  Rules out a `lam` subject in nat canonicity (its
classifier is a `piTyCode`).  `natTypeCell` is a no-step leaf, `piTyCode` is head-stable; a shared reduct would
carry both `gen_natCode` and `gen_piTyCode` — `Generator.noConfusion`.  The nat twin of
`Conv.boolTypeCell_not_piTyCode`. -/
theorem Conv.natTypeCell_not_piTyCode {scope : Nat}
    {piDomain : RawTerm scope} {piCodomain : RawTerm (scope + 1)}
    (convertibility : Conv (natTypeCell : RawTerm scope) (piTyCodeCell piDomain piCodomain)) :
    False := by
  obtain ⟨_commonReduct, leftChain, rightChain⟩ := convertibility
  have leftCommonEq :=
    StepStar.eq_of_noStep
      (fun reduct step =>
        RawTerm.isStepNormalForm_blocks_step
          (rfl : RawTerm.isStepNormalForm (natTypeCell : RawTerm scope)) reduct step)
      leftChain
  obtain ⟨_, _, rightCommonEq, _, _⟩ := StepStar.shapeStable_piTyCode rightChain
  rw [leftCommonEq] at rightCommonEq
  exact Generator.noConfusion
    (congrArg RawTerm.headGenerator rightCommonEq :
      Generator.gen_natCode = Generator.gen_piTyCode)

/-- **`natCode` is never convertible to a Σ-code** — the Σ dual of `natTypeCell_not_piTyCode` (parity with the
bool rigidity; the grown half of any future Σ-vs-Nat discrimination). -/
theorem Conv.natTypeCell_not_sigmaTyCode {scope : Nat}
    {sigmaDomain : RawTerm scope} {sigmaCodomain : RawTerm (scope + 1)}
    (convertibility :
      Conv (natTypeCell : RawTerm scope) (sigmaTyCodeCell sigmaDomain sigmaCodomain)) :
    False := by
  obtain ⟨_commonReduct, leftChain, rightChain⟩ := convertibility
  have leftCommonEq :=
    StepStar.eq_of_noStep
      (fun reduct step =>
        RawTerm.isStepNormalForm_blocks_step
          (rfl : RawTerm.isStepNormalForm (natTypeCell : RawTerm scope)) reduct step)
      leftChain
  obtain ⟨_, _, rightCommonEq, _, _⟩ := StepStar.shapeStable_sigmaTyCode rightChain
  rw [leftCommonEq] at rightCommonEq
  exact Generator.noConfusion
    (congrArg RawTerm.headGenerator rightCommonEq :
      Generator.gen_natCode = Generator.gen_sigmaTyCode)

/-- **`natCode` is never convertible to a universe code.**  Rules out every type-former subject in nat
canonicity (their classifier is `universeCode`).  Both `natTypeCell` and `universeCodeCell` are no-step leaves,
so a shared reduct equals both — `Generator.noConfusion` on `gen_natCode` vs `gen_universeCode`. -/
theorem Conv.natTypeCell_not_universeCode {scope : Nat}
    {levelExpr : LevelExpr} {flag : UniverseFlag}
    (convertibility : Conv (natTypeCell : RawTerm scope) (universeCodeCell levelExpr flag)) :
    False := by
  obtain ⟨_commonReduct, leftChain, rightChain⟩ := convertibility
  have leftCommonEq :=
    StepStar.eq_of_noStep
      (fun reduct step =>
        RawTerm.isStepNormalForm_blocks_step
          (rfl : RawTerm.isStepNormalForm (natTypeCell : RawTerm scope)) reduct step)
      leftChain
  have rightCommonEq :=
    StepStar.eq_of_noStep
      (fun _reduct step => StepStar.noStep_universeCode (levelExpr, flag) step) rightChain
  rw [leftCommonEq] at rightCommonEq
  exact Generator.noConfusion
    (congrArg RawTerm.headGenerator rightCommonEq :
      Generator.gen_natCode = Generator.gen_universeCode)

end FX1Poly.Typed
