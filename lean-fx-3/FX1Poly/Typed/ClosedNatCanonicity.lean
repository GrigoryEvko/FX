import FX1Poly.Typed.HasTypeDescNatIntro
import FX1Poly.Typed.GrownRigidityCanonicity
import FX1Poly.Typed.ConvBoolCodeRigidity

/-! # FX1Poly/Typed/ClosedNatCanonicity — SN-048: closed Nat canonicity via the syntactic route

The bool twin (`ClosedBoolCanonicity` / `GrownRigidityCanonicity`) closed SN-047 by the syntactic route:
the generic grown-rigidity packaging `dataCanonicityFromGrownRigidity` makes a data type's canonicity a
per-type instantiation needing only (1) the type's standalone closed-canonical-forms and (2) its two shipped
`Conv`-rigidities (`dataCode ≢ piTyCode` rules out `lam`; `dataCode ≢ universeCode` rules out every type
former).  `gen_natCode` + `HasTypeDescNatIntro` (DI-3) supplied the substrate; this file is the Nat
instantiation.

## What this ships

  * **`IsNatNumeral`** — the closed-numeral predicate: `natZero` is one, `natSucc(p)` is one if `p` is.
    The "is a value" target for Nat canonicity (a recursive family — Nat has infinitely many numerals, unlike
    bool's two).
  * **`HasTypeDescNatIntro.subjectIsNatNumeral` (★)** — every `HasTypeDescNatIntro`-typed subject IS a numeral:
    structural induction over the nat-intro derivation (`natZeroIntro → .zero`; `natSuccIntro` with the
    recursive predecessor IH → `.succ`).  Since nat-intro terms are already normal values, no reduction is
    needed — the subject is a numeral on the nose.
  * **`standaloneNatCanonicalForms`** — the standalone-engine canonicity in the
    `dataCanonicityFromGrownRigidity` shape (`subject` reduces to a numeral by `StepStar.refl`).
  * **`Conv.natTypeCell_not_piTyCode` / `_not_sigmaTyCode` / `_not_universeCode`** — the cross-former
    rigidities (mirroring `ConvBoolCodeRigidity`): `natTypeCell` is a no-step leaf (`isStepNormalForm` by
    `rfl`), so a shared `Conv` reduct would carry both `gen_natCode` and the former's head —
    `Generator.noConfusion`.
  * **`closedNatCanonicalForms` (★ SN-048)** — the headline: a closed term typed at `natTypeCell` by the
    nat-intro engine OR the grown engine reduces to a numeral.  The standalone arm is
    `standaloneNatCanonicalForms`; the grown arm is `noClosedGrownTermAtDataClassifier` (the grown engine has
    no closed inhabitant of `natTypeCell`).  Non-vacuous (`closedNatCanonicalForms.natOne`: `succ 0` is
    canonical).

## What remains (honest)

`closedNatCanonicalForms` ranges over the nat-intro + grown engines — the two engines that can mention a closed
term at `natTypeCell`.  The data-VALUE-branch nat ELIMINATOR (`natElim` computing canonicity, the recursive
analogue of `BoolElimValueCanonicity`, #1138) is the follow-on; it needs the recursive ι-unfolding to terminate
on the numeral structure.  Nat numeral canonicity via the REDUCIBILITY route is separately shipped (#678/SN-062).

## Zero-axiom verification

`subjectIsNatNumeral` is a two-arm `induction`; the rigidities are `StepStar.eq_of_noStep` + `rfl` normality +
the shipped `StepStar.shapeStable_*` / `noStep_universeCode` + `Generator.noConfusion`; the headline is
`dataCanonicityFromGrownRigidity` instantiated with the above.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
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

/-- **★ Every `HasTypeDescNatIntro`-typed subject IS a numeral.**  Structural induction over the nat-intro
derivation: `natZeroIntro → IsNatNumeral.zero`; `natSuccIntro` recurses on the predecessor premise (its IH
`IsNatNumeral predecessor`) → `IsNatNumeral.succ`.  The classifier is generalized (both arms conclude a numeral
independent of the classifier), dodging the fixed-index issue.  nat-intro terms are already normal values, so
this is the closed-FORMS content directly — no reduction. -/
theorem HasTypeDescNatIntro.subjectIsNatNumeral {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescNatIntro profile context subject classifier) :
    IsNatNumeral subject := by
  induction derivation with
  | natZeroIntro => exact IsNatNumeral.zero
  | natSuccIntro _predecessor _predecessorTyped ih => exact IsNatNumeral.succ ih

/-- **Standalone-engine Nat canonical forms** in the `dataCanonicityFromGrownRigidity` shape: a closed
nat-intro-typed subject reduces (reflexively — it is already a value) to a numeral. -/
theorem standaloneNatCanonicalForms {profile : PolyProfile} {subject : RawTerm 0}
    (typed : HasTypeDescNatIntro profile (TypingContext.empty : TypingContext profile 0)
      subject natTypeCell) :
    ∃ value : RawTerm 0, StepStar subject value ∧ IsNatNumeral value :=
  ⟨subject, StepStar.refl _, typed.subjectIsNatNumeral⟩

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

/-- **★ SN-048: closed Nat canonicity.**  A closed term typed at `natTypeCell` by the nat-intro engine OR the
grown engine reduces to a numeral.  Through the generic `dataCanonicityFromGrownRigidity`: the standalone arm is
`standaloneNatCanonicalForms`; the grown arm is derived (`noClosedGrownTermAtDataClassifier` — the grown engine
has no closed inhabitant of `natTypeCell`, since `natCode ≢ piTyCode` / `≢ universeCode`).  Non-vacuous
(`closedNatCanonicalForms.natOne`). -/
theorem closedNatCanonicalForms {profile : PolyProfile} {subject : RawTerm 0}
    (typed :
      HasTypeDescNatIntro profile (TypingContext.empty : TypingContext profile 0) subject natTypeCell ∨
      HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject natTypeCell) :
    ∃ value : RawTerm 0, StepStar subject value ∧ IsNatNumeral value := by
  refine dataCanonicityFromGrownRigidity
    (profile := profile)
    (isValue := fun value => IsNatNumeral value)
    (StandaloneTyped := fun standaloneSubject =>
      HasTypeDescNatIntro profile .empty standaloneSubject natTypeCell)
    (fun _standaloneSubject standaloneTyped => standaloneNatCanonicalForms standaloneTyped)
    (fun _domainCode _codomainCode convToPiCode => Conv.natTypeCell_not_piTyCode convToPiCode)
    (fun _levelExpr _flag convToUniverseCode => Conv.natTypeCell_not_universeCode convToUniverseCode)
    subject typed

/-- **Non-vacuity**: `1 = succ 0` is a canonical closed nat — `closedNatCanonicalForms` on
`HasTypeDescNatIntro.natOneTyped` (the recursive-arm witness). -/
theorem closedNatCanonicalForms.natOne {profile : PolyProfile} :
    ∃ value : RawTerm 0, StepStar (natSuccCell natZeroCell : RawTerm 0) value ∧ IsNatNumeral value :=
  closedNatCanonicalForms (profile := profile) (Or.inl HasTypeDescNatIntro.natOneTyped)

end FX1Poly.Typed
