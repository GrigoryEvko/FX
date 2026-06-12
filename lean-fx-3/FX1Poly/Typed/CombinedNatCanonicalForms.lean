import FX1Poly.Typed.CombinedClosedNormalValueHeads
import FX1Poly.Typed.ClosedNatCanonicity
import FX1Poly.Typed.HasTypeDescDataIntroMetatheory
import FX1Poly.Core.ConvNormalForm

/-! # FX1Poly/Typed/CombinedNatCanonicalForms — per-classifier Nat canonicity over the FULL
    value-engine union (CAN-5, the #1048 per-classifier assembly at the recursive classifier).

The bool instance of the per-classifier assembly shipped in CANON-1b
(`closedNormalBoolCanonicalForms`, over the then-current 3 engines).  CAN-4 widened the value
union to 8 engines (`TypedByValueEngine`).  This file assembles the per-classifier canonicity
at the RECURSIVE classifier `Nat` over the FULL union:

★ `closedNormalNatCanonicalFormsCombined` — a closed normal term typed at `natTypeCell` by ANY
value engine IS a numeral (`IsNatNumeral`).  The three arm kinds:

  * GROWN: `closedNatCanonicalForms` (the 2-engine theorem) produces a numeral REDUCT; the
    normality hypothesis collapses the chain (`StepStar.eq_of_noStep` — a normal term is
    `StepStar`-rigid), so the subject IS the numeral.
  * NAT-INTRO: `subjectIsNatNumeral` directly (nat-intro subjects are numerals on the nose).
  * THE OTHER SIX INTRO ENGINES: classifier-shape mismatch — each engine pins its classifier
    to its own type cell (`classifierIsBoolTypeCell` / `classifierIsProduct` / … ), whose head
    generator differs from `gen_natCode`; `congrArg headGenerator` + constructor disjointness
    refutes (`nomatch`).

This is the recursive-classifier capstone of the per-classifier program: bool (CANON-1b) had
two values, `Nat` has infinitely many — the conclusion is the recursive `IsNatNumeral` family,
fed by the recursive intro engine.  Together with the head theorem (CAN-4) and the rule-out
substrate (`ClosedNatCanonicity` rigidities) this closes the Nat lane of CANON-1 (#1048).

## Zero-axiom

One 8-arm `cases`; the mismatch arms are `congrArg` + `nomatch` on distinct generator
constructors; the grown arm composes shipped theorems.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **★ CAN-5 (Nat lane): per-classifier canonicity over the full value-engine union.**  A
closed normal term typed at `Nat` by ANY value engine is a numeral. -/
theorem closedNormalNatCanonicalFormsCombined {profile : PolyProfile} {subject : RawTerm 0}
    (typed : TypedByValueEngine profile (TypingContext.empty : TypingContext profile 0)
      subject natTypeCell)
    (normal : RawTerm.isStepNormalForm subject) :
    IsNatNumeral subject := by
  cases typed with
  | ofGrown grownTyped =>
      obtain ⟨value, chain, valueIsNumeral⟩ := closedNatCanonicalForms (Or.inr grownTyped)
      have valueEqSubject : value = subject :=
        StepStar.eq_of_noStep
          (fun reduct step => RawTerm.isStepNormalForm_blocks_step normal reduct step) chain
      exact valueEqSubject ▸ valueIsNumeral
  | ofNatIntro natTyped =>
      exact HasTypeDescNatIntro.subjectIsNatNumeral natTyped
  | ofBoolIntro boolTyped =>
      rcases HasTypeDescDataIntro.subjectClassifierCoordinated boolTyped with
        ⟨_, hClassifier⟩ | ⟨_, hClassifier⟩ | ⟨_, hClassifier⟩ | ⟨_, hClassifier⟩
          | ⟨_, hClassifier⟩ | ⟨hSubject, _⟩
      · exact nomatch congrArg RawTerm.headGenerator hClassifier
      · exact nomatch congrArg RawTerm.headGenerator hClassifier
      · exact nomatch congrArg RawTerm.headGenerator hClassifier
      · exact nomatch congrArg RawTerm.headGenerator hClassifier
      · exact nomatch congrArg RawTerm.headGenerator hClassifier
      · exact hSubject ▸ IsNatNumeral.zero
  | ofListIntro listTyped =>
      obtain ⟨elementType, classifierEq⟩ := HasTypeDescListIntro.classifierIsList listTyped
      exact nomatch congrArg RawTerm.headGenerator classifierEq
  | ofPairIntro pairTyped =>
      obtain ⟨firstType, secondType, classifierEq⟩ :=
        HasTypeDescPairIntro.classifierIsProduct pairTyped
      exact nomatch congrArg RawTerm.headGenerator classifierEq
  | ofEitherIntro eitherTyped =>
      obtain ⟨leftType, rightType, classifierEq⟩ :=
        HasTypeDescEitherIntro.classifierIsEither eitherTyped
      exact nomatch congrArg RawTerm.headGenerator classifierEq
  | ofOptionIntro optionTyped =>
      obtain ⟨elementType, classifierEq⟩ :=
        HasTypeDescOptionIntro.classifierIsOption optionTyped
      exact nomatch congrArg RawTerm.headGenerator classifierEq
  | ofIdIntro idTyped =>
      obtain ⟨typeCode, endpoint, classifierEq⟩ :=
        HasTypeDescIdIntro.classifierIsReflexiveId idTyped
      exact nomatch congrArg RawTerm.headGenerator classifierEq

/-- **Non-vacuity**: `2 = succ (succ 0)` is a closed normal nat-intro value, and the combined
theorem classifies it as a numeral. -/
theorem closedNormalNatCanonicalFormsCombined.natTwo {profile : PolyProfile}
    (natTwoNormal : RawTerm.isStepNormalForm (natSuccCell (natSuccCell natZeroCell) : RawTerm 0)) :
    IsNatNumeral (natSuccCell (natSuccCell natZeroCell) : RawTerm 0) :=
  closedNormalNatCanonicalFormsCombined (profile := profile)
    (TypedByValueEngine.ofNatIntro (HasTypeDescNatIntro.natTwoTyped (profile := profile)))
    natTwoNormal

end FX1Poly.Typed
