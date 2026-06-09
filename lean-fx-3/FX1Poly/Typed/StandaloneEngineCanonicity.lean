import FX1Poly.Typed.HasTypeDescDataIntroInversion
import FX1Poly.Typed.HasTypeDescDataIntroMetatheory
import FX1Poly.Typed.HasTypeDescBaseTypeMetatheory

/-! # FX1Poly/Typed/StandaloneEngineCanonicity — combined canonical forms over the two STANDALONE
    (non-grown) typing engines: `HasTypeDescDataIntro` (data values) + `HasTypeDescBaseType` (base type
    codes).  A CANON-1 (#1048) ingredient — the cascade-free combined closed-canonical-forms frame.

`HasTypeDescDataIntro` types the data VALUE constructors at their data type codes (`boolTrue`/`boolFalse`
: `boolCode`); `HasTypeDescBaseType` types the nullary base TYPE codes at their universe (`boolCode`/
`emptyCode` : `Type@0`).  Combined bool canonicity asks: a closed term typed AT `boolCode` (the classifier)
by EITHER engine — what is it?  The two engines occupy DISJOINT classifier slots (the value engine
classifies at `boolCode`; the type engine classifies at `Type@0`), so the question resolves cleanly with no
overlap:

  * **`standaloneBoolCanonicalForms` (★)** — a subject typed at `boolTypeCell` by `HasTypeDescDataIntro` OR
    `HasTypeDescBaseType` is `boolTrueCell` or `boolFalseCell`.  The data-intro disjunct gives it directly
    (`subjectIsBoolConstructor`); the base-type disjunct is RULED OUT — the base-type classifier is
    `Type@0(standard)` (`classifierIsType0`), whose head `gen_universeCode` is not `boolCode`'s head
    (`gen_boolCode`), contradicting the hypothesis that the classifier is `boolTypeCell`.  The combined
    closed-canonical-forms over the standalone engines (the grown disjunct — `HasTypeDescPi` at `boolCode`,
    which can arise only via `conv`/`piElim` — is the remaining CANON-1 residual).
  * **`standaloneEmptyUninhabited`** — NOTHING is typed at `emptyTypeCell` by either standalone engine: the
    data-intro classifier is `boolCode` (≠ `Empty`), the base-type classifier is `Type@0` (≠ `Empty`).  The
    standalone-engine half of SN-050 consistency (`Empty` has no closed standalone inhabitant).
  * **`dataIntroAndBaseTypeSubjectsDisjoint`** — no subject is typed by BOTH engines: a data-intro subject
    is a VALUE (`boolTrue`/`boolFalse`), a base-type subject is a TYPE CODE (`boolCode`/`emptyCode`), and
    their head generators are disjoint.  The no-confusion fact that the combined engine is a genuine
    disjoint union (the value layer and the type layer never type the same term).

## Zero-axiom

The subject- and classifier-form lemmas (`subjectIsBoolConstructor` / `subjectIsBaseTypeCode` /
`classifierIsBoolTypeCell` / `classifierIsType0`) + `congrArg RawTerm.headGenerator` + `Generator.noConfusion`
(the cross-generator discrimination idiom).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **★ Combined bool canonical forms over the standalone engines.**  A subject typed at the bool type code
`boolTypeCell` by the data-intro engine OR the base-type engine is `boolTrueCell` or `boolFalseCell`.  The
data-intro disjunct yields the bool value directly; the base-type disjunct is impossible (its classifier is
`Type@0`, not `boolCode`).  The CANON-1 combined closed-canonical-forms over the two standalone engines. -/
theorem standaloneBoolCanonicalForms {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject : RawTerm scope}
    (typed : HasTypeDescDataIntro profile context subject boolTypeCell ∨
             HasTypeDescBaseType profile context subject boolTypeCell) :
    subject = boolTrueCell ∨ subject = boolFalseCell := by
  rcases typed with dataIntroTyped | baseTypeTyped
  · exact dataIntroTyped.subjectIsBoolConstructor
  · exact Generator.noConfusion
      (congrArg RawTerm.headGenerator baseTypeTyped.classifierIsType0 :
        Generator.gen_boolCode = Generator.gen_universeCode)

/-- **The empty type code has no closed standalone inhabitant.**  Nothing is typed at `emptyTypeCell` by
either standalone engine: the data-intro classifier is `boolTypeCell` (`gen_boolCode`), the base-type
classifier is `Type@0` (`gen_universeCode`), and neither head is `emptyCode`'s (`gen_emptyCode`).  The
standalone-engine half of SN-050 consistency. -/
theorem standaloneEmptyUninhabited {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject : RawTerm scope}
    (typed : HasTypeDescDataIntro profile context subject emptyTypeCell ∨
             HasTypeDescBaseType profile context subject emptyTypeCell) :
    False := by
  rcases typed with dataIntroTyped | baseTypeTyped
  · exact Generator.noConfusion
      (congrArg RawTerm.headGenerator dataIntroTyped.classifierIsBoolTypeCell :
        Generator.gen_emptyCode = Generator.gen_boolCode)
  · exact Generator.noConfusion
      (congrArg RawTerm.headGenerator baseTypeTyped.classifierIsType0 :
        Generator.gen_emptyCode = Generator.gen_universeCode)

/-- **The standalone engines are subject-disjoint.**  No subject is typed by BOTH `HasTypeDescDataIntro` and
`HasTypeDescBaseType`: a data-intro subject is a data VALUE (`boolTrueCell` / `boolFalseCell`), a base-type
subject is a TYPE CODE (`boolTypeCell` / `emptyTypeCell`), and the value and type head generators are
disjoint.  The no-confusion fact that the combined engine is a genuine disjoint union — the value layer and
the type layer never type the same term. -/
theorem dataIntroAndBaseTypeSubjectsDisjoint {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subject valueClassifier typeClassifier : RawTerm scope}
    (dataIntroTyped : HasTypeDescDataIntro profile context subject valueClassifier)
    (baseTypeTyped : HasTypeDescBaseType profile context subject typeClassifier) :
    False := by
  rcases dataIntroTyped.subjectIsBoolConstructor with valueIsTrue | valueIsFalse
  · rcases baseTypeTyped.subjectIsBaseTypeCode with typeIsBool | typeIsEmpty | typeIsNat
    · rw [valueIsTrue] at typeIsBool
      exact Generator.noConfusion
        (congrArg RawTerm.headGenerator typeIsBool :
          Generator.gen_boolTrue = Generator.gen_boolCode)
    · rw [valueIsTrue] at typeIsEmpty
      exact Generator.noConfusion
        (congrArg RawTerm.headGenerator typeIsEmpty :
          Generator.gen_boolTrue = Generator.gen_emptyCode)
    · rw [valueIsTrue] at typeIsNat
      exact Generator.noConfusion
        (congrArg RawTerm.headGenerator typeIsNat :
          Generator.gen_boolTrue = Generator.gen_natCode)
  · rcases baseTypeTyped.subjectIsBaseTypeCode with typeIsBool | typeIsEmpty | typeIsNat
    · rw [valueIsFalse] at typeIsBool
      exact Generator.noConfusion
        (congrArg RawTerm.headGenerator typeIsBool :
          Generator.gen_boolFalse = Generator.gen_boolCode)
    · rw [valueIsFalse] at typeIsEmpty
      exact Generator.noConfusion
        (congrArg RawTerm.headGenerator typeIsEmpty :
          Generator.gen_boolFalse = Generator.gen_emptyCode)
    · rw [valueIsFalse] at typeIsNat
      exact Generator.noConfusion
        (congrArg RawTerm.headGenerator typeIsNat :
          Generator.gen_boolFalse = Generator.gen_natCode)

end FX1Poly.Typed
