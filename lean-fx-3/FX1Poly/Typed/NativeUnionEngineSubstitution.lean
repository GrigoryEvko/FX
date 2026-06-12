import FX1Poly.Typed.NativeUnionCellSubstitution
import FX1Poly.Typed.HasTypeDescPiSubstitution
import FX1Poly.Typed.HasTypeDescBaseType
import FX1Poly.Typed.HasTypeDescDataIntro

/-! # FX1Poly/Typed/NativeUnionEngineSubstitution — per-engine term substitution for the scrutinee /
    base-type / data-intro embedding engines (the native-union substitution lemma's embedding-arm legs)

The native-union substitution lemma routes each engine-embedding arm through that engine's own
`substRespectingContext`.  The grown engine (`HasTypeDescPi`) and the term-indexed former
(`HasTypeDescTermIndexedFormer`) ship theirs; this file supplies the small ones the embedding arms need —
the nullary base-type / data-intro formations (subject `mkGen`, classifier a closed universe / type code,
no binder-crossing premises).  (The six zoo value-constructor substitution twins — Nat / Option /
Either / Id / Pair / List — were RETIRED with the NATIVE-42 embedding-arm deletion: those values now
enter the union through native table rows whose premises recurse in the union itself.)

Each is `cases` over the engine + the cell-subst `rfl` commutations.  The base-type and
data-intro nullary arms reconstruct the abstract `mkGen` via `RawTerm.subst_mkGen_of_ne_var` exactly as
`HasTypeDesc.substIntoGrown`'s `genFormation` case does.

## Zero-axiom

`cases`/`induction` + `subst_mkGen_of_ne_var` + the cell-subst `rfl` lemmas + `HasTypeDescPi`'s shipped
substitution.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Audit-gated in `FX1PolyAudit/AuditNativeUnionSubstitution.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-! ## Generators excluded from `gen_var` — needed to reconstruct the abstract nullary `mkGen` cells -/

/-- A base-type table hit forces the generator off `gen_var` (a base type-code is not a variable). -/
theorem baseTypeRuleImpliesNotVariable {generator : Generator} {rule : BaseTypeRuleDesc}
    (isBaseType : baseTypeRuleDescOf generator = some rule) :
    generator ≠ Generator.gen_var := by
  intro isVar
  subst isVar
  exact absurd isBaseType (by intro hit; cases hit)

/-- A nullary data-intro table hit forces the generator off `gen_var`. -/
theorem dataIntroNullaryRuleImpliesNotVariable {generator : Generator}
    {rule : DataIntroNullaryRuleDesc}
    (isDataIntro : dataIntroNullaryRuleDescOf generator = some rule) :
    generator ≠ Generator.gen_var := by
  intro isVar
  subst isVar
  exact absurd isDataIntro (by intro hit; cases hit)

/-- A nullary data-intro rule's output type code is a closed nullary cell, hence substitution-invariant
across scopes (`subst σ (output source) = output target`).  Reads off the five-row table. -/
theorem dataIntroNullaryRuleDescOf_outputSubstStable {generator : Generator}
    {rule : DataIntroNullaryRuleDesc}
    (isDataIntro : dataIntroNullaryRuleDescOf generator = some rule)
    {sourceScope targetScope : Nat} (substitution : RawTermSubst sourceScope targetScope) :
    RawTerm.subst substitution (rule.outputTypeCode sourceScope)
      = rule.outputTypeCode targetScope := by
  rcases dataIntroNullaryRuleDescOf_isNullaryValueConstructor isDataIntro with
    hTrue | hFalse | hUnit | hZero | hOne | hNatZero
  · subst hTrue
    have hrule : rule = { outputTypeCode := fun _ => boolTypeCell } :=
      (Option.some.inj isDataIntro).symm
    rw [hrule]
    rfl
  · subst hFalse
    have hrule : rule = { outputTypeCode := fun _ => boolTypeCell } :=
      (Option.some.inj isDataIntro).symm
    rw [hrule]
    rfl
  · subst hUnit
    have hrule : rule = { outputTypeCode := fun _ => unitTypeCell } :=
      (Option.some.inj isDataIntro).symm
    rw [hrule]
    rfl
  · subst hZero
    have hrule : rule = { outputTypeCode := fun _ => intervalTypeCell } :=
      (Option.some.inj isDataIntro).symm
    rw [hrule]
    rfl
  · subst hOne
    have hrule : rule = { outputTypeCode := fun _ => intervalTypeCell } :=
      (Option.some.inj isDataIntro).symm
    rw [hrule]
    rfl
  · subst hNatZero
    have hrule : rule = { outputTypeCode := fun _ => natTypeCell } :=
      (Option.some.inj isDataIntro).symm
    rw [hrule]
    rfl

/-! ## Base-type formation substitution (closed nullary subjects/classifiers) -/

/-- **Base-type formation substitution.**  `HasTypeDescBaseType` is preserved along any substitution: the
subject is a nullary `mkGen` (reconstructed via `subst_mkGen_of_ne_var`), the classifier is the rule's
closed output universe (substitution-invariant). -/
theorem HasTypeDescBaseType.substRespectingContext {profile : PolyProfile} {sourceScope : Nat}
    {sourceContext : TypingContext profile sourceScope} {subject classifier : RawTerm sourceScope}
    (derivation : HasTypeDescBaseType profile sourceContext subject classifier) :
    ∀ {targetScope : Nat} (targetContext : TypingContext profile targetScope)
      (substitution : RawTermSubst sourceScope targetScope),
      (∀ index : Fin sourceScope,
        HasTypeDescPi profile targetContext (substitution index)
          (RawTerm.subst substitution (sourceContext.lookup index))) →
      HasTypeDescBaseType profile targetContext
        (RawTerm.subst substitution subject) (RawTerm.subst substitution classifier) := by
  cases derivation with
  | baseFormation generator payload children rule isBaseType =>
      intro targetScope targetContext substitution _condition
      have hNotVar : generator ≠ Generator.gen_var := baseTypeRuleImpliesNotVariable isBaseType
      -- The output universe is `universeCodeCell lzero standard` for every base row, subst-invariant.
      have outputClosed : RawTerm.subst substitution (rule.outputUniverse sourceScope)
          = rule.outputUniverse targetScope := by
        rw [baseTypeRuleDescOf_outputIsType0 isBaseType]
        rfl
      rw [RawTerm.subst_mkGen_of_ne_var substitution hNotVar, outputClosed]
      exact HasTypeDescBaseType.baseFormation targetContext generator
        (Generator.payload_scope_invariant_of_not_var hNotVar _ _ ▸ payload)
        (RawTermChildren.subst substitution children) rule isBaseType

/-! ## Data-intro (nullary) substitution -/

/-- **Nullary data-intro substitution.**  `HasTypeDescDataIntro` is preserved: the subject is a nullary
`mkGen` (reconstructed via `subst_mkGen_of_ne_var`), the classifier is the rule's closed output type code. -/
theorem HasTypeDescDataIntro.substRespectingContext {profile : PolyProfile} {sourceScope : Nat}
    {sourceContext : TypingContext profile sourceScope} {subject classifier : RawTerm sourceScope}
    (derivation : HasTypeDescDataIntro profile sourceContext subject classifier) :
    ∀ {targetScope : Nat} (targetContext : TypingContext profile targetScope)
      (substitution : RawTermSubst sourceScope targetScope),
      (∀ index : Fin sourceScope,
        HasTypeDescPi profile targetContext (substitution index)
          (RawTerm.subst substitution (sourceContext.lookup index))) →
      HasTypeDescDataIntro profile targetContext
        (RawTerm.subst substitution subject) (RawTerm.subst substitution classifier) := by
  cases derivation with
  | nullaryIntro generator payload children rule isDataIntro =>
      intro targetScope targetContext substitution _condition
      have hNotVar : generator ≠ Generator.gen_var := dataIntroNullaryRuleImpliesNotVariable isDataIntro
      rw [RawTerm.subst_mkGen_of_ne_var substitution hNotVar,
        dataIntroNullaryRuleDescOf_outputSubstStable isDataIntro substitution]
      exact HasTypeDescDataIntro.nullaryIntro targetContext generator
        (Generator.payload_scope_invariant_of_not_var hNotVar _ _ ▸ payload)
        (RawTermChildren.subst substitution children) rule isDataIntro

/-! ## Nat-intro substitution (closed: classifier `natTypeCell`, predecessor recursive) -/

/-! ## Option-intro substitution -/

/-! ## Either-intro substitution -/

/-! ## Id-intro substitution -/

/-! ## Pair-intro substitution -/

/-! ## List-intro substitution -/

end FX1Poly.Typed
