import FX1Poly.Typed.NativeUnionCellSubstitution
import FX1Poly.Typed.HasTypeDescPiSubstitution
import FX1Poly.Typed.HasTypeDescBaseType
import FX1Poly.Typed.HasTypeDescDataIntro
import FX1Poly.Typed.HasTypeDescNatIntro
import FX1Poly.Typed.HasTypeDescOptionIntro
import FX1Poly.Typed.HasTypeDescEitherIntro
import FX1Poly.Typed.HasTypeDescIdIntro
import FX1Poly.Typed.HasTypeDescPairIntro
import FX1Poly.Typed.HasTypeDescListIntro

/-! # FX1Poly/Typed/NativeUnionEngineSubstitution — per-engine term substitution for the scrutinee /
    base-type / data-intro embedding engines (the native-union substitution lemma's embedding-arm legs)

The native-union substitution lemma routes each engine-embedding arm through that engine's own
`substRespectingContext`.  The grown engine (`HasTypeDescPi`) and the term-indexed former
(`HasTypeDescTermIndexedFormer`) ship theirs; this file supplies the small ones the embedding arms need —
the nullary base-type / data-intro formations (subject `mkGen`, classifier a closed universe / type code,
no binder-crossing premises) and the value-constructor engines (Nat / Option / Either / Id / Pair / List,
1-2 arm inductives whose only host premises route through `HasTypeDescPi.substRespectingContext`).

Each is `cases`/`induction` over the engine + the cell-subst `rfl` commutations.  The base-type and
data-intro nullary arms reconstruct the abstract `mkGen` via `RawTerm.subst_mkGen_of_ne_var` exactly as
`HasTypeDesc.substIntoGrown`'s `genFormation` case does; the value engines push the substitution through
their member cells and recurse / cite `HasTypeDescPi.substRespectingContext` on the value premises.

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
    hTrue | hFalse | hUnit | hZero | hOne
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

/-- **Nat-intro substitution.**  `natZero` / `natSucc(p)` both classify at `natTypeCell` (subst-invariant);
`natSucc` recurses on the predecessor.  No substituent condition is consulted (the predecessor is
nat-intro-typed, not host-typed). -/
theorem HasTypeDescNatIntro.substRespectingContext {profile : PolyProfile} {sourceScope : Nat}
    {sourceContext : TypingContext profile sourceScope} {subject classifier : RawTerm sourceScope}
    (derivation : HasTypeDescNatIntro profile sourceContext subject classifier) :
    ∀ {targetScope : Nat} (targetContext : TypingContext profile targetScope)
      (substitution : RawTermSubst sourceScope targetScope),
      (∀ index : Fin sourceScope,
        HasTypeDescPi profile targetContext (substitution index)
          (RawTerm.subst substitution (sourceContext.lookup index))) →
      HasTypeDescNatIntro profile targetContext
        (RawTerm.subst substitution subject) (RawTerm.subst substitution classifier) := by
  induction derivation with
  | natZeroIntro =>
      intro targetScope targetContext substitution _condition
      rw [subst_natZeroCell, subst_natTypeCell]
      exact HasTypeDescNatIntro.natZeroIntro targetContext
  | natSuccIntro predecessor _predecessorTyped predecessorIH =>
      intro targetScope targetContext substitution condition
      rw [subst_natSuccCell, subst_natTypeCell]
      have predecessorSubst := predecessorIH targetContext substitution condition
      rw [subst_natTypeCell] at predecessorSubst
      exact HasTypeDescNatIntro.natSuccIntro targetContext
        (RawTerm.subst substitution predecessor) predecessorSubst

/-! ## Option-intro substitution -/

/-- **Option-intro substitution.**  `optionNone` / `optionSome(v)` classify at `option(A)`; the
element-type formation / value premises route through `HasTypeDescPi.substRespectingContext`. -/
theorem HasTypeDescOptionIntro.substRespectingContext {profile : PolyProfile} {sourceScope : Nat}
    {sourceContext : TypingContext profile sourceScope} {subject classifier : RawTerm sourceScope}
    (derivation : HasTypeDescOptionIntro profile sourceContext subject classifier) :
    ∀ {targetScope : Nat} (targetContext : TypingContext profile targetScope)
      (substitution : RawTermSubst sourceScope targetScope),
      (∀ index : Fin sourceScope,
        HasTypeDescPi profile targetContext (substitution index)
          (RawTerm.subst substitution (sourceContext.lookup index))) →
      HasTypeDescOptionIntro profile targetContext
        (RawTerm.subst substitution subject) (RawTerm.subst substitution classifier) := by
  cases derivation with
  | optionNoneIntro elementType elementLevel flag elementTypeFormed =>
      intro targetScope targetContext substitution condition
      rw [subst_optionNoneCell, subst_optionTypeCell]
      have elementFormSubst := elementTypeFormed.substRespectingContext targetContext substitution condition
      rw [subst_universeCodeCell] at elementFormSubst
      exact HasTypeDescOptionIntro.optionNoneIntro targetContext
        (RawTerm.subst substitution elementType) elementLevel flag elementFormSubst
  | optionSomeIntro value elementType valueTyped =>
      intro targetScope targetContext substitution condition
      rw [subst_optionSomeCell, subst_optionTypeCell]
      exact HasTypeDescOptionIntro.optionSomeIntro targetContext
        (RawTerm.subst substitution value) (RawTerm.subst substitution elementType)
        (valueTyped.substRespectingContext targetContext substitution condition)

/-! ## Either-intro substitution -/

/-- **Either-intro substitution.**  `eitherInl(v)` / `eitherInr(v)` classify at `either(A, B)`; the value
and free-type premises route through `HasTypeDescPi.substRespectingContext`. -/
theorem HasTypeDescEitherIntro.substRespectingContext {profile : PolyProfile} {sourceScope : Nat}
    {sourceContext : TypingContext profile sourceScope} {subject classifier : RawTerm sourceScope}
    (derivation : HasTypeDescEitherIntro profile sourceContext subject classifier) :
    ∀ {targetScope : Nat} (targetContext : TypingContext profile targetScope)
      (substitution : RawTermSubst sourceScope targetScope),
      (∀ index : Fin sourceScope,
        HasTypeDescPi profile targetContext (substitution index)
          (RawTerm.subst substitution (sourceContext.lookup index))) →
      HasTypeDescEitherIntro profile targetContext
        (RawTerm.subst substitution subject) (RawTerm.subst substitution classifier) := by
  cases derivation with
  | eitherInlIntro leftValue leftType rightType rightLevel flag leftTyped rightTypeFormed =>
      intro targetScope targetContext substitution condition
      rw [subst_eitherInlCell, subst_eitherTypeCell]
      have rightFormSubst := rightTypeFormed.substRespectingContext targetContext substitution condition
      rw [subst_universeCodeCell] at rightFormSubst
      exact HasTypeDescEitherIntro.eitherInlIntro targetContext
        (RawTerm.subst substitution leftValue) (RawTerm.subst substitution leftType)
        (RawTerm.subst substitution rightType) rightLevel flag
        (leftTyped.substRespectingContext targetContext substitution condition) rightFormSubst
  | eitherInrIntro rightValue leftType rightType leftLevel flag rightTyped leftTypeFormed =>
      intro targetScope targetContext substitution condition
      rw [subst_eitherInrCell, subst_eitherTypeCell]
      have leftFormSubst := leftTypeFormed.substRespectingContext targetContext substitution condition
      rw [subst_universeCodeCell] at leftFormSubst
      exact HasTypeDescEitherIntro.eitherInrIntro targetContext
        (RawTerm.subst substitution rightValue) (RawTerm.subst substitution leftType)
        (RawTerm.subst substitution rightType) leftLevel flag
        (rightTyped.substRespectingContext targetContext substitution condition) leftFormSubst

/-! ## Id-intro substitution -/

/-- **Id-intro substitution.**  `refl(w)` classifies at `Id(A, w, w)`; the witness premise routes through
`HasTypeDescPi.substRespectingContext`. -/
theorem HasTypeDescIdIntro.substRespectingContext {profile : PolyProfile} {sourceScope : Nat}
    {sourceContext : TypingContext profile sourceScope} {subject classifier : RawTerm sourceScope}
    (derivation : HasTypeDescIdIntro profile sourceContext subject classifier) :
    ∀ {targetScope : Nat} (targetContext : TypingContext profile targetScope)
      (substitution : RawTermSubst sourceScope targetScope),
      (∀ index : Fin sourceScope,
        HasTypeDescPi profile targetContext (substitution index)
          (RawTerm.subst substitution (sourceContext.lookup index))) →
      HasTypeDescIdIntro profile targetContext
        (RawTerm.subst substitution subject) (RawTerm.subst substitution classifier) := by
  cases derivation with
  | reflIntro witness typeCode witnessTyped =>
      intro targetScope targetContext substitution condition
      rw [subst_reflCell, subst_idTypeCell]
      exact HasTypeDescIdIntro.reflIntro targetContext
        (RawTerm.subst substitution witness) (RawTerm.subst substitution typeCode)
        (witnessTyped.substRespectingContext targetContext substitution condition)

/-! ## Pair-intro substitution -/

/-- **Pair-intro substitution.**  `pair(x, y)` classifies at `A × B`; both value premises route through
`HasTypeDescPi.substRespectingContext`. -/
theorem HasTypeDescPairIntro.substRespectingContext {profile : PolyProfile} {sourceScope : Nat}
    {sourceContext : TypingContext profile sourceScope} {subject classifier : RawTerm sourceScope}
    (derivation : HasTypeDescPairIntro profile sourceContext subject classifier) :
    ∀ {targetScope : Nat} (targetContext : TypingContext profile targetScope)
      (substitution : RawTermSubst sourceScope targetScope),
      (∀ index : Fin sourceScope,
        HasTypeDescPi profile targetContext (substitution index)
          (RawTerm.subst substitution (sourceContext.lookup index))) →
      HasTypeDescPairIntro profile targetContext
        (RawTerm.subst substitution subject) (RawTerm.subst substitution classifier) := by
  cases derivation with
  | pairIntro firstValue secondValue firstType secondType firstTyped secondTyped =>
      intro targetScope targetContext substitution condition
      rw [subst_pairCell, subst_productTypeCell]
      exact HasTypeDescPairIntro.pairIntro targetContext
        (RawTerm.subst substitution firstValue) (RawTerm.subst substitution secondValue)
        (RawTerm.subst substitution firstType) (RawTerm.subst substitution secondType)
        (firstTyped.substRespectingContext targetContext substitution condition)
        (secondTyped.substRespectingContext targetContext substitution condition)

/-! ## List-intro substitution -/

/-- **List-intro substitution.**  `listNil` / `listCons(h, t)` classify at `list(A)`; the element-type
formation / head premises route through `HasTypeDescPi.substRespectingContext`, the tail recurses. -/
theorem HasTypeDescListIntro.substRespectingContext {profile : PolyProfile} {sourceScope : Nat}
    {sourceContext : TypingContext profile sourceScope} {subject classifier : RawTerm sourceScope}
    (derivation : HasTypeDescListIntro profile sourceContext subject classifier) :
    ∀ {targetScope : Nat} (targetContext : TypingContext profile targetScope)
      (substitution : RawTermSubst sourceScope targetScope),
      (∀ index : Fin sourceScope,
        HasTypeDescPi profile targetContext (substitution index)
          (RawTerm.subst substitution (sourceContext.lookup index))) →
      HasTypeDescListIntro profile targetContext
        (RawTerm.subst substitution subject) (RawTerm.subst substitution classifier) := by
  induction derivation with
  | listNilIntro elementType elementLevel flag elementTypeFormed =>
      intro targetScope targetContext substitution condition
      rw [subst_listNilCell, subst_listTypeCell]
      have elementFormSubst := elementTypeFormed.substRespectingContext targetContext substitution condition
      rw [subst_universeCodeCell] at elementFormSubst
      exact HasTypeDescListIntro.listNilIntro targetContext
        (RawTerm.subst substitution elementType) elementLevel flag elementFormSubst
  | listConsIntro headValue tailList elementType headTyped _tailTyped tailIH =>
      intro targetScope targetContext substitution condition
      rw [subst_listConsCell, subst_listTypeCell]
      have tailSubst := tailIH targetContext substitution condition
      rw [subst_listTypeCell] at tailSubst
      exact HasTypeDescListIntro.listConsIntro targetContext
        (RawTerm.subst substitution headValue) (RawTerm.subst substitution tailList)
        (RawTerm.subst substitution elementType)
        (headTyped.substRespectingContext targetContext substitution condition) tailSubst

end FX1Poly.Typed
