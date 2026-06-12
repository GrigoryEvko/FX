import FX1Poly.Typed.HasTypeUnion
import FX1Poly.Core.IntervalCanonicalFormsCandidate

/-! # FX1Poly/Typed/StandaloneEngineCanonicity — combined canonical forms over the two NULLARY-FORMATION
    union arms: `HasTypeUnion.dataIntroNullary` (data values) + `HasTypeUnion.baseTypeFormation`
    (base type codes).  A CANON-1 (#1048) ingredient — the cascade-free combined closed-canonical-forms frame.

The `dataIntroNullary` arm types the data VALUE constructors at their data type codes (`boolTrue`/`boolFalse`
: `boolCode`); the `baseTypeFormation` arm types the nullary base TYPE codes at their universe (`boolCode`/
`emptyCode` : `Type@0`).  Combined bool canonicity asks: a closed cell typed AT `boolCode` (the classifier)
by EITHER arm — what is it?  The two arms occupy DISJOINT classifier slots (the value arm classifies at
`boolCode`; the type arm classifies at `Type@0`), so the question resolves cleanly with no overlap.

Each lemma takes the arm's table-rule WITNESS data directly — the generator, its `…RuleDescOf … = some rule`
hit, and the classifier-equality (`rule.outputTypeCode scope = boolTypeCell` / `rule.outputUniverse scope =
boolTypeCell`) — so a caller holding a `dataIntroNullary` / `baseTypeFormation` arm at the relevant classifier
feeds it directly after destructuring the arm.  The arm rows are decoded with the `UnionRuleTables`
helpers (`dataIntroNullaryRuleTableHitIsValueConstructor` / `baseTypeRuleTableOutputIsType0`); the two retired
nullary data engines that previously stated these are gone — their formation/intro content is now the
`dataIntroNullary` / `baseTypeFormation` arms of `HasTypeUnion`.

  * **`standaloneBoolCanonicalForms` (★)** — a cell typed at `boolTypeCell` by the `dataIntroNullary` row OR
    the `baseTypeFormation` row is `boolTrueCell` or `boolFalseCell`.  The data-intro disjunct gives it
    directly (the boolTrue/boolFalse rows pin `outputTypeCode = boolTypeCell`; the other four rows are RULED
    OUT by classifier-head mismatch); the base-type disjunct is RULED OUT — the base-type row's output is
    `Type@0(standard)` (`baseTypeRuleTableOutputIsType0`), whose head `gen_universeCode` is not
    `boolCode`'s head (`gen_boolCode`), contradicting the hypothesis that the classifier is `boolTypeCell`.
  * **`standaloneIntervalCanonicalForms`** — the interval twin: a cell typed at `intervalTypeCell` by either
    row is `intervalZeroValueCell` or `intervalOneValueCell`.
  * **`standaloneEmptyUninhabited`** — NOTHING is typed at `emptyTypeCell` by either row: the data-intro row
    output is one of the four non-empty data codes, the base-type row output is `Type@0`.  The
    nullary-formation half of SN-050 consistency (`Empty` has no closed nullary-formation inhabitant).
  * **`standaloneDataIntroAndBaseTypeSubjectsDisjoint`** — no cell is typed by BOTH rows: a data-intro cell
    is a VALUE constructor, a base-type cell is a TYPE CODE, and their head generators are disjoint.

## Zero-axiom

The rule-row decoders (`dataIntroNullaryRuleTableHitIsValueConstructor` /
`baseTypeRuleTableOutputIsType0`), `Option.some.inj` to pin the rule, + `congrArg RawTerm.headGenerator` +
`Generator.noConfusion` (the cross-generator discrimination idiom).  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- A `dataIntroNullary` table row whose output type code is `boolTypeCell` pins the generator to
`gen_boolTrue` or `gen_boolFalse` — the only two rows with bool output.  The other four rows
(`unit` / `interval0` / `interval1` / `natZero`) carry unit / interval / nat output, head-distinct from
`boolCode`, contradicting `rule.outputTypeCode scope = boolTypeCell`. -/
theorem dataIntroNullaryBoolRowIsBoolConstructor {scope : Nat} {generator : Generator}
    {rule : DataIntroNullaryRuleDesc}
    (isDataIntro : dataIntroNullaryRuleDescOf generator = some rule)
    (classifierEq : rule.outputTypeCode scope = boolTypeCell) :
    generator = .gen_boolTrue ∨ generator = .gen_boolFalse := by
  rcases dataIntroNullaryRuleTableHitIsValueConstructor isDataIntro with
    isTrue | isFalse | isUnit | isZero | isOne | isNatZero
  · exact Or.inl isTrue
  · exact Or.inr isFalse
  · subst isUnit
    have ruleEq : rule = { outputTypeCode := fun _ => unitTypeCell } :=
      (Option.some.inj isDataIntro).symm
    subst ruleEq
    exact Generator.noConfusion
      (congrArg RawTerm.headGenerator classifierEq :
        Generator.gen_unitCode = Generator.gen_boolCode)
  · subst isZero
    have ruleEq : rule = { outputTypeCode := fun _ => intervalTypeCell } :=
      (Option.some.inj isDataIntro).symm
    subst ruleEq
    exact Generator.noConfusion
      (congrArg RawTerm.headGenerator classifierEq :
        Generator.gen_intervalCode = Generator.gen_boolCode)
  · subst isOne
    have ruleEq : rule = { outputTypeCode := fun _ => intervalTypeCell } :=
      (Option.some.inj isDataIntro).symm
    subst ruleEq
    exact Generator.noConfusion
      (congrArg RawTerm.headGenerator classifierEq :
        Generator.gen_intervalCode = Generator.gen_boolCode)
  · subst isNatZero
    have ruleEq : rule = { outputTypeCode := fun _ => natTypeCell } :=
      (Option.some.inj isDataIntro).symm
    subst ruleEq
    exact Generator.noConfusion
      (congrArg RawTerm.headGenerator classifierEq :
        Generator.gen_natCode = Generator.gen_boolCode)

/-- **★ Combined bool canonical forms over the nullary-formation union arms.**  A cell
`.mkGen generator payload children` typed at the bool type code `boolTypeCell` by the `dataIntroNullary`
row (left disjunct: the table hit `isDataIntro` with classifier `rule.outputTypeCode scope = boolTypeCell`)
OR the `baseTypeFormation` row (right disjunct: the table hit `isBaseType` with classifier
`rule.outputUniverse scope = boolTypeCell`) is `boolTrueCell` or `boolFalseCell`.  The data-intro disjunct
yields the bool value via `dataIntroNullaryBoolRowIsBoolConstructor`; the base-type disjunct is impossible
(its output is `Type@0`, not `boolCode`).  The CANON-1 combined closed-canonical-forms over the two nullary
arms. -/
theorem standaloneBoolCanonicalForms {scope : Nat} {generator : Generator}
    {payload : generator.payload scope} {children : RawTermChildren generator.binderShifts scope}
    (typed :
      (∃ rule : DataIntroNullaryRuleDesc,
          dataIntroNullaryRuleDescOf generator = some rule ∧
          rule.outputTypeCode scope = boolTypeCell)
      ∨ (∃ rule : BaseTypeRuleDesc,
          baseTypeRuleDescOf generator = some rule ∧
          rule.outputUniverse scope = boolTypeCell)) :
    (RawTerm.mkGen generator payload children) = boolTrueCell ∨
    (RawTerm.mkGen generator payload children) = boolFalseCell := by
  rcases typed with ⟨rule, isDataIntro, classifierEq⟩ | ⟨rule, isBaseType, classifierEq⟩
  · rcases dataIntroNullaryBoolRowIsBoolConstructor isDataIntro classifierEq with isTrue | isFalse
    · subst isTrue; cases payload; cases children; exact Or.inl rfl
    · subst isFalse; cases payload; cases children; exact Or.inr rfl
  · rw [congrFun (baseTypeRuleTableOutputIsType0 isBaseType) scope] at classifierEq
    exact Generator.noConfusion
      (congrArg RawTerm.headGenerator classifierEq :
        Generator.gen_universeCode = Generator.gen_boolCode)

/-- A `dataIntroNullary` table row whose output type code is `intervalTypeCell` pins the generator to
`gen_interval0` or `gen_interval1`. -/
theorem dataIntroNullaryIntervalRowIsEndpoint {scope : Nat} {generator : Generator}
    {rule : DataIntroNullaryRuleDesc}
    (isDataIntro : dataIntroNullaryRuleDescOf generator = some rule)
    (classifierEq : rule.outputTypeCode scope = intervalTypeCell) :
    generator = .gen_interval0 ∨ generator = .gen_interval1 := by
  rcases dataIntroNullaryRuleTableHitIsValueConstructor isDataIntro with
    isTrue | isFalse | isUnit | isZero | isOne | isNatZero
  · subst isTrue
    have ruleEq : rule = { outputTypeCode := fun _ => boolTypeCell } :=
      (Option.some.inj isDataIntro).symm
    subst ruleEq
    exact Generator.noConfusion
      (congrArg RawTerm.headGenerator classifierEq :
        Generator.gen_boolCode = Generator.gen_intervalCode)
  · subst isFalse
    have ruleEq : rule = { outputTypeCode := fun _ => boolTypeCell } :=
      (Option.some.inj isDataIntro).symm
    subst ruleEq
    exact Generator.noConfusion
      (congrArg RawTerm.headGenerator classifierEq :
        Generator.gen_boolCode = Generator.gen_intervalCode)
  · subst isUnit
    have ruleEq : rule = { outputTypeCode := fun _ => unitTypeCell } :=
      (Option.some.inj isDataIntro).symm
    subst ruleEq
    exact Generator.noConfusion
      (congrArg RawTerm.headGenerator classifierEq :
        Generator.gen_unitCode = Generator.gen_intervalCode)
  · exact Or.inl isZero
  · exact Or.inr isOne
  · subst isNatZero
    have ruleEq : rule = { outputTypeCode := fun _ => natTypeCell } :=
      (Option.some.inj isDataIntro).symm
    subst ruleEq
    exact Generator.noConfusion
      (congrArg RawTerm.headGenerator classifierEq :
        Generator.gen_natCode = Generator.gen_intervalCode)

/-- **★ Combined interval canonical forms over the nullary-formation union arms (NATIVE-10).**  A cell
typed at the interval/dimension type code `intervalTypeCell` by the `dataIntroNullary` row OR the
`baseTypeFormation` row is `intervalZeroValueCell` or `intervalOneValueCell` — the two interval endpoints.
The interval twin of `standaloneBoolCanonicalForms`. -/
theorem standaloneIntervalCanonicalForms {scope : Nat} {generator : Generator}
    {payload : generator.payload scope} {children : RawTermChildren generator.binderShifts scope}
    (typed :
      (∃ rule : DataIntroNullaryRuleDesc,
          dataIntroNullaryRuleDescOf generator = some rule ∧
          rule.outputTypeCode scope = intervalTypeCell)
      ∨ (∃ rule : BaseTypeRuleDesc,
          baseTypeRuleDescOf generator = some rule ∧
          rule.outputUniverse scope = intervalTypeCell)) :
    (RawTerm.mkGen generator payload children) = intervalZeroValueCell ∨
    (RawTerm.mkGen generator payload children) = intervalOneValueCell := by
  rcases typed with ⟨rule, isDataIntro, classifierEq⟩ | ⟨rule, isBaseType, classifierEq⟩
  · rcases dataIntroNullaryIntervalRowIsEndpoint isDataIntro classifierEq with isZero | isOne
    · subst isZero; cases payload; cases children; exact Or.inl rfl
    · subst isOne; cases payload; cases children; exact Or.inr rfl
  · rw [congrFun (baseTypeRuleTableOutputIsType0 isBaseType) scope] at classifierEq
    exact Generator.noConfusion
      (congrArg RawTerm.headGenerator classifierEq :
        Generator.gen_universeCode = Generator.gen_intervalCode)

/-- **The two interval canonical forms are DISTINCT.**  `interval0 ≠ interval1` — distinct head
generators (`gen_interval0` vs `gen_interval1`, refuted by `Generator.noConfusion`).  The faithfulness
companion to `standaloneIntervalCanonicalForms`: the interval/dimension type has no endpoint collapse. -/
theorem intervalEndpointsDistinct {scope : Nat} :
    (intervalZeroValueCell : RawTerm scope) ≠ intervalOneValueCell :=
  fun endpointsEqual =>
    Generator.noConfusion
      (congrArg RawTerm.headGenerator endpointsEqual :
        Generator.gen_interval0 = Generator.gen_interval1)

/-- **★ The interval type has EXACTLY TWO distinct closed canonical forms.**  A cell typed at
`intervalTypeCell` by either nullary-formation arm is `interval0` or `interval1` (canonicity), and the two
are distinct (faithfulness) — so the bridge-dimension type has precisely two closed canonical inhabitants. -/
theorem standaloneIntervalCanonicalFormsExactlyTwo {scope : Nat} {generator : Generator}
    {payload : generator.payload scope} {children : RawTermChildren generator.binderShifts scope}
    (typed :
      (∃ rule : DataIntroNullaryRuleDesc,
          dataIntroNullaryRuleDescOf generator = some rule ∧
          rule.outputTypeCode scope = intervalTypeCell)
      ∨ (∃ rule : BaseTypeRuleDesc,
          baseTypeRuleDescOf generator = some rule ∧
          rule.outputUniverse scope = intervalTypeCell)) :
    ((RawTerm.mkGen generator payload children) = intervalZeroValueCell ∨
     (RawTerm.mkGen generator payload children) = intervalOneValueCell) ∧
    (intervalZeroValueCell : RawTerm scope) ≠ intervalOneValueCell :=
  ⟨standaloneIntervalCanonicalForms typed, intervalEndpointsDistinct⟩

/-- **The empty type code has no closed nullary-formation inhabitant.**  Nothing is typed at `emptyTypeCell`
by either nullary-formation union arm: the data-intro row output is one of the four non-empty data codes
(`boolCode` / `unitCode` / `intervalCode` / `natCode`), the base-type row output is `Type@0`
(`gen_universeCode`), and neither head is `emptyCode`'s (`gen_emptyCode`).  The nullary-formation half of
SN-050 consistency. -/
theorem standaloneEmptyUninhabited {scope : Nat} {generator : Generator}
    (typed :
      (∃ rule : DataIntroNullaryRuleDesc,
          dataIntroNullaryRuleDescOf generator = some rule ∧
          rule.outputTypeCode scope = emptyTypeCell)
      ∨ (∃ rule : BaseTypeRuleDesc,
          baseTypeRuleDescOf generator = some rule ∧
          rule.outputUniverse scope = emptyTypeCell)) :
    False := by
  rcases typed with ⟨rule, isDataIntro, classifierEq⟩ | ⟨rule, isBaseType, classifierEq⟩
  · rcases dataIntroNullaryRuleTableHitIsValueConstructor isDataIntro with
      isTrue | isFalse | isUnit | isZero | isOne | isNatZero
    · subst isTrue
      have ruleEq : rule = { outputTypeCode := fun _ => boolTypeCell } :=
        (Option.some.inj isDataIntro).symm
      subst ruleEq
      exact Generator.noConfusion
        (congrArg RawTerm.headGenerator classifierEq :
          Generator.gen_boolCode = Generator.gen_emptyCode)
    · subst isFalse
      have ruleEq : rule = { outputTypeCode := fun _ => boolTypeCell } :=
        (Option.some.inj isDataIntro).symm
      subst ruleEq
      exact Generator.noConfusion
        (congrArg RawTerm.headGenerator classifierEq :
          Generator.gen_boolCode = Generator.gen_emptyCode)
    · subst isUnit
      have ruleEq : rule = { outputTypeCode := fun _ => unitTypeCell } :=
        (Option.some.inj isDataIntro).symm
      subst ruleEq
      exact Generator.noConfusion
        (congrArg RawTerm.headGenerator classifierEq :
          Generator.gen_unitCode = Generator.gen_emptyCode)
    · subst isZero
      have ruleEq : rule = { outputTypeCode := fun _ => intervalTypeCell } :=
        (Option.some.inj isDataIntro).symm
      subst ruleEq
      exact Generator.noConfusion
        (congrArg RawTerm.headGenerator classifierEq :
          Generator.gen_intervalCode = Generator.gen_emptyCode)
    · subst isOne
      have ruleEq : rule = { outputTypeCode := fun _ => intervalTypeCell } :=
        (Option.some.inj isDataIntro).symm
      subst ruleEq
      exact Generator.noConfusion
        (congrArg RawTerm.headGenerator classifierEq :
          Generator.gen_intervalCode = Generator.gen_emptyCode)
    · subst isNatZero
      have ruleEq : rule = { outputTypeCode := fun _ => natTypeCell } :=
        (Option.some.inj isDataIntro).symm
      subst ruleEq
      exact Generator.noConfusion
        (congrArg RawTerm.headGenerator classifierEq :
          Generator.gen_natCode = Generator.gen_emptyCode)
  · rw [congrFun (baseTypeRuleTableOutputIsType0 isBaseType) scope] at classifierEq
    exact Generator.noConfusion
      (congrArg RawTerm.headGenerator classifierEq :
        Generator.gen_universeCode = Generator.gen_emptyCode)

/-- **The two nullary-formation arms are subject-disjoint.**  No cell is typed by BOTH the `dataIntroNullary`
row and the `baseTypeFormation` row: a data-intro cell is a data VALUE (one of the six nullary constructors),
a base-type cell is a TYPE CODE (one of the five nullary base codes), and the value and type head generators
are disjoint.  The no-confusion fact that the combined nullary layer is a genuine disjoint union — the value
layer and the type layer never type the same cell. -/
theorem standaloneDataIntroAndBaseTypeSubjectsDisjoint {generator : Generator}
    {dataRule : DataIntroNullaryRuleDesc} {baseRule : BaseTypeRuleDesc}
    (isDataIntro : dataIntroNullaryRuleDescOf generator = some dataRule)
    (isBaseType : baseTypeRuleDescOf generator = some baseRule) :
    False := by
  rcases dataIntroNullaryRuleTableHitIsValueConstructor isDataIntro with
      valueEq | valueEq | valueEq | valueEq | valueEq | valueEq <;>
    rcases baseTypeRuleTableHitIsNullaryBaseCode isBaseType with
      typeEq | typeEq | typeEq | typeEq | typeEq <;>
      (rw [valueEq] at typeEq
       exact Generator.noConfusion typeEq)

end FX1Poly.Typed
