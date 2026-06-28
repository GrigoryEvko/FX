import FX1Poly.Typed.Engine.Union.HasTypeUnion
import FX1Poly.Typed.Cell.RawTermHeadGenerator
import FX1Poly.Typed.Engine.WfContext.WfContextDescPiFromWfContextDesc
import FX1Poly.Typed.Equality.Eta.TableBetaEtaRootConvAlgebra

/-! # FX1Poly/Typed/UnitEtaJudgmentalEquality
   — ★ typed unit-η: the judgmental equality βη-conversion CANNOT express, decidable (#362 core)

The first genuinely TYPE-DIRECTED judgmental-equality extension: `DefEqUnitEta` is the table-native
union beta-eta conversion (`ConvTableBetaEtaRoot`, decided by `decidableOfWfTyped`) extended by the
unit-η rule — ANY two terms typed at `unitTypeCell` are equal.  Raw rewriting can never have this
rule: an unconditional
raw unit-η is unsound (deliberately excluded from `Step.eta`), because whether the collapse is
justified depends on the TYPE, not the term's shape.  This module ships the relation, its
equivalence package, the strictness witness, and the decider:

  * `DefEqUnitEta` — two arms, presupposition-carrying: `ofConvTable` (wf context + both subjects
    grown-typed at the classifier + the TABLE-NATIVE `ConvTableBetaEtaRoot`) and `unitEta` (both
    subjects typed at `unitTypeCell` by the nullary value layer or the grown engine — no reduction,
    no well-formedness: the one-value collapse is type-directed).  The conversion arm is
    table-native throughout; consumers build the `ConvTableBetaEtaRoot` join directly (β/ι joins
    via `ConvTableBetaEtaRoot.ofConv`, η-expansions via `ConvTableBetaEtaRoot.etaLamExpansion`).
  * `refl` / `sym` / `trans` — `trans` is UNCONDITIONAL given the derivations (the union peak is
    discharged by `ConvTableBetaEtaRoot.transAtTypedMiddle` with the wf + middle-typing the first arm
    CARRIES; every unit-involving case re-fires `unitEta`).
  * ★ `strictlyExtendsConvTable` — the textbook witness: a unit-typed VARIABLE vs the unit value
    `unitCell`, in the raw context binding `unitTypeCell`.  Both are union-normal and distinct, so
    NOT `ConvTableBetaEtaRoot`; both are typed at `unitTypeCell` (the grown var rule needs no
    well-formedness), so `DefEqUnitEta`.  This is inexpressible at the raw layer and was
    inexpressible before UNIT-1 landed the unit type.
  * `dataIntroUnitPairsCollapseToRefl` — the honest degeneracy boundary: on the nullary value fragment
    the `unitEta` arm is refl-degenerate (closed unit canonicity already collapses both sides to
    `unitCell`); the strictness genuinely lives at open unit-typed NEUTRALS.
  * ★ `decidableOfWfTyped` — the decider: compare the classifier with `unitTypeCell` (structural
    `DecidableEq`); at unit type the answer is always YES (`unitEta`); off unit type the `unitEta`
    arm is impossible (`convTableOfNotUnit` inversion) and the decision is exactly the table-native
    `ConvTableBetaEtaRoot.decidableOfWfTyped`.

## Honest boundaries

(1) NOT congruent: `DefEqUnitEta` does not collapse unit-typed SUBTERMS (a pair of unit-typed
components is not equated to a pair of `unitCell`s); the congruent closure is the η-long
type-directed readback (#481 / the #364 remainder), the named follow-on.  (2) DISCHARGED: the
nullary `unitCode` formation row landed (flag-pinned `nullaryFormerOutput`), so `WfContextDesc`
binds `unitTypeCell` (`unitVariableContextWellFormed`) and the strictness witness lives on the
DECIDABLE wf fragment (`strictlyExtendsConvTableOnWfFragment` / `unitVariableDecidable`); the
grown lift `unitVariableContextWellFormedPi` hands unit-typed variables the full wf metatheory
(open SN, open βη-SN, βη Church-Rosser, both deciders).  (3) SProp/modal η kin (η-M15e) remain
open.

## Zero-axiom verification

Structural `cases` on the two-arm relation, the table-native `ConvTableBetaEtaRoot` decider +
typed-middle transitivity, `reduceOnceTableBetaEtaRoot?_blocksStep` at `rfl`-computing union-normal
leaves, and `decide` head-clash discrimination.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`,
`native_decide`, `omega`.  Gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Nullary data-value typing — the union's nullary `intro` arm, projected.**  A childless data
constructor (`boolTrue` / `boolFalse` / `unit` / `interval0` / `interval1` / `natZero`) inhabits its
tabled output type-code.  This is exactly the content of the uniform `HasTypeUnion.intro` builder at a
nullary `IntroRule` row, kept as a
standalone projection so the unit-η judgment can carry a value-typed disjunct WITHOUT pulling the whole
union inductive (whose other arms would also type `gen_pair` cells, defeating the `subjectIsUnit`
inversion below).  Construct it from the union arm via `ofUnion`. -/
inductive NullaryDataValueTyped (profile : PolyProfile) {scope : Nat}
    (context : TypingContext profile scope) : RawTerm scope → RawTerm scope → Prop where
  | intro (generator : Generator) (payload : generator.payload scope)
      (children : RawTermChildren generator.binderShifts scope)
      (rule : DataIntroNullaryRuleDesc)
      (isDataIntro : dataIntroNullaryRuleDescOf generator = some rule) :
      NullaryDataValueTyped profile context (.mkGen generator payload children)
        (rule.outputTypeCode scope)

/-- The nullary data-value typing lifts into the union's `dataIntroNullary` arm — the projection is
faithful (every nullary value the projection types is union-typed at the same classifier). -/
theorem NullaryDataValueTyped.ofUnion {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (typed : NullaryDataValueTyped profile context subject classifier) :
    HasTypeUnion profile context subject classifier := by
  cases typed with
  | intro generator payload children rule isDataIntro =>
      rcases dataIntroNullaryRuleTableHitIsValueConstructor isDataIntro with
        isTrue | isFalse | isUnit | isInterval0 | isInterval1 | isNatZero
      · -- boolTrue : Bool
        subst isTrue
        obtain rfl : rule = { outputTypeCode := fun _ => boolTypeCell } :=
          Option.some.inj (isDataIntro.symm.trans dataIntroNullaryRuleDescOf_boolTrue)
        cases payload; cases children
        refine HasTypeUnion.intro context .gen_boolTrue boolTrueIntroRule .childNil .childNil
          LevelExpr.lzero LevelExpr.lzero UniverseFlag.standard rfl trivial ?_
          (by dischargeUsability boolTrueIntroRule)
        intro obligation hmem; cases hmem
      · -- boolFalse : Bool
        subst isFalse
        obtain rfl : rule = { outputTypeCode := fun _ => boolTypeCell } :=
          Option.some.inj (isDataIntro.symm.trans dataIntroNullaryRuleDescOf_boolFalse)
        cases payload; cases children
        refine HasTypeUnion.intro context .gen_boolFalse boolFalseIntroRule .childNil .childNil
          LevelExpr.lzero LevelExpr.lzero UniverseFlag.standard rfl trivial ?_
          (by dischargeUsability boolFalseIntroRule)
        intro obligation hmem; cases hmem
      · -- unit : Unit
        subst isUnit
        obtain rfl : rule = { outputTypeCode := fun _ => unitTypeCell } :=
          Option.some.inj (isDataIntro.symm.trans dataIntroNullaryRuleDescOf_unit)
        cases payload; cases children
        refine HasTypeUnion.intro context .gen_unit unitIntroRule .childNil .childNil
          LevelExpr.lzero LevelExpr.lzero UniverseFlag.standard rfl trivial ?_
          (by dischargeUsability unitIntroRule)
        intro obligation hmem; cases hmem
      · -- interval0 : Interval
        subst isInterval0
        obtain rfl : rule = { outputTypeCode := fun _ => intervalTypeCell } :=
          Option.some.inj (isDataIntro.symm.trans dataIntroNullaryRuleDescOf_interval0)
        cases payload; cases children
        refine HasTypeUnion.intro context .gen_interval0 interval0IntroRule .childNil .childNil
          LevelExpr.lzero LevelExpr.lzero UniverseFlag.standard rfl trivial ?_
          (by dischargeUsability interval0IntroRule)
        intro obligation hmem; cases hmem
      · -- interval1 : Interval
        subst isInterval1
        obtain rfl : rule = { outputTypeCode := fun _ => intervalTypeCell } :=
          Option.some.inj (isDataIntro.symm.trans dataIntroNullaryRuleDescOf_interval1)
        cases payload; cases children
        refine HasTypeUnion.intro context .gen_interval1 interval1IntroRule .childNil .childNil
          LevelExpr.lzero LevelExpr.lzero UniverseFlag.standard rfl trivial ?_
          (by dischargeUsability interval1IntroRule)
        intro obligation hmem; cases hmem
      · -- natZero : Nat
        subst isNatZero
        obtain rfl : rule = { outputTypeCode := fun _ => natTypeCell } :=
          Option.some.inj (isDataIntro.symm.trans dataIntroNullaryRuleDescOf_natZero)
        cases payload; cases children
        refine HasTypeUnion.intro context .gen_natZero natZeroIntroRule .childNil .childNil
          LevelExpr.lzero LevelExpr.lzero UniverseFlag.standard rfl trivial ?_
          (by dischargeUsability natZeroIntroRule)
        intro obligation hmem; cases hmem

/-- **`unit : unitCode` at the nullary value layer.**  The ONE canonical inhabitant of the unit type,
typed at its code — the substrate the typed unit-η judgment collapses to (the union's `dataIntroNullary`
arm at the `gen_unit` row). -/
theorem NullaryDataValueTyped.unitValueTyped {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) :
    NullaryDataValueTyped profile context unitCell unitTypeCell :=
  NullaryDataValueTyped.intro .gen_unit () .childNil
    { outputTypeCode := fun _ => unitTypeCell } rfl

/-- **The nullary value-constructor rows are exactly the six childless data constructors.**  A local
copy of the rule-table enumerator (kept here so this file is self-sufficient over `UnionRuleTables`'s
`dataIntroNullaryRuleDescOf` def, independent of where the engine satellites relocate). -/
private theorem nullaryDataRowGenerators {generator : Generator} {rule : DataIntroNullaryRuleDesc}
    (isDataIntro : dataIntroNullaryRuleDescOf generator = some rule) :
    generator = .gen_boolTrue ∨ generator = .gen_boolFalse ∨ generator = .gen_unit ∨
      generator = .gen_interval0 ∨ generator = .gen_interval1 ∨ generator = .gen_natZero := by
  by_cases hTrue : generator = .gen_boolTrue
  · exact Or.inl hTrue
  · by_cases hFalse : generator = .gen_boolFalse
    · exact Or.inr (Or.inl hFalse)
    · by_cases hUnit : generator = .gen_unit
      · exact Or.inr (Or.inr (Or.inl hUnit))
      · by_cases hZero : generator = .gen_interval0
        · exact Or.inr (Or.inr (Or.inr (Or.inl hZero)))
        · by_cases hOne : generator = .gen_interval1
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hOne))))
          · by_cases hNatZero : generator = .gen_natZero
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hNatZero))))
            · exfalso
              dsimp only [dataIntroNullaryRuleDescOf] at isDataIntro
              rw [if_neg hTrue, if_neg hFalse, if_neg hUnit, if_neg hZero, if_neg hOne,
                if_neg hNatZero] at isDataIntro
              contradiction

/-- **Subject/classifier coordination for the nullary value rows.**  One `cases` pass yields the exact
(subject, classifier) PAIR for each table row — the unit value at `unitTypeCell`, the bool constructors at
`boolTypeCell`, etc.  Coordination via the rule-table enumerator (`dataIntroNullaryRuleDescOf`). -/
theorem NullaryDataValueTyped.subjectClassifierCoordinated {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (typed : NullaryDataValueTyped profile context subject classifier) :
    (subject = .mkGen .gen_boolTrue () .childNil ∧ classifier = boolTypeCell) ∨
      (subject = .mkGen .gen_boolFalse () .childNil ∧ classifier = boolTypeCell) ∨
      (subject = unitCell ∧ classifier = unitTypeCell) ∨
      (subject = .mkGen .gen_interval0 () .childNil ∧ classifier = intervalTypeCell) ∨
      (subject = .mkGen .gen_interval1 () .childNil ∧ classifier = intervalTypeCell) ∨
      (subject = .mkGen .gen_natZero () .childNil ∧ classifier = natTypeCell) := by
  cases typed with
  | intro generator payload children rule isDataIntro =>
      rcases nullaryDataRowGenerators isDataIntro with
        isTrue | isFalse | isUnit | isZero | isOne | isNatZero
      · subst isTrue
        have ruleEq : rule = { outputTypeCode := fun _ => boolTypeCell } :=
          (Option.some.inj isDataIntro).symm
        cases payload
        cases children
        exact Or.inl ⟨rfl, by rw [ruleEq]⟩
      · subst isFalse
        have ruleEq : rule = { outputTypeCode := fun _ => boolTypeCell } :=
          (Option.some.inj isDataIntro).symm
        cases payload
        cases children
        exact Or.inr (Or.inl ⟨rfl, by rw [ruleEq]⟩)
      · subst isUnit
        have ruleEq : rule = { outputTypeCode := fun _ => unitTypeCell } :=
          (Option.some.inj isDataIntro).symm
        cases payload
        cases children
        exact Or.inr (Or.inr (Or.inl ⟨rfl, by rw [ruleEq]⟩))
      · subst isZero
        have ruleEq : rule = { outputTypeCode := fun _ => intervalTypeCell } :=
          (Option.some.inj isDataIntro).symm
        cases payload
        cases children
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by rw [ruleEq]⟩)))
      · subst isOne
        have ruleEq : rule = { outputTypeCode := fun _ => intervalTypeCell } :=
          (Option.some.inj isDataIntro).symm
        cases payload
        cases children
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by rw [ruleEq]⟩))))
      · subst isNatZero
        have ruleEq : rule = { outputTypeCode := fun _ => natTypeCell } :=
          (Option.some.inj isDataIntro).symm
        cases payload
        cases children
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, by rw [ruleEq]⟩))))

/-- **★ Unit canonical form at the nullary value layer: a value typed at `unitTypeCell` IS the unit
value.**  The classifier discriminates the table rows by head generator (`unitTypeCell` and the others
have distinct heads, refuted by `Generator.noConfusion`), so typed-at-`unitTypeCell` forces the `gen_unit`
row — the one-value collapse the typed unit-η judgment is built on. -/
theorem NullaryDataValueTyped.subjectIsUnitOfUnitClassifier {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject : RawTerm scope}
    (typed : NullaryDataValueTyped profile context subject unitTypeCell) :
    subject = unitCell := by
  rcases typed.subjectClassifierCoordinated with
    ⟨_, hClassifier⟩ | ⟨_, hClassifier⟩ | ⟨hSubject, _⟩ | ⟨_, hClassifier⟩ | ⟨_, hClassifier⟩
      | ⟨_, hClassifier⟩
  · exact Generator.noConfusion (congrArg RawTerm.headGenerator hClassifier)
  · exact Generator.noConfusion (congrArg RawTerm.headGenerator hClassifier)
  · exact hSubject
  · exact Generator.noConfusion (congrArg RawTerm.headGenerator hClassifier)
  · exact Generator.noConfusion (congrArg RawTerm.headGenerator hClassifier)
  · exact Generator.noConfusion (congrArg RawTerm.headGenerator hClassifier)

/-- **The typed unit-η judgmental equality**: βη-conversion of grown-typed terms, extended by the
type-directed one-value collapse at `unitTypeCell`.  Presupposition-carrying: each arm carries the
typings (and, for the conversion arm, the context well-formedness) its metatheory needs, so the
equivalence package below is unconditional given derivations.  The conversion arm carries the
TABLE-NATIVE `ConvTableBetaEtaRoot` (join over `StepTable ∪ StepEtaRootTable`); consumers build
that join directly (β/ι via `ConvTableBetaEtaRoot.ofConv`, η-expansion via
`ConvTableBetaEtaRoot.etaLamExpansion`). -/
inductive DefEqUnitEta (profile : PolyProfile) {scope : Nat}
    (context : TypingContext profile scope) :
    RawTerm scope → RawTerm scope → RawTerm scope → Prop where
  /-- The table-native βη embedding: well-typed terms convertible under the canonical union
  conversion `ConvTableBetaEtaRoot` (join over `StepTable ∪ StepEtaRootTable`) are judgmentally
  equal — the conservative base, table-native. -/
  | ofConvTable {leftTerm rightTerm classifier : RawTerm scope}
      (contextWellFormed : WfContextDesc context)
      (leftTyped : HasTypeDescPi profile context leftTerm classifier)
      (rightTyped : HasTypeDescPi profile context rightTerm classifier)
      (convertible : ConvTableBetaEtaRoot leftTerm rightTerm) :
      DefEqUnitEta profile context leftTerm rightTerm classifier
  /-- **Unit-η**: ANY two terms typed at `unitTypeCell` (by the nullary value layer — the unit value —
  or the grown engine — variables/neutrals) are judgmentally equal.  Type-directed: no reduction
  relates them; the TYPE alone justifies the collapse. -/
  | unitEta {leftTerm rightTerm : RawTerm scope}
      (leftTypedAtUnit :
        NullaryDataValueTyped profile context leftTerm unitTypeCell ∨
          HasTypeDescPi profile context leftTerm unitTypeCell)
      (rightTypedAtUnit :
        NullaryDataValueTyped profile context rightTerm unitTypeCell ∨
          HasTypeDescPi profile context rightTerm unitTypeCell) :
      DefEqUnitEta profile context leftTerm rightTerm unitTypeCell

namespace DefEqUnitEta

/-- Reflexivity at any grown typing (via the reflexive union conversion). -/
theorem reflOfGrownTyped {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {term classifier : RawTerm scope}
    (contextWellFormed : WfContextDesc context)
    (typed : HasTypeDescPi profile context term classifier) :
    DefEqUnitEta profile context term term classifier :=
  .ofConvTable contextWellFormed typed typed (ConvTableBetaEtaRoot.refl term)

/-- Symmetry (both arms are symmetric in their premises). -/
theorem sym {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    {leftTerm rightTerm classifier : RawTerm scope}
    (defEq : DefEqUnitEta profile context leftTerm rightTerm classifier) :
    DefEqUnitEta profile context rightTerm leftTerm classifier := by
  cases defEq with
  | ofConvTable contextWellFormed leftTyped rightTyped convertible =>
      exact .ofConvTable contextWellFormed rightTyped leftTyped
        (ConvTableBetaEtaRoot.sym convertible)
  | unitEta leftTypedAtUnit rightTypedAtUnit =>
      exact .unitEta rightTypedAtUnit leftTypedAtUnit

/-- **Transitivity — unconditional given the derivations.**  The βη-βη peak is discharged by typed
βη Church-Rosser through the middle term (whose well-formedness + typing the FIRST derivation
carries); every case touching `unitEta` re-fires `unitEta` (the endpoints' unit typings come from
the arms' own premises — the grown typing at the now-pinned `unitTypeCell` classifier supplies the
missing side). -/
theorem trans {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
    {leftTerm middleTerm rightTerm classifier : RawTerm scope}
    (leftToMiddle : DefEqUnitEta profile context leftTerm middleTerm classifier)
    (middleToRight : DefEqUnitEta profile context middleTerm rightTerm classifier) :
    DefEqUnitEta profile context leftTerm rightTerm classifier := by
  cases leftToMiddle with
  | ofConvTable contextWellFormed leftTyped middleTypedFirst convertibleFirst =>
      cases middleToRight with
      | ofConvTable _ _ rightTyped convertibleSecond =>
          exact .ofConvTable contextWellFormed leftTyped rightTyped
            (ConvTableBetaEtaRoot.transAtTypedMiddle contextWellFormed middleTypedFirst
              convertibleFirst convertibleSecond)
      | unitEta _ rightTypedAtUnit =>
          exact .unitEta (Or.inr leftTyped) rightTypedAtUnit
  | unitEta leftTypedAtUnit _ =>
      cases middleToRight with
      | ofConvTable _ _ rightTyped _ =>
          exact .unitEta leftTypedAtUnit (Or.inr rightTyped)
      | unitEta _ rightTypedAtUnit =>
          exact .unitEta leftTypedAtUnit rightTypedAtUnit

end DefEqUnitEta

/-- The raw context binding `unitTypeCell` — the home of the unit-typed VARIABLE.  Raw, not
`WfContextDesc`-well-formed: the formation engine has no `unitCode` row (the nullary
flag-uniqueness obstruction), but the var TYPING rule needs no well-formedness. -/
def unitVariableContext (profile : PolyProfile) : TypingContext profile 1 :=
  (TypingContext.empty : TypingContext profile 0).cons unitTypeCell

/-- The variable bound at `unitTypeCell` IS grown-typed at `unitTypeCell` — the formation var rule
fires in ANY context, and looking up the newest binding weakens the closed leaf `unitTypeCell` to
itself. -/
theorem unitVariableTyped (profile : PolyProfile) :
    HasTypeDescPi profile (unitVariableContext profile)
      (variableCell ⟨0, Nat.zero_lt_one⟩) unitTypeCell :=
  HasTypeDescPi.ofFormation
    (HasTypeDesc.var (unitVariableContext profile) ⟨0, Nat.zero_lt_one⟩)

/-- The unit-typed variable and the unit value are NOT union-convertible (`ConvTableBetaEtaRoot`):
both are union-normal leaves (`reduceOnceTableBetaEtaRoot? = none` by `rfl`), so any union join
forces them syntactically equal — refuted by the distinct cells via `not_of_bothNormal_ne`
(`decide` on the head clash `gen_var ≠ gen_unit`).  The refutation half shared by both strictness
witnesses (raw-context and wf-fragment). -/
theorem unitVariableNotConvTableUnitValue :
    ¬ ConvTableBetaEtaRoot (variableCell ⟨0, Nat.zero_lt_one⟩ : RawTerm 1) unitCell :=
  ConvTableBetaEtaRoot.not_of_bothNormal_ne
    (fun _ unionStep =>
      RawTerm.reduceOnceTableBetaEtaRoot?_blocksStep
        (rfl : (variableCell ⟨0, Nat.zero_lt_one⟩ : RawTerm 1).reduceOnceTableBetaEtaRoot? = none)
        unionStep)
    (fun _ unionStep =>
      RawTerm.reduceOnceTableBetaEtaRoot?_blocksStep
        (rfl : (unitCell : RawTerm 1).reduceOnceTableBetaEtaRoot? = none)
        unionStep)
    (by decide)

/-- **★ Unit-η is STRICTLY beyond union conversion**: the unit-typed variable and the unit value
are judgmentally equal (`unitEta` — both typed at `unitTypeCell`) but provably NOT
`ConvTableBetaEtaRoot` (both are union-normal leaves, so a join forces them syntactically equal —
distinct head generators).  The textbook motivation for type-directed η, machine-checked: no
rewriting relation can close this pair, only the type can. -/
theorem DefEqUnitEta.strictlyExtendsConvTable (profile : PolyProfile) :
    ∃ (context : TypingContext profile 1) (leftTerm rightTerm : RawTerm 1),
      DefEqUnitEta profile context leftTerm rightTerm unitTypeCell ∧
        ¬ ConvTableBetaEtaRoot leftTerm rightTerm :=
  ⟨unitVariableContext profile, variableCell ⟨0, Nat.zero_lt_one⟩, unitCell,
    .unitEta (Or.inr (unitVariableTyped profile))
      (Or.inl (NullaryDataValueTyped.unitValueTyped (unitVariableContext profile))),
    unitVariableNotConvTableUnitValue⟩

/-- **The honest degeneracy boundary**: on the nullary value fragment the `unitEta` arm is
refl-degenerate — closed unit canonicity (`subjectIsUnitOfUnitClassifier`) already collapses both
sides to `unitCell`, so the two terms are EQUAL, not merely judgmentally equal.  The strict content
of unit-η lives exactly at open unit-typed NEUTRALS (the variable witness above). -/
theorem DefEqUnitEta.dataIntroUnitPairsCollapseToRefl {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {leftTerm rightTerm : RawTerm scope}
    (leftTyped : NullaryDataValueTyped profile context leftTerm unitTypeCell)
    (rightTyped : NullaryDataValueTyped profile context rightTerm unitTypeCell) :
    leftTerm = rightTerm :=
  (NullaryDataValueTyped.subjectIsUnitOfUnitClassifier leftTyped).trans
    (NullaryDataValueTyped.subjectIsUnitOfUnitClassifier rightTyped).symm

/-- **Inversion off the unit type**: at a classifier that is NOT `unitTypeCell`, only the
table-native conversion arm can have fired — the `unitEta` arm pins its classifier index.  Extracts
the carried `ConvTableBetaEtaRoot` directly. -/
theorem DefEqUnitEta.convTableOfNotUnit {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {leftTerm rightTerm classifier : RawTerm scope}
    (defEq : DefEqUnitEta profile context leftTerm rightTerm classifier)
    (notUnitClassifier : classifier ≠ unitTypeCell) :
    ConvTableBetaEtaRoot leftTerm rightTerm := by
  cases defEq with
  | ofConvTable _ _ _ convertible => exact convertible
  | unitEta _ _ => exact absurd rfl notUnitClassifier

/-- **★ The decider** — typed unit-η judgmental equality is decidable for grown-typed terms over a
well-formed context: compare the classifier with `unitTypeCell` structurally; at unit type the
answer is always YES (the one-value collapse), off unit type the decision is exactly the
table-native union conversion decider. -/
def DefEqUnitEta.decidableOfWfTyped {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {leftTerm rightTerm classifier : RawTerm scope}
    (contextWellFormed : WfContextDesc context)
    (leftTyped : HasTypeDescPi profile context leftTerm classifier)
    (rightTyped : HasTypeDescPi profile context rightTerm classifier) :
    Decidable (DefEqUnitEta profile context leftTerm rightTerm classifier) :=
  if isUnitClassifier : classifier = unitTypeCell then
    .isTrue (by
      subst isUnitClassifier
      exact .unitEta (Or.inr leftTyped) (Or.inr rightTyped))
  else
    match ConvTableBetaEtaRoot.decidableOfWfTyped contextWellFormed leftTyped rightTyped with
    | .isTrue convertible =>
        .isTrue (.ofConvTable contextWellFormed leftTyped rightTyped convertible)
    | .isFalse notConvertible =>
        .isFalse (fun defEq => notConvertible (defEq.convTableOfNotUnit isUnitClassifier))

/-! ## The formation-row payoff — unit-typed variables get the wf metatheory

The nullary `unitCode` formation row (flag-pinned `nullaryFormerOutput`) discharges honest
boundary (2): `unitTypeCell` is a formation TYPE, so `WfContextDesc` binds it, the grown lift
hands the unit-variable context to the full wf metatheory (open SN / open βη-SN / βη
Church-Rosser), and the strictness witness + the unit-η decider now live on the DECIDABLE wf
fragment. -/

/-- **`unitTypeCell` is formation-typed at the pinned `Type@0`** — the nullary `unitCode` row
fires with the empty telescope in ANY context (the row is context-uniform; the empty telescope's
floating flag is absorbed by the flag-IGNORING pinned output). -/
theorem unitTypeCellFormationTyped {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) :
    HasTypeDesc profile context unitTypeCell
      (universeCodeCell LevelExpr.lzero UniverseFlag.standard) :=
  HasTypeDesc.genFormation context .gen_unitCode () .childNil [] UniverseFlag.standard
    { outputType := nullaryFormerOutput } typingRuleDescOf_unitCode
    (DescTelescope.nil (currentDepth := 0) context UniverseFlag.standard)

/-- `unitTypeCell` is a formation type — the `IsTypeDesc` triple at the pinned
`(lzero, standard)`. -/
theorem unitTypeCellIsTypeDesc {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) :
    IsTypeDesc profile context unitTypeCell :=
  ⟨LevelExpr.lzero, UniverseFlag.standard, unitTypeCellFormationTyped context⟩

/-- **★ The wf upgrade**: the unit-variable context is formation-well-formed — `WfContextDesc`
now binds `unitTypeCell` (honest boundary (2), discharged by the formation row). -/
theorem unitVariableContextWellFormed (profile : PolyProfile) :
    WfContextDesc (unitVariableContext profile) :=
  WfContextDesc.cons WfContextDesc.emptyIsWellFormed
    (unitTypeCellIsTypeDesc TypingContext.empty)

/-- The grown lift: the unit-variable context is grown-well-formed, so the FULL wf metatheory —
open SN (`HasTypeDescPi` + `WfContextDescPi` ⟹ strongly normalizing), open βη-SN, βη
Church-Rosser, the #1202 βη decider, and the unit-η decider below — applies to unit-typed
variables. -/
theorem unitVariableContextWellFormedPi (profile : PolyProfile) :
    WfContextDescPi (unitVariableContext profile) :=
  WfContextDescPi.ofWfContextDesc (unitVariableContextWellFormed profile)

/-- **★ The strictness witness on the WELL-FORMED fragment**: the same variable-vs-`unitCell`
pair, now over a context certified `WfContextDesc` — unit-η strictly extends union conversion
exactly where the wf metatheory (and the decider) operates, not merely in a raw context. -/
theorem DefEqUnitEta.strictlyExtendsConvTableOnWfFragment (profile : PolyProfile) :
    ∃ (context : TypingContext profile 1), WfContextDesc context ∧
      ∃ (leftTerm rightTerm : RawTerm 1),
        DefEqUnitEta profile context leftTerm rightTerm unitTypeCell ∧
          ¬ ConvTableBetaEtaRoot leftTerm rightTerm :=
  ⟨unitVariableContext profile, unitVariableContextWellFormed profile,
    variableCell ⟨0, Nat.zero_lt_one⟩, unitCell,
    .unitEta (Or.inr (unitVariableTyped profile))
      (Or.inl (NullaryDataValueTyped.unitValueTyped (unitVariableContext profile))),
    unitVariableNotConvTableUnitValue⟩

/-- **The decider instantiates at the unit-variable context** — previously impossible (boundary
(2) blocked the `WfContextDesc` premise).  The unit-η judgment over the wf unit context is
DECIDED, completing the #362 story: relation + strictness + decidability, all on the wf
fragment. -/
def DefEqUnitEta.unitVariableDecidable (profile : PolyProfile) :
    Decidable (DefEqUnitEta profile (unitVariableContext profile)
      (variableCell ⟨0, Nat.zero_lt_one⟩) (variableCell ⟨0, Nat.zero_lt_one⟩) unitTypeCell) :=
  DefEqUnitEta.decidableOfWfTyped (unitVariableContextWellFormed profile)
    (unitVariableTyped profile) (unitVariableTyped profile)

end FX1Poly.Typed
