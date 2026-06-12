import FX1Poly.Typed.TypingContext
import FX1Poly.Typed.CellConstructors
import FX1Poly.Core.StepStarConfluence

/-! # FX1Poly/Typed/HasTypeDesc — the description-driven generic typing engine
    (the moonshot core: the Natural-Model display map as a data-driven `gen` arm)

polycell.md §11.8.5 Decision 4 / §5.2: the typing display map `Tm ↠ Ty` realized
cellularly by a CASCADE-FREE generic `gen` arm — a new feature is one
`TypingRuleDesc` DATA row, never a new `HasTypeDesc` arm.  This file carries that arm
for the dependent-type-FORMER family (the most uniform shape).

`HasTypeDesc` is the formation typing engine.  Its metatheory is proved
INTRINSICALLY — validity (`HasTypeDesc.classifierIsTypeDesc`), uniqueness
(`HasTypeDesc.uniqueness`), inversion, and strong normalization are all by
recursion on `HasTypeDesc` itself over the native well-formedness `WfContextDesc`.
Arms:
* `var`, `conv` — the irreducible core (every typed-layer engine has them).
* `universeFormation` — the nullary universe-code shape.  Genuinely special: its
  output level comes from the PAYLOAD (`lsucc`), not from children, so its output
  is not computed from the children's levels; it stays a (single-generator) arm.
* `genFormation` — THE generic arm.  Over ANY `generator` with a
  `TypingRuleDesc` (the `typingRuleDescOf` table), it types `mkGen generator
  payload children` by checking the children form a dependent telescope of types
  at `levels` (the mutual `DescTelescope` spine), and concludes the cell inhabits
  the rule's OUTPUT classifier `rule.outputType scope levels flag` (for the
  type-formers, `universeCodeCell (lmaxAll levels) flag`).  Adding a new dependent
  type-former (Π, Σ, and future n-ary dependent records …) is ONE
  `typingRuleDescOf` row — ZERO new arms (the two reconstruction theorems below
  witness Π and Σ through the SAME arm; P13 cascade-freedom).  The `outputType`
  field opens the §11.8.5 "non-uniform output" seam: output is rule-DATA, not
  hardwired to a universe code — the structural prerequisite for typing
  non-formers (eliminators).

## Positivity / zero-axiom

The desc (`TypingRuleDesc.outputType : (scope) → List LevelExpr → UniverseFlag →
RawTerm scope`) is PURE syntax — it contains NO `HasTypeDesc`, so the
`genFormation` arm is strictly positive.  `HasTypeDesc` appears only POSITIVELY, in the mutual
`DescTelescope` spine's `cons` premise.  The spine's shift-rebasing discipline:
children indexed at a fixed `baseScope`, only the context grows via
`currentDepth`, so `(baseScope+currentDepth)+1 = baseScope+(currentDepth+1)`
definitionally.  The output universe level is an
explicit INDEX (`Prop`-valued, P14 erasure).  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Audit-gated.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- Combine a telescope of child universe levels into the former's output level.
For the dependent type-formers (Π, Σ) this is the iterated `lmax` (the level of
`Π A. B` / `Σ A. B` is `lmax (level A) (level B)`).  `lmaxAll [e] = e`,
`lmaxAll [e₀, e₁] = lmax e₀ e₁` (definitionally — the singleton arm precedes the
cons arm), so it matches the binary `piFormation`/`sigmaFormation` output
exactly. -/
def lmaxFold (accumulator : LevelExpr) : List LevelExpr → LevelExpr
  | [] => accumulator
  | headLevel :: restLevels =>
      lmaxFold (LevelExpr.lmax accumulator headLevel) restLevels

def lmaxAll : List LevelExpr → LevelExpr
  | [] => LevelExpr.lzero
  | headLevel :: restLevels => lmaxFold headLevel restLevels

/-- A typing-rule description: the per-generator datum is the rule's OUTPUT
classifier as a function of the children's universe levels (and the flag/scope).
`outputType` lets the output be arbitrary rule-DATA, realizing the §11.8.5
"non-uniform output" seam — the structural prerequisite for non-formation rules.
For the dependent type-formers (Π, Σ) the output is a universe code at the
iterated-`lmax` level, so `outputType _ levels flag = universeCodeCell (lmaxAll
levels) flag`.  This covers output-FROM-LEVELS; the children-dependent eliminator
output (motive applied to scrutinee) is the open part of the seam.  (Binder
structure is read from the generator's `binderShifts`; the children-are-types
premise is the `DescTelescope` spine.) -/
structure TypingRuleDesc where
  /-- The rule's output classifier, as a function of the scope, the children's
  universe levels (from the `DescTelescope` premise), and the flag. -/
  outputType : (scope : Nat) → List LevelExpr → UniverseFlag → RawTerm scope

/-- The output classifier shared by the dependent type-formers: a universe code
at the iterated-`lmax` of the children's levels.  Factored out so the Π and Σ
rows are visibly the same rule (and the `rfl` metadata lemmas + reconstruction
proofs reduce through one definition). -/
def universeFormerOutput (scope : Nat) (levels : List LevelExpr)
    (flag : UniverseFlag) : RawTerm scope :=
  universeCodeCell (lmaxAll levels) flag

/-- The output classifier of a NULLARY (childless) former: pinned to `Type@0(standard)`,
IGNORING both the level list and the flag.  A childless former's telescope premise
`DescTelescope ... [] flag .childNil` holds for EVERY flag (no head child anchors it), so a
flag-USING output would classify one subject at many non-`Conv` universe codes and break
uniqueness of typing; a nullary row must pin its output instead — uniqueness at a nullary
former is then by output CONSTANCY rather than by telescope flag-anchoring.  Matches the
base-type engine's pinning (`baseTypeRuleDescOf` sends every nullary base code to
`Type@0(standard)`). -/
def nullaryFormerOutput (scope : Nat) (_levels : List LevelExpr)
    (_flag : UniverseFlag) : RawTerm scope :=
  universeCodeCell LevelExpr.lzero UniverseFlag.standard

/-- The per-generator description table.  `gen_piTyCode` and `gen_sigmaTyCode`
are the dependent type-formers, both with `universeFormerOutput`; `gen_listCode` /
`gen_optionCode` are the one-child data formers at the same rule; `gen_unitCode` is the
first NULLARY former, with the flag-ignoring `nullaryFormerOutput` (Unit : Type@0).
Adding a future dependent former is one more row here — never a new `HasTypeDesc`
arm (P13). -/
def typingRuleDescOf (generator : Generator) : Option TypingRuleDesc :=
  if generator = .gen_piTyCode then some { outputType := universeFormerOutput }
  else if generator = .gen_sigmaTyCode then some { outputType := universeFormerOutput }
  else if generator = .gen_listCode then some { outputType := universeFormerOutput }
  else if generator = .gen_optionCode then some { outputType := universeFormerOutput }
  else if generator = .gen_unitCode then some { outputType := nullaryFormerOutput }
  else none

mutual

/-- The description-driven typing judgment (moonshot core).  `var` + `conv` +
nullary `universeFormation` + the generic `genFormation` arm consuming
`typingRuleDescOf`. -/
inductive HasTypeDesc (profile : PolyProfile) :
    {scope : Nat} → TypingContext profile scope →
      RawTerm scope → RawTerm scope → Prop where
  | var {scope : Nat} (context : TypingContext profile scope)
      (index : Fin scope) :
      HasTypeDesc profile context (variableCell index) (context.lookup index)
  | conv {scope : Nat} {context : TypingContext profile scope}
      {subject classifier reclassifier : RawTerm scope}
      (levelExpr : LevelExpr) (flag : UniverseFlag)
      (typed : HasTypeDesc profile context subject classifier)
      (converts : Conv classifier reclassifier)
      (reclassifierTyped :
        HasTypeDesc profile context reclassifier
          (universeCodeCell levelExpr flag)) :
      HasTypeDesc profile context subject reclassifier
  | universeFormation {scope : Nat} (context : TypingContext profile scope)
      (levelExpr : LevelExpr) (flag : UniverseFlag) :
      HasTypeDesc profile context (universeCodeCell levelExpr flag)
        (universeCodeCell levelExpr.lsucc flag)
  | genFormation {scope : Nat} (context : TypingContext profile scope)
      (generator : Generator) (payload : generator.payload scope)
      (children : RawTermChildren generator.binderShifts scope)
      (levels : List LevelExpr) (flag : UniverseFlag)
      (rule : TypingRuleDesc)
      (isFormation : typingRuleDescOf generator = some rule)
      (premises :
        DescTelescope profile (currentDepth := 0) context levels flag children) :
      HasTypeDesc profile context (.mkGen generator payload children)
        (rule.outputType scope levels flag)

/-- The description engine's premise spine: the children form a cumulative
dependent telescope of TYPES at `levels`.  Mutual with `HasTypeDesc` (its index
signature references only `PolyProfile`/`Nat`/`LevelExpr`/`UniverseFlag`/`List
Nat`/`TypingContext`/`RawTermChildren`, never `HasTypeDesc` — mutual-index rule;
`HasTypeDesc` appears only positively in `cons`'s `headTyped`).  Fixed-`baseScope`,
growing-`currentDepth` rebasing discipline: children stay indexed at `baseScope`
while the context extends. -/
inductive DescTelescope (profile : PolyProfile) :
    {baseScope : Nat} → {currentDepth : Nat} → {binderShifts : List Nat} →
      TypingContext profile (baseScope + currentDepth) →
      List LevelExpr → UniverseFlag →
      RawTermChildren binderShifts baseScope → Prop where
  | nil {baseScope : Nat} {currentDepth : Nat}
      (context : TypingContext profile (baseScope + currentDepth))
      (flag : UniverseFlag) :
      DescTelescope profile context [] flag .childNil
  | cons {baseScope : Nat} {currentDepth : Nat} {restShifts : List Nat}
      (context : TypingContext profile (baseScope + currentDepth))
      (head : RawTerm (baseScope + currentDepth))
      (headLevel : LevelExpr) (restLevels : List LevelExpr) (flag : UniverseFlag)
      (rest : RawTermChildren restShifts baseScope)
      (headTyped :
        HasTypeDesc profile context head (universeCodeCell headLevel flag))
      (restTyped :
        DescTelescope profile (currentDepth := currentDepth + 1)
          (context.cons head) restLevels flag rest) :
      DescTelescope profile context (headLevel :: restLevels) flag
        (.childCons head rest)

end

/-- `gen_piTyCode`'s description is the `universeFormerOutput` rule (metadata
check). -/
theorem typingRuleDescOf_piTyCode :
    typingRuleDescOf .gen_piTyCode = some { outputType := universeFormerOutput } := rfl

/-- `gen_sigmaTyCode`'s description is the `universeFormerOutput` rule (metadata
check). -/
theorem typingRuleDescOf_sigmaTyCode :
    typingRuleDescOf .gen_sigmaTyCode = some { outputType := universeFormerOutput } := rfl

/-- `gen_listCode`'s description is the `universeFormerOutput` rule (metadata
check).  The data-type-code former (GTL-11): `List A` lives at the universe of its
element `A`, exactly the `universeFormerOutput` rule the dependent formers carry. -/
theorem typingRuleDescOf_listCode :
    typingRuleDescOf .gen_listCode = some { outputType := universeFormerOutput } := rfl

/-- `gen_optionCode`'s description is the `universeFormerOutput` rule (metadata
check).  The one-child data-type-code former (GTL-13): `Option A` lives at the universe of its
element `A`, exactly the `universeFormerOutput` rule the dependent formers and `listCode` carry. -/
theorem typingRuleDescOf_optionCode :
    typingRuleDescOf .gen_optionCode = some { outputType := universeFormerOutput } := rfl

/-- `gen_unitCode`'s description is the `nullaryFormerOutput` rule (metadata check) — the first
NULLARY formation row: `Unit : Type@0(standard)`, the output IGNORING the (empty) level list and
the (unanchored) flag. -/
theorem typingRuleDescOf_unitCode :
    typingRuleDescOf .gen_unitCode = some { outputType := nullaryFormerOutput } := rfl

/-- **The ≥1-child formation family outputs the `universeFormerOutput` rule.**  Every NON-NULLARY
`typingRuleDescOf` row (the dependent type-formers and the one-child data formers) carries the SHARED
`universeFormerOutput` rule (a former lives at the `lmax` of its children's levels).  This lemma enumerates
the table ONCE: any generator carrying a formation rule, other than the nullary `gen_unitCode`, has
`rule.outputType = universeFormerOutput`.

It is the cascade-death substrate for the ≥1-CHILD formation metatheory: a consumer obtains
`rule.outputType = universeFormerOutput` from HERE instead of its own `unfold typingRuleDescOf` +
per-generator split.  The NULLARY row is excluded by hypothesis — its output is flag-pinned
(`nullaryFormerOutput`), and nullary consumers work by output CONSTANCY instead
(`typingRuleDescOf_output_eq_outputData` below covers BOTH shapes constructively).

Zero-axiom — the established `subst` + `Option.some.inj` and `unfold`/`if_neg`/`contradiction`
(the non-former branch) pattern; no `propext`/`Quot.sound`/`Classical`/`native_decide`/`omega`. -/
theorem typingRuleDescOf_outputIsUniverseFormer {generator : Generator} {rule : TypingRuleDesc}
    (isFormation : typingRuleDescOf generator = some rule)
    (isNotNullary : generator ≠ Generator.gen_unitCode) :
    rule.outputType = universeFormerOutput := by
  by_cases hPi : generator = .gen_piTyCode
  · subst hPi
    have hRule : rule = { outputType := universeFormerOutput } := Option.some.inj isFormation.symm
    rw [hRule]
  · by_cases hSigma : generator = .gen_sigmaTyCode
    · subst hSigma
      have hRule : rule = { outputType := universeFormerOutput } := Option.some.inj isFormation.symm
      rw [hRule]
    · by_cases hList : generator = .gen_listCode
      · subst hList
        have hRule : rule = { outputType := universeFormerOutput } := Option.some.inj isFormation.symm
        rw [hRule]
      · by_cases hOption : generator = .gen_optionCode
        · subst hOption
          have hRule : rule = { outputType := universeFormerOutput } := Option.some.inj isFormation.symm
          rw [hRule]
        · exfalso
          dsimp only [typingRuleDescOf] at isFormation
          rw [if_neg hPi, if_neg hSigma, if_neg hList, if_neg hOption,
            if_neg isNotNullary] at isFormation
          contradiction

/-- **A formation generator is never the variable generator.**  `typingRuleDescOf .gen_var = none`
(the variable is not a type former), so any generator carrying a formation rule is non-`gen_var`.  The
discharge for the `generator ≠ .gen_var` side condition of `RawTerm.subst_mkGen_of_ne_var` /
`rename_mkGen_of_ne_var`: every formation-family consumer that reconstructs a formation cell over an
ABSTRACT generator obtains the non-variable witness from HERE.  Zero-axiom (the established
`unfold`/`if_neg`/`contradiction` non-former branch; the `.gen_var ≠` inequalities are
`Generator.noConfusion`). -/
theorem formationRuleImpliesNotVariable {generator : Generator} {rule : TypingRuleDesc}
    (isFormation : typingRuleDescOf generator = some rule) :
    generator ≠ Generator.gen_var := by
  intro isVariable
  subst isVariable
  dsimp only [typingRuleDescOf] at isFormation
  rw [if_neg (fun isPi => Generator.noConfusion isPi),
    if_neg (fun isSigma => Generator.noConfusion isSigma),
    if_neg (fun isList => Generator.noConfusion isList),
    if_neg (fun isOption => Generator.noConfusion isOption),
    if_neg (fun isUnit => Generator.noConfusion isUnit)] at isFormation
  cases isFormation

/-- **A ≥1-child formation rule IS the universe-former rule (full structure).**  The single-field
strengthening of `typingRuleDescOf_outputIsUniverseFormer`: since `TypingRuleDesc` has exactly the
`outputType` field, the output-type equation upgrades to a structure equation
`rule = { outputType := universeFormerOutput }`.  This is what a cell-RECONSTRUCTION consumer needs —
`obtain rfl` makes `rule` concrete (replacing the old per-branch `Option.some.inj`), so the reconstructed
`genFormation` cell carries `isFormation` directly.  Excludes the nullary `gen_unitCode` row by
hypothesis (its rule is `{ outputType := nullaryFormerOutput }`, pinned by
`typingRuleDescOf_unitCode` directly). -/
theorem formationRuleIsUniverseFormer {generator : Generator} {rule : TypingRuleDesc}
    (isFormation : typingRuleDescOf generator = some rule)
    (isNotNullary : generator ≠ Generator.gen_unitCode) :
    rule = { outputType := universeFormerOutput } := by
  have outputIsFormer : rule.outputType = universeFormerOutput :=
    typingRuleDescOf_outputIsUniverseFormer isFormation isNotNullary
  cases rule
  rw [← outputIsFormer]

/-! ### The ROW-SHAPE-AGNOSTIC output interface

`typingRuleDescOf_outputIsUniverseFormer` / `formationRuleIsUniverseFormer` pin a ≥1-CHILD row's
output to EXACTLY `universeFormerOutput`; the nullary `gen_unitCode` row instead carries the
flag-pinned `nullaryFormerOutput` (a nullary row's telescope premise
`DescTelescope ... [] flag .childNil` accepts EVERY flag, so its output must IGNORE the flag to
preserve uniqueness).  What most consumers actually NEED from the output is weaker and uniform
across BOTH row shapes:

  * it is a UNIVERSE CODE (validity: the classifier is a type) — `output_isUniverseCode` below;
  * its (level, flag) is COMPUTABLE row data — `formationOutputData` +
    `typingRuleDescOf_output_eq_outputData` below (the constructive form a `Type`-valued decider
    needs: a `Prop`-valued `∃` cannot eliminate into `Σ'`/`PSum`);
  * it is RENAME- and SUBST-STABLE (the weakening/substitution reconstructions) —
    `typingRuleDescOf_output_renameStable` / `_substStable`, housed with the rename/subst
    vocabulary in `HasTypeDescWeakening` / `HasTypeDescSubstitution`. -/

/-- **The output is a universe code** — for every row, scope, level list, and flag.  The
row-shape-agnostic validity interface: the ≥1-child rows output at `(lmaxAll levels, flag)`, the
nullary row at the pinned `(lzero, standard)`. -/
theorem typingRuleDescOf_output_isUniverseCode {generator : Generator} {rule : TypingRuleDesc}
    (isFormation : typingRuleDescOf generator = some rule)
    (scope : Nat) (levels : List LevelExpr) (flag : UniverseFlag) :
    ∃ (outputLevel : LevelExpr) (outputFlag : UniverseFlag),
      rule.outputType scope levels flag = universeCodeCell outputLevel outputFlag := by
  by_cases isNullary : generator = Generator.gen_unitCode
  · subst isNullary
    obtain rfl : rule = { outputType := nullaryFormerOutput } :=
      Option.some.inj (isFormation.symm.trans typingRuleDescOf_unitCode)
    exact ⟨LevelExpr.lzero, UniverseFlag.standard, rfl⟩
  · rw [typingRuleDescOf_outputIsUniverseFormer isFormation isNullary]
    exact ⟨lmaxAll levels, flag, rfl⟩

/-- **Computable formation-output data**: the `(level, flag)` of a formation row's output universe
code, as a FUNCTION of the generator and the telescope's levels/flag.  The constructive twin of
`typingRuleDescOf_output_isUniverseCode` — a `Type`-valued consumer (the `IsTypeDesc` decider's
`Σ'` witness) must EXHIBIT the level/flag as data, which the `Prop`-valued `∃` cannot provide
(no large elimination out of `Prop`).  A future nullary row adds one branch HERE plus one case in
the soundness equation below — the same single-point-of-extension as the table itself. -/
def formationOutputData (generator : Generator) (levels : List LevelExpr)
    (flag : UniverseFlag) : LevelExpr × UniverseFlag :=
  if generator = Generator.gen_unitCode then (LevelExpr.lzero, UniverseFlag.standard)
  else (lmaxAll levels, flag)

/-- **Soundness of `formationOutputData`**: every formation rule's output IS the universe code at
the computed data — for BOTH row shapes. -/
theorem typingRuleDescOf_output_eq_outputData {generator : Generator} {rule : TypingRuleDesc}
    (isFormation : typingRuleDescOf generator = some rule)
    (scope : Nat) (levels : List LevelExpr) (flag : UniverseFlag) :
    rule.outputType scope levels flag
      = universeCodeCell (formationOutputData generator levels flag).1
          (formationOutputData generator levels flag).2 := by
  by_cases isNullary : generator = Generator.gen_unitCode
  · subst isNullary
    obtain rfl : rule = { outputType := nullaryFormerOutput } :=
      Option.some.inj (isFormation.symm.trans typingRuleDescOf_unitCode)
    rfl
  · rw [typingRuleDescOf_outputIsUniverseFormer isFormation isNullary]
    dsimp only [formationOutputData]
    rw [if_neg isNullary]
    rfl

/-- **The nullary row's output is CONSTANT**: `gen_unitCode`'s formation rule ignores its level
list and flag entirely — every instantiation is the pinned `Type@0(standard)`.  This output
CONSTANCY is what replaces telescope flag-anchoring in uniqueness arguments at the nullary row
(the telescope `DescTelescope ... [] flag .childNil` holds at every flag, so nothing else pins
the classifier). -/
theorem typingRuleDescOf_unitCode_outputConstant {rule : TypingRuleDesc}
    (isFormation : typingRuleDescOf Generator.gen_unitCode = some rule)
    (scope : Nat) (levels : List LevelExpr) (flag : UniverseFlag) :
    rule.outputType scope levels flag
      = universeCodeCell LevelExpr.lzero UniverseFlag.standard := by
  obtain rfl : rule = { outputType := nullaryFormerOutput } :=
    Option.some.inj (isFormation.symm.trans typingRuleDescOf_unitCode)
  rfl

/-- **A formation telescope's level list and the generator's shift list have equal length.**  Structural
recursion on the telescope (`DescTelescope` is mutual with `HasTypeDesc`, so `induction` is unavailable —
term-mode `match` recurses through the `restTyped` field; `cons` prepends exactly one shift and one level).
The cascade-death substrate for the flag-uniqueness guard of `HasTypeDesc.uniqueness`: a non-empty shift
list forces a non-empty level list, which pins the formation flag through the telescope's head child.
Zero-axiom (`congrArg Nat.succ` over the structural recursion). -/
theorem DescTelescope.levels_length_eq_binderShifts {profile : PolyProfile}
    {baseScope currentDepth : Nat} {binderShifts : List Nat}
    {context : TypingContext profile (baseScope + currentDepth)}
    {levels : List LevelExpr} {flag : UniverseFlag}
    {children : RawTermChildren binderShifts baseScope}
    (telescope : DescTelescope profile context levels flag children) :
    levels.length = binderShifts.length :=
  match telescope with
  | .nil _ _ => rfl
  | .cons _ _ _ _ _ _ _ restTyped =>
      congrArg Nat.succ (DescTelescope.levels_length_eq_binderShifts restTyped)

/-- **Every NON-NULLARY formation generator carries a non-empty shift list (≥1-child family).**
The ≥1-child rows (`gen_piTyCode` / `gen_sigmaTyCode` at `[0, 1]`, `gen_listCode` /
`gen_optionCode` at `[0]`) all bind at least one child — the shape invariant the flag-uniqueness
guard needs (a non-empty telescope anchors the flag at its head child).  The NULLARY
`gen_unitCode` row (`binderShifts = []`) is excluded by hypothesis: a nullary former's flag is
pinned by the formation RULE itself (`nullaryFormerOutput` /
`typingRuleDescOf_unitCode_outputConstant`), so uniqueness there is by output constancy, not by
telescope anchoring.  Zero-axiom (`decide` on the closed shift lists + the non-former `if_neg`
branch). -/
theorem typingRuleDescOf_binderShiftsNonEmpty {generator : Generator} {rule : TypingRuleDesc}
    (isFormation : typingRuleDescOf generator = some rule)
    (isNotNullary : generator ≠ Generator.gen_unitCode) :
    generator.binderShifts ≠ [] := by
  by_cases hPi : generator = .gen_piTyCode
  · subst hPi; decide
  · by_cases hSigma : generator = .gen_sigmaTyCode
    · subst hSigma; decide
    · by_cases hList : generator = .gen_listCode
      · subst hList; decide
      · by_cases hOption : generator = .gen_optionCode
        · subst hOption; decide
        · exfalso
          dsimp only [typingRuleDescOf] at isFormation
          rw [if_neg hPi, if_neg hSigma, if_neg hList, if_neg hOption,
            if_neg isNotNullary] at isFormation
          contradiction

/-- **The CURRENT formation table is exactly `{gen_piTyCode, gen_sigmaTyCode}`.**  Any generator carrying a
formation rule is one of the two dependent type-formers.  This is the canonical "enumerate the current
formers" companion to `typingRuleDescOf_binderShiftsNonEmpty`: the tool a former-DISPATCH consumer (e.g. the
reducibility-FT `genFormation` arm's `toPiMember` / `toSigmaMember` choice) uses to obtain its former tag from
`isFormation`.  Like the binder-shift fact, this is a CURRENT-TABLE enumeration, NOT a permanent cascade
invariant — every new formation row (a data type code) adds one disjunct here.  Zero-axiom (`by_cases` +
`if_neg` non-former branch).

NOTE (GTL-05/06 boundary): this fact alone does NOT genericize the reducibility-FT `genFormation` arm.  That
arm's `by_cases` is irreducibly entangled with generator-ARITY — the conclusion's subject
`mkGen generator payload (childCons domain (childCons codomain childNil))` is a 2-child spine that is
ill-typed over an ABSTRACT generator (the spine forces `generator.binderShifts = [0,1]` and fixes the child
scopes), and the two consumers operate over DIFFERENT telescope inductives (`DescTelescope` vs
`DescTelescopePi`).  Factoring `toPiMember`/`toSigmaMember` into a generic `toFormerMember` dispatch therefore
requires the arity-generic telescope→member candidate-bridge (BFT-15 / CON-A3), not a table enumeration.  The
TYPING-layer metatheory (validity / subst / weaken / inversion / uniqueness) is fully table-generic; the
REDUCIBILITY-layer former-closure is the deep residual. -/
theorem typingRuleDescOf_isPiOrSigmaOrListOrOptionCode {generator : Generator} {rule : TypingRuleDesc}
    (isFormation : typingRuleDescOf generator = some rule)
    (isNotNullary : generator ≠ Generator.gen_unitCode) :
    generator = Generator.gen_piTyCode ∨ generator = Generator.gen_sigmaTyCode ∨
      generator = Generator.gen_listCode ∨ generator = Generator.gen_optionCode := by
  by_cases hPi : generator = .gen_piTyCode
  · exact Or.inl hPi
  · by_cases hSigma : generator = .gen_sigmaTyCode
    · exact Or.inr (Or.inl hSigma)
    · by_cases hList : generator = .gen_listCode
      · exact Or.inr (Or.inr (Or.inl hList))
      · by_cases hOption : generator = .gen_optionCode
        · exact Or.inr (Or.inr (Or.inr hOption))
        · exfalso
          dsimp only [typingRuleDescOf] at isFormation
          rw [if_neg hPi, if_neg hSigma, if_neg hList, if_neg hOption,
            if_neg isNotNullary] at isFormation
          contradiction

/-- **The CURRENT formation table is exactly the four ≥1-child formers plus the nullary
`gen_unitCode`.**  The full (unhypothesized) enumeration companion to
`typingRuleDescOf_isPiOrSigmaOrListOrOptionCode` — every new formation row adds one disjunct
here.  Zero-axiom. -/
theorem typingRuleDescOf_formerEnumeration {generator : Generator} {rule : TypingRuleDesc}
    (isFormation : typingRuleDescOf generator = some rule) :
    generator = Generator.gen_piTyCode ∨ generator = Generator.gen_sigmaTyCode ∨
      generator = Generator.gen_listCode ∨ generator = Generator.gen_optionCode ∨
      generator = Generator.gen_unitCode := by
  by_cases isNullary : generator = Generator.gen_unitCode
  · exact Or.inr (Or.inr (Or.inr (Or.inr isNullary)))
  · rcases typingRuleDescOf_isPiOrSigmaOrListOrOptionCode isFormation isNullary with
      hPi | hSigma | hList | hOption
    · exact Or.inl hPi
    · exact Or.inr (Or.inl hSigma)
    · exact Or.inr (Or.inr (Or.inl hList))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hOption)))

/-- **A NON-NULLARY formation cell's telescope levels are non-empty.**  Combines the length equality with
the shift-non-emptiness: the consumer-facing form for `HasTypeDesc.uniqueness`'s flag-uniqueness guard,
generic over the ≥1-child formation generator (no per-former `by_cases`); the nullary `gen_unitCode` row
(whose telescope levels ARE `[]`) is excluded by hypothesis.  Zero-axiom. -/
theorem DescTelescope.levels_ne_nil_of_isFormation {profile : PolyProfile}
    {baseScope currentDepth : Nat}
    {context : TypingContext profile (baseScope + currentDepth)}
    {generator : Generator} {rule : TypingRuleDesc}
    (isFormation : typingRuleDescOf generator = some rule)
    (isNotNullary : generator ≠ Generator.gen_unitCode)
    {levels : List LevelExpr} {flag : UniverseFlag}
    {children : RawTermChildren generator.binderShifts baseScope}
    (telescope : DescTelescope profile context levels flag children) :
    levels ≠ [] := by
  intro emptyLevels
  have lengthEq := DescTelescope.levels_length_eq_binderShifts telescope
  rw [emptyLevels] at lengthEq
  exact typingRuleDescOf_binderShiftsNonEmpty isFormation isNotNullary
    (List.eq_nil_of_length_eq_zero lengthEq.symm)

/-- Reconstruction: the generic `genFormation` arm derives Π-formation.  Domain
typed at `Type@(domainLevel, flag)`, codomain at `Type@(codomainLevel, flag)`
UNDER the domain binder ⟹ `piTyCodeCell` inhabits `Type@(lmax domainLevel
codomainLevel, flag)` — the canonical Π-formation conclusion, through
the data-driven generic arm (`lmaxAll [domainLevel, codomainLevel]` reduces to
`lmax domainLevel codomainLevel`). -/
theorem hasTypeDesc_piFormation_viaGenArm
    {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (domain : RawTerm scope) (codomain : RawTerm (scope + 1))
    (domainLevel codomainLevel : LevelExpr) (flag : UniverseFlag)
    (domainTyped :
      HasTypeDesc profile context domain (universeCodeCell domainLevel flag))
    (codomainTyped :
      HasTypeDesc profile (context.cons domain) codomain
        (universeCodeCell codomainLevel flag)) :
    HasTypeDesc profile context (piTyCodeCell domain codomain)
      (universeCodeCell (LevelExpr.lmax domainLevel codomainLevel) flag) := by
  refine HasTypeDesc.genFormation context .gen_piTyCode ()
    (RawTermChildren.binderShape domain codomain) [domainLevel, codomainLevel]
    flag { outputType := universeFormerOutput } typingRuleDescOf_piTyCode ?_
  refine DescTelescope.cons (currentDepth := 0) context domain domainLevel
    [codomainLevel] flag (.childCons codomain .childNil) domainTyped ?_
  exact DescTelescope.cons (currentDepth := 1) (context.cons domain) codomain
    codomainLevel [] flag .childNil codomainTyped
    (DescTelescope.nil (currentDepth := 2) (context.cons domain |>.cons codomain) flag)

/-- Reconstruction: the SAME generic `genFormation` arm derives Σ-formation,
with ZERO new code — one `typingRuleDescOf` row (`gen_sigmaTyCode`) suffices.
The P13 cascade-freedom witness for the description engine. -/
theorem hasTypeDesc_sigmaFormation_viaGenArm
    {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (domain : RawTerm scope) (codomain : RawTerm (scope + 1))
    (domainLevel codomainLevel : LevelExpr) (flag : UniverseFlag)
    (domainTyped :
      HasTypeDesc profile context domain (universeCodeCell domainLevel flag))
    (codomainTyped :
      HasTypeDesc profile (context.cons domain) codomain
        (universeCodeCell codomainLevel flag)) :
    HasTypeDesc profile context (sigmaTyCodeCell domain codomain)
      (universeCodeCell (LevelExpr.lmax domainLevel codomainLevel) flag) := by
  refine HasTypeDesc.genFormation context .gen_sigmaTyCode ()
    (RawTermChildren.binderShape domain codomain) [domainLevel, codomainLevel]
    flag { outputType := universeFormerOutput } typingRuleDescOf_sigmaTyCode ?_
  refine DescTelescope.cons (currentDepth := 0) context domain domainLevel
    [codomainLevel] flag (.childCons codomain .childNil) domainTyped ?_
  exact DescTelescope.cons (currentDepth := 1) (context.cons domain) codomain
    codomainLevel [] flag .childNil codomainTyped
    (DescTelescope.nil (currentDepth := 2) (context.cons domain |>.cons codomain) flag)

end FX1Poly.Typed
