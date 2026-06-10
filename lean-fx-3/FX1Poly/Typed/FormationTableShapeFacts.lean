import FX1Poly.Typed.TelescopeReducible
import FX1Poly.Core.FlatCodeTaitCandidate

/-! # FX1Poly/Typed/FormationTableShapeFacts
   — generic shape equation + arity bound for the formation table (GTL-06 brick 3b support)

The two call-site facts the by_cases-free dispatch refit needs at a SYMBOLIC generator:

  * `DescTelescope.shiftsShape` — the shape equation `binderShifts = consecutiveShifts
    currentDepth levels.length` extracted GENERICALLY from the premise telescope by index
    induction.  Retires the per-generator `gen_X_binderShifts_eq` rfl lemmas at dispatch
    sites: the telescope itself carries the shape, for every present and future row.
  * `formationRowArityBound` / `formationLevelsArityBound` — every formation row has at most
    two children.  This is the ONE table-mirroring fact in the generic dispatch chain (five
    defeq cases, one line per row, co-located with the table's semantics); a self-updating
    tag-bounded decision form is the recorded follow-on.  The levels-length form converts
    through `consecutiveShifts_length`.

## Zero-axiom verification

An index induction, a `Nat` induction, and a five-way `by_cases` mirror of the rule table
closing by defeq `Nat.le` constructors and the table-miss `Option.noConfusion`.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Gated in
`FX1PolyAudit/AuditTypedTypingEngines.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- The consecutive-shifts list has exactly the requested length. -/
theorem consecutiveShifts_length (currentDepth count : Nat) :
    (consecutiveShifts currentDepth count).length = count := by
  induction count generalizing currentDepth with
  | zero => rfl
  | succ remaining countIH =>
      exact congrArg Nat.succ (countIH (currentDepth + 1))

/-- **The shape equation, extracted generically from the telescope.**  A formation premise
telescope forces its children's binder shifts to be exactly the consecutive shifts of its
level list — for EVERY generator, present or future.  Index induction over the telescope;
the cons case extends the rest-telescope's shape by the current depth. -/
theorem DescTelescope.shiftsShape {profile : PolyProfile} {baseScope currentDepth : Nat}
    {binderShifts : List Nat}
    {context : TypingContext profile (baseScope + currentDepth)}
    {levels : List LevelExpr} {flag : UniverseFlag}
    {children : RawTermChildren binderShifts baseScope}
    (telescope : DescTelescope profile context levels flag children) :
    binderShifts = consecutiveShifts currentDepth levels.length := by
  induction levels generalizing binderShifts currentDepth children with
  | nil =>
      cases telescope
      rfl
  | cons _headLevel _restLevels restIH =>
      cases telescope with
      | cons _context _head _headLevel _restLevels _flag _rest _headTyped restTelescope =>
          exact congrArg (List.cons _) (restIH restTelescope)

/-- **The shape equation for the GROWN premise telescope** — the `DescTelescopePi` twin of
`DescTelescope.shiftsShape`, same levels-induction recipe (the grown telescope is mutual with
`HasTypeDescPi`, so direct telescope induction is unsupported). -/
theorem DescTelescopePi.shiftsShape {profile : PolyProfile} {baseScope currentDepth : Nat}
    {binderShifts : List Nat}
    {context : TypingContext profile (baseScope + currentDepth)}
    {levels : List LevelExpr} {flag : UniverseFlag}
    {children : RawTermChildren binderShifts baseScope}
    (telescope : DescTelescopePi profile context levels flag children) :
    binderShifts = consecutiveShifts currentDepth levels.length := by
  induction levels generalizing binderShifts currentDepth children with
  | nil =>
      cases telescope
      rfl
  | cons _headLevel _restLevels restIH =>
      cases telescope with
      | cons _context _head _headLevel _restLevels _flag _rest _headTyped restTelescope =>
          exact congrArg (List.cons _) (restIH restTelescope)

/-- **Every formation row has at most two children** — the one table-mirroring fact in the
generic dispatch chain: five defeq cases, one line per row, table-miss closes the rest. -/
theorem formationRowArityBound {generator : Generator} {rule : TypingRuleDesc}
    (isFormation : typingRuleDescOf generator = some rule) :
    generator.binderShifts.length ≤ 2 := by
  by_cases isPiFormer : generator = .gen_piTyCode
  · subst isPiFormer; exact Nat.le_refl 2
  by_cases isSigmaFormer : generator = .gen_sigmaTyCode
  · subst isSigmaFormer; exact Nat.le_refl 2
  by_cases isListFormer : generator = .gen_listCode
  · subst isListFormer; exact Nat.le_succ 1
  by_cases isOptionFormer : generator = .gen_optionCode
  · subst isOptionFormer; exact Nat.le_succ 1
  by_cases isUnitFormer : generator = .gen_unitCode
  · subst isUnitFormer; exact Nat.zero_le 2
  exfalso
  dsimp only [typingRuleDescOf] at isFormation
  rw [if_neg isPiFormer, if_neg isSigmaFormer, if_neg isListFormer, if_neg isOptionFormer,
    if_neg isUnitFormer] at isFormation
  exact nomatch isFormation

/-- The arity bound in LEVELS-length form — the shape the arity-dispatch supplier consumes,
converted through the shape equation and `consecutiveShifts_length`. -/
theorem formationLevelsArityBound {generator : Generator} {rule : TypingRuleDesc}
    {levels : List LevelExpr}
    (isFormation : typingRuleDescOf generator = some rule)
    (shapeEq : generator.binderShifts = consecutiveShifts 0 levels.length) :
    levels.length ≤ 2 := by
  have lengthEq : generator.binderShifts.length = levels.length :=
    (congrArg List.length shapeEq).trans (consecutiveShifts_length 0 levels.length)
  exact lengthEq ▸ formationRowArityBound isFormation

/-- **A formation row is never the empty code** — cascade-free table-miss discrimination: at
the literal `gen_emptyCode` the rule table reduces definitionally to `none` (the Empty type is
typed by the base-type engine, not by a formation row).  The bounded relation's `neutral` arm
gate. -/
theorem formationRowIsNotEmpty {generator : Generator} {rule : TypingRuleDesc}
    (isFormation : typingRuleDescOf generator = some rule) :
    generator ≠ .gen_emptyCode := by
  intro isEmpty
  subst isEmpty
  exact nomatch (show (none : Option TypingRuleDesc) = some rule from isFormation)

/-- **No formation row is a flat data code** — table-mirroring fact (five defeq cases, the
same row-mirror discipline as `formationRowArityBound`): the bounded relation pins flat codes
to their data candidates, so its `neutral` arm requires this gate at a symbolic generator. -/
theorem formationRowIsNotFlat {generator : Generator} {rule : TypingRuleDesc}
    (isFormation : typingRuleDescOf generator = some rule) :
    generator.isFlatDataCode = false := by
  by_cases isPiFormer : generator = .gen_piTyCode
  · subst isPiFormer; rfl
  by_cases isSigmaFormer : generator = .gen_sigmaTyCode
  · subst isSigmaFormer; rfl
  by_cases isListFormer : generator = .gen_listCode
  · subst isListFormer; rfl
  by_cases isOptionFormer : generator = .gen_optionCode
  · subst isOptionFormer; rfl
  by_cases isUnitFormer : generator = .gen_unitCode
  · subst isUnitFormer; rfl
  exfalso
  dsimp only [typingRuleDescOf] at isFormation
  rw [if_neg isPiFormer, if_neg isSigmaFormer, if_neg isListFormer, if_neg isOptionFormer,
    if_neg isUnitFormer] at isFormation
  exact nomatch isFormation

/-- **The unique childless formation row is the unit former** — table-mirroring fact: the
non-nullary rows all carry at least one binder shift, so a childless formation generator must
be `gen_unitCode`.  Converts the budget's `gen_unitCode`-named nullary gate into the
levels-empty form the generic arity-dispatch supplier consumes. -/
theorem formationRowNullaryIsUnit {generator : Generator} {rule : TypingRuleDesc}
    (isFormation : typingRuleDescOf generator = some rule)
    (isChildless : generator.binderShifts = []) :
    generator = .gen_unitCode := by
  by_cases isPiFormer : generator = .gen_piTyCode
  · subst isPiFormer; exact nomatch isChildless
  by_cases isSigmaFormer : generator = .gen_sigmaTyCode
  · subst isSigmaFormer; exact nomatch isChildless
  by_cases isListFormer : generator = .gen_listCode
  · subst isListFormer; exact nomatch isChildless
  by_cases isOptionFormer : generator = .gen_optionCode
  · subst isOptionFormer; exact nomatch isChildless
  by_cases isUnitFormer : generator = .gen_unitCode
  · exact isUnitFormer
  exfalso
  dsimp only [typingRuleDescOf] at isFormation
  rw [if_neg isPiFormer, if_neg isSigmaFormer, if_neg isListFormer, if_neg isOptionFormer,
    if_neg isUnitFormer] at isFormation
  exact nomatch isFormation

/-- **The empty formation telescope at a SYMBOLIC childless spine.**  Over a free
`binderShifts` index pinned to `[]`, any child spine is the empty spine and carries the
empty telescope — the row-generic form of `DescTelescope.nil` a dispatch site needs at a
symbolic generator whose shape equation forces childlessness (the nullary-row deferral). -/
theorem DescTelescope.nilAtChildless {profile : PolyProfile} {baseScope : Nat}
    {binderShifts : List Nat}
    (context : TypingContext profile baseScope) (flag : UniverseFlag)
    (children : RawTermChildren binderShifts baseScope)
    (isChildless : binderShifts = []) :
    DescTelescope profile (currentDepth := 0) context [] flag children := by
  subst isChildless
  match children with
  | .childNil => exact DescTelescope.nil (currentDepth := 0) context flag

/-- **Every formation row's output is a universe code at the iterated-`lmax` level** — the
LEVEL-PINNED strengthening of `typingRuleDescOf_output_isUniverseCode`, which the BOUNDED
dispatch needs: its gate extraction bounds the CHILD levels, so the output's level must be
named as `lmaxAll levels` (not an opaque existential) to conclude the output is below the
bound.  The `universeFormerOutput` rows hold definitionally; the nullary row's pinned `lzero`
output coincides with `lmaxAll []` once the shape equation forces `levels = []`. -/
theorem formationRowOutputLevel {generator : Generator} {rule : TypingRuleDesc}
    {levels : List LevelExpr}
    (isFormation : typingRuleDescOf generator = some rule)
    (shapeEq : generator.binderShifts = consecutiveShifts 0 levels.length)
    (scope : Nat) (flag : UniverseFlag) :
    ∃ outputFlag : UniverseFlag,
      rule.outputType scope levels flag = universeCodeCell (lmaxAll levels) outputFlag := by
  by_cases isPiFormer : generator = .gen_piTyCode
  · subst isPiFormer
    obtain rfl : rule = { outputType := universeFormerOutput } := Option.some.inj isFormation.symm
    exact ⟨flag, rfl⟩
  by_cases isSigmaFormer : generator = .gen_sigmaTyCode
  · subst isSigmaFormer
    obtain rfl : rule = { outputType := universeFormerOutput } := Option.some.inj isFormation.symm
    exact ⟨flag, rfl⟩
  by_cases isListFormer : generator = .gen_listCode
  · subst isListFormer
    obtain rfl : rule = { outputType := universeFormerOutput } := Option.some.inj isFormation.symm
    exact ⟨flag, rfl⟩
  by_cases isOptionFormer : generator = .gen_optionCode
  · subst isOptionFormer
    obtain rfl : rule = { outputType := universeFormerOutput } := Option.some.inj isFormation.symm
    exact ⟨flag, rfl⟩
  by_cases isUnitFormer : generator = .gen_unitCode
  · subst isUnitFormer
    obtain rfl : rule = { outputType := nullaryFormerOutput } :=
      Option.some.inj (isFormation.symm.trans typingRuleDescOf_unitCode)
    match levels, shapeEq with
    | [], _shapeEq => exact ⟨UniverseFlag.standard, rfl⟩
    | _ :: _, impossibleShape => exact nomatch impossibleShape
  exfalso
  dsimp only [typingRuleDescOf] at isFormation
  rw [if_neg isPiFormer, if_neg isSigmaFormer, if_neg isListFormer, if_neg isOptionFormer,
    if_neg isUnitFormer] at isFormation
  exact nomatch isFormation

end FX1Poly.Typed
