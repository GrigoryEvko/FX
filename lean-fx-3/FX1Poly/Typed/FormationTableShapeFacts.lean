import FX1Poly.Typed.TelescopeReducible

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

end FX1Poly.Typed
