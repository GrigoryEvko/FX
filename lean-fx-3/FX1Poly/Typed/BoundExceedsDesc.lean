import FX1Poly.Typed.HasTypeDesc
import FX1Poly.Universe.LevelExprSimplify

/-! # FX1Poly/Typed/BoundExceedsDesc
    — the per-derivation universe-level budget predicate (the BFT-11/12 fuel)

The bounded FORMATION fundamental theorem (`HasTypeDesc.rec` dispatch, BFT-11) needs the `universeFormation` arm's
`belowBound : denote (lsucc levelExpr) env < bound`.  Unlike conv / genFormation / var (which extract or ignore the
gate), `universeFormation` is a LEAF with no sub-derivation to read it off — so the bound must EXCEED the denoted
`lsucc`-level of every `universeFormation` node in the derivation.  This per-term "fuel" is the bounded route's
analogue of the denote route's universe-unbounded candidate.

## Why an INDUCTIVE (not a function)

A budget FUNCTION `HasTypeDesc … → Prop` would be LARGE ELIMINATION — eliminating a multi-constructor `Prop`
inductive into `Type`-where-`Prop`-lives — which Lean forbids (a non-subsingleton `Prop` has no large-elim
recursor).  So the budget is an inductive `Prop` family INDEXED by the derivation, mutual with the telescope
budget.  This also cleanly handles the `conv` arm: its constructor carries `BoundExceeds` for BOTH the subject and
the reclassifier sub-derivations BY CONSTRUCTION, so no term-budget-over-the-(arbitrary)-inner-classifier is needed
(the recurring obstruction of a term-syntactic budget).

## The discharge plan (BFT-12)

`∃ bound, BoundExceeds env bound d` is provable by induction on `d` (CONSTRUCTING the budget, summing
sub-bounds), using monotonicity `BoundExceeds env b d → b ≤ b' → BoundExceeds env b' d` (generic induction on the
budget derivation — no specific-index inversion).  The `universeFormation` leaf supplies `denote (lsucc e) env +
1`; every `genFormation` node supplies `premisesBound + 1` so the nullary `gen_unitCode` row's pinned `Type@0`
output sits strictly below the bound.  The FT arms (BFT-11) then INVERT `BoundExceeds (ctor …)` — which needs the
index-equality-witness recipe (`cases` at a specific index fails because `genFormation`'s `rule.outputType` index
is opaque).

## The nullary output gate

`genFormation` carries `nullaryBelowBound : generator = gen_unitCode → 0 < bound`.  The `gen_unitCode` row's
output is the level/flag-pinned `Type@0`, whose bounded-membership needs the universe candidate reducible at the
bound, i.e. `denote lzero env < bound = 0 < bound`.  Unlike the ≥1-child formers (whose output level is gate-
EXTRACTED from a child universe member at FT time), the nullary row binds no children, so its output positivity
must be carried in the budget.  The gate is an IMPLICATION from the nullary-generator equation so the ≥1-child
formers discharge it vacuously (the antecedent is false) at no cost.

## Zero-axiom verification

A mutual inductive `Prop` family indexed by `HasTypeDesc` / `DescTelescope` derivations; constructors mirror the
typing constructors, the `universeFormation` constructor carrying the `belowBound` gate and `genFormation` the
nullary output gate.  Inductives introduce no axioms (checked: depends on no axioms).  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/- **The per-derivation universe-level budget (indexed inductive `Prop`).**  `BoundExceeds env bound d` asserts
`bound` exceeds the denoted `lsucc`-level of every `universeFormation` leaf in the derivation `d` AND the pinned
output level of every nullary `gen_unitCode` formation node (`nullaryBelowBound`); conv and genFormation carry the
sub-derivations' budgets by construction.  Mutual with `BoundExceedsTelescope`. -/
mutual
inductive BoundExceeds {profile : PolyProfile} (env : Nat → Nat) (bound : Nat) :
    {scope : Nat} → {context : TypingContext profile scope} → {subject classifier : RawTerm scope} →
    HasTypeDesc profile context subject classifier → Prop where
  | var {scope : Nat} (context : TypingContext profile scope) (index : Fin scope) :
      BoundExceeds env bound (HasTypeDesc.var context index)
  | conv {scope : Nat} {context : TypingContext profile scope}
      {subject classifier reclassifier : RawTerm scope} (levelExpr : LevelExpr) (flag : UniverseFlag)
      {typed : HasTypeDesc profile context subject classifier} {converts : Conv classifier reclassifier}
      {reclassifierTyped : HasTypeDesc profile context reclassifier (universeCodeCell levelExpr flag)}
      (subjectBudget : BoundExceeds env bound typed)
      (reclassifierBudget : BoundExceeds env bound reclassifierTyped) :
      BoundExceeds env bound (HasTypeDesc.conv levelExpr flag typed converts reclassifierTyped)
  | universeFormation {scope : Nat} (context : TypingContext profile scope) (levelExpr : LevelExpr)
      (flag : UniverseFlag)
      (belowBound : LevelExpr.denote (LevelExpr.lsucc levelExpr) env < bound) :
      BoundExceeds env bound (HasTypeDesc.universeFormation context levelExpr flag)
  | genFormation {scope : Nat} (context : TypingContext profile scope) (generator : Generator)
      (payload : generator.payload scope) (children : RawTermChildren generator.binderShifts scope)
      (levels : List LevelExpr) (flag : UniverseFlag) (rule : TypingRuleDesc)
      (isFormation : typingRuleDescOf generator = some rule)
      (nullaryBelowBound : generator = Generator.gen_unitCode → 0 < bound)
      {premises : DescTelescope profile (currentDepth := 0) context levels flag children}
      (premisesBudget : BoundExceedsTelescope env bound premises) :
      BoundExceeds env bound
        (HasTypeDesc.genFormation context generator payload children levels flag rule isFormation premises)
inductive BoundExceedsTelescope {profile : PolyProfile} (env : Nat → Nat) (bound : Nat) :
    {baseScope currentDepth : Nat} → {binderShifts : List Nat} →
    {context : TypingContext profile (baseScope + currentDepth)} → {levels : List LevelExpr} →
    {flag : UniverseFlag} → {children : RawTermChildren binderShifts baseScope} →
    DescTelescope profile context levels flag children → Prop where
  | nil {baseScope currentDepth : Nat} (context : TypingContext profile (baseScope + currentDepth))
      (flag : UniverseFlag) :
      BoundExceedsTelescope env bound (DescTelescope.nil context flag)
  | cons {baseScope currentDepth : Nat} {restShifts : List Nat}
      (context : TypingContext profile (baseScope + currentDepth)) (head : RawTerm (baseScope + currentDepth))
      (headLevel : LevelExpr) (restLevels : List LevelExpr) (flag : UniverseFlag)
      (rest : RawTermChildren restShifts baseScope)
      {headTyped : HasTypeDesc profile context head (universeCodeCell headLevel flag)}
      {restTyped : DescTelescope profile (currentDepth := currentDepth + 1) (context.cons head)
        restLevels flag rest}
      (headBudget : BoundExceeds env bound headTyped)
      (restBudget : BoundExceedsTelescope env bound restTyped) :
      BoundExceedsTelescope env bound
        (DescTelescope.cons context head headLevel restLevels flag rest headTyped restTyped)
end

end FX1Poly.Typed
