import FX1Poly.Typed.HasTypeHonesty
import FX1Poly.Core.RawTermChildrenUnique

/-! # FX1Poly/Typed/UniverseCodeShape
    — raw-cell inversion for universe-code cells

`eq_universeCodeCell_of_headGenerator` recovers the full `universeCodeCell`
shape from the head generator alone: any cell whose head is `gen_universeCode`
*is* `universeCodeCell e flag` for the `e`, `flag` in its payload.  Two facts
collapse the cell: its nullary child-spine is `childNil`
(`RawTermChildren.eq_childNil`, since `gen_universeCode.binderShifts = []`), and
its payload is a `LevelExpr x UniverseFlag` pair (Prod-eta is definitional), so
once the spine is `childNil` the reconstruction is by reflexivity.

This is the raw destructor that `Decidable IsType` (#303) needs: to confirm a
candidate type is a universe code — and apply `HasType.universeFormation` — the
decision procedure must turn `headGenerator = gen_universeCode` into a concrete
`universeCodeCell e flag`.

## Zero-axiom verification

`cases` on the single-constructor `RawTerm`, then `change` (defeq, NOT `simp`)
exposes `generator = gen_universeCode`, `subst`, and
`RawTermChildren.eq_childNil` collapses the spine.  No `propext` / `Quot.sound` /
`Classical`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- A cell whose head generator is `gen_universeCode` is a `universeCodeCell`:
its nullary child-spine is `childNil` (`eq_childNil`) and its payload is the
`(level, flag)` pair. -/
theorem eq_universeCodeCell_of_headGenerator {scope : Nat}
    {cell : RawTerm scope}
    (headIsUniverseCode :
      RawTerm.headGenerator cell = Generator.gen_universeCode) :
    ∃ (levelExpr : LevelExpr) (flag : UniverseFlag),
      cell = universeCodeCell levelExpr flag := by
  cases cell with
  | mkGen generator payload children =>
      change generator = Generator.gen_universeCode at headIsUniverseCode
      subst headIsUniverseCode
      refine ⟨payload.1, payload.2, ?_⟩
      rw [RawTermChildren.eq_childNil children]
      rfl

/-- A cell whose head generator is `gen_var` is a `variableCell`: the same
nullary child-spine collapse (`RawTermChildren.eq_childNil`, since
`gen_var.binderShifts = []`) as the universe-code case, with the cell's payload
serving directly as the de Bruijn index.  This is the second raw destructor
`Decidable IsType` (#303) needs — to case on a `gen_var` cell and recover its
index as data (`Exists` admits no large elimination, so the index must come from
destructuring the cell, not from an existential witness). -/
theorem eq_variableCell_of_headGenerator {scope : Nat}
    {cell : RawTerm scope}
    (headIsVariable :
      RawTerm.headGenerator cell = Generator.gen_var) :
    ∃ index : Fin scope, cell = variableCell index := by
  cases cell with
  | mkGen generator payload children =>
      change generator = Generator.gen_var at headIsVariable
      subst headIsVariable
      refine ⟨payload, ?_⟩
      rw [RawTermChildren.eq_childNil children]
      rfl

/-- The head generator of a universe-code cell is `gen_universeCode` (the cell
unfolds to `mkGen gen_universeCode _ _`, and the matcher reads the head field).
Stated with `scope` pinned so the defeq check does not stall on a metavariable.
The dual destructor `eq_universeCodeCell_of_headGenerator` is the converse. -/
theorem headGenerator_universeCodeCell {scope : Nat} (levelExpr : LevelExpr)
    (flag : UniverseFlag) :
    RawTerm.headGenerator (universeCodeCell levelExpr flag : RawTerm scope)
      = Generator.gen_universeCode := by
  rfl

/-- The head generator of a variable cell is `gen_var`.  `scope` is pinned by the
index's `Fin scope` type. -/
theorem headGenerator_variableCell {scope : Nat} (index : Fin scope) :
    RawTerm.headGenerator (variableCell index) = Generator.gen_var := by
  rfl

end FX1Poly.Typed
