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

end FX1Poly.Typed
