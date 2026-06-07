import FX1Poly.Typed.ListCodeShape

/-! # FX1Poly/Typed/OptionCodeShape
    — the `optionCode` head-generator → children reconstruction (GTL-13 canonical-forms substrate)

The one-child data-former analogue of `eq_listCodeCell_of_headGenerator` (`ListCodeShape.lean`): a cell whose
head generator is `gen_optionCode` IS an `optionCode` cell over a recovered element child.  The element is
recovered by destructuring the `[0]`-indexed `RawTermChildren` and collapsing the `childNil` tail; the `()`
payload is collapsed by Lean's definitional structure-eta on `Unit`.

This is the canonical-forms reconstruction the `gen_optionCode` branch of the formation canonical-forms
consumers needs once `gen_optionCode` joins `typingRuleDescOf` (GTL-13): from a closed formation-typed term
whose head is `gen_optionCode`, recover its `Option element` shape (so the closed-canonical-forms / consistency
arguments can refute it at `emptyTypeCell` by `Generator.noConfusion`, exactly as for Π / Σ / universe / list
codes).  Row-independent — pure `RawTerm` shape reconstruction, no `typingRuleDescOf` dependency, so it lands
ahead of the formation row.

## Zero-axiom verification

`cases cell` + `cases children` twice (the second is the `childNil` tail) + `RawTermChildren.eq_childNil` +
`rfl` (structure-eta collapses the `Unit` payload) — the verbatim discipline of `eq_listCodeCell_of_head-
Generator`, one data former over.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **A cell with head `gen_optionCode` is an `optionCode` cell.**  The one-child data-former twin of
`eq_listCodeCell_of_headGenerator`: the element child is recovered by destructuring the `[0]`-indexed
`RawTermChildren` and collapsing the `childNil` tail (and the `Unit` payload by structure-eta). -/
theorem eq_optionCodeCell_of_headGenerator {scope : Nat}
    {cell : RawTerm scope}
    (headIsOption : RawTerm.headGenerator cell = Generator.gen_optionCode) :
    ∃ element : RawTerm scope,
      cell = .mkGen .gen_optionCode () (.childCons element .childNil) := by
  cases cell with
  | mkGen generator payload children =>
      change generator = Generator.gen_optionCode at headIsOption
      subst headIsOption
      change RawTermChildren [0] scope at children
      cases children with
      | childCons element restChildren =>
          refine ⟨element, ?_⟩
          rw [RawTermChildren.eq_childNil restChildren]
          rfl

end FX1Poly.Typed
