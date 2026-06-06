import FX1Poly.Typed.SigmaCodeShape

/-! # FX1Poly/Typed/ListCodeShape
    — the `listCode` head-generator → children reconstruction (GTL-11 canonical-forms substrate)

The one-child data-former analogue of `eq_sigmaTyCodeCell_of_headGenerator` (`SigmaCodeShape.lean`): a cell
whose head generator is `gen_listCode` IS a `listCode` cell over a recovered element child.  The element is
recovered by destructuring the `[0]`-indexed `RawTermChildren` and collapsing the `childNil` tail; the `()`
payload is collapsed by Lean's definitional structure-eta on `Unit`.

This is the canonical-forms reconstruction the `gen_listCode` branch of the formation canonical-forms
consumers (`HasTypeDesc.subjectIsVariableOrFormerHead` → `closedSubjectIsTypeFormer`,
`HasTypeDescClosedForms.lean`) needs once `gen_listCode` joins `typingRuleDescOf` (GTL-11): from a closed
formation-typed term whose head is `gen_listCode`, recover its `List element` shape (so the closed-canonical-
forms / consistency arguments can refute it at `emptyTypeCell` by `Generator.noConfusion`, exactly as for
Π / Σ / universe codes).

## Zero-axiom verification

`cases cell` + `cases children` twice (the second is the `childNil` tail) + `RawTermChildren.eq_childNil` +
`rfl` (structure-eta collapses the `Unit` payload) — the verbatim discipline of `eq_sigmaTyCodeCell_of_head-
Generator`, one child shorter.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **A cell with head `gen_listCode` is a `listCode` cell.**  The one-child data-former twin of
`eq_sigmaTyCodeCell_of_headGenerator`: the element child is recovered by destructuring the `[0]`-indexed
`RawTermChildren` and collapsing the `childNil` tail (and the `Unit` payload by structure-eta). -/
theorem eq_listCodeCell_of_headGenerator {scope : Nat}
    {cell : RawTerm scope}
    (headIsList : RawTerm.headGenerator cell = Generator.gen_listCode) :
    ∃ element : RawTerm scope,
      cell = .mkGen .gen_listCode () (.childCons element .childNil) := by
  cases cell with
  | mkGen generator payload children =>
      change generator = Generator.gen_listCode at headIsList
      subst headIsList
      change RawTermChildren [0] scope at children
      cases children with
      | childCons element restChildren =>
          refine ⟨element, ?_⟩
          rw [RawTermChildren.eq_childNil restChildren]
          rfl

end FX1Poly.Typed
