import FX1Poly.Core.RawTerm

/-! # Foundation/PolyCell/Core/RawTermChildrenUnique
    — `childNil` is the unique inhabitant of the empty child-spine

`RawTermChildren` is indexed by its `binderShifts` list.  At the empty index
`[]` only `childNil` can construct it: `childCons` produces the non-empty index
`shift :: restShifts`.  So every `children : RawTermChildren [] scope` equals
`childNil`.

## Why this brick

It is the prerequisite for destructuring a nullary-spine cell — in particular a
`gen_universeCode` cell `mkGen gen_universeCode (e, flag) children`, whose
`children : RawTermChildren gen_universeCode.binderShifts scope` reduces to
`RawTermChildren [] scope`.  Reconstructing `t = universeCodeCell e flag` (to
apply `HasType.universeFormation`) needs exactly `children = childNil`, which is
this lemma.  That reconstruction is the missing step for `Decidable IsType`
(#303) and thence decidable typed checking (P11, the ★ MILESTONE-A line).

## Zero-axiom verification

The `cases` *tactic* on an indexed inductive eliminates the impossible
`childCons` constructor through the index type's (`List`) `noConfusion`, not
through match-compiler equation lemmas — so it avoids the restricted-index
`propext` leak that a match-based `def` (or `match` expression) would incur.
Swept by `#audit_namespace FX1Poly.Core` in `FX1PolyAudit/AuditCoreSubstrate.lean`.
-/

namespace FX1Poly.Core
namespace RawTermChildren

/-- `childNil` is the unique inhabitant of `RawTermChildren [] scope`: the only
constructor whose index is `[]`. -/
theorem eq_childNil {scope : Nat} (children : RawTermChildren [] scope) :
    children = .childNil := by
  cases children
  rfl

/-- The empty child-spine is a subsingleton: any two empty spines agree (both
are `childNil`). -/
instance instSubsingletonEmpty {scope : Nat} :
    Subsingleton (RawTermChildren [] scope) :=
  ⟨fun firstChildren secondChildren => by
    rw [eq_childNil firstChildren, eq_childNil secondChildren]⟩

end RawTermChildren
end FX1Poly.Core
