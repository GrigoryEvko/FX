import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionCongruenceClosesGeneric
import FX1Poly.Tier0.Term.Core.RawSize

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/UnionChildSubjectReductionBounded
    — the fuel-bounded single-step-SR predicate + the closure frame (SR-WF-TIEOFF step 1)

The SR full arc's last open node is `UnionChildSubjectReduction` (universal single-step SR), to be discharged by
STRUCTURAL-FUEL recursion (the propext-safe substitute for `WellFounded.fix`, which leaks here).  This file ships
the fuel-bounded form and the frame that turns "single-step SR holds for every term of size `< bound`, for every
`bound`" into the universal statement.

`UnionChildSubjectReductionBelow profile bound` is `UnionChildSubjectReduction` gated by `subterm.size < bound`
(`RawTerm.size`, the structural measure).  The frame:

  * `UnionChildSubjectReduction.toBelow` — the universal gives every bounded form (forget the bound);
  * `UnionChildSubjectReductionBelow.weaken` — a larger bound gives a smaller one (the fuel-induction step
    consumes `Below n` where it needs `Below (n+1)`-restricted-to-children);
  * ★ `unionChildSubjectReductionOfAllBelow` — the CLOSURE ENABLER: if the bounded form holds at EVERY bound,
    the universal holds (instantiate `bound := subterm.size + 1`).  So the remaining tie-off reduces to proving
    `∀ bound, UnionChildSubjectReductionBelow profile bound` by induction on `bound` — at `bound + 1`, the
    congruence closer re-types a STEPPED CHILD strictly smaller than the cell (`RawSize` child-decrease:
    `RawTermChildren.size_lt_childCons_head` + the `mkGen` size step), so the `Below bound` hypothesis from the
    induction supplies it.

This is the structural frame the BOUNDED congruence gates (the next steps) fill; the closure enabler is the
load-bearing piece that lets the fuel-bounded family collapse to the universal `UnionChildSubjectReduction`.

## Zero-axiom

`Prop` definition + three forwarding lemmas over `Nat` order (`Nat.lt_of_lt_of_le`, `Nat.lt_succ_self`).  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/`. -/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- **The fuel-bounded single-step subject-reduction self-reference.**  `UnionChildSubjectReduction` gated by a
size bound: single-step SR holds for every union-typed `subterm` whose structural size is `< bound`.  The fuel a
structural recursion decrements — discharged by induction on `bound`, with the congruence closer's child
re-typing supplied by the `Below (bound - 1)` hypothesis (children are strictly smaller). -/
def UnionChildSubjectReductionBelow (profile : PolyProfile) (bound : Nat) : Prop :=
  ∀ {scope : Nat} {context : TypingContext profile scope} {subterm reduct subtermType : RawTerm scope},
    subterm.size < bound → HasTypeUnion profile context subterm subtermType → Step subterm reduct →
      ∃ reductType : RawTerm scope,
        HasTypeUnion profile context reduct reductType ∧ Conv subtermType reductType

/-- The universal self-reference gives the bounded form at ANY bound — simply forget the size hypothesis. -/
theorem UnionChildSubjectReduction.toBelow {profile : PolyProfile} {bound : Nat}
    (childSubjectReduction : UnionChildSubjectReduction profile) :
    UnionChildSubjectReductionBelow profile bound :=
  fun _sizeLt typed step => childSubjectReduction typed step

/-- The bounded form is ANTITONE in the bound: a larger bound's SR specializes to a smaller bound (a term of
size `< bound` is a fortiori of size `< bound'` when `bound ≤ bound'`).  The fuel-induction step uses this to
feed a `Below (bound + 1)` obligation from the `Below bound` inductive hypothesis once the cell's children are
known strictly smaller. -/
theorem UnionChildSubjectReductionBelow.weaken {profile : PolyProfile} {bound bound' : Nat}
    (boundLe : bound ≤ bound') (childSubjectReductionBelow : UnionChildSubjectReductionBelow profile bound') :
    UnionChildSubjectReductionBelow profile bound :=
  fun sizeLt typed step => childSubjectReductionBelow (Nat.lt_of_lt_of_le sizeLt boundLe) typed step

/-- ★ **The closure enabler.**  If the fuel-bounded single-step SR holds at EVERY bound, then the UNIVERSAL
`UnionChildSubjectReduction` holds — instantiate the bound at `subterm.size + 1` (every term is below its own
size-plus-one).  So discharging the SR full arc's last node reduces to proving
`∀ bound, UnionChildSubjectReductionBelow profile bound`, which a structural induction on `bound` closes (the
congruence closer recurses only on children, strictly smaller, covered by the inductive hypothesis at the
predecessor bound). -/
theorem unionChildSubjectReductionOfAllBelow {profile : PolyProfile}
    (allBelow : ∀ bound : Nat, UnionChildSubjectReductionBelow profile bound) :
    UnionChildSubjectReduction profile :=
  fun {_scope _context subterm _reduct _subtermType} typed step =>
    allBelow (subterm.size + 1) (Nat.lt_succ_self _) typed step

end FX1Poly.Typed
