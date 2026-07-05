import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingFreshShift

/-! # MatchingMapCongruence — pointwise map congruence over a `Nat` list (propext-free)

The diagram-leg fold of the cup-head partner cancel needs: two partner-index lists that
`List.map` the same boundary range with per-element-agreeing readoff functions are EQUAL.
Core `List.map_congr_left` routes through `∈`-iff lemmas that leak `propext`; this brick
re-rolls the congruence structurally over the list — `List.Mem.head` / `List.Mem.tail` are
plain constructors, `List.map` on a cons reduces definitionally, so the whole argument is a
two-clause structural recursion with zero axioms.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **Pointwise map congruence over a `Nat` list.**  If two readoff functions agree on
every element of `values`, then mapping either over `values` gives the same list.  Structural
recursion on `values`: the nil case is `rfl`; the cons case rewrites the head via agreement
(`List.Mem.head`) and recurses on the tail (`List.Mem.tail`).  No `∈`-iff, no `propext`. -/
theorem natMapCongrOfMemAgree (firstMap secondMap : Nat → Nat) :
    (values : List Nat) →
    (∀ value, value ∈ values → firstMap value = secondMap value) →
    values.map firstMap = values.map secondMap
  | [], _ => rfl
  | head :: rest, agree => by
      show firstMap head :: rest.map firstMap = secondMap head :: rest.map secondMap
      rw [agree head (List.Mem.head rest),
        natMapCongrOfMemAgree firstMap secondMap rest
          (fun value valueInRest => agree value (List.Mem.tail head valueInRest))]

/-! ## Honesty marker -/

/-- **Honesty marker — the propext-free `Nat`-list map congruence is SHIPPED.**
`natMapCongrOfMemAgree` gives `values.map firstMap = values.map secondMap` from per-element
agreement, by structural recursion over the list (no `∈`-iff lemma, no `propext`).  This is
the list-congruence the cup-head diagram-partner fold consumes: with the boundary range as
`values` and the two runs' `partnerIndexOf` readoffs as the maps, per-index agreement lifts
to the whole partner-list equality.  What this marker does NOT claim: the per-index agreement
itself (the same-classification cells + the orbit).  `= true`. -/
def fxMode_hasNatMapCongruence : Bool := true

end FX1Poly.Polygraph
