import LeanFX2.Term.ToRaw

/-! # Tools/Tactics/HEq — HEq → Eq via Term-typing

When proving Term-level equalities, HEq frequently appears via
substitution / renaming of dependent index types.  Helpers in this
file convert HEq to Eq when the types align, and refute incompatible
HEq witnesses via the raw projection.

## Key helpers

* `Term.eq_of_heq_typeEq` — convert HEq + type/raw Eq to a cast'd Eq.
  After casting both indices into agreement, the underlying values are
  Eq.
* `Term.heq_iff_eq_after_cast` — the iff form of the above.
* `Term.refuteViaToRaw` — refute incompatible HEq via raw inequality.
  Two Terms can only be HEq if their raw projections agree (since
  Term.toRaw t = t's raw index is rfl).

## Why

HEq is frequently introduced when matching on Step/Step.par cases where
the target type depends on substituted indices.  Converting HEq to
plain Eq makes downstream proof manipulation cleaner.  The refutation
helper shorts inversion proofs that would otherwise hit the dep-elim
wall.

## Dependencies

* `Term/ToRaw.lean` — for the rfl projection identity

## Downstream

* `Reduction/Compat.lean` — β-arm cast alignment uses `eq_of_heq_typeEq`
* `Confluence/*.lean` — typed inversions use `refuteViaToRaw`
* `Bridge.lean` — typed→raw correspondence uses both
-/

namespace LeanFX2

/-- Convert a Term-level HEq into a cast'd Eq once the type and raw
indices are known to agree propositionally.

After substituting the type and raw equalities, both Terms have the
exact same Lean type, so HEq collapses to Eq.  The result has the form
`typeEq ▸ rawEq ▸ t1 = t2` which is the casted version of `HEq t1 t2`. -/
theorem Term.eq_of_heq_typeEq
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {firstType secondType : Ty level scope}
    {firstRaw secondRaw : RawTerm scope}
    {firstTerm : Term context firstType firstRaw}
    {secondTerm : Term context secondType secondRaw}
    (typeEq : firstType = secondType)
    (rawEq : firstRaw = secondRaw)
    (heq : HEq firstTerm secondTerm) :
    typeEq ▸ rawEq ▸ firstTerm = secondTerm := by
  subst typeEq
  subst rawEq
  exact eq_of_heq heq

/-- Bidirectional version: HEq is equivalent to cast'd Eq when the
type and raw indices match propositionally. -/
theorem Term.heq_iff_eq_after_cast
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {firstType secondType : Ty level scope}
    {firstRaw secondRaw : RawTerm scope}
    {firstTerm : Term context firstType firstRaw}
    {secondTerm : Term context secondType secondRaw}
    (typeEq : firstType = secondType)
    (rawEq : firstRaw = secondRaw) :
    HEq firstTerm secondTerm ↔ typeEq ▸ rawEq ▸ firstTerm = secondTerm := by
  subst typeEq
  subst rawEq
  exact ⟨eq_of_heq, heq_of_eq⟩

-- `refuteViaToRaw` (HEq surgery via Term.toRaw) is deferred until
-- after `Term.subst_compose` is in place — its proof needs careful
-- HEq motive selection that's better tackled once the broader cascade
-- infrastructure is built.

end LeanFX2
