import FX1Poly.Core.SconingWitness
import FX1Poly.Core.EmptyCanonicalFormsCandidate

/-! # FX1Poly/Core/ConsistencyViaSconing
    — consistency via the sconing leg: no closed well-typed proof of the empty type

`DataCanonicityViaSconing.lean` / `DataMetatheoryViaSconing.lean` carry the sconing leg's NORMALIZATION
and CANONICITY for the data types that HAVE value constructors.  CONSISTENCY is the same construction at
the OPPOSITE extreme — the empty type, whose value predicate is identically `False` (`emptyIsValue`): it
has no constructors, so its candidate `CanonicalFormsPredicate emptyIsValue` has no closed members at all
(`emptyHasNoClosedMember`: a closed member would reduce to a value, but an empty value is a proof of
`False`).  Feeding that through the BKS sconing machinery with the DEGENERATE canonical-form notion
`fun _ => False` yields consistency: every closed well-typed term of the empty type is absurd.

This completes the sconing-leg metatheory TRIAD at the logical-predicate level — normalization (CR1),
canonicity (`closedReducesToValue`), and consistency (`emptyHasNoClosedMember`) — each derived from
the SAME fundamental obligation, the BKS "sconing is enough" thesis (the consistency corner).

* `consistencyScone` — the sconing witness for consistency.  `computable` is the empty candidate; the
  canonical-form notion is `fun _ => False` (the empty type has NO canonical forms); EXTRACTION is the
  fundamental-free `emptyHasNoClosedMember`; `fundamental` (closed well-typed empty term ⟹ candidate member —
  the fundamental theorem) is the explicit sole obligation.
* `consistencyViaSconing` — `SconingWitness.canonicity` applied: given the fundamental, every closed
  well-typed term of the empty type yields `False`.  This is consistency via Path C —
  structurally identical to the canonicity derivation, since consistency IS canonicity at the empty type.

## Honest scope

FUNDAMENTAL-FREE EXTRACTION.  The `fundamental` obligation (closed well-typed empty term ⟹ empty-candidate
member) is the typed reducibility fundamental theorem, and is an explicit
hypothesis here — not discharged.  This mirrors the canonicity files exactly.

## Zero-axiom verification

A record literal over `SconingWitness` whose `extraction` field is the shipped fundamental-free
`emptyHasNoClosedMember`, plus `SconingWitness.canonicity` (composition).  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation

/-- **The consistency sconing witness (Path C), fundamental-free EXTRACTION.**  The empty type's reducibility
candidate `CanonicalFormsPredicate emptyIsValue` is the displayed computability predicate; the
canonical-form notion is the DEGENERATE `fun _ => False` (the empty type has no canonical forms); its
EXTRACTION obligation is discharged fundamental-free by `emptyHasNoClosedMember` (no closed term inhabits the
empty candidate, because a closed member would reduce to a value and an empty value is a proof of
`False`).  The FUNDAMENTAL obligation (closed well-typed empty term ⟹ candidate member) is the explicit
parameter — the typed reducibility fundamental theorem. -/
def consistencyScone {isWellTyped : RawTerm 0 → Prop}
    (fundamental : ∀ term : RawTerm 0,
      isWellTyped term → CanonicalFormsPredicate emptyIsValue term) :
    SconingWitness isWellTyped (fun _term : RawTerm 0 => False) :=
  { computable := CanonicalFormsPredicate emptyIsValue
    fundamental := fundamental
    extraction := fun _term member => emptyHasNoClosedMember member }

/-- **Consistency via the sconing leg: no closed well-typed proof of the empty type.**
`SconingWitness.canonicity` on `consistencyScone`: given the fundamental obligation (closed well-typed
empty term ⟹ empty-candidate member), every closed well-typed term of the empty type yields `False`.
This is the consistency corner of the BKS "sconing is enough" thesis — structurally the canonicity
derivation specialized to the empty type, where canonicity ("reduces to a constructor") degenerates to
absurdity (there are no constructors).  Completes the sconing-leg triad: normalization + canonicity +
consistency, all from one fundamental.  The extraction half is fundamental-free. -/
theorem consistencyViaSconing {isWellTyped : RawTerm 0 → Prop}
    (fundamental : ∀ term : RawTerm 0,
      isWellTyped term → CanonicalFormsPredicate emptyIsValue term)
    (term : RawTerm 0) (typed : isWellTyped term) : False :=
  (consistencyScone fundamental).canonicity term typed

end FX1Poly.Core
