import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BaseTypeFormationNeutralMembers

/-! # FX1Poly/Typed/BoundedDataMemberExtraction
    — a bounded member of a flat-data type code is a member of that code's `dataTaitCandidate` (DEP-MODEL bridge)

The §5 reducibility model pins each flat data type code (now including `gen_boolCode`, after DEP-MODEL added it
to `Generator.isFlatDataCode` / `flatCodeValuePredicate`) to the head-expansion-closed candidate
`dataTaitCandidate (flatCodeValuePredicate code)` via the `ReducibleTypeStepBounded.dataFlat` arm.  By the
family-level determinism (`ReducibleTypeAtBounded.deterministic`), ANY candidate a bounded member of that code
rides in is pointwise-equivalent to the canonical `dataTaitCandidate`, so the member transfers into it.

This is the extraction the dependent data-eliminator bounded bridges consume: the boolElim bridge's scrutinee
obligation arrives as `IsReducibleMemberAtBounded env bound boolTypeCell σscrutinee`, and the Core member
`boolElimDependentReducibleMember` needs it as `dataTaitCandidate boolIsValue σscrutinee` — exactly this lemma.
Nat / option / either / list extractions land here too as those data codes join `isFlatDataCode`.

## Zero-axiom verification

`ReducibleTypeStepBounded.dataFlat` (the canonical-candidate witness, gates by `rfl`) + `ReducibleTypeAtBounded.\
deterministic` (the model's functional determinism) + the `PointwiseIff.mp` transfer.  `flatCodeValuePredicate
boolTypeCell.rootGenerator` reduces to `boolIsValue` by `rfl` (the if-chain hits the `gen_boolCode` branch), so the
candidate identity is definitional.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or
`omega`.  Per-declaration gated in `FX1PolyAudit/`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Tier0.Syntax

/-- **A bounded member of `boolTypeCell` is a member of `dataTaitCandidate boolIsValue`.**  The bool type code
pins to `dataTaitCandidate (flatCodeValuePredicate gen_boolCode) = dataTaitCandidate boolIsValue` via the
`dataFlat` arm; the member's own candidate is pointwise-equivalent to it by `ReducibleTypeAtBounded.deterministic`,
so the membership transfers.  The scrutinee bridge for the dependent `boolElim` bounded FT engine. -/
theorem boolMemberAtBounded_dataTaitCandidate {scope : Nat} {env : Nat → Nat} {bound : Nat}
    {term : RawTerm scope}
    (member : IsReducibleMemberAtBounded env bound (boolTypeCell (scope := scope)) term) :
    dataTaitCandidate boolIsValue term := by
  obtain ⟨candidate, candidateReducible, termInCandidate⟩ := member
  have canonicalReducible :
      ReducibleTypeAtBounded env bound (boolTypeCell (scope := scope))
        (dataTaitCandidate (flatCodeValuePredicate (boolTypeCell (scope := scope)).rootGenerator)) :=
    ReducibleTypeStepBounded.dataFlat (typeCode := boolTypeCell (scope := scope)) rfl rfl
  have pointwise : PointwiseIff candidate
      (dataTaitCandidate (flatCodeValuePredicate (boolTypeCell (scope := scope)).rootGenerator)) :=
    ReducibleTypeAtBounded.deterministic candidateReducible canonicalReducible
  exact (pointwise term).mp termInCandidate

end FX1Poly.Typed
