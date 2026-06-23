import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BaseTypeFormationNeutralMembers
import FX1Poly.Core.Metatheory.Canonicity.NatStructuredCandidate
import FX1Poly.Core.Metatheory.Canonicity.OptionCanonicalFormsCandidate
import FX1Poly.Core.Metatheory.Canonicity.ListStructuredCandidate
import FX1Poly.Typed.Metatheory.Denote.Bounded.DenoteKeyedBoundedCarrierAwareShape
import FX1Poly.Core.Metatheory.Reducibility.Candidates.CarrierAwareEitherCandidate
import FX1Poly.Core.Metatheory.Reducibility.Candidates.CarrierAwarePairCandidate

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

/-- **A bounded member of `natTypeCell` is a member of `dataTaitCandidate IsNatStructured`.**  The nat type code
pins to `dataTaitCandidate (flatCodeValuePredicate gen_natCode) = dataTaitCandidate IsNatStructured` via the
`dataFlat` arm (DEP-NAT-MODEL — nat joined `isFlatDataCode` carrying the RECURSIVE structured-numeral predicate);
the member's own candidate is pointwise-equivalent to it by `ReducibleTypeAtBounded.deterministic`, so the
membership transfers.  The scrutinee bridge for the dependent recursive `natElim` / `natRec` bounded FT engine —
`natElimDependentReducibleMember` consumes its scrutinee as `dataTaitCandidate IsNatStructured`, exactly this. -/
theorem natMemberAtBounded_dataTaitCandidate {scope : Nat} {env : Nat → Nat} {bound : Nat}
    {term : RawTerm scope}
    (member : IsReducibleMemberAtBounded env bound (natTypeCell (scope := scope)) term) :
    dataTaitCandidate IsNatStructured term := by
  obtain ⟨candidate, candidateReducible, termInCandidate⟩ := member
  have canonicalReducible :
      ReducibleTypeAtBounded env bound (natTypeCell (scope := scope))
        (dataTaitCandidate (flatCodeValuePredicate (natTypeCell (scope := scope)).rootGenerator)) :=
    ReducibleTypeStepBounded.dataFlat (typeCode := natTypeCell (scope := scope)) rfl rfl
  have pointwise : PointwiseIff candidate
      (dataTaitCandidate (flatCodeValuePredicate (natTypeCell (scope := scope)).rootGenerator)) :=
    ReducibleTypeAtBounded.deterministic candidateReducible canonicalReducible
  exact (pointwise term).mp termInCandidate

/-- **The REVERSE of `natMemberAtBounded_dataTaitCandidate`: a member of `dataTaitCandidate IsNatStructured` is a
bounded member of `natTypeCell`.**  The dependent recursive `natElim` / `natRec` FT bridge needs this direction
to feed the predecessor and each scrutinee VALUE back into the motive-side result-type recovery
(`dependentMotiveResultTypeReducibleAtBoundedValue`) and into the two-binder fill environment
(`ReducibleEnvAtBounded.cons`), whose binding types are `natTypeCell`.  The `dataFlat` pin makes the canonical nat
candidate `dataTaitCandidate (flatCodeValuePredicate gen_natCode)` definitionally `dataTaitCandidate IsNatStructured`,
so the structured membership IS the member's candidate witness directly — the bounded member is the canonical triple.
Zero-axiom (`ReducibleTypeStepBounded.dataFlat rfl rfl` + the defeq candidate). -/
theorem natMemberAtBounded_ofDataTaitCandidate {scope : Nat} {env : Nat → Nat} {bound : Nat}
    {term : RawTerm scope} (structured : dataTaitCandidate IsNatStructured term) :
    IsReducibleMemberAtBounded env bound (natTypeCell (scope := scope)) term :=
  ⟨dataTaitCandidate (flatCodeValuePredicate (natTypeCell (scope := scope)).rootGenerator),
   ReducibleTypeStepBounded.dataFlat (typeCode := natTypeCell (scope := scope)) rfl rfl,
   structured⟩

/-- **A bounded member of `optionTypeCell typeParamA` is a member of `dataTaitCandidate isOptionValue`.**  The
option type code pins to `dataTaitCandidate (flatCodeValuePredicate gen_optionCode) = dataTaitCandidate isOptionValue`
via the `dataFlat` arm (DEP-OPTION-MODEL — option joined `isFlatDataCode` as a CONTENT-FREE flat code,
`carrierCombinator? = none`, so unlike sum/product it pins to the content-free `dataFlat` candidate DIRECTLY, the
`bool` / `nat` route — not the carrier-aware inversion `either` needs); the member's own candidate is
pointwise-equivalent to it by `ReducibleTypeAtBounded.deterministic`, so the membership transfers.  The scrutinee
bridge for the dependent `optionMatch` bounded FT engine — `optionMatchDependentReducibleMember` consumes its
scrutinee as `dataTaitCandidate isOptionValue`, exactly this. -/
theorem optionMemberAtBounded_dataTaitCandidate {scope : Nat} {env : Nat → Nat} {bound : Nat}
    {typeParamA term : RawTerm scope}
    (member : IsReducibleMemberAtBounded env bound (optionTypeCell typeParamA) term) :
    dataTaitCandidate isOptionValue term := by
  obtain ⟨candidate, candidateReducible, termInCandidate⟩ := member
  have canonicalReducible :
      ReducibleTypeAtBounded env bound (optionTypeCell typeParamA)
        (dataTaitCandidate (flatCodeValuePredicate (optionTypeCell typeParamA).rootGenerator)) :=
    ReducibleTypeStepBounded.dataFlat (typeCode := optionTypeCell typeParamA) rfl rfl
  have pointwise : PointwiseIff candidate
      (dataTaitCandidate (flatCodeValuePredicate (optionTypeCell typeParamA).rootGenerator)) :=
    ReducibleTypeAtBounded.deterministic candidateReducible canonicalReducible
  exact (pointwise term).mp termInCandidate

/-- **A bounded member of `listTypeCell elementType` is a member of `dataTaitCandidate IsListStructured`.**  The
list type code pins to `dataTaitCandidate (flatCodeValuePredicate gen_listCode) = dataTaitCandidate IsListStructured`
via the `dataFlat` arm (DEP-LIST-MODEL — list joined `isFlatDataCode` as a CONTENT-FREE flat code
(`carrierCombinator? = none`) carrying the RECURSIVE structured-spine predicate `IsListStructured`, the `nat`
route — not the carrier-aware inversion `either`/`product` need); the member's own candidate is
pointwise-equivalent to it by `ReducibleTypeAtBounded.deterministic`, so the membership transfers.  The recursive
tail bridge for the `listCons` intro FT row and the scrutinee bridge for the dependent `listElim` bounded FT
engine — both consume the list as `dataTaitCandidate IsListStructured`, exactly this. -/
theorem listMemberAtBounded_dataTaitCandidate {scope : Nat} {env : Nat → Nat} {bound : Nat}
    {elementType term : RawTerm scope}
    (member : IsReducibleMemberAtBounded env bound (listTypeCell elementType) term) :
    dataTaitCandidate IsListStructured term := by
  obtain ⟨candidate, candidateReducible, termInCandidate⟩ := member
  have canonicalReducible :
      ReducibleTypeAtBounded env bound (listTypeCell elementType)
        (dataTaitCandidate (flatCodeValuePredicate (listTypeCell elementType).rootGenerator)) :=
    ReducibleTypeStepBounded.dataFlat (typeCode := listTypeCell elementType) rfl rfl
  have pointwise : PointwiseIff candidate
      (dataTaitCandidate (flatCodeValuePredicate (listTypeCell elementType).rootGenerator)) :=
    ReducibleTypeAtBounded.deterministic candidateReducible canonicalReducible
  exact (pointwise term).mp termInCandidate

/-- **A bounded member of `eitherTypeCell firstCode secondCode` is a member of the content-free
`dataTaitCandidate isEitherValue`.**  Unlike `bool` / `nat` — whose type codes pin to the content-free `dataFlat`
candidate directly — the sum code `gen_eitherCode` is `CarrierCombinator`-tagged, so the `dataFlat` arm is EXCLUDED
(by `notCarrierAware`) and `eitherTypeCell A B`'s canonical candidate comes from the `dataFlatCarrierAware` arm as
the carrier-aware `carrierAwareEitherCandidate candA candB`.  This extraction therefore routes through the
carrier-aware inversion `ReducibleTypeAtBounded.carrierAwareTypeInversion` (recovering the component candidates and
the `assemble`-form `PointwiseIff`) and then FORGETS the carrier content via
`carrierAwareEitherCandidate_toWeakEitherCandidate`.  The scrutinee bridge for the dependent `eitherMatch` bounded FT
engine: `eitherMatchDependentReducibleMember` consumes its scrutinee as `dataTaitCandidate isEitherValue`, exactly
this.  (`fst`/`snd` over `productTypeCell` and the eventual `equiv` reuse the same carrier-aware route at their
combinator.) -/
theorem eitherMemberAtBounded_dataTaitCandidate {scope : Nat} {env : Nat → Nat} {bound : Nat}
    {firstCode secondCode term : RawTerm scope}
    (member : IsReducibleMemberAtBounded env bound (eitherTypeCell firstCode secondCode) term) :
    dataTaitCandidate isEitherValue term := by
  obtain ⟨candidate, candidateReducible, termInCandidate⟩ := member
  obtain ⟨firstCandidate, secondCandidate, _firstReducible, _secondReducible, pointwiseIff⟩ :=
    ReducibleTypeAtBounded.carrierAwareTypeInversion (combinator := CarrierCombinator.coproductLike)
      (firstCode := firstCode) (secondCode := secondCode) candidateReducible
  have carrierMember : carrierAwareEitherCandidate firstCandidate secondCandidate term :=
    (pointwiseIff term).mp termInCandidate
  exact carrierAwareEitherCandidate_toWeakEitherCandidate carrierMember

/-- **A bounded member of `productTypeCell firstCode secondCode` is a member of the content-free
`dataTaitCandidate isPairValue`.**  Like `either` (and unlike `bool`/`nat`/`option`), the Σ product code
`gen_productCode` is `CarrierCombinator`-tagged (`pairLike`), so the `dataFlat` arm is EXCLUDED and the
canonical candidate comes from the `dataFlatCarrierAware` arm as `carrierAwarePairCandidate candFirst candSecond`.
This extraction therefore routes through the carrier-aware inversion `ReducibleTypeAtBounded.carrierAwareType\
Inversion` at `pairLike` (recovering the component candidates and the `assemble`-form `PointwiseIff`) and then
FORGETS the carrier content via `carrierAwarePairCandidate_toWeakPairCandidate`.  The scrutinee bridge for the
dependent `fst` / `snd` bounded FT engines: `fst`/`sndDependentReducibleMember` consume their scrutinee as
`dataTaitCandidate isPairValue`, exactly this.  The Σ-projection twin of `eitherMemberAtBounded_dataTaitCandidate`. -/
theorem productMemberAtBounded_dataTaitCandidate {scope : Nat} {env : Nat → Nat} {bound : Nat}
    {firstCode secondCode term : RawTerm scope}
    (member : IsReducibleMemberAtBounded env bound (productTypeCell firstCode secondCode) term) :
    dataTaitCandidate isPairValue term := by
  obtain ⟨candidate, candidateReducible, termInCandidate⟩ := member
  obtain ⟨firstCandidate, secondCandidate, _firstReducible, _secondReducible, pointwiseIff⟩ :=
    ReducibleTypeAtBounded.carrierAwareTypeInversion (combinator := CarrierCombinator.pairLike)
      (firstCode := firstCode) (secondCode := secondCode) candidateReducible
  have carrierMember : carrierAwarePairCandidate firstCandidate secondCandidate term :=
    (pointwiseIff term).mp termInCandidate
  exact carrierAwarePairCandidate_toWeakPairCandidate carrierMember

end FX1Poly.Typed
