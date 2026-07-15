import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BaseTypeFormationNeutralMembers
import FX1Poly.Core.Metatheory.Canonicity.NatStructuredCandidate
import FX1Poly.Core.Metatheory.Canonicity.OptionCanonicalFormsCandidate
import FX1Poly.Core.Metatheory.Canonicity.ListStructuredCandidate
import FX1Poly.Typed.Metatheory.Denote.Bounded.DenoteKeyedBoundedCarrierAwareShape
import FX1Poly.Core.Metatheory.Reducibility.Candidates.CarrierAwareEitherCandidate
import FX1Poly.Core.Metatheory.Reducibility.Candidates.CarrierAwarePairCandidate
import FX1Poly.Core.Metatheory.Reducibility.Candidates.ProjectionPairCandidate
import FX1Poly.Core.Metatheory.Reducibility.Candidates.ReachAwareEitherModelCandidate
import FX1Poly.Core.Metatheory.Reducibility.Candidates.ReachAwareListModelCandidate

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

open FX1Poly.Core FX1Poly.Axis.Syntax

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
    ReducibleTypeStepBounded.dataFlat (typeCode := boolTypeCell (scope := scope)) rfl rfl rfl rfl
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
    ReducibleTypeStepBounded.dataFlat (typeCode := natTypeCell (scope := scope)) rfl rfl rfl rfl
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
   ReducibleTypeStepBounded.dataFlat (typeCode := natTypeCell (scope := scope)) rfl rfl rfl rfl,
   structured⟩

/-- **A bounded member of `optionTypeCell typeParamA` is a member of `dataTaitCandidate isOptionValue`.**  After
gate-1 swap 3 the option type code is unary-carrier-aware (`unaryCarrierCombinator? = some optionLike`), so its
bound-reducibility comes through the `dataUnaryCarrierAware` arm carrying the reach-aware option model candidate
`reachAwareOptionCandidate elementCandidate` — NOT the content-free `dataFlat` lane (whose 4th gate
`notUnaryCarrierAware` now excludes option).  The scrutinee's bound-reducible `option(A)` membership is inverted
(`ReducibleTypeAtBounded.unaryCarrierAwareTypeInversion`) to recover that reach-aware candidate, whose weak
`carrierAwareOptionCandidate` conjunct then FORGETS down to `dataTaitCandidate isOptionValue` via
`reachAwareOptionCandidate_toWeakOptionCandidate` — the scrutinee bridge the dependent `optionMatch` bounded FT
engine consumes, exactly as before the swap. -/
theorem optionMemberAtBounded_dataTaitCandidate {scope : Nat} {env : Nat → Nat} {bound : Nat}
    {typeParamA term : RawTerm scope}
    (member : IsReducibleMemberAtBounded env bound (optionTypeCell typeParamA) term) :
    dataTaitCandidate isOptionValue term := by
  obtain ⟨candidate, candidateReducible, termInCandidate⟩ := member
  obtain ⟨_elementCandidate, _elementReducible, pointwise⟩ :=
    ReducibleTypeAtBounded.unaryCarrierAwareTypeInversion
      (combinator := UnaryCarrierCombinator.optionLike) (elementCode := typeParamA) candidateReducible
  exact reachAwareOptionCandidate_toWeakOptionCandidate ((pointwise term).mp termInCandidate)

/-- **A bounded member of `optionTypeCell elementCode` is a member of the reach-aware option candidate over a
reducible element candidate.**  The UNARY twin of `eitherMemberAtBounded_carrierAware`: post gate-1 swap 3 the
option type code pins to `dataUnaryCarrierAware @ optionLike`, whose candidate is `reachAwareOptionCandidate
elementCandidate`; the member's own candidate is pointwise-equivalent to it by `unaryCarrierAwareTypeInversion`, so
the membership transfers, carrying the element candidate's reducibility AND the forward-closed some-reach clause.
This is the extraction the dependent `optionMatch` some-branch discharge consumes — the reach clause supplies the
reached payload's element membership, dissolving the former threaded `someBranchMemberIfReachesSome` residue. -/
theorem optionMemberAtBounded_carrierAware {scope : Nat} {env : Nat → Nat} {bound : Nat}
    {elementCode term : RawTerm scope}
    (member : IsReducibleMemberAtBounded env bound (optionTypeCell elementCode) term) :
    ∃ elementCandidate : RawTerm scope → Prop,
      ReducibleTypeAtBounded env bound elementCode elementCandidate ∧
      reachAwareOptionCandidate elementCandidate term := by
  obtain ⟨candidate, candidateReducible, termInCandidate⟩ := member
  obtain ⟨elementCandidate, elementReducible, pointwiseIff⟩ :=
    ReducibleTypeAtBounded.unaryCarrierAwareTypeInversion
      (combinator := UnaryCarrierCombinator.optionLike) (elementCode := elementCode) candidateReducible
  exact ⟨elementCandidate, elementReducible, (pointwiseIff term).mp termInCandidate⟩

/-- **A bounded member of `listTypeCell elementType` is a member of `dataTaitCandidate IsListStructured`.**  After
gate-1 swap 4 the list type code is unary-carrier-aware (`unaryCarrierCombinator? = some listLike`), so its
bound-reducibility comes through the `dataUnaryCarrierAware` arm carrying the RECURSIVE reach-aware list model
candidate `reachAwareListCandidate elementCandidate` — NOT the content-free `dataFlat` lane (whose 4th gate
`notUnaryCarrierAware` now excludes list, just as it excludes option).  The scrutinee's bound-reducible `list(A)`
membership is inverted (`ReducibleTypeAtBounded.unaryCarrierAwareTypeInversion`) to recover that reach-aware
candidate, whose carrier-aware conjunct then FORGETS down to `dataTaitCandidate IsListStructured` via
`reachAwareListCandidate_toWeakListCandidate` — the recursive tail bridge for the `listCons` intro FT row and the
scrutinee bridge for the dependent `listElim` bounded FT engine, exactly as before the swap. -/
theorem listMemberAtBounded_dataTaitCandidate {scope : Nat} {env : Nat → Nat} {bound : Nat}
    {elementType term : RawTerm scope}
    (member : IsReducibleMemberAtBounded env bound (listTypeCell elementType) term) :
    dataTaitCandidate IsListStructured term := by
  obtain ⟨candidate, candidateReducible, termInCandidate⟩ := member
  obtain ⟨_elementCandidate, _elementReducible, pointwise⟩ :=
    ReducibleTypeAtBounded.unaryCarrierAwareTypeInversion
      (combinator := UnaryCarrierCombinator.listLike) (elementCode := elementType) candidateReducible
  exact reachAwareListCandidate_toWeakListCandidate ((pointwise term).mp termInCandidate)

/-- **A bounded member of `listTypeCell elementCode` is a member of the reach-aware list candidate over a reducible
element candidate.**  The RECURSIVE twin of `optionMemberAtBounded_carrierAware`: post gate-1 swap 4 the list type
code pins to `dataUnaryCarrierAware @ listLike`, whose candidate is `reachAwareListCandidate elementCandidate`; the
member's own candidate is pointwise-equivalent to it by `unaryCarrierAwareTypeInversion`, so the membership
transfers, carrying the element candidate's reducibility AND the forward-closed reach clauses (every reached
`cons head tail` records `head ∈ elementCandidate` and the tail's RECURSIVE reach-aware membership).  This is the
extraction the dependent `listElim` bounded FT bridge consumes — the reach clauses supply each reached cons's head
and tail membership, dissolving the former `listMemberAtBounded_ofDataTaitCandidate` reconstruction. -/
theorem listMemberAtBounded_carrierAware {scope : Nat} {env : Nat → Nat} {bound : Nat}
    {elementCode term : RawTerm scope}
    (member : IsReducibleMemberAtBounded env bound (listTypeCell elementCode) term) :
    ∃ elementCandidate : RawTerm scope → Prop,
      ReducibleTypeAtBounded env bound elementCode elementCandidate ∧
      reachAwareListCandidate elementCandidate term := by
  obtain ⟨candidate, candidateReducible, termInCandidate⟩ := member
  obtain ⟨elementCandidate, elementReducible, pointwiseIff⟩ :=
    ReducibleTypeAtBounded.unaryCarrierAwareTypeInversion
      (combinator := UnaryCarrierCombinator.listLike) (elementCode := elementCode) candidateReducible
  exact ⟨elementCandidate, elementReducible, (pointwiseIff term).mp termInCandidate⟩

/-- **A reach-aware list value over a reducible element candidate is a bounded member of `listTypeCell elementCode`.**
The reverse of `listMemberAtBounded_carrierAware` (replacing the pre-swap content-free `listMemberAtBounded_\
ofDataTaitCandidate`): since `listTypeCell elementCode` pins to `dataUnaryCarrierAware @ listLike`, whose candidate is
`reachAwareListCandidate elementCandidate`, a reach-aware list value at that element candidate inhabits the canonical
candidate directly — the type-reducibility is one `ReducibleTypeStepBounded.dataUnaryCarrierAware` over the element
candidate's reducibility, and the reach-aware witness IS the candidate membership.  The value-indexed
`resultTypeReducibleAtValue` discharge in the dependent `listElim` bounded FT bridge consumes exactly this — turning
a reached structured recursion-value (carrying its element membership) back into a `listTypeCell` member to feed the
motive's universe membership.  Unlike the pre-swap reverse, this REQUIRES the element candidate (a bare structured
value no longer suffices), exactly as the carrier-aware model demands. -/
theorem listMemberAtBounded_ofReachAware {scope : Nat} {env : Nat → Nat} {bound : Nat}
    {elementCode term : RawTerm scope} {elementCandidate : RawTerm scope → Prop}
    (elementReducible : ReducibleTypeAtBounded env bound elementCode elementCandidate)
    (reachAware : reachAwareListCandidate elementCandidate term) :
    IsReducibleMemberAtBounded env bound (listTypeCell elementCode) term :=
  ⟨reachAwareListCandidate elementCandidate,
   ReducibleTypeStepBounded.dataUnaryCarrierAware (combinator := UnaryCarrierCombinator.listLike) elementReducible,
   reachAware⟩

/-- **A bounded member of `idTypeCell typeCode left right` is a member of the two-endpoint based candidate
`dataTaitCandidate (isReflValueBetween left right)`.**  The identity type code pins to
`dataTaitCandidate (termIndexedCodeValuePredicate gen_idCode left right) = dataTaitCandidate (isReflValueBetween
left right)` via the `dataTermIndexed` arm (DEP-ID — `gen_idCode` is `isTermIndexedCode`, carved out of the
content-free `dataFlat` codes by `notTermIndexed`, so its reducibility candidate reads BOTH endpoints off the
arity-3 `[type, left, right]` cell rather than the endpoint-blind unary `isReflValue`); the member's own candidate
is pointwise-equivalent to it by `ReducibleTypeAtBounded.deterministic`, so the membership transfers.  The witness
bridge for the dependent `idJ` bounded FT engine — it consumes its reflexive-identity witness as
`dataTaitCandidate (isReflValueBetween left right)`, the based content path induction needs. -/
theorem idMemberAtBounded_dataTaitCandidate {scope : Nat} {env : Nat → Nat} {bound : Nat}
    {typeCode left right term : RawTerm scope}
    (member : IsReducibleMemberAtBounded env bound (idTypeCell typeCode left right) term) :
    dataTaitCandidate (termIndexedCodeValuePredicate .gen_idCode left right) term := by
  obtain ⟨candidate, candidateReducible, termInCandidate⟩ := member
  have canonicalReducible :
      ReducibleTypeAtBounded env bound (idTypeCell typeCode left right)
        (dataTaitCandidate (termIndexedCodeValuePredicate .gen_idCode left right)) :=
    ReducibleTypeStepBounded.dataTermIndexed
  have pointwise : PointwiseIff candidate
      (dataTaitCandidate (termIndexedCodeValuePredicate .gen_idCode left right)) :=
    ReducibleTypeAtBounded.deterministic candidateReducible canonicalReducible
  exact (pointwise term).mp termInCandidate

/-- **A based `dataTaitCandidate (isReflValueBetween left right)` value is a bounded member of
`idTypeCell typeCode left right`.**  The reverse of `idMemberAtBounded_dataTaitCandidate`: since `idTypeCell typeCode
left right` pins to the term-indexed candidate `dataTaitCandidate (termIndexedCodeValuePredicate gen_idCode left
right) = dataTaitCandidate (isReflValueBetween left right)` (DEP-ID, the `dataTermIndexed` arm reading the endpoints
off the arity-3 `[type, left, right]` cell), a based-refl value — a `refl` whose reflected point is convertible to
BOTH endpoints — inhabits the canonical candidate at exactly that reflexive identity.  The `list` / `nat` twins
(`*_ofDataTaitCandidate`); the dependent `idJ` bounded FT bridge consumes this where the J motive's result type must
be shown reducible at the based reflexive witness. -/
theorem idMemberAtBounded_ofDataTaitCandidate {scope : Nat} {env : Nat → Nat} {bound : Nat}
    {typeCode left right term : RawTerm scope}
    (structured : dataTaitCandidate (termIndexedCodeValuePredicate .gen_idCode left right) term) :
    IsReducibleMemberAtBounded env bound (idTypeCell typeCode left right) term :=
  ⟨dataTaitCandidate (termIndexedCodeValuePredicate .gen_idCode left right),
   ReducibleTypeStepBounded.dataTermIndexed,
   structured⟩

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
  have carrierMember : reachAwareEitherCandidate firstCandidate secondCandidate term :=
    (pointwiseIff term).mp termInCandidate
  exact reachAwareEitherCandidate_toWeakEitherCandidate carrierMember

/-- **A bounded member of `eitherTypeCell firstCode secondCode` rides in the REACH-AWARE coproduct candidate,
with both component candidates recovered as bound-reducible.**  The carrier-keeping refinement of
`eitherMemberAtBounded_dataTaitCandidate`: rather than forgetting the reach content via
`reachAwareEitherCandidate_toWeakEitherCandidate`, this exposes the full output of the carrier-aware inversion
`ReducibleTypeAtBounded.carrierAwareTypeInversion` at `coproductLike` — the two component candidates, each a
bound-reducible type at its component code, and the scrutinee's membership in
`reachAwareEitherCandidate firstCandidate secondCandidate` (the candidate stored at `coproductLike` after the
swap).  This is the substrate the dependent `eitherMatch` elim-FT row's reach-conditioned branch residues
(`leftBranchMemberIfReachesInl` / `rightBranchMemberIfReachesInr`) discharge against: a reached
`inl` / `inr payload` yields the payload's carrier membership at the LITERAL reached payload via the reach-aware
member's forward-closed clause (`reachAwareEitherCandidate.reachableInlMember` / `...InrMember`), the Ω-fork-free
reach projection, and the component reducibilities pin the recovered carrier candidates to the branch motive's
result type. -/
theorem eitherMemberAtBounded_carrierAware {scope : Nat} {env : Nat → Nat} {bound : Nat}
    {firstCode secondCode term : RawTerm scope}
    (member : IsReducibleMemberAtBounded env bound (eitherTypeCell firstCode secondCode) term) :
    ∃ firstCandidate secondCandidate : RawTerm scope → Prop,
      ReducibleTypeAtBounded env bound firstCode firstCandidate ∧
      ReducibleTypeAtBounded env bound secondCode secondCandidate ∧
      reachAwareEitherCandidate firstCandidate secondCandidate term := by
  obtain ⟨candidate, candidateReducible, termInCandidate⟩ := member
  obtain ⟨firstCandidate, secondCandidate, firstReducible, secondReducible, pointwiseIff⟩ :=
    ReducibleTypeAtBounded.carrierAwareTypeInversion (combinator := CarrierCombinator.coproductLike)
      (firstCode := firstCode) (secondCode := secondCode) candidateReducible
  exact ⟨firstCandidate, secondCandidate, firstReducible, secondReducible,
    (pointwiseIff term).mp termInCandidate⟩

/-- **A bounded member of `productTypeCell firstCode secondCode` rides in the CARRIER-AWARE product candidate,
with both component candidates recovered as bound-reducible.**  The carrier-keeping refinement of
`productMemberAtBounded_dataTaitCandidate`: rather than forgetting the carrier content via
`carrierAwarePairCandidate_toWeakPairCandidate`, this exposes the full output of the carrier-aware inversion
`ReducibleTypeAtBounded.carrierAwareTypeInversion` at `pairLike` — the two component candidates, each a
bound-reducible type at its component code, and the scrutinee's membership in
`carrierAwarePairCandidate firstCandidate secondCandidate`.  This is the substrate the dependent `fst` / `snd`
elim-FT rows' reach-conditioned component residues (`firstMemberIfReachesPair` / `secondMemberIfReachesPair`) must
discharge against: the carrier-aware member records each NORMAL-form component's carrier membership, and the
recovered `firstReducible` / `secondReducible` pin the carrier candidates to the projection's result type.  (The
full open-level residue discharge additionally requires the carrier-aware candidate to record component membership
at every reachable — not merely normal — pair, the standard Girard `Σ`-candidate strengthening tracked separately;
this extractor supplies the inversion half route-agnostically, consumed by both the open strengthening and the
closed-canonical-forms consistency leg.)  The Σ-projection twin of `eitherMemberAtBounded_carrierAware`. -/
theorem productMemberAtBounded_carrierAware {scope : Nat} {env : Nat → Nat} {bound : Nat}
    {firstCode secondCode term : RawTerm scope}
    (member : IsReducibleMemberAtBounded env bound (productTypeCell firstCode secondCode) term) :
    ∃ firstCandidate secondCandidate : RawTerm scope → Prop,
      ReducibleTypeAtBounded env bound firstCode firstCandidate ∧
      ReducibleTypeAtBounded env bound secondCode secondCandidate ∧
      projectionPairCandidate firstCandidate secondCandidate term := by
  obtain ⟨candidate, candidateReducible, termInCandidate⟩ := member
  obtain ⟨firstCandidate, secondCandidate, firstReducible, secondReducible, pointwiseIff⟩ :=
    ReducibleTypeAtBounded.carrierAwareTypeInversion (combinator := CarrierCombinator.pairLike)
      (firstCode := firstCode) (secondCode := secondCode) candidateReducible
  exact ⟨firstCandidate, secondCandidate, firstReducible, secondReducible,
    (pointwiseIff term).mp termInCandidate⟩

end FX1Poly.Typed
