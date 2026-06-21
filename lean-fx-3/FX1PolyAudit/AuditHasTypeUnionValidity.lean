import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.Validity.HasTypeUnionValidity

/-! # FX1PolyAudit/AuditHasTypeUnionValidity — union classifier-validity zero-axiom gate

Per-declaration zero-axiom gate for `FX1Poly/Typed/Metatheory/Validity/HasTypeUnionValidity.lean`: the
union classifier-validity conclusion (`UnionClassifierIsType` + its constructors), the formation-output
helper, the two honest residual oracles (`UnionDataFormerValidity` / `UnionElimOutputValidity`), and the
main theorem `HasTypeUnion.classifierIsType`.  Every declaration below must be free of `propext`,
`Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The conclusion predicate + its constructors.
#assert_no_axioms FX1Poly.Typed.UnionClassifierIsType
#assert_no_axioms FX1Poly.Typed.UnionClassifierIsType.ofUniverseCode
#assert_no_axioms FX1Poly.Typed.UnionClassifierIsType.ofBaseTypeRow
#assert_no_axioms FX1Poly.Typed.UnionClassifierIsType.ofFormationOutput

-- ★ TYTAB-2 wave U3: the single-child cumulative data-former validity, now DISCHARGED unconditionally.
#assert_no_axioms FX1Poly.Typed.UnionClassifierIsType.optionFormed_ofValidity
#assert_no_axioms FX1Poly.Typed.UnionClassifierIsType.listFormed_ofValidity

-- ★ TYTAB-2 wave W3: the two-child SAME-FLAG cumulative / term-indexed data-former validity, DISCHARGED
-- unconditionally (the `lam` / `refl` intro rows supply both type-parameter premises at a common flag).
#assert_no_axioms FX1Poly.Typed.UnionClassifierIsType.piFormed_atCommonFlag
#assert_no_axioms FX1Poly.Typed.UnionClassifierIsType.idFormed_ofCarrier

-- ★ TYTAB-2 wave W5: the two-child FLAT data-former validity at a COMMON flag (the flag-coherence frontier
-- dissolved by the construction-side intro-rule refinement of pair / eitherInl / eitherInr).
#assert_no_axioms FX1Poly.Typed.UnionClassifierIsType.productFormed_atCommonFlag
#assert_no_axioms FX1Poly.Typed.UnionClassifierIsType.eitherFormed_atCommonFlag

-- ★ TYTAB-2 wave W3/W4: the type-code-head formation inversions (TOTAL after the kernel-wide free-`levels`
-- fix) + the elim-output discharges they feed.
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.invertAtBridgeCodeHeadCarrier
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.invertAtProductCodeHeadComponents
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.invertAtEitherCodeHeadComponents
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.invertAtPiCodeHeadCodomain
#assert_no_axioms FX1Poly.Typed.UnionClassifierIsType.pathAppOutputFormed_ofValidity
#assert_no_axioms FX1Poly.Typed.UnionClassifierIsType.fstOutputFormed_ofValidity
#assert_no_axioms FX1Poly.Typed.UnionClassifierIsType.sndOutputFormed_ofValidity
#assert_no_axioms FX1Poly.Typed.UnionClassifierIsType.eitherComponents_ofValidity
#assert_no_axioms FX1Poly.Typed.UnionClassifierIsType.appOutputFormed_ofValidityAndArg

-- ★ TYTAB-2 wave W4: the bridge code DISCHARGED (interval-endpoint substitution + the now-total bridge
-- reformation), plus the UNION well-formedness `WfContextUnion` (admits native bindings the host wf rejects)
-- and its API, and the host-subject classifier validity over it (the `ofGrown` arm engine).
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.intervalZeroTyped
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.intervalOneTyped
#assert_no_axioms FX1Poly.Typed.UnionClassifierIsType.bridgeFormed_ofBodyValidity
#assert_no_axioms FX1Poly.Typed.UnionClassifierIsType.bridgeFormed_ofBodyPremise
#assert_no_axioms FX1Poly.Typed.WfContextUnion
#assert_no_axioms FX1Poly.Typed.WfContextUnion.cons
#assert_no_axioms FX1Poly.Typed.WfContextUnion.tailWellFormed
#assert_no_axioms FX1Poly.Typed.WfContextUnion.headIsType
#assert_no_axioms FX1Poly.Typed.UnionClassifierIsType.weakenUnderBinding
#assert_no_axioms FX1Poly.Typed.WfContextUnion.lookupIsType
#assert_no_axioms FX1Poly.Typed.UnionClassifierIsType.ofIsTypeDescPi
#assert_no_axioms FX1Poly.Typed.WfContextUnion.ofDescPi
#assert_no_axioms FX1Poly.Typed.hostSubjectClassifierIsUnionType
#assert_no_axioms FX1Poly.Typed.formationSubjectClassifierIsUnionType

-- The residual oracles.  `UnionDataFormerValidity` (full) is retained; the SHRUNK `UnionDataFormerResidual`
-- (2 fields: either + product — the flag-coherence frontier) is what `classifierIsType` now takes, alongside
-- the SHRUNK `UnionElimOutputValidity` (1 field: eitherMatch — the handler-inhabitant gap).
#assert_no_axioms FX1Poly.Typed.UnionDataFormerValidity
#assert_no_axioms FX1Poly.Typed.UnionDataFormerResidual
#assert_no_axioms FX1Poly.Typed.UnionDataFormerResidual.ofFull
#assert_no_axioms FX1Poly.Typed.UnionElimOutputValidity

-- ★ The main theorem: union classifier validity (now on the shrunk residual).
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.classifierIsType

end FX1PolyAudit
