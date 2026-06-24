import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionEmptyTypeCongruenceCloser
import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionFlatFormationCongruence
import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionTermIndexedFormationCongruence

/-! # FX1PolyAudit/AuditUnionEmptyTypeCongruenceCloser — TYTAB-2-FT gate-2 empty-type congruence-closer audit

Per-declaration zero-axiom gate for the empty-type congruence closer reduced to the eliminator arm (gate-2
congruence half of TYTAB-2-FT, #1697): the bridge head-stability `headReaches_bridgeTypeCell`, the
eliminator-arm gate interface `UnionElimCongruenceClosesToEmptyType`, the generic context-threaded core
`congruenceClosesToEmptyTypeAux`, and the empty-context closer `congruenceClosesToEmptyTypeModuloElim`.  Each
must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.headReaches_bridgeTypeCell
#assert_no_axioms FX1Poly.Typed.variableCellHasNoCongruenceStep
#assert_no_axioms FX1Poly.Typed.universeCodeCellHasNoCongruenceStep
#assert_no_axioms FX1Poly.Typed.UnionElimCongruenceClosesToEmptyType
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.congruenceClosesToEmptyTypeAux
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.congruenceClosesToEmptyTypeModuloElim
-- THE FLAT-FORMER CONGRUENCE OBLIGATION TRANSFORM (HasTypeUnionFlatFormationCongruence): the formationRule arm of
-- the general single-step union SR for the flat family (product/either/equiv).  Recursion on the spine length
-- `binderShifts` (both StepChildren and RawTermChildren are mutual ⟹ `induction` rejected) + one-level `cases`; a
-- child congruence touches exactly one flat obligation's subject (universe-code classifier, children-independent),
-- re-typed by its SR + universe reclassification.  The first per-family brick of gate-2's formationRule arm.
#assert_no_axioms FX1Poly.Typed.flatFormationPremisesHoldAfter
-- THE TERM-INDEXED ENDPOINT CONGRUENCE TRANSFORM (HasTypeUnionTermIndexedFormationCongruence): the Id/Bridge
-- endpoint-obligation transform under a child congruence — every endpoint at the fixed `carrier` (binder-free, no
-- context drift), so a child congruence touches one endpoint subject, re-typed at `carrier` by its SR +
-- reclassification.  The term-indexed sibling of the flat brick; same spine-length recursion.
#assert_no_axioms FX1Poly.Typed.termIndexedEndpointObligationsHoldAfter
-- THE TERM-INDEXED ENDPOINT CARRIER-CONVERSION TRANSPORT (HasTypeUnionTermIndexedFormationCongruence): the
-- carrier-step complement — when the carrier child steps (`carrierOld ↝ carrierNew`), every endpoint typed at the
-- old carrier re-types at the new carrier through the carrier `Conv` + a `carrierNew`-is-type witness.  Children
-- unchanged (only the classifier carrier moves), so it is a pure spine-length transport, no `childStep`.
#assert_no_axioms FX1Poly.Typed.termIndexedEndpointObligationsHoldUnderCarrierConv

end FX1PolyAudit
