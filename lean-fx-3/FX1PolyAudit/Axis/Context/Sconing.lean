import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Context.Sconing

/-! # FX1PolyAudit/AuditAxisContextSconing — zero-axiom gate for context-11's sconing / STC

Per-declaration zero-axiom gate for `context-11`'s context-side deliverable
(`FX1Poly/Axis/Context/Sconing.lean`): synthetic Tait computability over the context base + relative
induction — the Artin gluing (scone) of `fxBaseSubstCategory` along the term presheaf `Tm`, realized as a
genuine category, with its display functor, split fibration, and the relative-induction interface.

  * `CovariantPointsFunctor` — the functor the scone glues along (pointwise laws, no `funext`);
  * `SubsconeObject` / `SubsconeHom` / `SubsconeHom.ext` — computability structures + predicate-preserving
    morphisms + the Prop-irrelevance extensionality (the zero-axiom engine);
  * `Subscone` — ★ the Artin gluing as a `RawCategory`;
  * `subsconeProjection` — the display functor `Subscone → category`;
  * `subsconeReindex` / `subsconeCartesianHom` — ★ reindexing of computability structures + the cartesian
    lift (the split-fibration / relative-induction substrate);
  * `ConvComputabilityModel` / `.sectionFunctor` / `.projection_section_object` /
    `.projection_section_morphism` — ★ displayed computability models = sections of the display functor
    (the relative-induction interface, splitting the projection);
  * `trivialComputabilityModel` — the terminal (`True`) model inhabiting the interface;
  * `fxTermPoints` — the term presheaf `Tm` as a points functor (laws = `context-7`'s `reindexTerm_*`);
  * `fxReducibilityScone` — ★ the concrete Tait-computability scone over the FX context base;
  * `FxSconing` / `fxSconing` — the assembled witness;
  * `fxSconing_hasProofRelevantComputability` / `fxSconing_hasFundamentalTheorem` — the honesty markers
    (`= false`): proof-relevant computability needs `funext` (`×type+term`); the fundamental theorem is the
    section out of the initial model (`×type+term`, `fib-6`);
  * `fxSconing_projection_section_smoke` — the section splits the display functor on the nose.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The points functor the gluing is along
#assert_no_axioms FX1Poly.Axis.CovariantPointsFunctor

-- The Artin gluing as a category (objects, morphisms, the Prop-irrelevance extensionality, the laws)
#assert_no_axioms FX1Poly.Axis.SubsconeObject
#assert_no_axioms FX1Poly.Axis.SubsconeHom
#assert_no_axioms FX1Poly.Axis.SubsconeHom.ext
#assert_no_axioms FX1Poly.Axis.Subscone

-- The display functor
#assert_no_axioms FX1Poly.Axis.subsconeProjection

-- The split fibration: reindexing of computability structures + the cartesian lift
#assert_no_axioms FX1Poly.Axis.subsconeReindex
#assert_no_axioms FX1Poly.Axis.subsconeCartesianHom

-- Relative induction: displayed models are sections of the display functor
#assert_no_axioms FX1Poly.Axis.ConvComputabilityModel
#assert_no_axioms FX1Poly.Axis.ConvComputabilityModel.sectionFunctor
#assert_no_axioms FX1Poly.Axis.ConvComputabilityModel.projection_section_object
#assert_no_axioms FX1Poly.Axis.ConvComputabilityModel.projection_section_morphism
#assert_no_axioms FX1Poly.Axis.trivialComputabilityModel

-- The concrete Tait-computability scone over the FX context base (built on context-7's Tm)
#assert_no_axioms FX1Poly.Axis.fxTermPoints
#assert_no_axioms FX1Poly.Axis.fxReducibilityScone

-- The assembled witness + honesty markers + smoke
#assert_no_axioms FX1Poly.Axis.FxSconing
#assert_no_axioms FX1Poly.Axis.fxSconing
#assert_no_axioms FX1Poly.Axis.fxSconing_hasProofRelevantComputability
#assert_no_axioms FX1Poly.Axis.fxSconing_hasFundamentalTheorem
#assert_no_axioms FX1Poly.Axis.fxSconing_projection_section_smoke

end FX1PolyAudit
