import FX1PolyAudit.DependencyAudit
import FX1PolyAudit.Polygraph.TwoCategory.WalkingMonad.MonadBespokeFreeWalk
import FX1Poly.Polygraph.TwoCategory.Amalgam.ReconstructedDecisionGen

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.ReconstructedDecisionGen — zero-axiom + bespoke-free gate for the
GENERIC-PRIMARY reconstructed decider (the SaturatedOver re-founding, Amalgam-side)

Per-declaration zero-axiom gate for `monadReconstructedDecisionGen` and its three live verdicts, PLUS the
constant-closure META-WALK that certifies the re-founding advance: `monadReconstructedDecisionGen` has NO bespoke
`monadSaturatedTwoCellDecision` / `MonadSaturatedTwoCellConv` in its FULL transitive constant closure, whereas the
prior `monadReconstructedDecision` DOES (the before/after needle-detector control — a checkable provenance advance).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

-- the generic-primary decider + its three live verdicts
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadReconstructedDecisionGen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadReconstructedDecisionGen_assoc
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadReconstructedDecisionGen_leftUnit
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadReconstructedDecisionGen_faces

-- the honesty markers
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasGenericPrimaryReconstructionDecision
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_reFoundingFileImportStaysGated

/-! ## The re-founding advance, MACHINE-CHECKED by the exhaustive constant-closure walk

`monadReconstructedDecisionGen`'s FULL transitive constant closure contains NEITHER the bespoke decider
`monadSaturatedTwoCellDecision` NOR the bespoke inductive `MonadSaturatedTwoCellConv` — the running term routes
through the born-generic `decideSaturatedConvOverMonadNative` (bespoke-free), plus `reseatReflect` /
`monadReconRefutes` (which consume the generic conv / refutation directly, no `monadSaturated_iff_generic` bridge). -/

#assert_constant_free_of FX1Poly.Polygraph.Amalgam.monadReconstructedDecisionGen
  needle FX1Poly.Polygraph.monadSaturatedTwoCellDecision
#assert_constant_free_of FX1Poly.Polygraph.Amalgam.monadReconstructedDecisionGen
  needle FX1Poly.Polygraph.MonadSaturatedTwoCellConv

/-! ## The BEFORE control: the prior decider DID depend on the bespoke (so the free_of gates are not vacuous) -/

#assert_constant_depends_on FX1Poly.Polygraph.Amalgam.monadReconstructedDecision
  needle FX1Poly.Polygraph.monadSaturatedTwoCellDecision
#assert_constant_depends_on FX1Poly.Polygraph.Amalgam.monadReconstructedDecision
  needle FX1Poly.Polygraph.MonadSaturatedTwoCellConv

end FX1PolyAudit
