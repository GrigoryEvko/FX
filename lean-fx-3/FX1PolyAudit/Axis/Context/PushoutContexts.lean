import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Context.PushoutContexts

/-! # FX1PolyAudit/AuditAxisContextPushoutContexts — zero-axiom gate for context-19

Per-declaration zero-axiom gate for `context-19`'s context-side deliverable
(`FX1Poly/Axis/Context/PushoutContexts.lean`): pushouts of contexts + the context-level strictness of
the gluing square.  Pushouts live in `fxBaseSubstCategory = 𝒞ᵒᵖ` (= pullbacks in the CwF context
category `𝒞`); a pushout over the empty context (the initial object) is the context coproduct.

  * `IsPushout` / `IsPushout.mediateHomExt` / `IsPushout.uniqueUpToIso` — the generic pushout universal
    property over a `RawCategory`, the jointly-epic injections, and pushout uniqueness up to iso;
  * `IsBinaryCoproduct.isPushoutOverInitial` — a coproduct + an initial object IS the pushout of the
    span over the initial object;
  * `IsPushout.ofIsoLeftLeg` / `IsPushout.ofIsoRightLeg` — gluing along an iso leg is strict-trivial;
  * `fxBaseSubstPushoutOverInitial` — ★ the concrete context pushout: gluing two contexts over the
    empty context is their context coproduct (scope addition);
  * `fxBaseSubstGlueSquare_definitional` — ★ the over-empty gluing square commutes DEFINITIONALLY (`rfl`);
  * `fxBaseSubstComprehensionPushout` — ★★ THE COMPREHENSION SQUARE IS A PUSHOUT: context extension
    `Δ.A` is the pushout of the substitution-stability span — the strictness of context extension, at
    full strength (mediator + β/η ARE the comprehension `cons`-laws);
  * `FxGluePushout` / `fxGluePushout` — the assembled witness;
  * `fxGluePushout_hasGlueWeldTypeFormers` — the honesty marker (`= false`); the `Glue` / `Weld` type
    formers and the cubical realignment axiom are `×type` (universe) / `×mode` (cofibration) deferrals;
  * `fxGluePushout_glue_singletons_smoke` — the (1,1)-pushout's left injection is the coproduct
    injection into scope `2`.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Axis.IsPushout
#assert_no_axioms FX1Poly.Axis.IsPushout.mediateHomExt
#assert_no_axioms FX1Poly.Axis.IsPushout.uniqueUpToIso
#assert_no_axioms FX1Poly.Axis.IsBinaryCoproduct.isPushoutOverInitial
#assert_no_axioms FX1Poly.Axis.IsPushout.ofIsoLeftLeg
#assert_no_axioms FX1Poly.Axis.IsPushout.ofIsoRightLeg
#assert_no_axioms FX1Poly.Axis.fxBaseSubstPushoutOverInitial
#assert_no_axioms FX1Poly.Axis.fxBaseSubstGlueSquare_definitional
#assert_no_axioms FX1Poly.Axis.fxBaseSubstComprehensionPushout
#assert_no_axioms FX1Poly.Axis.FxGluePushout
#assert_no_axioms FX1Poly.Axis.fxGluePushout
#assert_no_axioms FX1Poly.Axis.fxGluePushout_hasGlueWeldTypeFormers
#assert_no_axioms FX1Poly.Axis.fxGluePushout_glue_singletons_smoke

end FX1PolyAudit
