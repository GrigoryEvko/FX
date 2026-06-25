import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Context.ComprehensionCategory

/-! # FX1PolyAudit/AuditTier0ContextComprehensionCategory — zero-axiom gate for context-10

Per-declaration zero-axiom gate for `context-10`'s context-side deliverable
(`FX1Poly/Tier0/Context/ComprehensionCategory.lean`): the FX context base as a split COMPREHENSION
CATEGORY (Jacobs) — the display maps form a split fibration, and the dependent sum Σ (comprehension) is
stable under reindexing (Beck–Chevalley).

  * `IsSplitDisplayFibration` / `fxDisplaySplitFibration` — the display maps form a SPLIT (Grothendieck)
    fibration: strict cleavage (`lift_identity` / `lift_compose`) + cartesian display map
    (`weakening_compose_lift`, the Beck–Chevalley square);
  * `SubstVec.comprehensionBackward_natural` — ★ fibred Σ Beck–Chevalley (the extension / Σ-introduction is
    natural in the context — the dependent sum commutes with reindexing);
  * `SubstVec.comprehensionForward_natural` — the projection dual (the representability is natural);
  * `FxComprehensionCategory` / `fxComprehensionCategory` — the assembled split-comprehension-category object;
  * `fxComprehensionCategory_hasFibredPiRightAdjoint` — the honesty marker (`= false`): the fibred Π right
    adjoint needs LCC (`×type → context-16/fib-1`) and is NOT shipped here;
  * `fxComprehensionCategory_representability_backward_smoke` — the bundle's representability is the
    comprehension extension.

The fibred Π RIGHT adjoint (LCC, `×type`) and the Σ-as-type-former (`gen_sigmaTyCode`, `×type`/`×term`) are
the honest deferrals; only the unconditional context-side Σ left-adjoint / comprehension half ships here.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Tier0.IsSplitDisplayFibration
#assert_no_axioms FX1Poly.Tier0.fxDisplaySplitFibration
#assert_no_axioms FX1Poly.Tier0.SubstVec.comprehensionBackward_natural
#assert_no_axioms FX1Poly.Tier0.SubstVec.comprehensionForward_natural
#assert_no_axioms FX1Poly.Tier0.FxComprehensionCategory
#assert_no_axioms FX1Poly.Tier0.fxComprehensionCategory
#assert_no_axioms FX1Poly.Tier0.fxComprehensionCategory_hasFibredPiRightAdjoint
#assert_no_axioms FX1Poly.Tier0.fxComprehensionCategory_representability_backward_smoke

end FX1PolyAudit
