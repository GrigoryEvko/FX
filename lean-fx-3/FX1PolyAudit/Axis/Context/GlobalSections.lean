import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Context.GlobalSections

/-! # FX1PolyAudit/AuditAxisContextGlobalSections — zero-axiom gate for context-18

Per-declaration zero-axiom gate for `context-18`'s context-side deliverable
(`FX1Poly/Axis/Context/GlobalSections.lean`): the global-sections (points) functor `Γ = Hom(−, 0)`, the
crisp / global substitutions, and the flat no-go (`♭` non-trivial) — the elementary obstruction that
motivates crisp / modal type theory (Shulman), NOT LOPS18's universe-fibrancy no-go (that is `×type`).

  * `globalSections` / `globalSectionsReindex` (+ `_id` / `_comp`) — `Γ = Hom(−, 0)` as a representable
    presheaf on `fxBaseSubstCategory` with its functor laws;
  * `globalSections_empty_subsingleton` — `Γ` of the empty context is a point;
  * `IsGlobalSubst` / `isGlobalSubst_of_target_zero` / `isGlobalSubst_identity_zero` — the crisp / global
    substitutions (closed-image), and that closed environments are crisp;
  * `not_isGlobalSubst_identity_succ` / `isGlobalSubst_identity_iff` — ★ THE FLAT NO-GO: the identity is
    crisp iff the context is empty (the flat counit is not invertible — `♭` is not an ordinary base op);
  * `IsDiscreteContext` / `isDiscreteContext_iff_empty` (+ `_zero` / `not_..._succ`) — ★ only the empty
    context is discrete (`Disc` collapses, so `♭` is genuinely type-level);
  * `FxGlobalSections` / `fxGlobalSections` — the assembled object;
  * `fxGlobalSections_hasFlatTypeModality` — the honesty marker (`= false`); the flat comonad on TYPES,
    crisp-`J`, and the internal universe are `×type` / `×mode` deferrals;
  * `fxGlobalSections_open_identity_smoke` — the one-variable context has a non-crisp identity.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Axis.globalSections
#assert_no_axioms FX1Poly.Axis.globalSectionsReindex
#assert_no_axioms FX1Poly.Axis.globalSectionsReindex_id
#assert_no_axioms FX1Poly.Axis.globalSectionsReindex_comp
#assert_no_axioms FX1Poly.Axis.globalSections_empty_subsingleton
#assert_no_axioms FX1Poly.Axis.IsGlobalSubst
#assert_no_axioms FX1Poly.Axis.isGlobalSubst_of_target_zero
#assert_no_axioms FX1Poly.Axis.isGlobalSubst_identity_zero
#assert_no_axioms FX1Poly.Axis.not_isGlobalSubst_identity_succ
#assert_no_axioms FX1Poly.Axis.isGlobalSubst_identity_iff
#assert_no_axioms FX1Poly.Axis.IsDiscreteContext
#assert_no_axioms FX1Poly.Axis.isDiscreteContext_zero
#assert_no_axioms FX1Poly.Axis.not_isDiscreteContext_succ
#assert_no_axioms FX1Poly.Axis.isDiscreteContext_iff_empty
#assert_no_axioms FX1Poly.Axis.FxGlobalSections
#assert_no_axioms FX1Poly.Axis.fxGlobalSections
#assert_no_axioms FX1Poly.Axis.fxGlobalSections_hasFlatTypeModality
#assert_no_axioms FX1Poly.Axis.fxGlobalSections_open_identity_smoke

end FX1PolyAudit
