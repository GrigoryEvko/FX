import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Context.GlobalSections

/-! # FX1PolyAudit/AuditTier0ContextGlobalSections — zero-axiom gate for context-18

Per-declaration zero-axiom gate for `context-18`'s context-side deliverable
(`FX1Poly/Tier0/Context/GlobalSections.lean`): the global-sections (points) functor `Γ = Hom(−, 0)`, the
crisp / global substitutions, and the LOPS18 no-go.

  * `globalSections` / `globalSectionsReindex` (+ `_id` / `_comp`) — `Γ = Hom(−, 0)` as a representable
    presheaf on `fxBaseSubstCategory` with its functor laws;
  * `globalSections_empty_subsingleton` — `Γ` of the empty context is a point;
  * `IsGlobalSubst` / `isGlobalSubst_of_target_zero` / `isGlobalSubst_identity_zero` — the crisp / global
    substitutions (closed-image), and that closed environments are crisp;
  * `not_isGlobalSubst_identity_succ` / `isGlobalSubst_identity_iff` — ★ THE LOPS18 NO-GO: the identity is
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

#assert_no_axioms FX1Poly.Tier0.globalSections
#assert_no_axioms FX1Poly.Tier0.globalSectionsReindex
#assert_no_axioms FX1Poly.Tier0.globalSectionsReindex_id
#assert_no_axioms FX1Poly.Tier0.globalSectionsReindex_comp
#assert_no_axioms FX1Poly.Tier0.globalSections_empty_subsingleton
#assert_no_axioms FX1Poly.Tier0.IsGlobalSubst
#assert_no_axioms FX1Poly.Tier0.isGlobalSubst_of_target_zero
#assert_no_axioms FX1Poly.Tier0.isGlobalSubst_identity_zero
#assert_no_axioms FX1Poly.Tier0.not_isGlobalSubst_identity_succ
#assert_no_axioms FX1Poly.Tier0.isGlobalSubst_identity_iff
#assert_no_axioms FX1Poly.Tier0.IsDiscreteContext
#assert_no_axioms FX1Poly.Tier0.isDiscreteContext_zero
#assert_no_axioms FX1Poly.Tier0.not_isDiscreteContext_succ
#assert_no_axioms FX1Poly.Tier0.isDiscreteContext_iff_empty
#assert_no_axioms FX1Poly.Tier0.FxGlobalSections
#assert_no_axioms FX1Poly.Tier0.fxGlobalSections
#assert_no_axioms FX1Poly.Tier0.fxGlobalSections_hasFlatTypeModality
#assert_no_axioms FX1Poly.Tier0.fxGlobalSections_open_identity_smoke

end FX1PolyAudit
