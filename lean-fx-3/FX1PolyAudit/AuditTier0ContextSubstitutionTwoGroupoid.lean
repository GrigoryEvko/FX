import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Context.SubstitutionTwoGroupoid

/-! # FX1PolyAudit/AuditTier0ContextSubstitutionTwoGroupoid — zero-axiom gate for context-20

Per-declaration zero-axiom gate for `context-20`'s context-side deliverable
(`FX1Poly/Tier0/Context/SubstitutionTwoGroupoid.lean`): the dim-2 homotopy layer of the substitution
category — the equality-2-cell (2,1)-category structure + the substitution-specific characterization of
2-cells as pointwise lookup-homotopies.

  * `RawCategory.whiskerLeft` / `whiskerRight` / `horizontalCompose` — whiskering + Godement horizontal
    composition of 2-cells, generic over any `RawCategory`;
  * `RawCategory.whiskerLeft_id` / `whiskerRight_id` / `whiskerLeft_vcomp` / `whiskerRight_vcomp` — the
    whisker functoriality laws;
  * `RawCategory.whisker_exchange` / `horizontalCompose_eq_whiskers` — the exchange law + the whisker
    decomposition of `hcomp`;
  * `RawCategory.interchange` — ★ THE INTERCHANGE LAW (the defining (2,1)-category coherence);
  * `SubstVec.twoCellOfPointwise` / `pointwiseOfTwoCell` — ★ a 2-cell IS a pointwise lookup-homotopy
    (`ext` ↔ `congrArg`);
  * `FxSubstitutionTwoGroupoid` / `fxSubstitutionTwoGroupoid` — the assembled witness (invertibility +
    interchange + the pointwise characterization);
  * `fxSubstitutionTwoGroupoid_higherCellsAreContentful` — the honesty marker (`= false`); the dim-2
    layer is strict/discrete (set-level base, 1-truncated ω-groupoid), contentful higher cells are the
    `×type` identity layer;
  * `fxSubstitutionTwoGroupoid_whiskerLeft_id_smoke` — left-whiskering the identity 2-cell is identity.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Tier0.RawCategory.whiskerLeft
#assert_no_axioms FX1Poly.Tier0.RawCategory.whiskerRight
#assert_no_axioms FX1Poly.Tier0.RawCategory.horizontalCompose
#assert_no_axioms FX1Poly.Tier0.RawCategory.whiskerLeft_id
#assert_no_axioms FX1Poly.Tier0.RawCategory.whiskerRight_id
#assert_no_axioms FX1Poly.Tier0.RawCategory.whiskerLeft_vcomp
#assert_no_axioms FX1Poly.Tier0.RawCategory.whiskerRight_vcomp
#assert_no_axioms FX1Poly.Tier0.RawCategory.whisker_exchange
#assert_no_axioms FX1Poly.Tier0.RawCategory.horizontalCompose_eq_whiskers
#assert_no_axioms FX1Poly.Tier0.RawCategory.interchange
#assert_no_axioms FX1Poly.Tier0.SubstVec.twoCellOfPointwise
#assert_no_axioms FX1Poly.Tier0.SubstVec.pointwiseOfTwoCell
#assert_no_axioms FX1Poly.Tier0.FxSubstitutionTwoGroupoid
#assert_no_axioms FX1Poly.Tier0.fxSubstitutionTwoGroupoid
#assert_no_axioms FX1Poly.Tier0.fxSubstitutionTwoGroupoid_higherCellsAreContentful
#assert_no_axioms FX1Poly.Tier0.fxSubstitutionTwoGroupoid_whiskerLeft_id_smoke

end FX1PolyAudit
