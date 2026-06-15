import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Context.Instances.Subst.FxBaseSubstColimits

/-! # FX1PolyAudit/AuditTier0ContextColimits — zero-axiom gate for context-3's colimits leg

Per-declaration zero-axiom gate for `context-3`'s strictly context-side deliverable
(`FX1Poly/Tier0/Context/Instances/Subst/FxBaseSubstColimits.lean`): the FINITE COPRODUCTS of the
context category `fxBaseSubstCategory` — the INITIAL object (scope `0`, the empty context) and the
binary COPRODUCT (scope addition), each as a genuine, PROVED categorical universal property.

  * the generic universal properties `IsInitialObject` / `IsBinaryCoproduct` over a `RawCategory`;
  * `fxBaseSubstInitial` — scope 0 is initial (`SubstVec target 0 = PUnit`, uniqueness by eta);
  * `SubstVec.append` + the structural index injections + the two append-lookup laws;
  * the variable-injection substitutions, the projections, and the `append_split` η-law;
  * `fxBaseSubstBinaryCoproduct` — the full universal property (both β-laws via the append-lookup
    laws, η/uniqueness via `append_split`).

The dimensional adjoint quadruple (transpension proper) is the cross-axis `× mode` deliverable and
is deferred to `fib-4`; only the context-side finite colimits the substitution category owns
outright are gated here.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The generic universal properties over a RawCategory
#assert_no_axioms FX1Poly.Tier0.IsInitialObject
#assert_no_axioms FX1Poly.Tier0.IsBinaryCoproduct

-- The initial object: scope 0 (the empty context)
#assert_no_axioms FX1Poly.Tier0.fxBaseSubstInitial

-- Append + the structural coproduct index injections + the append-lookup laws
#assert_no_axioms FX1Poly.Tier0.SubstVec.append
#assert_no_axioms FX1Poly.Tier0.finIntoCoproductRight
#assert_no_axioms FX1Poly.Tier0.finIntoCoproductLeft
#assert_no_axioms FX1Poly.Tier0.SubstVec.lookup_append_right
#assert_no_axioms FX1Poly.Tier0.SubstVec.lookup_append_left

-- The injections, projections, and the append/split eta-law
#assert_no_axioms FX1Poly.Tier0.SubstVec.tabulate_congr
#assert_no_axioms FX1Poly.Tier0.SubstVec.coproductInjectLeft
#assert_no_axioms FX1Poly.Tier0.SubstVec.coproductInjectRight
#assert_no_axioms FX1Poly.Tier0.SubstVec.coproductInjectLeft_lookup
#assert_no_axioms FX1Poly.Tier0.SubstVec.coproductInjectRight_lookup
#assert_no_axioms FX1Poly.Tier0.SubstVec.coproductSplitLeft
#assert_no_axioms FX1Poly.Tier0.SubstVec.coproductSplitRight
#assert_no_axioms FX1Poly.Tier0.SubstVec.append_split
#assert_no_axioms FX1Poly.Tier0.SubstVec.coproductSplitLeft_eq_compose
#assert_no_axioms FX1Poly.Tier0.SubstVec.coproductSplitRight_eq_compose

-- The binary coproduct universal property (both beta-laws + uniqueness)
#assert_no_axioms FX1Poly.Tier0.fxBaseSubstBinaryCoproduct

end FX1PolyAudit
