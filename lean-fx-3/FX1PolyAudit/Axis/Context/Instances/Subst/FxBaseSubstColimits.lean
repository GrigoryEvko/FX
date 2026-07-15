import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Context.Instances.Subst.FxBaseSubstColimits

/-! # FX1PolyAudit/AuditAxisContextColimits — zero-axiom gate for context-3's colimits leg

Per-declaration zero-axiom gate for `context-3`'s strictly context-side deliverable
(`FX1Poly/Axis/Context/Instances/Subst/FxBaseSubstColimits.lean`): the FINITE COPRODUCTS of the
context category `fxBaseSubstCategory` — the INITIAL object (scope `0`, the empty context) and the
binary COPRODUCT (scope addition), each as a genuine, PROVED categorical universal property.

  * the generic universal properties `IsInitialObject` / `IsBinaryCoproduct` over a `RawCategory`;
  * `fxBaseSubstInitial` — scope 0 is initial (`SubstVec target 0 = PUnit`, uniqueness by eta);
  * `SubstVec.append` + the structural index injections + the two append-lookup laws;
  * the variable-injection substitutions, the projections, and the `append_split` η-law;
  * `fxBaseSubstBinaryCoproduct` — the full universal property (both β-laws via the append-lookup
    laws, η/uniqueness via `append_split`).
  * the GENERIC categorical calculus of finite coproducts (over any `RawCategory`): initial
    hom-uniqueness, the η-rule `copair inl inr = id`, post-composition fusion, jointly-epic
    extensionality; and the concrete coproduct BIFUNCTOR `SubstVec.coproductMap` on `+` with its
    naturality squares and both functor laws (preserves identities + composition).

The dimensional adjoint quadruple (transpension proper) is the cross-axis `× mode` deliverable and
is deferred to `fib-4`; only the context-side finite colimits the substitution category owns
outright are gated here.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The generic universal properties over a RawCategory
#assert_no_axioms FX1Poly.Axis.IsInitialObject
#assert_no_axioms FX1Poly.Axis.IsBinaryCoproduct

-- The initial object: scope 0 (the empty context)
#assert_no_axioms FX1Poly.Axis.fxBaseSubstInitial

-- Append + the structural coproduct index injections + the append-lookup laws
#assert_no_axioms FX1Poly.Axis.SubstVec.append
#assert_no_axioms FX1Poly.Axis.finIntoCoproductRight
#assert_no_axioms FX1Poly.Axis.finIntoCoproductLeft
#assert_no_axioms FX1Poly.Axis.SubstVec.lookup_append_right
#assert_no_axioms FX1Poly.Axis.SubstVec.lookup_append_left

-- The injections, projections, and the append/split eta-law
#assert_no_axioms FX1Poly.Axis.SubstVec.tabulate_congr
#assert_no_axioms FX1Poly.Axis.SubstVec.coproductInjectLeft
#assert_no_axioms FX1Poly.Axis.SubstVec.coproductInjectRight
#assert_no_axioms FX1Poly.Axis.SubstVec.coproductInjectLeft_lookup
#assert_no_axioms FX1Poly.Axis.SubstVec.coproductInjectRight_lookup
#assert_no_axioms FX1Poly.Axis.SubstVec.coproductSplitLeft
#assert_no_axioms FX1Poly.Axis.SubstVec.coproductSplitRight
#assert_no_axioms FX1Poly.Axis.SubstVec.append_split
#assert_no_axioms FX1Poly.Axis.SubstVec.coproductSplitLeft_eq_compose
#assert_no_axioms FX1Poly.Axis.SubstVec.coproductSplitRight_eq_compose

-- The binary coproduct universal property (both beta-laws + uniqueness)
#assert_no_axioms FX1Poly.Axis.fxBaseSubstBinaryCoproduct

-- The generic categorical calculus of finite coproducts
#assert_no_axioms FX1Poly.Axis.IsInitialObject.homExt
#assert_no_axioms FX1Poly.Axis.IsBinaryCoproduct.copairInjections
#assert_no_axioms FX1Poly.Axis.IsBinaryCoproduct.copairPostCompose
#assert_no_axioms FX1Poly.Axis.IsBinaryCoproduct.homExt

-- The substitution coproduct BIFUNCTOR + its two functor laws + naturality
#assert_no_axioms FX1Poly.Axis.SubstVec.homExt
#assert_no_axioms FX1Poly.Axis.SubstVec.append_compose
#assert_no_axioms FX1Poly.Axis.SubstVec.coproductMap
#assert_no_axioms FX1Poly.Axis.SubstVec.injectLeft_coproductMap
#assert_no_axioms FX1Poly.Axis.SubstVec.injectRight_coproductMap
#assert_no_axioms FX1Poly.Axis.SubstVec.coproductMap_identity
#assert_no_axioms FX1Poly.Axis.SubstVec.coproductMap_compose

-- The coproduct is SYMMETRIC: the braiding A + B ≅ B + A (no Nat.add_comm)
#assert_no_axioms FX1Poly.Axis.IsBinaryCoproduct.braid
#assert_no_axioms FX1Poly.Axis.IsBinaryCoproduct.braid_braid
#assert_no_axioms FX1Poly.Axis.IsBinaryCoproduct.braidIsIso
#assert_no_axioms FX1Poly.Axis.fxBaseSubstCoproductSymmetry

end FX1PolyAudit
