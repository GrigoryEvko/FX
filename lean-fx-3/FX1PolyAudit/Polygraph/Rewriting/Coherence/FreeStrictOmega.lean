import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Rewriting.Coherence.FreeStrictOmega

/-! # FX1PolyAudit/AuditAxisTermFreeStrictOmega — zero-axiom gate for term-17 (free strict ω-cat + Gray)

Per-declaration zero-axiom gate for `FX1Poly/Axis/Term/Rewrite/FreeStrictOmega.lean`: the free-category
universal property at dimension 1 (`RewritePath.foldMap` + `foldMap_nil` / `foldMap_single` /
`foldMap_comp` functoriality / `foldMap_unique` / `foldMap_id`) and the strict interchange at dimension 2
(`interchangeWhiskerSource` / `interchangeWhiskerTarget` / `rewriteInterchange_strict`).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The free-category recursor + the universal property (existence/functoriality + uniqueness)
#assert_no_axioms FX1Poly.Core.RewritePath.foldMap
#assert_no_axioms FX1Poly.Core.RewritePath.foldMap_nil
#assert_no_axioms FX1Poly.Core.RewritePath.foldMap_single
#assert_no_axioms FX1Poly.Core.RewritePath.foldMap_comp
#assert_no_axioms FX1Poly.Core.RewritePath.foldMap_unique
#assert_no_axioms FX1Poly.Core.RewritePath.foldMap_id

-- The strict interchange at dimension 2 (the Gray interchanger degenerates to the identity)
#assert_no_axioms FX1Poly.Core.interchangeWhiskerSource
#assert_no_axioms FX1Poly.Core.interchangeWhiskerTarget
#assert_no_axioms FX1Poly.Core.rewriteInterchange_strict

-- The dimension-2 universal property (existence + uniqueness), completing the free strict ω-cat to both dims
#assert_no_axioms FX1Poly.Core.freeStrictTwoCategory_dim2UniversalProperty
#assert_no_axioms FX1Poly.Core.freeStrictTwoCategory_dim2Uniqueness

end FX1PolyAudit
