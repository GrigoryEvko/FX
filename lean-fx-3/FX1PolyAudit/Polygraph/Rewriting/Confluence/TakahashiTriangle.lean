import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Rewriting.Confluence.TakahashiTriangle

/-! # FX1PolyAudit.Polygraph.Rewriting.Confluence.TakahashiTriangle

Zero-axiom audit shard mirroring kernel module `FX1Poly.Polygraph.Rewriting.Confluence.TakahashiTriangle`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The Takahashi triangle lemma: the linear route to the parallel-reduction diamond.  A completeDevelopment
-- function with the TriangleProperty (every reduct steps to the source's complete development) yields
-- DiamondProperty.ofTriangle and Confluent.ofTriangle, reducing the parallel diamond from a quadratic
-- redex-pair join to the single linear "exhibit completeDevelopment + its triangle" obligation (Takahashi
-- 1995).  Composes with diamondConfluence; the TABLE lane (TableTakahashiTriangle) consumes it.
#assert_no_axioms FX1Poly.Core.DiamondProperty.ofTriangle

#assert_no_axioms FX1Poly.Core.Confluent.ofTriangle

-- The existential per-source form (HasMaximalReduct): generalizes the function-based TriangleProperty
-- (HasMaximalReduct.ofTriangle) and is the form a concrete parallel reduction discharges by structural
-- recursion on the source (no separately-defined total completeDevelopment function over RawTerm needed).
-- ofMaximalReduct yields the diamond; Confluent.ofMaximalReduct composes with diamondConfluence.
#assert_no_axioms FX1Poly.Core.HasMaximalReduct.ofTriangle

#assert_no_axioms FX1Poly.Core.DiamondProperty.ofMaximalReduct

#assert_no_axioms FX1Poly.Core.Confluent.ofMaximalReduct

end FX1PolyAudit
