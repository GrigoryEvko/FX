import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Rewriting.Coherence.SquierCoherence

/-! # FX1PolyAudit/AuditAxisTermSquier — zero-axiom gate for term-4 (Squier coherence)

Per-declaration zero-axiom gate for `FX1Poly/Axis/Term/Rewrite/SquierCoherence.lean`: the proof-relevant
rewriting 2-category (`RewritePath` + composition + category laws), the homotopy congruence
(`RewriteHomotopy` + whiskering), the diamond generating-confluences (`DiamondProperty`), and the
coherence theorem (`DiamondConfluence` + `strip` + `confluent` + `coherence`: the diamonds are a homotopy
basis — parallel paths to a normal form are homotopic).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega` — in particular the indexed-inductive `match` in `coherence` and the recursive
`def`s must not leak `propext`. -/

namespace FX1PolyAudit

-- The proof-relevant rewriting 2-category: paths + composition + the genuine category laws
#assert_no_axioms FX1Poly.Core.RewritePath
#assert_no_axioms FX1Poly.Core.RewritePath.single
#assert_no_axioms FX1Poly.Core.RewritePath.comp
#assert_no_axioms FX1Poly.Core.RewritePath.nil_comp
#assert_no_axioms FX1Poly.Core.RewritePath.cons_comp
#assert_no_axioms FX1Poly.Core.RewritePath.comp_nil
#assert_no_axioms FX1Poly.Core.RewritePath.comp_assoc

-- The diamond generating-confluences + the homotopy congruence (the 2-cells)
#assert_no_axioms FX1Poly.Core.SquierDiamond
#assert_no_axioms FX1Poly.Core.RewriteHomotopy
#assert_no_axioms FX1Poly.Core.RewriteHomotopy.whiskerLeftPath
#assert_no_axioms FX1Poly.Core.RewriteHomotopy.whiskerRightPath

-- The coherent confluence: strip + confluent + coherence (the NF specialization)
#assert_no_axioms FX1Poly.Core.SquierConfluence
#assert_no_axioms FX1Poly.Core.SquierDiamond.strip
#assert_no_axioms FX1Poly.Core.SquierDiamond.confluent
#assert_no_axioms FX1Poly.Core.SquierDiamond.coherence

-- The least-congruence universal property (the diamonds generate the homotopy)
#assert_no_axioms FX1Poly.Core.HomotopyModel
#assert_no_axioms FX1Poly.Core.RewriteHomotopy.toModel

-- The concrete witness: coherent confluence is non-vacuous (the complete relation)
#assert_no_axioms FX1Poly.Core.completeStep
#assert_no_axioms FX1Poly.Core.completeDiamond
#assert_no_axioms FX1Poly.Core.completeCoherentJoin

end FX1PolyAudit
