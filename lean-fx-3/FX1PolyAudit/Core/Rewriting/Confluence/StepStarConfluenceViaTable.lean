import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Rewriting.Confluence.StepStarConfluenceViaTable

/-! # FX1PolyAudit.Core.Rewriting.Confluence.StepStarConfluenceViaTable

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Rewriting.Confluence.StepStarConfluenceViaTable`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.StepOverTable.canonicalConfluent

#assert_no_axioms FX1Poly.Core.StepStar.toTableClosure

#assert_no_axioms FX1Poly.Core.ReflTransClosure.toStepStar

#assert_no_axioms FX1Poly.Core.StepStar.tableRouteConfluence

#assert_no_axioms FX1Poly.Core.StepStar.tableRouteStrip

-- The local one-step join (one-vs-one instance of the table confluence) — the shape the
-- historical per-iota critical-pair matrix (cd_lemma over the CriticalPairs/CdLemma enumeration,
-- now DELETED) proved by quadratic case analysis.  Every former cd_lemma consumer (the
-- accessibility Newman bridge, the beta-only fragment of the betaEta local Church-Rosser, the
-- certified word-rewrite reflection) now draws its local join from here.
#assert_no_axioms FX1Poly.Core.StepStar.localJoin

end FX1PolyAudit
