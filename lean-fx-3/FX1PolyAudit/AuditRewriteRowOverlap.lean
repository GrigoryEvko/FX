import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.RewriteRowOverlap

/-! # FX1PolyAudit/AuditRewriteRowOverlap — RW-3 shard

Per-declaration zero-axiom gate for the unified (ι × η) row-pair overlap checker (RW-3).

Increment 1 — the STATIC certificate: the heterogeneous `RewriteRow`, its root head, the unified
`overlaps?` test folding the three bespoke orthogonality notions, the pairwise `allRewriteRowsDisjoint`
fold, the combined `rewriteBundle`, and the ★ canonical disjointness pin spanning BOTH tables.

Increment 2 — the OPERATIONAL soundness: the unified `rewriteAtRoot?` dispatch with its two
definitional unfolds, the zero-axiom `List.Mem` membership lemmas (append-split + map-extraction +
bundle classifier), the ★ `rewriteBundle_rootDeterministic` (two disjoint rows firing on one cell
agree on the reduct — ι×ι determinism, η×η determinism, mixed ι×η vacuous), and its canonical
instance `fxRewriteBundle_rootDeterministic`.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

/-! ## Increment 1 — the static overlap certificate -/

#assert_no_axioms FX1Poly.Core.RewriteRow
#assert_no_axioms FX1Poly.Core.RewriteRow.rootHead
#assert_no_axioms FX1Poly.Core.RewriteRow.overlaps?
#assert_no_axioms FX1Poly.Core.rewriteRowsDisjoint
#assert_no_axioms FX1Poly.Core.allRewriteRowsDisjoint
#assert_no_axioms FX1Poly.Core.rewriteBundle
#assert_no_axioms FX1Poly.Core.fxRewriteBundle_rowsDisjoint

/-! ## Increment 2 — the unified root dispatch -/

#assert_no_axioms FX1Poly.Core.RewriteRow.rewriteAtRoot?
#assert_no_axioms FX1Poly.Core.RewriteRow.rewriteAtRoot?_iotaRow
#assert_no_axioms FX1Poly.Core.RewriteRow.rewriteAtRoot?_etaRow

/-! ## Increment 2 — the zero-axiom `List.Mem` membership lemmas -/

#assert_no_axioms FX1Poly.Core.mem_appendOr
#assert_no_axioms FX1Poly.Core.mem_mapIotaRow
#assert_no_axioms FX1Poly.Core.mem_mapEtaRow
#assert_no_axioms FX1Poly.Core.mem_rewriteBundle

/-! ## Increment 2 — ★ operational root determinism -/

#assert_no_axioms FX1Poly.Core.rewriteBundle_rootDeterministic
#assert_no_axioms FX1Poly.Core.fxRewriteBundle_rootDeterministic

end FX1PolyAudit
