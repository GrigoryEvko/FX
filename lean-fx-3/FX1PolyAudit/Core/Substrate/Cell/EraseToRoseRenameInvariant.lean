import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Substrate.Cell.EraseToRoseRenameInvariant

/-! # FX1PolyAudit.Core.Substrate.Cell.EraseToRoseRenameInvariant

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Substrate.Cell.EraseToRoseRenameInvariant`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- eraseToRose rename-invariance (the eta-embedding substrate): `eraseToRose` forgets the payload and every
-- binder shift, so a rename (which only rewrites the var-arm payload + renames children) leaves the rose
-- image unchanged.  This is what lets eta-reduction RPO-decrease the SAME eraseToRose order the ι fragment
-- uses: each eta-contraction leaves a SUBTERM of the source modulo a weakening rename (etaLam/etaPathLam put
-- the inner function under one extra binder, reached by RawTerm.weaken), and weaken-invariance erases that
-- gap.  Proven by the mutual term+children recursion mirroring RawTerm.rename_pointwise (var arm closes
-- definitionally; non-var via rename_mkGen_of_ne_var + the children IH).  eraseToRose_weaken is the corollary
-- the binder eta arms consume directly.
#assert_no_axioms FX1Poly.Core.eraseToRose_rename

#assert_no_axioms FX1Poly.Core.eraseChildren_rename

#assert_no_axioms FX1Poly.Core.eraseToRose_weaken

end FX1PolyAudit
