import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Substrate.Neutral.NeutralTermRename

/-! # FX1PolyAudit.Core.Substrate.Neutral.NeutralTermRename

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Substrate.Neutral.NeutralTermRename`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- CR3 structural ingredient: neutrality is preserved by renaming (needed so the applied fresh-var head
-- `rename furtherRenaming functionTerm` stays neutral in the Kripke arrow's neutral backward closure).
#assert_no_axioms FX1Poly.Core.IsNeutral.rename

end FX1PolyAudit
