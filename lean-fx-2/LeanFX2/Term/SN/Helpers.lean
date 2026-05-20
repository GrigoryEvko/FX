import LeanFX2.Reducibility.SN.Helpers

/-! # LeanFX2.Term.SN.Helpers — compatibility shim

SN helper proofs semantically depend on raw reduction inversion and
compatibility lemmas, so the implementation lives in
`LeanFX2.Reducibility.SN.Helpers`.  This module preserves the historical
import path while keeping direct `Reduction.*` imports out of the Term layer.
-/

namespace LeanFX2

end LeanFX2
