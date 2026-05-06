prelude
import LeanFX2.FX1.LeanKernel.Inductive
import LeanFX2.FX1.LeanKernel.HasType
import LeanFX2.FX1.LeanKernel.Check
import LeanFX2.FX1.LeanKernel.Soundness
import LeanFX2.FX1.LeanKernel.Audit

/-! # FX1/LeanKernel

Lean-kernel model over the minimal FX1 root.

Root status: LeanKernel-FX1 scaffold.

This umbrella collects the current Lean-kernel syntax, substitution, reduction,
and declaration slices after moving them out of the historical
`LeanFX2.Lean.Kernel` path.  It is not a TCB-reduction claim by itself:
`LeanFX2.FX1.LeanKernel.check_sound` remains the load-bearing theorem for that
claim.
-/

namespace LeanFX2.FX1.LeanKernel

end LeanFX2.FX1.LeanKernel
