import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadMonotoneEngine

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingMonad.MonadMonotoneEngine — relocation note

The monotone-fold ENGINE stratum this file used to gate is relocated (MONAD-R7 r4) to the bespoke-free deep bridge
`MonadSaturatedDeltaReps`; its per-declaration zero-axiom gates now live in that bridge's audit twin.  This file
remains a chain link (its `MonadMonotoneEngine` shim import keeps the module in the umbrella). -/

namespace FX1PolyAudit

end FX1PolyAudit
