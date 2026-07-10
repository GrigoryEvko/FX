import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadDeltaDecision
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadSaturatedCanonReps

/-! # WalkingMonad/MonadCanonicalWord — relocated to `MonadSaturatedCanonReps` (MONAD-R7 r4)

The whole conv-FREE Eilenberg–Zilber canonical-WORD skeleton (`monadTPower`, `monadGadget`, `wordFromCounts`,
`reconstructFrom`, `countsDomainPath`, `consReplicate`, …) is relocated VERBATIM (names / namespace / meaning
preserved) to the bespoke-free deep leaf `MonadSaturatedCanonReps`.  This file remains a chain link: it imports
`MonadDeltaDecision` so the pure-bespoke `MonadSaturatedTwoCellConv` inductive stays reachable downstream, and
imports the canonical-word leaf so the relocated decls stay available to any module importing this one. -/
