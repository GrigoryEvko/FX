import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadMonotoneEngine
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadSaturatedDeltaReps

/-! # WalkingMonad/MonadMapFactorization — relocated to `MonadSaturatedDeltaReps` (MONAD-R7 r4)

The whole map-FACTORIZATION stratum (the `mapEqOfConv` structural machinery and its supporting decompositions) is
conv-FREE, so it is relocated VERBATIM (names / namespace / meaning preserved) to the bespoke-free deep bridge
`MonadSaturatedDeltaReps`.  This file remains a chain link: it imports `MonadMonotoneEngine` so the pure-bespoke
`MonadSaturatedTwoCellConv` inductive stays reachable downstream, and imports the bridge so the relocated decls
stay available to any module importing this one. -/
