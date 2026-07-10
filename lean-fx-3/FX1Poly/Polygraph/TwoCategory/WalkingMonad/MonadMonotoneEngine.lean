import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadDeltaModel
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadSaturatedDeltaReps

/-! # WalkingMonad/MonadMonotoneEngine — relocated to `MonadSaturatedDeltaReps` (MONAD-R7 r4)

The whole monotone-fold ENGINE stratum (`monadMonoProcessSpine` / `monadRunMonoCell`, the fold-decomposition
`monadMonoProcessSpine_spineDiff`, the peel / shift / irrelevance laws, the length-width invariant
`monadRunMonoCell_width`, the three monad laws at an arbitrary left-whisker context, and the non-vacuity witnesses)
is conv-FREE, so it is relocated VERBATIM (names / namespace / meaning preserved) to the bespoke-free deep bridge
`MonadSaturatedDeltaReps`.  This file remains a chain link: it imports `MonadDeltaModel` so the pure-bespoke
`MonadSaturatedTwoCellConv` inductive stays reachable downstream, and imports the bridge so the relocated engine
decls stay available to any module importing this one. -/
