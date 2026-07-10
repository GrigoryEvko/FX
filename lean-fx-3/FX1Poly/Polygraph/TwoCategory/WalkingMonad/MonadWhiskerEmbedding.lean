import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadMapFactorization
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadSaturatedSkeletonReps
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadSaturatedDeltaReps

/-! # WalkingMonad/MonadWhiskerEmbedding — relocated to `MonadSaturatedDeltaReps` (MONAD-R7 r4)

The whole whisker-EMBEDDING fold-support stratum (`embedLocalMap_composeMap` / `embedLocalMap_nest`,
`monadMonotoneMapOf_length` / `_mapsInto`, `monadRunMonoCell_localEmbed`, the two whisker fold laws
`monadMonotoneMapOf_whiskerLeft` / `_whiskerRight`, and the two fold-congruence lemmas
`monadMonotoneMapOf_whiskerLeftCongr` / `_whiskerRightCongr`) is conv-FREE, so it is relocated VERBATIM
(names / namespace / meaning preserved) to the bespoke-free deep bridge `MonadSaturatedDeltaReps` (which imports the
shallow embed-primitive bridge `MonadSaturatedSkeletonReps` these decls build on).  This file remains a chain link:
it imports `MonadMapFactorization` so the pure-bespoke `MonadSaturatedTwoCellConv` inductive stays reachable
downstream, and imports the bridge so the relocated decls stay available to any module importing this one. -/
