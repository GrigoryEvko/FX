import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadCanonicalWord
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadSaturatedCanonReps

/-! # WalkingMonad/MonadCountsRoundTrip — relocated to `MonadSaturatedCanonReps` (MONAD-R7 r4)

The whole conv-FREE fibre-COUNTS round-trip stratum (`countsOf`, `runLengthAt`, `dropRunAt`, and the round-trip
identities) is relocated VERBATIM (names / namespace / meaning preserved) to the bespoke-free deep leaf
`MonadSaturatedCanonReps`.  This file remains a chain link: it imports `MonadCanonicalWord` so the pure-bespoke
`MonadSaturatedTwoCellConv` inductive stays reachable downstream, and imports the canonical-word leaf so the
relocated decls stay available to any module importing this one. -/
