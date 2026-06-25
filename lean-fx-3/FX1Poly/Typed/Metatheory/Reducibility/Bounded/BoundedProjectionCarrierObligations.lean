import FX1Poly.Core.Metatheory.Reducibility.Candidates.ProjectionPairCandidate
import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BoundedMemberWeakHeadExpansion

/-! # FX1Poly/Typed/BoundedProjectionCarrierObligations
    — every bounded-reducible type's candidate meets the projection candidate's `CarrierObligations`

The projection-based Σ candidate `projectionPairCandidate` (`ProjectionPairCandidate.lean`, the Geuvers route)
needs each component carrier to satisfy `CarrierObligations`: a reducibility candidate PLUS member weak-head
expansion under any `WeakHeadStep`.  The bounded reducibility model supplies BOTH for every bound-reducible
type, family-wide and unconditionally:

  * candidacy by `ReducibleTypeAtBounded.isReducibilityCandidate` (the unconditional CR1/CR2/CR3);
  * member weak-head expansion by `ReducibleTypeAtBounded.memberWeakHeadExpansion` (the per-arm weak-head
    expansion — data/empty reuse the per-candidate expansions, `universeCode` reattaches, `piType` lands the
    arrow candidate per argument through the `appCongruence` weak-head step).

So a component candidate recovered by the carrier-aware inversions (`productMemberAtBounded_carrierAware` and the
forthcoming projection inversion) — itself a `ReducibleTypeAtBounded firstCode firstCandidate` — feeds the
projection candidate's `CarrierObligations` hypotheses directly.  This is the bridge the eventual `pairLike`
`CarrierCombinator.assemble` swap (assemble ↦ `projectionPairCandidate`) consumes to discharge the `fst` / `snd`
reach-conditioned residues (`projectionPairCandidate_reachableComponentMembers`) forward, for arbitrary
(Π-included) component carriers.

## Zero-axiom verification

A structure assembly of the two shipped bounded-model carriers (`ReducibleTypeAtBounded.isReducibilityCandidate`
+ `ReducibleTypeAtBounded.memberWeakHeadExpansion`, fed the `ReducibleTypeAtBounded` value at the
definitionally-equal `ReducibleTypeStepBounded` form).  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- **Every bound-reducible type's candidate satisfies the projection candidate's `CarrierObligations`.**  The
bridge feeding `projectionPairCandidate`'s component-carrier hypotheses from the bounded inversions: candidacy
from `ReducibleTypeAtBounded.isReducibilityCandidate`, member weak-head expansion from
`ReducibleTypeAtBounded.memberWeakHeadExpansion` (the `ReducibleTypeAtBounded` value is definitionally the
`ReducibleTypeStepBounded` form the weak-head-expansion lemma expects). -/
theorem boundedTypeCarrierObligations {scope : Nat} {env : Nat → Nat} {bound : Nat}
    {typeCode : RawTerm (scope + 1)} {candidate : RawTerm (scope + 1) → Prop}
    (reducible : ReducibleTypeAtBounded env bound typeCode candidate) :
    CarrierObligations candidate where
  isCandidate := ReducibleTypeAtBounded.isReducibilityCandidate reducible
  memberWeakHeadExpansion := fun weakHeadStep sourceStronglyNormalizing reductMember =>
    ReducibleTypeAtBounded.memberWeakHeadExpansion reducible weakHeadStep sourceStronglyNormalizing reductMember

end FX1Poly.Typed
