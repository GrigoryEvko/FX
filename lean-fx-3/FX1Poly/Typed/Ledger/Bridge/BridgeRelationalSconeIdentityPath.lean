import FX1Poly.Typed.Ledger.Bridge.BridgeRelationalScone
import FX1Poly.Typed.Ledger.Bridge.BridgeEndpointStep
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationConstructors
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationRenameForwardGeneral

/-! # FX1Poly/Typed/BridgeRelationalSconeIdentityPath — identity-path membership (NATIVE-58)

The reflexivity-bridge (identity-path) inhabitant of the relational Bridge scone (NATIVE-57).
`constantBridgeGradedOfTyped` already TYPES the reflexivity bridge `pathLam(weaken t) :
Bridge(T, t, t)` — the derivable `refl` of internal parametricity, both endpoints collapsing to
`t`.  This file gives it its SEMANTIC counterpart: the reflexivity bridge is a MEMBER of the
relational scone over `(t, t)` exactly when the carrier relation is reflexive at `t`.

That conditional is the whole content.  The identity-extension property of a parametricity model is
precisely "every element is related to itself in the relational interpretation"; here it is exposed
as the requirement `carrierRelation t t` on the carrier — the reflexive-graph condition.  The bridge
type provides the inhabitant; the carrier relation must supply the reflexivity.

  * `reflexivityBridge` — the canonical identity path `pathLam(weaken t)`, the term
    `constantBridgeGradedOfTyped` types at `Bridge(T, t, t)`.
  * `reflexivityBridge_isStronglyNormalizing` — SN, via the shipped `pathLam`-cong SN closure over
    the weakening SN closure (`pathLam_isStronglyNormalizing_of_body ∘
    weaken_isStronglyNormalizing_forward`).
  * `reflexivityBridge_endpointBetaComputes` — operational coherence: applied to ANY interval
    argument the reflexivity bridge computes to `t` (`endpointBetaConstantBodyFiresOverTable`), so
    BOTH endpoints are literally `t` — it inhabits the `(t, t)` diagonal of the scone.
  * ★ `reflexivityBridge_memberOfReflexiveScone` — THE identity-path membership: a reflexive
    carrier (`carrierRelation t t`) plus SN of `t` makes the reflexivity bridge a scone member over
    `(t, t)`.  The semantic twin of `constantBridgeGradedOfTyped`.
  * ★ `reflexivityBridge_canonicalMemberAtDataValue` — the canonical (not dummy) witness: over the
    self-related data value `firstWitnessPairValue` the reflexivity bridge is the natural scone
    inhabitant — upgrading NATIVE-57's `emptyTypeCell` placeholder to the `refl`-shaped member.

Honest scope: the carrier-reflexivity premise is genuine — the relational scone does NOT make every
element self-related for free (that would erase the relational content NATIVE-57's teeth guard).
The reflexivity bridge witnesses self-relatedness precisely WHEN the carrier model already provides
it.  The affine premise's semantic role (why a non-affine dimension would collapse the relation to
that diagonal) is NATIVE-59.

Zero-axiom; gated in `FX1PolyAudit/AuditBridgeRelationalSconeIdentityPath.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- The canonical **reflexivity bridge** (identity path) on `carrierTerm`: the dimension-constant
path abstraction `pathLam(weaken carrierTerm)`.  Both its endpoints collapse to `carrierTerm`
(`endpointBetaConstantBodyFiresOverTable`); it is the term `constantBridgeGradedOfTyped` types at
`Bridge(T, carrierTerm, carrierTerm)`. -/
def reflexivityBridge {scope : Nat} (carrierTerm : RawTerm scope) : RawTerm scope :=
  pathLamCell (RawTerm.weaken carrierTerm)

/-- **The reflexivity bridge is strongly normalizing** when its carrier is — the `pathLam`-cong SN
closure over the weakening SN closure. -/
theorem reflexivityBridge_isStronglyNormalizing {scope : Nat} {carrierTerm : RawTerm scope}
    (carrierTerminates : IsStronglyNormalizing carrierTerm) :
    IsStronglyNormalizing (reflexivityBridge carrierTerm) :=
  pathLam_isStronglyNormalizing_of_body
    (weaken_isStronglyNormalizing_forward carrierTerminates)

/-- **Operational coherence**: applied to ANY interval argument, the reflexivity bridge computes to
`carrierTerm` — both endpoints are literally `carrierTerm`, so it inhabits the `(t, t)` diagonal. -/
theorem reflexivityBridge_endpointBetaComputes {scope : Nat}
    (carrierTerm argument : RawTerm scope) :
    StepTable (pathAppCell (reflexivityBridge carrierTerm) argument) carrierTerm :=
  endpointBetaConstantBodyFiresOverTable carrierTerm argument

/-- ★ **The identity-path membership.**  When the carrier relation is reflexive at `carrierTerm`
(`carrierRelation carrierTerm carrierTerm`) and `carrierTerm` is SN, the reflexivity bridge is a
member of the relational scone over the diagonal `(carrierTerm, carrierTerm)` — the semantic twin
of the typing `constantBridgeGradedOfTyped`.  This is the identity-extension property exposed as a
reflexive-graph condition on the carrier. -/
theorem reflexivityBridge_memberOfReflexiveScone {scope : Nat}
    {carrierRelation : BinaryCandidate scope} {carrierTerm : RawTerm scope}
    (carrierTerminates : IsStronglyNormalizing carrierTerm)
    (carrierReflexive : carrierRelation carrierTerm carrierTerm) :
    bridgeRelationalCandidate carrierRelation carrierTerm carrierTerm
      (reflexivityBridge carrierTerm) :=
  bridgeRelationalCandidate.intro
    (reflexivityBridge_isStronglyNormalizing carrierTerminates)
    carrierReflexive

/-- ★ **The canonical concrete witness.**  Over the self-related data value `firstWitnessPairValue`
(`binaryPairCandidate_relatesSelf`), the reflexivity bridge is the natural scone inhabitant — the
`refl`-shaped member, upgrading NATIVE-57's `emptyTypeCell` placeholder. -/
theorem reflexivityBridge_canonicalMemberAtDataValue :
    bridgeRelationalCandidate (binaryDataCandidate isPairValue)
      firstWitnessPairValue firstWitnessPairValue
      (reflexivityBridge firstWitnessPairValue) :=
  reflexivityBridge_memberOfReflexiveScone
    (IsStronglyNormalizing.ofIsStepNormalForm
      (isPairValue_impliesStepNormalForm firstWitnessPairValue_isPairValue))
    binaryPairCandidate_relatesSelf

end FX1Poly.Typed
