import FX1Poly.Core.Metatheory.Normalization.Orders.RawIotaRpoAssembly

/-! # IotaFragmentOrdinalAnalysis — ORD-NORM (#1448): the certified ι-fragment's proof-theoretic ordinal, made explicit

The reframe "ordinal analysis = normalization" applied to FX's shipped
RPO machinery.  A classical ordinal analysis assigns each term an
ordinal and shows every reduction step DESCENDS, so that strong
normalization IS the well-foundedness of the ordinal.  FX already
shipped exactly this for the certified oriented-ι (Tier-2) fragment —
but unnamed.  This module names it:

  * the **proof-theoretic ordinal** of the fragment is the RECURSIVE
    PATH ORDER over the finite generator precedence,
    `RpoBelow iotaGenPrecedence`, whose well-foundedness is the shipped
    `iotaGenRpoWellFounded` (Dershowitz's RPO ordinal over a finite
    signature);
  * the **ordinal assignment** is `eraseToRose` (term ↦ its rose-tree
    rank), and EVERY oriented root-ι reduction STRICTLY DECREASES it
    (`IotaHeadStep.rpoEmbeds`) — this IS the ordinal-descent content of
    an ordinal analysis;
  * **SN = the ordinal's well-foundedness**: the fragment is strongly
    normalizing PRECISELY BECAUSE that RPO ordinal is well-founded; the
    SN proof is `Subrelation.wf` + `InvImage.wf eraseToRose` over it,
    re-stated here with the ordinal as an EXPLICIT hypothesis so the
    dependency is visible, then discharged.

**Honest two-tier scope.**  This is the ordinal analysis of the
oriented-ι fragment ONLY.  Raw β admits NO recursive path order
(`betaNotOrientableByErasure`, HCAP-NOGO-rpoSN #1145), and the two
substituting succ-iota arms sit at the β-imported boundary.  Their
proof-theoretic ordinal is the LARGER Tait / sconing ordinal (the
SN-101/110 logical-relation argument), not the RPO ordinal.  So: the
ι-fragment's ordinal IS the RPO ordinal (here); the β-fragment's is the
Tait ordinal (there).  Naming the RPO half does not claim the whole
kernel's ordinal.

Zero-axiom; audit-gated in
`FX1PolyAudit/AuditIotaFragmentOrdinalAnalysis.lean`. -/

namespace FX1Poly.Core

open FX1Poly.Core.RpoInductive
open FX1Poly.Core.RawIotaRpo

/-- ★ **The ordinal assignment descends** — every oriented root-ι
reduction STRICTLY DECREASES the RPO ordinal of the term's erasure.
This is the per-step descent that an ordinal analysis demands: each term
carries the ordinal `eraseToRose t` ranked by `Rpo iotaGenPrecedence`,
and `source ↝ target` forces `source`'s rank strictly above `target`'s.
Direct from the shipped `IotaHeadStep.rpoEmbeds`. -/
theorem iotaOrientedReduction_strictlyDecreasesRpoOrdinal {scope : Nat}
    {source target : RawTerm scope} (step : IotaOrientedHeadStep source target) :
    Rpo iotaGenPrecedence (eraseToRose source) (eraseToRose target) :=
  IotaHeadStep.rpoEmbeds step.1 step.2

/-- ★ **Ordinal analysis = normalization** — the certified oriented-ι
fragment is strongly normalizing PRECISELY BECAUSE the RPO ordinal
`RpoBelow iotaGenPrecedence` is well-founded.  The ordinal's
well-foundedness appears as an EXPLICIT hypothesis, exhibiting that the
fragment's SN is *derived from and bounded by* that ordinal — the
content of an ordinal analysis read off the shipped RPO embedding. -/
theorem iotaFragmentSN_fromRpoOrdinalWellFounded {scope : Nat}
    (rpoOrdinalWellFounded : WellFounded (RpoBelow iotaGenPrecedence)) :
    WellFounded (IotaOrientedHeadStep.successor (scope := scope)) :=
  Subrelation.wf
    (r := InvImage (RpoBelow iotaGenPrecedence) eraseToRose)
    (fun orientedStep => IotaHeadStep.rpoEmbeds orientedStep.1 orientedStep.2)
    (InvImage.wf eraseToRose rpoOrdinalWellFounded)

/-- The fragment's proof-theoretic ordinal IS the RPO ordinal: SN holds,
with its well-foundedness witness routed explicitly through the shipped
`iotaGenRpoWellFounded`.  The ordinal-analysis corollary — SN is the
discharge of the RPO ordinal's well-foundedness. -/
theorem iotaFragmentSN_byRpoOrdinal {scope : Nat} :
    WellFounded (IotaOrientedHeadStep.successor (scope := scope)) :=
  iotaFragmentSN_fromRpoOrdinalWellFounded iotaGenRpoWellFounded

end FX1Poly.Core
