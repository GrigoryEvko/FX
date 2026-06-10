import FX1PolyAudit.DependencyAudit
import FX1PolyAudit.FX0CrossCheckCertified
import FX1Poly.Typed.MilestoneASpineValueLayer
import FX1Poly.Typed.ClosedNatCanonicity
import FX1Poly.Typed.CombinedNatCanonicalForms
import FX1Poly.Typed.HonestCapstoneSignoff
import FX1Poly.Typed.MilestoneA0SimplyTypedFloor
import FX1Poly.Typed.ClosedStronglyNormalizing
import FX1Poly.Typed.HasTypeDescDecidable
import FX1Poly.Typed.ThirdWayBoundaries
import FX1Poly.Core.ConvWordJoinableBridge

/-! # FX1PolyAudit/CapstoneSignoff — the per-milestone capstone sign-off, pillar theorems BY NAME

One audit module, three milestones, no slogans: each milestone's pillar theorems are enumerated by
their actual declaration names and re-verified zero-axiom right here.  Where a milestone is NOT met,
its exact residuals are named — nothing is silently absorbed.

## MILESTONE-A SPINE (tracker #501) — SIGNED OFF in this file

The three soundness pillars of the grown typed kernel `HasTypeDescPi`, each unconditional:

  * SN (SN-043):       `HasTypeDescPi.stronglyNormalizingOfWfContextDesc` (open, wf-conditional only)
                       + `HasTypeDescPi.closedStronglyNormalizing` (closed, hypothesis-free)
  * consistency:       `emptyConsistencyViaCandidateBridge` (candidate bridge)
                       + `emptyTypeConsistencySyntactic` (independent syntactic confirm)
  * canonicity:        `closedBoolCanonicalForms` (bool, 3 engines), `closedNatCanonicalForms`
                       (Nat numerals), `closedNormalNatCanonicalFormsCombined` (per-classifier,
                       constructor heads — the CAN-5 assembly)

plus the SN-triangulation parity (`honestCapstoneMet_holds`).  The POSITIVE assembled capstone is
`milestoneASpineSignoffHolds` (NEW, below): the value-layer spine record + Nat canonicity + the
honest triangulation, one checked object — replacing the lone negative
`threeWayCapstone_not_yet_met` as the spine's headline.

## POWERFUL-SN (tracker #653) — the HONEST capstone, CLOSED

Shipped and gated here: `honestCapstoneMet_holds` + `honestCapstone_met_while_threeWay_unreachable`
(the criterion: SN/canonicity/consistency each proven once by Tait; SN triangulated twice; the
literal three-INDEPENDENT-ways criterion is itself proven unreachable), `snColumnIsHonest` +
`snPrimaryTait` / `snConfirmSconingBridged` / `snConfirmRpoFragment` / `snRpoBetaBoundary` (the SN
column), and the three cross-leg boundary bricks (`ThirdWayBoundaries`): #1146 =
`thirdWayConsistencyBoundaryHolds` + `thirdWayConsistencyAssembled` (consistency-at-`Empty`
decomposed Tait-free ⊕ Tait-imported, the import visible as one proof step); #642 =
`typedRootWordReductionTerminates` + `infiniteTermChainInducesInfiniteWordChain` (the chain-level
termination ≡ SN correspondence; the canonicity half stays dropped per
`convergentNormalFormNeedNotBeCanonical`); #641 = `Conv.toWordJoinable` (forward, shipped) +
`RawTerm.toCode_not_injective` (the committed reverse blocker — payload collapse; the
word→`Conv` reverse needs a payload-faithful encoding, the named follow-on).

## MILESTONE A0 (tracker #464) — shipped pillars gated; NOT closed

Shipped and gated here: `wfContextDefensibleKernel` (open SN + decidable `Conv` of well-typed terms
over EVERY well-formed context — the A0 decidability floor), `HasTypeDesc.decidableOfWellFormed`
(decidable formation checking), and the FX0 external cross-check
`FX0CrossCheck.externalVerify_accepts_certified` (the standalone re-checker accepts the encoding of
every wf-typed subject, with SN).  EXACT residuals keeping #464 open: #220 (host-minimal
`certifyRawCellExact?` prelude-only gate), the STRICT-COMPLEXITY witnesses (#268 / #471 / #648),
and the joint-decidability apex (O-NORM, open research — A0's deciders are per-fragment/wf-scoped).
CERTIFICATE-NOTION CAVEAT (post O-STACK #1194): A0's external-verification leg is the
sort-AGNOSTIC FX0 re-checker; the sort-disciplined `certifyRawCellExact?` provably does NOT cover
all typed subjects (`typedDoesNotFactorThroughCertification`) — any A0 release text must say "FX0
re-checked", not "structurally certified".

## Zero-axiom verification

`milestoneASpineSignoffHolds` is a three-field record whose fields are the shipped theorems named
above; everything else in this file is `#assert_no_axioms` re-verification of named declarations.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The Milestone-A spine sign-off** — the value-layer spine record (SN + consistency + bool
canonicity), Nat-numeral canonicity, and the honest SN-triangulation parity, as ONE `Prop`.  The
positive assembled capstone that #501 asked for. -/
structure MilestoneASpineSignoff (profile : PolyProfile) : Prop where
  /-- SN + consistency + bool canonicity, bundled (`milestoneAValueLayerSpineHolds`). -/
  valueLayerSpine : MilestoneAValueLayerSpine profile
  /-- Nat canonicity: a closed term typed at `natTypeCell` (intro or grown engine) reduces to a
  numeral (`closedNatCanonicalForms`). -/
  natCanonicity : ∀ {subject : RawTerm 0},
    (HasTypeDescNatIntro profile (TypingContext.empty : TypingContext profile 0) subject
        natTypeCell ∨
      HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject natTypeCell) →
      ∃ value : RawTerm 0, StepStar subject value ∧ IsNatNumeral value
  /-- The honest SN triangulation: Tait fully independent, sconing bridged, RPO fragment
  (`honestCapstoneMet_holds`). -/
  snTriangulationHonest : FX1Poly.Core.ParityMatrix.honestCapstoneMet

/-- **★ The Milestone-A spine sign-off HOLDS** — each field is the shipped named theorem:
`milestoneAValueLayerSpineHolds`, `closedNatCanonicalForms`, `honestCapstoneMet_holds`. -/
theorem milestoneASpineSignoffHolds {profile : PolyProfile} :
    MilestoneASpineSignoff profile where
  valueLayerSpine := milestoneAValueLayerSpineHolds
  natCanonicity typed := closedNatCanonicalForms typed
  snTriangulationHonest := FX1Poly.Core.ParityMatrix.honestCapstoneMet_holds

end FX1Poly.Typed

-- ===== MILESTONE-A SPINE (#501) — pillar theorems by name, re-verified =====
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.stronglyNormalizingOfWfContextDesc
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedStronglyNormalizing
#assert_no_axioms FX1Poly.Typed.emptyConsistencyViaCandidateBridge
#assert_no_axioms FX1Poly.Typed.closedBoolCanonicalForms
#assert_no_axioms FX1Poly.Typed.closedNatCanonicalForms
#assert_no_axioms FX1Poly.Typed.closedNormalNatCanonicalFormsCombined
#assert_no_axioms FX1Poly.Typed.milestoneAValueLayerSpineHolds
-- ★ the positive assembled spine capstone (#501)
#assert_no_axioms FX1Poly.Typed.milestoneASpineSignoffHolds

-- ===== POWERFUL-SN (#653) — honest triangulation by name, all three boundary bricks in =====
#assert_no_axioms FX1Poly.Core.ParityMatrix.honestCapstoneMet_holds
#assert_no_axioms FX1Poly.Core.ParityMatrix.honestCapstone_met_while_threeWay_unreachable
#assert_no_axioms FX1Poly.Core.ParityMatrix.snColumnIsHonest
#assert_no_axioms FX1Poly.Core.ParityMatrix.snPrimaryTait
#assert_no_axioms FX1Poly.Core.ParityMatrix.snConfirmSconingBridged
#assert_no_axioms FX1Poly.Core.ParityMatrix.snConfirmRpoFragment
#assert_no_axioms FX1Poly.Core.ParityMatrix.snRpoBetaBoundary
-- #1146: third-way consistency = Tait-free normal-form half ⊕ Tait-imported normalization half
#assert_no_axioms FX1Poly.Typed.thirdWayConsistencyBoundaryHolds
#assert_no_axioms FX1Poly.Typed.thirdWayConsistencyAssembled
-- #642: chain-level termination ≡ SN (the canonicity half stays dropped per the NO-GO)
#assert_no_axioms FX1Poly.Typed.typedRootWordReductionTerminates
#assert_no_axioms FX1Poly.Typed.infiniteTermChainInducesInfiniteWordChain
#assert_no_axioms FX1Poly.Core.convergentNormalFormNeedNotBeCanonical
-- #641: word-joinability forward + the committed reverse blocker (payload collapse)
#assert_no_axioms FX1Poly.Core.Conv.toWordJoinable
#assert_no_axioms FX1Poly.Core.RawTerm.toCode_not_injective

-- ===== MILESTONE A0 (#464) — shipped pillars by name; residuals #220, #268/#471/#648, O-NORM =====
#assert_no_axioms FX1Poly.Typed.wfContextDefensibleKernel
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.decidableOfWellFormed
#assert_no_axioms FX1Poly.FX0CrossCheck.externalVerify_accepts_certified
