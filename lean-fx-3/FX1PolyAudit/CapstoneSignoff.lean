import FX1PolyAudit.DependencyAudit
import FX1PolyAudit.FX0CrossCheckCertified
import FX1Poly.Typed.MilestoneASpineValueLayer
import FX1Poly.Typed.ClosedNatCanonicity
import FX1Poly.Typed.HasTypeNativeUnionCanonicalForms
import FX1Poly.Typed.HonestCapstoneSignoff
import FX1Poly.Typed.MilestoneA0SimplyTypedFloor
import FX1Poly.Typed.ClosedStronglyNormalizing
import FX1Poly.Typed.HasTypeDescDecidable
import FX1Poly.Typed.HasTypeDescPiCheckOfInferred
import FX1Poly.Typed.SemanticTierSoundness
import FX1Poly.Typed.BetaEtaConvDecidable
import FX1Poly.Typed.TypedNbeConvDecision
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
                       (Nat numerals), `HasTypeNativeUnion.closedNormalNatCanonicalForms`
                       (per-classifier, constructor heads — the CAN-5 assembly carried by the
                       NATIVE-38 union lane master since NATIVE-42 retired the zoo mini-union)

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

## MILESTONE A0 (tracker #464) — SIGNED OFF in this file, per §11.8.12.0

The spec (polycell.md §11.8.12.0) defines A₀ as exactly three pillars — decidable typed checking
on the live typed fragment with a PROVEN boundary, decidable typed conversion on the same
fragment, and the FX0 cross-check — and EXPLICITLY excludes the joint-apex normalization (O-NORM)
from A₀'s claims ("A₀ does NOT claim: joint-apex normalization (O-NORM) …").  An earlier revision
of this docstring cited O-NORM as "the exact residual keeping #464 open" — that framing
CONTRADICTED the spec it cites and is retired: O-NORM is a non-claim of A₀ by definition, tracked
at revised-MILESTONE-A and beyond, not an A₀ residual.  Per the spec, the sign-off artifact is
this audit module enumerating the pillar carriers by name, "after which #464 closes".

The POSITIVE assembled capstone is **`milestoneA0SignoffHolds`** (below): one checked record
whose seven fields are the shipped pillar carriers —
  * checking: `HasTypeDesc.decidableOfWellFormed` (native formation decider) +
    `HasTypeDescPi.decidableCheckOfInferredUniqueAtType` (the grown bidirectional compare step);
  * boundary: `reservedTierUntypedByEveryEngine` (reserved generators head no typed cell — the
    grown conjunct is the record field; the full nine-engine conjunction is gated by name);
  * conversion: `wfContextDefensibleKernel.convDecidable` (typed `Conv` decider, every wf
    context) + `BetaEtaConv.decidableOfWfTyped` (the βη decider) + `checkNbeEqual_sound` (the
    NbE normalize-and-compare check certifies the full judgmental equality `DefEqUnitEtaCong`);
  * FX0: `FX0CrossCheck.externalVerify_accepts_certified` (the independent re-checker accepts
    every wf-typed subject's encoding, with SN).
Supporting load-bearing facts (independently gated here and in `AuditTyped`): open SN, the
Milestone-A spine record, uniqueness, the honesty ledger.

Two honest caveats carried forward unchanged: the host-minimal certifier gate (FX0-PC.1, #220)
is SHIPPED (`#assert_host_minimal` in `AuditFX0Poly`); the STRICT-COMPLEXITY witnesses (#268 /
#471 / #648) are SHIPPED two-tier honest (`levelDenoteEquivDecisionComplexity` polynomial where
true; EXACT counters + Statman non-elementarity literature-cited where no size-polynomial is
true).  CERTIFICATE-NOTION CAVEAT (post O-STACK #1194): A₀'s external-verification leg is the
sort-AGNOSTIC FX0 re-checker; the sort-disciplined `certifyRawCellExact?` provably does NOT cover
all typed subjects (`typedDoesNotFactorThroughCertification`) — any A₀ release text must say "FX0
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

/-- **The Milestone-A₀ sign-off record (#464)** — the §11.8.12.0 release gate as ONE checked
object: the three A₀ pillars (decidable typed checking + proven boundary, decidable typed
conversion, FX0 cross-check), each field instantiated by a shipped named theorem.  `Type`-valued
because the decider fields are decision DATA. -/
structure MilestoneA0Signoff (profile : PolyProfile) : Type where
  /-- Pillar 1a — decidable FORMATION checking over every well-formed context
  (`HasTypeDesc.decidableOfWellFormed`). -/
  checkingDecidableFormation :
    ∀ {scope : Nat} {context : TypingContext profile scope},
      WfContextDesc context → ∀ (subject classifier : RawTerm scope),
        Decidable (HasTypeDesc profile context subject classifier)
  /-- Pillar 1b — the GROWN bidirectional compare step: checking against a known-type target is
  decidable given inference + per-subject uniqueness (`decidableCheckOfInferredUniqueAtType`). -/
  checkingDecidableGrownCompare :
    ∀ {scope : Nat} {context : TypingContext profile scope},
      WfContextDesc context →
      ∀ {subject inferredType inferredTypeClassifier targetType : RawTerm scope}
        {targetLevel : LevelExpr} {targetFlag : UniverseFlag},
        HasTypeDescPi profile context subject inferredType →
        HasTypeDescPi profile context inferredType inferredTypeClassifier →
        HasTypeDescPi profile context targetType (universeCodeCell targetLevel targetFlag) →
        (∀ {otherType : RawTerm scope},
          HasTypeDescPi profile context subject otherType → Conv inferredType otherType) →
        Decidable (HasTypeDescPi profile context subject targetType)
  /-- Pillar 1c — the typed-fragment boundary is PROVEN: a reserved-tier generator heads no
  grown-typed cell (the grown conjunct of `reservedTierUntypedByEveryEngine`; the full
  nine-engine conjunction is gated by name alongside). -/
  typedFragmentBoundary :
    ∀ {generator : Generator}, semanticTier generator = .reserved →
      ∀ {scope : Nat} {context : TypingContext profile scope} {subject : RawTerm scope},
        RawTerm.headGenerator subject = generator →
        ∀ classifier : RawTerm scope, ¬ HasTypeDescPi profile context subject classifier
  /-- Pillar 2a — decidable typed `Conv` of well-typed terms over every well-formed context
  (`wfContextDefensibleKernel.convDecidable`). -/
  conversionDecidableConv :
    ∀ {scope : Nat} {context : TypingContext profile scope}
      {leftSubject leftClassifier rightSubject rightClassifier : RawTerm scope},
      WfContextDesc context →
        HasTypeDescPi profile context leftSubject leftClassifier →
          HasTypeDescPi profile context rightSubject rightClassifier →
            Decidable (Conv leftSubject rightSubject)
  /-- Pillar 2b — decidable βη-conversion on the wf fragment
  (`BetaEtaConv.decidableOfWfTyped`). -/
  conversionDecidableBetaEta :
    ∀ {scope : Nat} {context : TypingContext profile scope}
      {leftTerm leftClassifier rightTerm rightClassifier : RawTerm scope},
      WfContextDesc context →
      HasTypeDescPi profile context leftTerm leftClassifier →
      HasTypeDescPi profile context rightTerm rightClassifier →
      Decidable (BetaEtaConv leftTerm rightTerm)
  /-- Pillar 2c — the typed-NbE normalize-and-compare check is SOUND for the full judgmental
  equality with type-directed unit-η and congruence (`checkNbeEqual_sound`, #364). -/
  conversionNbeCheckSound :
    ∀ {scope : Nat} {context : TypingContext profile scope}
      {classifier leftTerm rightTerm : RawTerm scope} {leftFuel rightFuel : Nat}
      {contextWellFormed : WfContextDesc context}
      {leftTyped : HasTypeDescPi profile context leftTerm classifier}
      {rightTyped : HasTypeDescPi profile context rightTerm classifier}
      {classifierLevel : LevelExpr} {classifierFlag : UniverseFlag},
      HasTypeDesc profile context classifier
        (universeCodeCell classifierLevel classifierFlag) →
      HasTypeDescPi.checkNbeEqual leftFuel rightFuel contextWellFormed leftTyped rightTyped
        = true →
      DefEqUnitEtaCong profile context leftTerm rightTerm
  /-- Pillar 3 — the FX0 cross-check: the independent structural re-checker accepts the encoding
  of every wf-typed subject, which is moreover strongly normalizing
  (`FX0CrossCheck.externalVerify_accepts_certified`). -/
  fx0CrossCheckAccepts :
    ∀ {scope : Nat} {context : TypingContext profile scope}
      {subject classifier : RawTerm scope},
      WfContextDesc context →
      HasTypeDescPi profile context subject classifier →
      FX1Poly.FX0CrossCheck.externalVerify
          (FX0Poly.Cert.encode (FX1Poly.FX0Bridge.encodeCell subject))
          (FX1Poly.FX0Bridge.encodeCell subject).budget
        = FX0Poly.CheckVerdict.accepted
      ∧ StepStar.IsStronglyNormalizing subject

/-- **★ The Milestone-A₀ sign-off HOLDS (#464)** — every field is the shipped named carrier:
`HasTypeDesc.decidableOfWellFormed`, `HasTypeDescPi.decidableCheckOfInferredUniqueAtType`,
`reservedTierUntypedByEveryEngine`, `wfContextDefensibleKernel.convDecidable`,
`BetaEtaConv.decidableOfWfTyped`, `HasTypeDescPi.checkNbeEqual_sound`,
`FX0CrossCheck.externalVerify_accepts_certified`.  Zero-axiom; A₀'s named non-claims (O-NORM,
full per-classifier canonicity assembly, grown η-SR breadth, complexity polynomials beyond the
shipped two-tier witnesses, the external non-Lean FX0 implementation) remain non-claims. -/
def milestoneA0SignoffHolds {profile : PolyProfile} : MilestoneA0Signoff profile where
  checkingDecidableFormation wellFormed subject classifier :=
    HasTypeDesc.decidableOfWellFormed wellFormed subject classifier
  checkingDecidableGrownCompare wellFormed :=
    HasTypeDescPi.decidableCheckOfInferredUniqueAtType wellFormed
  typedFragmentBoundary := fun {_generator} reserved {_scope} {_context} {_subject} headEq =>
    (reservedTierUntypedByEveryEngine reserved headEq).1
  conversionDecidableConv := wfContextDefensibleKernel.convDecidable
  conversionDecidableBetaEta contextWellFormed leftTyped rightTyped :=
    BetaEtaConv.decidableOfWfTyped contextWellFormed leftTyped rightTyped
  conversionNbeCheckSound classifierTyped checkPasses :=
    HasTypeDescPi.checkNbeEqual_sound classifierTyped checkPasses
  fx0CrossCheckAccepts contextWellFormed typed :=
    FX1Poly.FX0CrossCheck.externalVerify_accepts_certified contextWellFormed typed

end FX1Poly.Typed

-- ===== MILESTONE-A SPINE (#501) — pillar theorems by name, re-verified =====
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.stronglyNormalizingOfWfContextDesc
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedStronglyNormalizing
#assert_no_axioms FX1Poly.Typed.emptyConsistencyViaCandidateBridge
#assert_no_axioms FX1Poly.Typed.closedBoolCanonicalForms
#assert_no_axioms FX1Poly.Typed.closedNatCanonicalForms
#assert_no_axioms FX1Poly.Typed.HasTypeNativeUnion.closedNormalNatCanonicalForms
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

-- ===== MILESTONE A0 (#464) — the §11.8.12.0 pillar carriers by name, SIGNED OFF =====
#assert_no_axioms FX1Poly.Typed.wfContextDefensibleKernel
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.decidableOfWellFormed
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.decidableCheckOfInferredUniqueAtType
#assert_no_axioms FX1Poly.Typed.reservedTierUntypedByEveryEngine
#assert_no_axioms FX1Poly.Typed.semanticTierReservedSound
#assert_no_axioms FX1Poly.Typed.BetaEtaConv.decidableOfWfTyped
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.checkNbeEqual_sound
#assert_no_axioms FX1Poly.FX0CrossCheck.externalVerify_accepts_certified
-- ★ the positive assembled A0 capstone (#464 closes per §11.8.12.0)
#assert_no_axioms FX1Poly.Typed.milestoneA0SignoffHolds
