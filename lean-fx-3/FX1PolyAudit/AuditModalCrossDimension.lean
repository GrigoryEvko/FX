import FX1PolyAudit.DependencyAudit
import FX1Poly.Modal.ResourceGraded
import FX1Poly.Modal.GradeVector
import FX1Poly.Modal.GradeVectorGeneric
import FX1Poly.Modal.UsageDiscipline
import FX1Poly.Modal.GradedTypingGeneric
import FX1Poly.Modal.GradedGradeExactness
import FX1Poly.Modal.GradeErasureGeneric
import FX1Poly.Modal.GradedWeakeningGeneric
import FX1Poly.Modal.GradedSubstitutionGeneric
import FX1Poly.Modal.GradedSubjectReductionGeneric
import FX1Poly.Modal.GradedCompositionGeneric
import FX1Poly.Modal.GradeSemiringProduct
import FX1Poly.Modal.GradeSemiringMonoidal
import FX1Poly.Modal.GradeSemiringFunctorial
import FX1Poly.Modal.SimpleStrongNormalization
import FX1Poly.Modal.GradedSubstitutionAlgebra
import FX1Poly.Modal.GradedReductionSubstitution
import FX1Poly.Modal.GradedFundamentalTheorem
import FX1Poly.Modal.GradedReductionConfluence
import FX1Poly.Modal.GradedNormalization
import FX1Poly.Modal.ComplexitySemiring
import FX1Poly.Modal.EffectLatticeClassification
import FX1Poly.Modal.OverflowLatticeDimension
import FX1Poly.Modal.PrecisionOverflowCollision
import FX1Poly.Modal.SoundnessCollisionSchema
import FX1Poly.Modal.ThreeWayCollisionClassifiedAsyncSession
import FX1Poly.Modal.FlagshipMultiDimensionSignature
import FX1Poly.Modal.SoundnessCollisionCatalog
import FX1Poly.Modal.SoundnessCollisionCatalogComplete
import FX1Poly.Modal.BoundedJoinSemilatticeUniversal
import FX1Poly.Modal.BoundedJoinSemilatticeProductOrder
import FX1Poly.Modal.UnifiedGradeMonoid
import FX1Poly.Modal.FractionalPermission
import FX1Poly.Modal.ClockDomainLatticeDimension
import FX1Poly.Modal.ProvenanceLatticeDimension
import FX1Poly.Modal.MutationChainLatticeDimension
import FX1Poly.Modal.PreorderDimension
import FX1Poly.Modal.DimensionRepetitionContrast
import FX1Poly.Modal.DimensionMultiplicationContrast
import FX1Poly.Modal.LatticeDistributivityClassification
import FX1Poly.Modal.SessionDualityDimension
import FX1Poly.Modal.SessionCommunication
import FX1Poly.Modal.SelfApplicationUntypable
import FX1Poly.Modal.GradedProgress
import FX1Poly.Modal.GradedEvaluation
import FX1Poly.Modal.GradedLogicalConsistency
import FX1Poly.Modal.VersionCategoryDimension
import FX1Poly.Modal.GradedNormalizerValue

/-! # FX1PolyAudit/AuditModalCrossDimension — modal/dimension-layer zero-axiom gates, shard 4 of 4 (split from the AuditModal monolith for parallel gate elaboration) -/

/-! ## The FIRST cross-dimension comparison (`DimensionRepetitionContrast`) — usage vs security on repetition

The DIM track built each dimension's algebra in isolation; this is the first theorem CONTRASTING two
dimensions' check behaviors.  At the unit `R.one` (`semiringUnits_eq`: usage one = `.one`, security one =
`.classified`), usage `+` is NON-idempotent (`usageAddUnitUnit_eq_omega`: `1+1 = ω ≠ 1` — occurrence
counting, repetition PENALIZED, so `usageRepetitionExceedsLinear`: `ω ≰ 1`) while security `+` IS idempotent
(`securityAddUnitUnit_idempotent`: `classified+classified = classified` — flow join, repetition NOT
penalized, so `securityRepetitionStaysWithinUnit`: `classified ≤ classified`).  usageAndSecurityDifferOn
Repetition: the SAME combine-with-itself operation exceeds the usage bound but stays within the security
bound — composing pointwise in one grade vector (§6.1), each dimension enforces its own discipline
(linearity vs information flow), the algebraic root of §6.8's "the dimensions are NOT orthogonal".  All rfl
over the propext-free enum tables UsageGrade/SecurityGrade .add/.le. -/

#assert_no_axioms FX1Poly.Modal.semiringUnits_eq
#assert_no_axioms FX1Poly.Modal.usageAddUnitUnit_eq_omega
#assert_no_axioms FX1Poly.Modal.usageRepetitionExceedsLinear
#assert_no_axioms FX1Poly.Modal.securityAddUnitUnit_idempotent
#assert_no_axioms FX1Poly.Modal.securityRepetitionStaysWithinUnit
#assert_no_axioms FX1Poly.Modal.usageAndSecurityDifferOnRepetition

/-! ## The MULTIPLICATIVE cross-dimension contrast (`DimensionMultiplicationContrast`) — usage vs security
on the `(R, ×, 1)` monoid + where its unit sits in the order

The multiplicative sibling of `DimensionRepetitionContrast` (which contrasted `+`).  The two dimensions'
MULTIPLICATIVE units sit at OPPOSITE order positions: usage's `×`-unit `1` is SUB-MAXIMAL
(`usageUnitIsSubMaximal`: `1 ≤ ω ∧ 1 ≠ ω` — unrestricted use strictly exceeds linear, usage GRANTS a
beyond-unit `@[copy]` capability) while security's `×`-unit `classified` is MAXIMAL
(`securityUnitIsMaximal`: `classified ≰ unclassified`, `unclassified ≤ classified` — the top secrecy, no
"beyond classified").  The `×`-annihilator (= additive `0`, the universal semiring law `r × 0 = 0`)
differs in MEANING: usage's `0` is erased/ghost (`usageMulAnnihilatesAtZero`: `0 × ω = 0`, the §1.5
erasure / §6.2 `1/ω = 0` context division) while security's `0` is `unclassified`/public
(`securityMulAnnihilatesAtUnclassified`: `classified × unclassified = unclassified` — "ghost computation
on a secret leaks nothing", §6.3 dim 5).  usageAndSecurityDifferOnUnitMaximality: composing pointwise in
one grade vector (§6.1), each dimension's `(R, ×, 1)` relates to its order differently — usage's unit
admits a strict over-grade, security's does not — so the 21-dim product is heterogeneous on `×`/`≤` too
(§6.8).  All rfl/decide over the propext-free enum tables UsageGrade/SecurityGrade .mul/.le. -/

#assert_no_axioms FX1Poly.Modal.usageUnitIsSubMaximal
#assert_no_axioms FX1Poly.Modal.securityUnitIsMaximal
#assert_no_axioms FX1Poly.Modal.usageMulAnnihilatesAtZero
#assert_no_axioms FX1Poly.Modal.securityMulAnnihilatesAtUnclassified
#assert_no_axioms FX1Poly.Modal.usageAndSecurityDifferOnUnitMaximality

/-! ## The chain-vs-diamond DISTRIBUTIVITY dichotomy (`LatticeDistributivityClassification`)

The structural capstone of the lattice-family work: classify FX's bounded-lattice dimensions by distributivity,
the deepest lattice-theoretic invariant.  MutationGrade.meet (the chain MIN, dual to the shipped chain-max join)
+ meet-semilattice laws (comm/assoc/idempotent) + the two absorption laws (mutationJoinMeetAbsorb /
mutationMeetJoinAbsorb) establish the mutation 4-chain is a genuine bounded LATTICE.  mutationIsDistributive: the
4-chain satisfies `a ∧ (b ∨ c) = (a ∧ b) ∨ (a ∧ c)` (chains are always distributive; min distributes over max,
64-leaf cases<;>rfl — a non-trivial chain, not a 2-element triviality).  ★ mutationChainDistributesButOverflow
DiamondDoesNot: the dichotomy — mutation distributes but the overflow diamond M3 does NOT (citing the shipped
overflowIsNonDistributive).  Among FX's lattice dimensions, distributivity tracks the order shape exactly: the
chains are distributive, only the antichain-bearing diamond M3 is non-distributive — §6.8 heterogeneity at the
deepest lattice level.  All zero-axiom (cases<;>rfl + the shipped overflowIsNonDistributive). -/

#assert_no_axioms FX1Poly.Modal.MutationGrade.meet
#assert_no_axioms FX1Poly.Modal.mutationMeet_comm
#assert_no_axioms FX1Poly.Modal.mutationMeet_assoc
#assert_no_axioms FX1Poly.Modal.mutationMeet_idempotent
#assert_no_axioms FX1Poly.Modal.mutationJoinMeetAbsorb
#assert_no_axioms FX1Poly.Modal.mutationMeetJoinAbsorb
#assert_no_axioms FX1Poly.Modal.mutationIsDistributive
#assert_no_axioms FX1Poly.Modal.mutationChainDistributesButOverflowDiamondDoesNot

/-! ## The session-type dimension (§6.3 Dim 6 / §11) — the first INVOLUTION-structured dimension
(`SessionDualityDimension`)

Every prior dimension is an order/algebra (semiring / lattice / PCM / preorder); the PROTOCOL dimension is
structurally different — its defining operation is DUALITY, an INVOLUTION (the protocol of the opposite
endpoint), not a binary combine.  SessionType (5-ctor: endSession / send / receive / selectChoice / branchOffer)
+ SessionType.dual (§11.2: send↔receive, select↔branch, end self-dual, payload-agnostic) + the 5 per-ctor duality
equations (rfl). ★ SessionType.dual_involutive: dual(dual S)=S (the headline — the structural signature of Dim 6;
a channel's two endpoints are mutually dual, §11.2). SessionType.dual_injective: duality is INJECTIVE hence a
BIJECTION on the protocol space (involution ⟹ bijective). selfDual_iff_endSession: endSession is the UNIQUE
self-dual protocol (any communicating protocol's head ctor flips under duality, so it has a DISTINCT dual). ★
sessionDualityIsInvolutionButNotIdentity: an involution but NOT the identity (a send is not its own dual) — the
genuine reversal distinguishing this dimension from the order/algebra ones. Complements L1-SESSION (#959, the
§27.2 linearity-mechanism witness) with the session-type ALGEBRA. All zero-axiom (plain-inductive recursor +
rfl + congrArg + noConfusion + decide). -/

#assert_no_axioms FX1Poly.Modal.SessionType
#assert_no_axioms FX1Poly.Modal.SessionType.dual
#assert_no_axioms FX1Poly.Modal.dual_endSession
#assert_no_axioms FX1Poly.Modal.dual_send
#assert_no_axioms FX1Poly.Modal.dual_receive
#assert_no_axioms FX1Poly.Modal.dual_selectChoice
#assert_no_axioms FX1Poly.Modal.dual_branchOffer
#assert_no_axioms FX1Poly.Modal.SessionType.dual_involutive
#assert_no_axioms FX1Poly.Modal.SessionType.dual_injective
#assert_no_axioms FX1Poly.Modal.selfDual_iff_endSession
#assert_no_axioms FX1Poly.Modal.sessionDualityIsInvolutionButNotIdentity

/-! ## Session-type OPERATIONAL semantics (§11.3 / §11.11) — communication preserves duality + no deadlock
(`SessionCommunication`)

The dynamics over the duality algebra. CommStep (6-arm: matched send/receive exchange + select/branch resolution
left/right + the mirror) is one synchronized communication on a PAIR of endpoints (a channel = a dual pair,
§11.2). ★ CommStep.preservesDuality: session FIDELITY — a DUAL pair steps to a DUAL pair (the core safety:
well-formed channels never reach a mismatched state; the dual hypothesis forces matched continuations, by cases +
injection auto-subst). dualPairProgresses: a non-end dual channel can always step. dualChannelProgressesOrIsDone:
the PROGRESS dichotomy — a dual channel either steps or IS the terminal (end,end), so no stuck states except
completion (§11.11 deadlock-freedom for a single channel). endChannelIsTerminal: (end,end) has no step.
concreteChannelStep: non-vacuity (send 0.end / receive 0.end actually exchanges). Builds on firing-82's
SessionDualityDimension; complements L1-SESSION (#959). All zero-axiom (inductive Prop relation + cases +
injection + noConfusion). -/

#assert_no_axioms FX1Poly.Modal.CommStep
#assert_no_axioms FX1Poly.Modal.CommStep.preservesDuality
#assert_no_axioms FX1Poly.Modal.dualPairProgresses
#assert_no_axioms FX1Poly.Modal.dualChannelProgressesOrIsDone
#assert_no_axioms FX1Poly.Modal.endChannelIsTerminal
#assert_no_axioms FX1Poly.Modal.concreteChannelStep
-- WHY DUALITY IS NECESSARY (SessionCommunication, §27.2-flavored necessity completing the session arc): the
-- complement of dualChannelProgressesOrIsDone — drop the duality hypothesis and deadlock returns. A mismatched
-- send/send channel (send 0.end, send 0.end) is STUCK (sendSendStuck — no CommStep arm matches two senders) yet
-- not terminal, and exactly NON-dual (sendSendIsNotDual). nonDualChannelDeadlocks: ∃ a non-dual stuck non-terminal
-- config. dualPartnerFixesTheMismatchedDeadlock: the SAME first endpoint deadlocks with a mismatched partner but
-- COMMUNICATES with its dual partner (via concreteChannelStep) — duality IS the fix. ★ dualityIsNecessaryForDead
-- lockFreedom: dual channels never deadlock but a non-dual one can, so the duality hypothesis is ESSENTIAL (the
-- session analogue of SN-NECESSITY #950: the discipline rules out the bad behavior). Caps the session arc (82
-- algebra / 83 safety / 84 necessity). All zero-axiom (cases-impossibility + decide + cite).
#assert_no_axioms FX1Poly.Modal.sendSendStuck
#assert_no_axioms FX1Poly.Modal.sendSendIsNotDual
#assert_no_axioms FX1Poly.Modal.nonDualChannelDeadlocks
#assert_no_axioms FX1Poly.Modal.dualPartnerFixesTheMismatchedDeadlock
#assert_no_axioms FX1Poly.Modal.dualityIsNecessaryForDeadlockFreedom

/-! ## §6.3 Dim 8 / §1.1 provenance dimension — the FIRST INFINITE FULL LATTICE M_omega
(`ProvenanceLatticeDimension`)

Combines the two prior lattice advances: clock shipped the INFINITE carrier (but join-only); overflow shipped
the FULL lattice (but a FINITE M3).  Provenance `{opaqueOrigin (bottom), source (originId : Nat), unknown (top)}`
is the first lattice BOTH infinite AND full — the kernel's first concrete M_omega (infinitely many origin atoms,
all joining to `unknown` and meeting to `opaqueOrigin`).  The `source`-`source` join/meet laws reuse the clock
`Nat.beq` facts; the meet (`provenanceMeet_comm`/`_assoc`) + absorption (`provenanceJoinMeetAbsorb`/`provenance
MeetJoinAbsorb`) upgrade the join-semilattice to a full lattice; `provenanceIsNonDistributive` is the concrete
M3-sublattice failure (M_omega contains M3).  The GENUINELY-NEW SEMANTIC content: unlike clock's `crossDomain
Error` (a type error), provenance's `unknown` is a LEGITIMATE value a sink rejects — `isKnownSource` accepts
`source _`, rejects `unknown`/`opaqueOrigin`, and `provenanceKnownSourceLostOnDistinctMerge` shows the
known-origin property is LOST when two distinct origins merge (the §25.5 supply-chain guarantee).  `provenance
ClockProductIsLawful` is the FIRST composition of TWO infinite-antichain dimensions.  All propext-free; general
symbolic modularity deferred (the concrete non-distributivity pins it as genuinely non-distributive). -/

#assert_no_axioms FX1Poly.Modal.ProvenanceGrade.join
#assert_no_axioms FX1Poly.Modal.ProvenanceGrade.meet
#assert_no_axioms FX1Poly.Modal.provenanceJoinSourceWithSelf
#assert_no_axioms FX1Poly.Modal.provenanceLattice
#assert_no_axioms FX1Poly.Modal.provenanceJoinCommutes
#assert_no_axioms FX1Poly.Modal.provenanceJoinAssociates
#assert_no_axioms FX1Poly.Modal.provenanceIsLawfulBoundedJoinSemilattice
#assert_no_axioms FX1Poly.Modal.provenanceSourceIncomparableOfDistinct
#assert_no_axioms FX1Poly.Modal.provenanceSource01Incomparable
#assert_no_axioms FX1Poly.Modal.provenanceOpaqueIsLeast
#assert_no_axioms FX1Poly.Modal.provenanceUnknownIsGreatest
#assert_no_axioms FX1Poly.Modal.provenanceMeetSourceWithSelf
#assert_no_axioms FX1Poly.Modal.provenanceMeet_comm
#assert_no_axioms FX1Poly.Modal.provenanceMeet_assoc
#assert_no_axioms FX1Poly.Modal.provenanceJoinMeetAbsorb
#assert_no_axioms FX1Poly.Modal.provenanceMeetJoinAbsorb
#assert_no_axioms FX1Poly.Modal.provenanceMeetDistinctIsOpaque
#assert_no_axioms FX1Poly.Modal.provenanceIsNonDistributive
#assert_no_axioms FX1Poly.Modal.ProvenanceGrade.isKnownSource
#assert_no_axioms FX1Poly.Modal.provenanceKnownSourceAccepts
#assert_no_axioms FX1Poly.Modal.provenanceUnknownRejected
#assert_no_axioms FX1Poly.Modal.provenanceOpaqueRejected
#assert_no_axioms FX1Poly.Modal.provenanceJoinDistinctSourcesIsUnknown
#assert_no_axioms FX1Poly.Modal.provenanceKnownSourceLostOnDistinctMerge
#assert_no_axioms FX1Poly.Modal.provenanceClockProductLattice
#assert_no_axioms FX1Poly.Modal.provenanceClockProductIsLawful

/-! ### Self-application untypability — the occurs-check that excludes `Ω` from the typed calculus

`λx. x x` has no `HasGradeOver R` derivation in any graded dimension: self-application would force the
binder type `D = (D -> codomain)`, impossible for the finite `GTypeOver R`.  This is the metatheoretic
reason the typed graded calculus is SN despite `Ω` diverging untyped (#950/#960) — the SR-breaking term
is excluded at the typing layer.  Generic over `R`, instantiated at usage + security. -/

#assert_no_axioms FX1Poly.Modal.gTypeOver_ne_self_arrow
#assert_no_axioms FX1Poly.Modal.selfApplicationLambda_untypableOver
#assert_no_axioms FX1Poly.Modal.omegaCombinator_untypableOver
#assert_no_axioms FX1Poly.Modal.usageSelfApp_untypable
#assert_no_axioms FX1Poly.Modal.securitySelfApp_untypable

/-! ### Progress / canonical forms — the second half of type safety for the graded engine

A closed well-typed `HasGradeOver R` term is never stuck: it β-reduces or is a `.lam` value
(`closedWellTypedProgress`), the structural core being canonical forms (a closed normal form is a
`.lam`, `closedNormalFormIsLam`).  With β SR (preservation, #905/#906) and SN (#878) this completes the
safety kit; base type has no closed values (`closedBaseTypeAlwaysSteps`).  Generic over every graded
dimension. -/

#assert_no_axioms FX1Poly.Modal.closedNormalFormIsLam
#assert_no_axioms FX1Poly.Modal.closedWellTypedProgress
#assert_no_axioms FX1Poly.Modal.closedBaseTypeAlwaysSteps
#assert_no_axioms FX1Poly.Modal.usageLinearIdentity_isValue

/-! ### Full-β subject reduction + evaluation — the graded type-safety capstone

Lifts SR from root-β to the FULL congruence-closed β-reduction (`hasGradeOver_reducesPreservation`,
grades exact) + its `ReducesStar` closure, and combines preservation + progress + SN into EVALUATION:
every closed well-typed term β-reduces to a `.lam` value (`closedReducesToLam`).  Well-typed graded
programs evaluate — generic over every dimension. -/

#assert_no_axioms FX1Poly.Modal.hasGradeOver_reducesPreservation
#assert_no_axioms FX1Poly.Modal.hasGradeOver_reducesStarPreservation
#assert_no_axioms FX1Poly.Modal.closedReducesToLam
#assert_no_axioms FX1Poly.Modal.usageLinearIdentity_reducesToLam

/-! ### Logical consistency — the Curry-Howard conclusion of the graded type-safety story

Reading `GTypeOver R` as a proposition and `HasGradeOver R [] _ term T` as a closed proof of `T`, the
graded calculus is CONSISTENT: its atomic proposition `GTypeOver.base` has no closed proof
(`closedBaseTypeUninhabited`), over EVERY dimension `R` at once.  A closed base-typed term would
evaluate to a `.lam` (`closedReducesToLam`), which stays base-typed by SR-over-↝* yet a `.lam` is only
arrow-typed (`invertLam`) — a constructor clash.  `closedTermIsArrowTyped` is the positive reading
(every closed inhabitant is a function); `usageBaseTypeUninhabited` instantiates at the linear
`{0,1,ω}` semiring.  The graded analogue of the grown SN-050 `EmptyType` consistency — atom vs
dedicated empty type. -/

#assert_no_axioms FX1Poly.Modal.closedBaseTypeUninhabited
#assert_no_axioms FX1Poly.Modal.closedTermIsArrowTyped
#assert_no_axioms FX1Poly.Modal.usageBaseTypeUninhabited

/-! ### Version dimension — the first CATEGORY-structured dimension (§6.3 Tier V / §15)

Version labels + total migration adapters form a genuine category: composition + identity + the
category laws (`Migration.compose_assoc`/`identity_compose`/`compose_identity`), `refines` as the induced
reachability preorder, the §14.1 UserApi v1→v2→v3 chain, the §14.2 add/remove retraction pair, and
non-thin hom-sets (proof-relevant adapters).  The first dimension whose grades carry composable morphism
DATA, not a bare order. -/

#assert_no_axioms FX1Poly.Modal.Migration.identity
#assert_no_axioms FX1Poly.Modal.Migration.compose
#assert_no_axioms FX1Poly.Modal.Migration.identity_compose
#assert_no_axioms FX1Poly.Modal.Migration.compose_identity
#assert_no_axioms FX1Poly.Modal.Migration.compose_assoc
#assert_no_axioms FX1Poly.Modal.migrateAddField
#assert_no_axioms FX1Poly.Modal.migrateUserV1toV3_apply
#assert_no_axioms FX1Poly.Modal.Refines.refl
#assert_no_axioms FX1Poly.Modal.Refines.trans
#assert_no_axioms FX1Poly.Modal.userApiV3_refines_v1
#assert_no_axioms FX1Poly.Modal.migrateDropField_addField
#assert_no_axioms FX1Poly.Modal.migrateAddField_injective_inDefault

/-! ### The verified normalizer evaluates well-typed terms to values

`GradedLambda.normalize` computes a `.lam` value for every closed well-typed term
(`closedNormalizesToLam`) — the executable payoff of progress + full-β SR + SN; plus typed evaluation
determinism (`closedConvertibleSameValue`) and the usage/security orthogonal-composition smokes. -/

#assert_no_axioms FX1Poly.Modal.closedNormalizesToLam
#assert_no_axioms FX1Poly.Modal.closedConvertibleSameValue
#assert_no_axioms FX1Poly.Modal.usageClosedNormalizesToLam
#assert_no_axioms FX1Poly.Modal.securityClosedNormalizesToLam

/-! ## PrecisionOverflowCollision — the FIRST §6.8 CROSS-DIMENSION soundness collision (`decimal × overflow(wrap)`)

§6.8 (the "dimensions are NOT orthogonal" catalog, distinct from the §27.2 known-unsoundness corpus) lists
`decimal × overflow(wrap)` among the cross-dimension collisions.  Built on the shipped `OverflowGrade`:
`PrecisionGrade {exact,inexact}` + `OverflowGrade.isExactnessPreserving` (exact/trap true; wrap/saturate/conflict
false) + `forcedPrecision` (dual view, coherent via `forcedPrecision_exactPrecision_iff_isExactnessPreserving`).
`IsJointlyConsistent precision overflow := precision = exact → overflow.isExactnessPreserving`.  THE COLLISION:
`exactPrecisionCollidesWithWrapOverflow` (★) — exact precision (decimal) and wrap overflow are NOT jointly
consistent (wrap silently yields a `mod 2^n` value ≠ the true result); + the `saturate` twin.  SPECIFIC, not
blanket: exact precision composes with the exactness-preserving modes (exact/trap), inexact precision with every
mode.  FULL characterization: `exactPrecisionCollision_iff_notPreserving` (collision set = exactly the
non-preserving modes) + `isJointlyConsistent_iff` (consistent ↔ inexact ∨ preserving).  The §6.8 thesis made
concrete: precision and overflow cannot be chosen independently.  All zero-axiom (Bool.noConfusion /
PrecisionGrade.noConfusion / cases-rfl, no propext). -/

#assert_no_axioms FX1Poly.Modal.OverflowGrade.isExactnessPreserving
#assert_no_axioms FX1Poly.Modal.OverflowGrade.forcedPrecision
#assert_no_axioms FX1Poly.Modal.forcedPrecision_exactPrecision_iff_isExactnessPreserving
#assert_no_axioms FX1Poly.Modal.exactPrecisionCollidesWithWrapOverflow
#assert_no_axioms FX1Poly.Modal.exactPrecisionCollidesWithSaturateOverflow
#assert_no_axioms FX1Poly.Modal.exactPrecisionConsistentWithExactOverflow
#assert_no_axioms FX1Poly.Modal.exactPrecisionConsistentWithTrapOverflow
#assert_no_axioms FX1Poly.Modal.inexactPrecisionConsistentWithEveryOverflow
#assert_no_axioms FX1Poly.Modal.exactPrecisionCollision_iff_notPreserving
#assert_no_axioms FX1Poly.Modal.isJointlyConsistent_iff

/-! ## SoundnessCollisionSchema — the §6.8 collision FORM abstracted; two collisions as ONE schema

The §6.8 catalog is instances of one pattern: a strong GUARANTEE-demand meeting a CAPABILITY that fails to
preserve the invariant.  SoundnessCollisionSchema (Demand/Capability/isStrongDemand/preservesInvariant) +
IsConsistent (strongDemand ⟹ preserved) + the generic notConsistent_iff (collision ⟺ strong ∧ ¬preserving) /
consistent_iff, proved once via Bool helpers notImplies_iff/implies_iff.  INSTANCE 1 decimalOverflowSchema
RECOVERS #1021 (decimalOverflowSchema_recovers_collision) and decimalOverflowSchema_consistent_iff_jointly
Consistent proves the schema SUBSUMES the bespoke IsJointlyConsistent (via isExact_eq_true_iff).  INSTANCE 2 (NEW)
monotonicConcurrentSchema over the shipped MutationGrade chain: concurrentCollidesWithMonotonic (★) — monotonic
mutation is unsound under unsynchronized concurrent access (out-of-order commits break the forward-only
invariant) + appendOnly/readWrite twins (all need sequencing); concurrentConsistentWithImmutable (read-only safe);
sequentialConsistentWithEveryMutation (no demand → no collision).  PAYOFF: two §6.8 collisions across four
dimensions (precision/overflow/mutation/concurrency) are the SAME theorem twice.  All zero-axiom (cases-Bool +
noConfusion + (notConsistent_iff _ _).mpr ⟨rfl,rfl⟩). -/

#assert_no_axioms FX1Poly.Modal.notImplies_iff
#assert_no_axioms FX1Poly.Modal.implies_iff
#assert_no_axioms FX1Poly.Modal.SoundnessCollisionSchema.IsConsistent
#assert_no_axioms FX1Poly.Modal.SoundnessCollisionSchema.notConsistent_iff
#assert_no_axioms FX1Poly.Modal.SoundnessCollisionSchema.consistent_iff
#assert_no_axioms FX1Poly.Modal.PrecisionGrade.isExact
#assert_no_axioms FX1Poly.Modal.decimalOverflowSchema
#assert_no_axioms FX1Poly.Modal.decimalOverflowSchema_recovers_collision
#assert_no_axioms FX1Poly.Modal.isExact_eq_true_iff
#assert_no_axioms FX1Poly.Modal.decimalOverflowSchema_consistent_iff_jointlyConsistent
#assert_no_axioms FX1Poly.Modal.ConcurrencyGrade.isConcurrent
#assert_no_axioms FX1Poly.Modal.MutationGrade.isConcurrencySafe
#assert_no_axioms FX1Poly.Modal.monotonicConcurrentSchema
#assert_no_axioms FX1Poly.Modal.concurrentCollidesWithMonotonic
#assert_no_axioms FX1Poly.Modal.concurrentCollidesWithAppendOnly
#assert_no_axioms FX1Poly.Modal.concurrentCollidesWithReadWrite
#assert_no_axioms FX1Poly.Modal.concurrentConsistentWithImmutable
#assert_no_axioms FX1Poly.Modal.sequentialConsistentWithEveryMutation

/-! ## ThreeWayCollisionClassifiedAsyncSession — §6.8's genuinely THREE-WAY collision (irreducible to any pair)

§6.8's catalog is eight TWO-WAY collisions (each a single dimension pair, captured by SoundnessCollisionSchema
#1022) PLUS one genuinely THREE-WAY collision: classified × async × session (a classified value's ordering leaks
through async session interleaving). IsClassifiedAsyncSessionAdmissible (c a s : Bool) := ¬(c ∧ a ∧ s). ★
classifiedAsyncSessionCollision: ¬admissible(true,true,true). The HEADLINE structural fact —
classifiedAsyncSessionIrreducible: each PAIR (third capability withheld) IS admissible (true,true,false /
true,false,true / false,true,true), so NO proper subset collides — the collision is genuinely 3-way, unlike the
2-way #1021/#1022 which collide on a single pair (no SoundnessCollisionSchema over any pair captures it).
isAdmissible_iff: admissible ↔ ≥1 capability withheld (De Morgan, cases + Bool.noConfusion). Spans §6.8
structurally: 2-way reducible + this 3-way irreducible. All zero-axiom. -/

#assert_no_axioms FX1Poly.Modal.IsClassifiedAsyncSessionAdmissible
#assert_no_axioms FX1Poly.Modal.classifiedAsyncSessionCollision
#assert_no_axioms FX1Poly.Modal.classifiedAsync_admissibleWithoutSession
#assert_no_axioms FX1Poly.Modal.classifiedSession_admissibleWithoutAsync
#assert_no_axioms FX1Poly.Modal.asyncSession_admissibleWithoutClassified
#assert_no_axioms FX1Poly.Modal.classifiedAsyncSessionIrreducible
#assert_no_axioms FX1Poly.Modal.isAdmissible_iff

/-! ### §1.3 flagship `encrypt_and_send` — jointly §6.8-admissible multi-dimension grade configuration
    (#1027 DIM-FLAGSHIP, FlagshipMultiDimensionSignature.lean)

The POSITIVE counterpart to the §6.8 collision corpus: a real multi-dimension signature lands in the
admissible region across every relevant collision at once. IsImplicitFlowAdmissible REFINES #1026's
co-occurrence 3-way collision per §12.2 (the collision fires only when the classified value CONTROLS
the async session scheduling, not when it merely co-occurs): encryptAndSendImplicitFlowAdmissible
admits the flagship (secret flows to CT encryption, not scheduling); secretControlsSchedulingCollision
keeps the genuine attack rejected; implicitFlowAdmissible_ofCoOccurrenceAdmissible = soundness of the
refinement; flagshipDistinguishesModels = it is strictly more permissive on the flagship itself.
encryptAndSendGradeMonoidIsLawful = the concrete usage×security×effect 3-factor grade vector is lawful
(free from productIsLawful); encryptAndSendJointlyAdmissible (★) = the signature satisfies the 3-way
implicit-flow + monotonic×concurrent + decimal×overflow constraints SIMULTANEOUSLY. All zero-axiom
(Bool.noConfusion / structure projections / shipped productIsLawful + sequentialConsistentWithEvery-
Mutation). -/

#assert_no_axioms FX1Poly.Modal.IsImplicitFlowAdmissible
#assert_no_axioms FX1Poly.Modal.encryptAndSendImplicitFlowAdmissible
#assert_no_axioms FX1Poly.Modal.secretControlsSchedulingCollision
#assert_no_axioms FX1Poly.Modal.implicitFlowAdmissible_ofCoOccurrenceAdmissible
#assert_no_axioms FX1Poly.Modal.flagshipDistinguishesModels
#assert_no_axioms FX1Poly.Modal.encryptAndSendGradeMonoidIsLawful
#assert_no_axioms FX1Poly.Modal.encryptAndSendKeyGrade_combine_identity
#assert_no_axioms FX1Poly.Modal.encryptAndSendMutationConcurrencyConsistent
#assert_no_axioms FX1Poly.Modal.encryptAndSendPrecisionOverflowConsistent
#assert_no_axioms FX1Poly.Modal.encryptAndSendJointlyAdmissible

/-! ### §6.8 collision catalog — completed + classified into co-occurrence vs scoping-refined
    (#1028 DIM-COLLISION-CATALOG, SoundnessCollisionCatalog.lean)

Generalizes #1027's implicit-flow insight into a whole structural CLASS. ghost×runtime = the clean
CO-OCCURRENCE entry (ghostObservedAtRuntimeCollision = grade-0 observed at runtime collides
unconditionally; runtimePresentValueObservable + unobservedGhostConsistent pin the specificity).
borrow×Async + borrow×unscoped-spawn = SCOPING-REFINED (the demand is the ESCAPE control, not presence):
borrowEscapeUnderAsyncCollision / borrowEscapeIntoUnscopedSpawnCollision collide, but confinedBorrowUnder
AsyncConsistent / borrowIntoScopedSpawnConsistent show a CONFINED borrow co-occurs soundly (= why
encrypt_and_send borrows under async, #1027). ★ catalogHasTwoCollisionClasses = the structural dichotomy
(co-occurrence collides on joint presence; scoping-refined is consistent on joint presence + respected
scope). All SoundnessCollisionSchema instances, zero-axiom (notConsistent_iff.mpr ⟨rfl,rfl⟩ /
Bool.noConfusion / fun _ => rfl). -/

#assert_no_axioms FX1Poly.Modal.ghostObservedAtRuntimeCollision
#assert_no_axioms FX1Poly.Modal.runtimePresentValueObservable
#assert_no_axioms FX1Poly.Modal.unobservedGhostConsistent
#assert_no_axioms FX1Poly.Modal.borrowEscapeUnderAsyncCollision
#assert_no_axioms FX1Poly.Modal.confinedBorrowUnderAsyncConsistent
#assert_no_axioms FX1Poly.Modal.borrowEscapeIntoUnscopedSpawnCollision
#assert_no_axioms FX1Poly.Modal.borrowIntoScopedSpawnConsistent
#assert_no_axioms FX1Poly.Modal.catalogHasTwoCollisionClasses

/-! ### §6.8 collision catalog COMPLETE — the last 3 entries (#1032 DIM-COLLISION-CATALOG-COMPLETE,
    SoundnessCollisionCatalogComplete.lean)

The final three §6.8 entries, all control-refined: CT×Async (constantTimeCollidesWithSecretDependentAsync +
constantTimeConsistentWithSecretIndependentAsync + variableTimeConsistentWithAnyAsync), classified×Fail
(secretControlledFailureCollidesWithObservableFailure + secretControlledFailureConsistentWithClassifiedFailure +
secretIndependentFailureConsistentWithAnyObservability), CT×Fail-on-secret (constantTimeCollidesWithSecret
DependentFailure + constantTimeConsistentWithSecretIndependentFailure). ★ sec68RemainingCatalogControlRefined =
all three co-occur soundly when the control is withheld. Completes the entire 9-entry §6.8 catalog (3 co-occurrence
+ 6 control-refined). All SoundnessCollisionSchema instances, zero-axiom (notConsistent_iff.mpr ⟨rfl,rfl⟩ /
Bool.noConfusion / fun _ => rfl). -/

#assert_no_axioms FX1Poly.Modal.constantTimeCollidesWithSecretDependentAsync
#assert_no_axioms FX1Poly.Modal.constantTimeConsistentWithSecretIndependentAsync
#assert_no_axioms FX1Poly.Modal.variableTimeConsistentWithAnyAsync
#assert_no_axioms FX1Poly.Modal.secretControlledFailureCollidesWithObservableFailure
#assert_no_axioms FX1Poly.Modal.secretControlledFailureConsistentWithClassifiedFailure
#assert_no_axioms FX1Poly.Modal.secretIndependentFailureConsistentWithAnyObservability
#assert_no_axioms FX1Poly.Modal.constantTimeCollidesWithSecretDependentFailure
#assert_no_axioms FX1Poly.Modal.constantTimeConsistentWithSecretIndependentFailure
#assert_no_axioms FX1Poly.Modal.sec68RemainingCatalogControlRefined
