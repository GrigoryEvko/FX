import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.CellSort
import FX1Poly.Core.GeneratorTagRoundTrip
import FX1Poly.Core.GeneratorFinitePolygraph
import FX1Poly.Core.GeneratorPolygraphMap
import FX1Poly.Core.GeneratorRedexHead
import FX1Poly.Core.GeneratorRedexHeadSoundness
import FX1Poly.Core.RawCellWordEncoding
import FX1Poly.Core.StepRewriteRuleMap
import FX1Poly.Core.StepWordRewriteSoundness
import FX1Poly.Core.StepWordRewriteEquivariance
import FX1Poly.Core.ConvWordJoinableBridge
import FX1Poly.Core.BetaEtaWordSystem
import FX1Poly.Core.MultisetOrder
import FX1Poly.Core.TerminationOrders
import FX1Poly.Core.RecursivePathOrder
import FX1Poly.Core.RecursiveEliminatorTermination
import FX1Poly.Core.RecursivePathOrderInductive
import FX1Poly.Core.RawIotaRpoBridge
import FX1Poly.Core.RawIotaRpoAssembly
import FX1Poly.Core.RawIotaFullStepSN
import FX1Poly.Core.EraseToRoseRenameInvariant
import FX1Poly.Core.EtaRpoEmbedding
import FX1Poly.Core.RawIotaEtaFullStepSN
import FX1Poly.Typed.RawIotaEtaOperationalSN
import FX1Poly.Typed.MilestoneAParityMatrix
import FX1Poly.Core.Newman
import FX1Poly.Core.DiamondConfluence
import FX1Poly.Core.StepParallelConfluence
import FX1Poly.Core.TakahashiTriangle
import FX1Poly.Core.ParallelReduction
import FX1Poly.Core.CompleteDevelopment
import FX1Poly.Core.ParStepSubstRename
import FX1Poly.Core.ParStepSubstPointwise
import FX1Poly.Core.ParStepInversion
import FX1Poly.Core.ParStepTriangle
import FX1Poly.Core.RawConfluence
import FX1Poly.Core.CommutationConfluence
import FX1Poly.Core.DeterministicConfluence
import FX1Poly.Core.KripkeReducibilityCandidate
import FX1Poly.Core.ReducibleTypeClosed
import FX1Poly.Core.PointwiseIffAlgebra
import FX1Poly.Core.StratifiedReducibleLevelCongr
import FX1Poly.Core.StratifiedReducibleMemberNeutral
import FX1Poly.Core.StratifiedReducibleMemberStepClosure
import FX1Poly.Core.StrongNormalizationSubterm
import FX1Poly.Core.StrongNormalizationCodeFormers
import FX1Poly.Core.StrongNormalizationModalEliminators
import FX1Poly.Core.StrongNormalizationUniverseModeBridges
import FX1Poly.Core.StrongNormalizationNatElim
import FX1Poly.Core.StrongNormalizationListElim
import FX1Poly.Core.StrongNormalizationMatch
import FX1Poly.Core.StrongNormalizationLinearFormers
import FX1Poly.Core.NatElimValueReducibility
import FX1Poly.Core.NatElimValueMember
import FX1Poly.Core.NatElimNeutralScrutineeMember
import FX1Poly.Core.RecursorReducibleScrutineeMember
import FX1Poly.Core.DataEliminatorReducibleScrutineeMember
import FX1Poly.Core.ListElimNeutralScrutineeMember
import FX1Poly.Core.DirectIotaEliminatorNeutralScrutineeMember
import FX1Poly.Core.MatchEliminatorNeutralScrutineeMember
import FX1Poly.Core.NeutralEliminatorMemberSmoke
import FX1Poly.Core.ListElimValueReducibility
import FX1Poly.Core.ListElimValueMember
import FX1Poly.Core.ApplicationStrongNormalizationForward
import FX1Poly.Core.BetaRedexStrongNormalization
import FX1Poly.Core.ListOptionIdCodeUniverseMembership
import FX1Poly.Core.EitherEquivCodeUniverseMembership
import FX1Poly.Core.LinearFormerUniverseMembership
import FX1Poly.Core.StrongNormalizationUnion
import FX1Poly.Core.StrongNormalizationBetaEtaUnion
import FX1Poly.Core.EtaPostponementOverBeta
import FX1Poly.Core.ModalEliminatorReducibility
import FX1Poly.Core.UniverseModeBridgeReducibility
import FX1Poly.Core.RawTermSubstLiftWeaken
import FX1Poly.Typed.ConvergentCanonicityBoundary
import FX1Poly.Core.SconingTaitCrossLeg
import FX1Poly.Core.SconingSNObjectUnique
import FX1Poly.Core.EtaRootClassifier
import FX1Poly.Core.ConvRenameReflection
import FX1Poly.Core.RawTermRenameInjective
import FX1Poly.Core.ConvRenameEquivariance
import FX1Poly.Core.FireRootEtaRedex
import FX1Poly.Core.NormalizeBetaEta
import FX1Poly.Typed.RawBetaNotRpoOrientable
import FX1Poly.Typed.SnTriangulationBundle
import FX1Poly.Typed.HonestCapstoneSignoff

/-! # FX1PolyAudit/AuditCoreUniverseMembership — core reduction-layer zero-axiom gates, shard 03 of 3 (split from the AuditCore monolith for parallel gate elaboration) -/

-- Universe membership of the one/three-child data-type codes: list/option/id codes are reducible members of
-- Type@levelExpr, each a direct dataFormerInUniverse instance fed the per-former SN combinator + the uniform
-- weak-head-normal (only rootIota could unify, killed by cases iotaStep) + root-distinctness from
-- piTyCode/universeCode.
#assert_no_axioms FX1Poly.Core.listCode_isReducibleMemberOfUniverse
#assert_no_axioms FX1Poly.Core.optionCode_isReducibleMemberOfUniverse
#assert_no_axioms FX1Poly.Core.idCode_isReducibleMemberOfUniverse
-- The two-child either/equiv codes complete the data-code family at the stratified layer, reusing the
-- two-child SN combinators (eitherCode/equivCode SN + Step.from_* inversions).  The whole universe-code-family
-- stratified membership (arrow/product/sum + list/option/either/id/equiv) is closed.
#assert_no_axioms FX1Poly.Core.eitherCode_isReducibleMemberOfUniverse
#assert_no_axioms FX1Poly.Core.equivCode_isReducibleMemberOfUniverse
-- Linear-logic type formers (linearArrow and tensorProduct) inhabit their universe too: both are two-child
-- .type formers, classified by dataFormerInUniverse on the two-child SN combinators (linearity is a usage
-- grade, orthogonal to the type-code-in-universe fact).
#assert_no_axioms FX1Poly.Core.linearArrow_isReducibleMemberOfUniverse
#assert_no_axioms FX1Poly.Core.tensorProduct_isReducibleMemberOfUniverse

-- Modal-core beta+iota SN coverage: gen_modElim / gen_subsume are congruence-only (no iota root rule; the
-- modal collapse is raw eta), so their cong inversions + one-child-cong SN closures complete the modal-core SN
-- coverage alongside modIntro (StrongNormalizationConstructors) and the modIntro reducibility candidate.
#assert_no_axioms FX1Poly.Core.Step.from_modElim
#assert_no_axioms FX1Poly.Core.Step.from_subsume
#assert_no_axioms FX1Poly.Core.StepStar.modElim_isStronglyNormalizing_of_child
#assert_no_axioms FX1Poly.Core.StepStar.subsume_isStronglyNormalizing_of_child

-- The reflection direction + reducibility-framing completing modElim/subsume reducibility.
-- isStronglyNormalizing_child_of_oneChildCong is the reusable converse of the forward one-child-cong SN
-- closure (SN reflects through a congruence wrapper).  modElim/subsume being non-neutral with no iota rule (by
-- design), the SN candidate is the ceiling: the operators send candidate members to SN-candidate members; the
-- box-member capstone ties modElim back to modIntroCanonicalFormsCandidate.
#assert_no_axioms FX1Poly.Core.StepStar.isStronglyNormalizing_child_of_oneChildCong
#assert_no_axioms FX1Poly.Core.StepStar.modElim_isStronglyNormalizing_child_of_parent
#assert_no_axioms FX1Poly.Core.StepStar.subsume_isStronglyNormalizing_child_of_parent
#assert_no_axioms FX1Poly.Core.StepStar.modElim_isStronglyNormalizing_iff
#assert_no_axioms FX1Poly.Core.StepStar.subsume_isStronglyNormalizing_iff
#assert_no_axioms FX1Poly.Core.StepStar.modElim_isStronglyNormalizing_of_candidateMember
#assert_no_axioms FX1Poly.Core.StepStar.subsume_isStronglyNormalizing_of_candidateMember
#assert_no_axioms FX1Poly.Core.StepStar.modElim_isStronglyNormalizing_ofBoxMember

-- The 2LTT universe-mode bridge twin of the modal-eliminator reducibility.  The lift (one child) + lower
-- (two children: outer + cofibrancy) are congruence-only/non-neutral with no beta+iota iota-rule (their
-- lower(lift x) collapse is not in the current substrate), so the SN candidate is the ceiling.  The lower's
-- two child reflections each slice the two-child operator into a one-child congruence wrapper, reusing the
-- generic isStronglyNormalizing_child_of_oneChildCong (the cofibrancy slice threads StepChildren.there past the
-- held outer child, as in listCons's tail projection).  Biconditionals + candidate-framing complete the picture.
#assert_no_axioms FX1Poly.Core.StepStar.liftInnerToOuter_isStronglyNormalizing_child_of_parent
#assert_no_axioms FX1Poly.Core.StepStar.lowerOuterToInner_outer_isStronglyNormalizing_of_parent
#assert_no_axioms FX1Poly.Core.StepStar.lowerOuterToInner_cofibrancy_isStronglyNormalizing_of_parent
#assert_no_axioms FX1Poly.Core.StepStar.liftInnerToOuter_isStronglyNormalizing_iff
#assert_no_axioms FX1Poly.Core.StepStar.lowerOuterToInner_isStronglyNormalizing_iff
#assert_no_axioms FX1Poly.Core.StepStar.liftInnerToOuter_isStronglyNormalizing_of_candidateMember
#assert_no_axioms FX1Poly.Core.StepStar.lowerOuterToInner_isStronglyNormalizing_of_candidateMembers

-- Cubical-former congruence-only SN is covered GENERICALLY by the former-congruence SN closures
-- (`isStronglyNormalizing_of_{one,two,three}ChildCong`): every cubical former with no beta+iota rule
-- is just a non-neutral node whose SN follows from its children's SN, with no per-former content.  When
-- the cubical computation rules (transp/hcomp/Kan/path-beta/Glue-collapse) land, their SN routes through
-- the generic operator machinery — not a per-former wrapper file.

-- Universe-mode bridge beta+iota SN coverage: gen_liftInnerToOuter (1-child inner-to-outer lift) and
-- gen_lowerOuterToInner (2-child outer-to-inner lower) are congruence-only (no iota root rule; the mode-bridge
-- collapse `lower (lift x)` is not in the current beta+iota substrate, like the modal modElim collapse), so
-- their cong inversions + one-/two-child-cong SN closures complete the 2LTT mode-bridge SN coverage.
#assert_no_axioms FX1Poly.Core.Step.from_liftInnerToOuter
#assert_no_axioms FX1Poly.Core.Step.from_lowerOuterToInner
#assert_no_axioms FX1Poly.Core.StepStar.liftInnerToOuter_isStronglyNormalizing_of_child
#assert_no_axioms FX1Poly.Core.StepStar.lowerOuterToInner_isStronglyNormalizing_of_children

-- Recursive-eliminator iota-redex SN: the natSucc one-child subterm-SN lemma (predecessor of an SN natSucc
-- is SN), and the conditional natElim successor-case redex SN (normal branches + the succ-contractum SN for
-- every SN predecessor implies the natElim redex with an SN scrutinee is SN).  The succ-contractum hypothesis
-- is the IH-carrying premise the numeral WF-recursion supplies.
#assert_no_axioms FX1Poly.Core.StepStar.predecessor_isStronglyNormalizing_of_natSucc
#assert_no_axioms FX1Poly.Core.StepStar.natElim_isStronglyNormalizing_of_normal_branches
-- natRec (dependent recursor) firing-case twin, completing the Nat recursor pair.
#assert_no_axioms FX1Poly.Core.StepStar.natRec_isStronglyNormalizing_of_normal_branches
-- The SN-from-SN-branches form for the recursor closed-membership: the branches need only be SN (members),
-- not normal, as the Tait/data-candidate recursor argument requires.  Triple nested accessibility induction on
-- (scrutinee, zeroBranch, succBranch); the succ-contractum SN hypothesis is threaded through both branch
-- inductions.  The recursive analogue of the matcher SN-from-SN-branches: the succ iota-contractum contains a
-- recursive natElim/natRec call, and the succ branch occurs twice (in app succBranch pred and the recursive
-- call), so its update under succ-congruence is two app/natElim-cong + IsStronglyNormalizing.inv hops.
#assert_no_axioms FX1Poly.Core.StepStar.natElim_isStronglyNormalizing_of_strongly_normalizing_branches
#assert_no_axioms FX1Poly.Core.StepStar.natRec_isStronglyNormalizing_of_strongly_normalizing_branches

-- The value case of non-dependent Nat-recursor reducibility (the computational heart): the recursor on a
-- numeral scrutinee lands in the result candidate, by IsNatValue structural induction firing the two iota rules
-- (zero to z, succ to app(app s pred)(natElim pred z s)) through the candidate's weak-head expansion.
-- Conditional on the interface (candidate weak-head-expansion + branch reducibility + SN-of-redex).
#assert_no_axioms FX1Poly.Core.natElimValueReducibility
#assert_no_axioms FX1Poly.Core.natRecValueReducibility

-- Value-case natElim reducibility with the recursor-SN obligation discharged: replaces the bespoke
-- redexStronglyNormalizing hypothesis of natElimValueReducibility with the universal candidate properties CR1
-- (members are SN) + CR2 (membership forward-closed under Step) + succBranchTerminates.  The scrutinee-fixed
-- cell-SN recursor (natElimNormalScrutineeCellStronglyNormalizing) does a double Acc induction over the
-- branches, carrying the branch interface forward via CR2, with the iota-reduct SN coming from its membership
-- via CR1, so it needs no bespoke succContractumTerminates.  The pure Tait value-recursor argument over a
-- fixed result candidate (fuel-independent).
#assert_no_axioms FX1Poly.Core.natElimNormalScrutineeCellStronglyNormalizing
#assert_no_axioms FX1Poly.Core.natElimValueMember
-- The dependent-recursor twin: identical discharge (CR1 + CR2 + succBranchTerminates replacing
-- redexStronglyNormalizing) via the natRec scrutinee-fixed cell-SN recursor, gen_natRec's five-way
-- Step.from_natRec inversion matching natElim's.
#assert_no_axioms FX1Poly.Core.natRecNormalScrutineeCellStronglyNormalizing
#assert_no_axioms FX1Poly.Core.natRecValueMember

-- The neutral-scrutinee regime of the Nat recursor, the dual of the value case.  A neutral scrutinee is
-- never a numeral and stays neutral under Step, so natElim/natRec never iota-fires and the cell is a stuck
-- neutral, which inhabits every candidate by CR3.  memberOfStronglyNormalizingNeutral is the reusable bridge
-- (SN neutral implies member of any candidate, generalizing the CanonicalFormsPredicate-only version);
-- rootGenerator_ne_natZero/natSucc are the iota-vacuity discriminators; the cell-SN recursors are a triple Acc
-- induction with the two iota cases vacuous by neutrality (fixed result candidate, fuel-independent).
#assert_no_axioms FX1Poly.Core.IsReducibilityCandidate.memberOfStronglyNormalizingNeutral
#assert_no_axioms FX1Poly.Core.IsNeutral.rootGenerator_ne_natZero
#assert_no_axioms FX1Poly.Core.IsNeutral.rootGenerator_ne_natSucc
#assert_no_axioms FX1Poly.Core.natElim_neutralScrutinee_isStronglyNormalizing
#assert_no_axioms FX1Poly.Core.natRec_neutralScrutinee_isStronglyNormalizing
#assert_no_axioms FX1Poly.Core.natElimNeutralScrutineeMember
#assert_no_axioms FX1Poly.Core.natRecNeutralScrutineeMember

-- The general-scrutinee regime of the Nat recursor: the full outer recursion.  The Nat data candidate
-- CanonicalFormsPredicate IsNatValue builds in the value-or-neutral dichotomy (SN and
-- neutral-or-reaches-a-numeral), so a reducible scrutinee splits exactly into the two regimes: neutral implies
-- the stuck cell is a member by CR3; value implies natElimValueReducibility lands the numeral cell, and
-- ofStepStarReachingValue lifts it back through the scrutinee congruence (the lift needs the numeral cell to
-- reach a value, extracted by refuting its neutrality via <recursor>_notNeutral_ofNatValueScrutinee).  The
-- open-scope generalization of the closed natElimClosedIsMember (where the neutral disjunct is vacuous).
#assert_no_axioms FX1Poly.Core.natElim_notNeutral_ofNatValueScrutinee
#assert_no_axioms FX1Poly.Core.natRec_notNeutral_ofNatValueScrutinee
#assert_no_axioms FX1Poly.Core.natElimReducibleScrutineeMember
#assert_no_axioms FX1Poly.Core.natRecReducibleScrutineeMember

-- The general-scrutinee regime of the List recursor: the listElim twin of the Nat general-scrutinee
-- dispatch, bringing the three recursive eliminators (natElim/natRec/listElim) to general-scrutinee parity.
-- Same dispatch on the List candidate's value-or-neutral disjunct, via listElimValueReducibility +
-- ofStepStarReachingValue (StepStar.listElimScrutinee), with the value side extracted by
-- listElim_notNeutral_ofListValueScrutinee.
#assert_no_axioms FX1Poly.Core.listElim_notNeutral_ofListValueScrutinee
#assert_no_axioms FX1Poly.Core.listElimReducibleScrutineeMember

-- The general-scrutinee regime of the non-recursive data eliminators (starting with boolElim): the
-- open-scope value regime + general dispatch alongside the closed membership and neutral regimes.
-- boolElimValueReducibility is the boolElim analogue of natElimValueReducibility (no IH, no successor
-- application); the dispatch mirrors the recursive case on the bool candidate's value-or-neutral disjunct.
-- rootGenerator_ne_boolTrue/False are the iota-vacuity discriminators.
#assert_no_axioms FX1Poly.Core.IsNeutral.rootGenerator_ne_boolTrue
#assert_no_axioms FX1Poly.Core.IsNeutral.rootGenerator_ne_boolFalse
#assert_no_axioms FX1Poly.Core.boolElim_notNeutral_ofBoolValueScrutinee
#assert_no_axioms FX1Poly.Core.boolValue_isStronglyNormalizing
#assert_no_axioms FX1Poly.Core.boolElimValueReducibility
#assert_no_axioms FX1Poly.Core.boolElimReducibleScrutineeMember

-- The neutral-scrutinee regime of the List recursor: the listElim mirror of the Nat regime, bringing the
-- three recursive recursors (natElim/natRec/listElim) to neutral-coverage parity.  A neutral scrutinee is never
-- a List constructor and stays neutral under Step, so listElim never iota-fires; the cell is a stuck neutral,
-- member of any candidate by memberOfStronglyNormalizingNeutral.  Discriminators
-- rootGenerator_ne_listNil/listCons + the triple-Acc cell-SN recursor (iota cases vacuous by neutrality).
#assert_no_axioms FX1Poly.Core.IsNeutral.rootGenerator_ne_listNil
#assert_no_axioms FX1Poly.Core.IsNeutral.rootGenerator_ne_listCons
#assert_no_axioms FX1Poly.Core.listElim_neutralScrutinee_isStronglyNormalizing
#assert_no_axioms FX1Poly.Core.listElimNeutralScrutineeMember

-- The neutral regime of the direct-iota eliminators (boolElim/fst/snd/idJ/idStrictRec): the non-recursive
-- companion to the natElim/listElim neutral regimes.  Each iota-reduct is a branch/component (not an
-- application), so the cell-SN-from-children needs no extra interface and each neutral member is a pure compose
-- with memberOfStronglyNormalizingNeutral + the IsNeutral.X arm.
#assert_no_axioms FX1Poly.Core.boolElimNeutralScrutineeMember
#assert_no_axioms FX1Poly.Core.fstNeutralArgumentMember
#assert_no_axioms FX1Poly.Core.sndNeutralArgumentMember
#assert_no_axioms FX1Poly.Core.idJNeutralWitnessMember
#assert_no_axioms FX1Poly.Core.idStrictRecNeutralWitnessMember

-- The neutral regime of the application-iota match eliminators (optionMatch/eitherMatch): the last 2 of 12
-- IsNeutral eliminators, completing the eliminator-neutral-coverage set.  Their iota is an application
-- (optionMatch (some v) ... to app s v), so cell-SN needs the bespoke triple-Acc (the natElim pattern, iota
-- cases vacuous by neutrality) + constructor discriminators
-- rootGenerator_ne_optionNone/optionSome/eitherInl/eitherInr, not a pure compose like the direct-iota five.
-- With these, all 12 IsNeutral eliminators are reducible over a neutral principal child.
#assert_no_axioms FX1Poly.Core.IsNeutral.rootGenerator_ne_optionNone
#assert_no_axioms FX1Poly.Core.IsNeutral.rootGenerator_ne_optionSome
#assert_no_axioms FX1Poly.Core.IsNeutral.rootGenerator_ne_eitherInl
#assert_no_axioms FX1Poly.Core.IsNeutral.rootGenerator_ne_eitherInr
#assert_no_axioms FX1Poly.Core.optionMatch_neutralScrutinee_isStronglyNormalizing
#assert_no_axioms FX1Poly.Core.eitherMatch_neutralScrutinee_isStronglyNormalizing
#assert_no_axioms FX1Poly.Core.optionMatchNeutralScrutineeMember
#assert_no_axioms FX1Poly.Core.eitherMatchNeutralScrutineeMember

-- Non-vacuous regression corpus for the eliminator-neutral set: each neutral member, instantiated at the SN
-- candidate with `var index` as the genuinely-neutral principal child, gives a concrete strong-normalization
-- fact for the stuck eliminator.  Guards the set against silently regressing to vacuity or losing zero-axiom
-- status.  Parametric over an arbitrary Fin scope index.
#assert_no_axioms FX1Poly.Core.natElimNeutralVarSmoke
#assert_no_axioms FX1Poly.Core.natRecNeutralVarSmoke
#assert_no_axioms FX1Poly.Core.listElimNeutralVarSmoke
#assert_no_axioms FX1Poly.Core.optionMatchNeutralVarSmoke
#assert_no_axioms FX1Poly.Core.eitherMatchNeutralVarSmoke
#assert_no_axioms FX1Poly.Core.boolElimNeutralVarSmoke
#assert_no_axioms FX1Poly.Core.fstNeutralVarSmoke
#assert_no_axioms FX1Poly.Core.sndNeutralVarSmoke
#assert_no_axioms FX1Poly.Core.idJNeutralVarSmoke
#assert_no_axioms FX1Poly.Core.idStrictRecNeutralVarSmoke

-- The value case of listElim recursor reducibility, the list analogue of the Nat recursor value-case:
-- listElim on a list-value scrutinee lands in the result candidate by IsListValue structural induction firing
-- the two iota rules (nil to nilBranch; cons to app(app(app c head)tail)(listElim tail n c)) through the
-- candidate's weak-head expansion.  Same conditional interface (weak-head-expansion + branch reducibility +
-- SN-of-redex).
#assert_no_axioms FX1Poly.Core.listElimValueReducibility

-- Value-case listElim reducibility with the recursor-SN obligation discharged (the twin of
-- natElimValueMember): CR1 + CR2 + consBranchTerminates replace the bespoke redexStronglyNormalizing, via the
-- listElim scrutinee-fixed cell-SN recursor.  The cons branch is the three-deep app (head + tail), recovered by
-- two childCons injection drills; otherwise identical to the Nat recursor discharge.
#assert_no_axioms FX1Poly.Core.listElimNormalScrutineeCellStronglyNormalizing
#assert_no_axioms FX1Poly.Core.listElimValueMember

-- SN of an application under the beta-contraction side-condition (the member weak-head-expansion brick):
-- app f a is SN given f SN, a SN, and every beta-contraction body[a] (for f reducing to lam body) SN.  The
-- side-condition is essential, since SN of the two positions alone does not give SN of the application (the
-- Omega term loops).  This is "application preserves SN" and the load-bearing Pi arm of the recursor-value
-- `headExpand` premise.  `descendStepStar` is the StepStar-iterated forward SN closure (every reduct of an SN
-- term is SN).
#assert_no_axioms FX1Poly.Core.IsStronglyNormalizing.descendStepStar
#assert_no_axioms FX1Poly.Core.isStronglyNormalizing_applicationCell_aux
#assert_no_axioms FX1Poly.Core.isStronglyNormalizing_applicationCell_ofBetaContractionsStronglyNormalizing

-- Recursive-eliminator iota-redex SN, second data type (List): the two listCons subterm-SN projections
-- (head/tail of an SN cons are SN) and the conditional listElim cons-case redex SN (normal branches + the
-- triple-app cons-contractum SN for every SN head/tail implies the listElim redex with an SN scrutinee is SN).
-- Same IH-carrying contractum premise as natElim; the cons scrutinee is 2-child.
#assert_no_axioms FX1Poly.Core.StepStar.headValue_isStronglyNormalizing_of_listCons
#assert_no_axioms FX1Poly.Core.StepStar.tailValue_isStronglyNormalizing_of_listCons
#assert_no_axioms FX1Poly.Core.StepStar.listElim_isStronglyNormalizing_of_normal_branches
-- The SN-from-SN-branches form for the listElim closed-membership: the list twin of the natElim
-- SN-from-SN-branches recursor.  Triple nested accessibility induction; the cons-contractum SN hypothesis (over
-- head + tail) is threaded through both branch inductions: nilBranch one hop (recursive listElim), consBranch
-- two hops (app (app consBranch head) tail, three app layers deep, and the recursive listElim).
#assert_no_axioms FX1Poly.Core.StepStar.listElim_isStronglyNormalizing_of_strongly_normalizing_branches

-- Non-recursive applied-branch eliminator iota-redex SN (optionMatch / eitherMatch): the three one-child
-- value subterm-SN lemmas (value of an SN optionSome/eitherInl/eitherInr is SN), and the two conditional
-- firing-case redex SN (normal branches + the applied `app branch value` contractum SN for every SN value
-- implies the matcher redex with an SN scrutinee is SN).  Covers the firing-case eliminator SN across
-- passive/recursive/applied-non-recursive shapes.
#assert_no_axioms FX1Poly.Core.StepStar.value_isStronglyNormalizing_of_optionSome
#assert_no_axioms FX1Poly.Core.StepStar.value_isStronglyNormalizing_of_eitherInl
#assert_no_axioms FX1Poly.Core.StepStar.value_isStronglyNormalizing_of_eitherInr
#assert_no_axioms FX1Poly.Core.StepStar.optionMatch_isStronglyNormalizing_of_normal_branches
#assert_no_axioms FX1Poly.Core.StepStar.eitherMatch_isStronglyNormalizing_of_normal_branches
-- The SN-from-SN-branches form for the optionMatch/eitherMatch closed-membership: the branches need only be
-- SN (members), not normal, as the Tait/data-candidate eliminator argument requires.  Triple nested
-- accessibility induction; the applied-branch contractum SN hypothesis (for all value, SN value implies
-- SN (app branch value)) is threaded through the branch induction, updated under branch-congruence via
-- app-head Step.cong + IsStronglyNormalizing.inv.  eitherMatch threads both left and right contractums.
#assert_no_axioms FX1Poly.Core.StepStar.optionMatch_isStronglyNormalizing_of_strongly_normalizing_branches
#assert_no_axioms FX1Poly.Core.StepStar.eitherMatch_isStronglyNormalizing_of_strongly_normalizing_branches

-- Linear-logic type-former SN (congruence-only, no beta+iota root rule): linearArrow and tensorProduct,
-- two-child formers structurally identical to arrowCode/productCode.  Cong inversions + twoChildCong SN.
-- Extends the former-SN coverage to the linear generator family.
#assert_no_axioms FX1Poly.Core.Step.from_linearArrow
#assert_no_axioms FX1Poly.Core.Step.from_tensorProduct
#assert_no_axioms FX1Poly.Core.StepStar.linearArrow_isStronglyNormalizing_of_source_target
#assert_no_axioms FX1Poly.Core.StepStar.tensorProduct_isStronglyNormalizing_of_factors

-- Single-contractum beta-redex SN (neutral arm of the member weak-head beta-expansion, the denote
-- lambda-arm engine): app (lam body) arg is SN given lam body, arg, and the single contractum subst0 body arg
-- are SN (body free to step).  Unlike the appLam family that fixes a normal body or demands a uniform
-- contractum-SN over all reducts, this needs only the single contractum, recovering the body-reduct contractums
-- by descendStepStar along StepStar.subst0Body.  stepStarLamInversion (a StepStar chain out of a lambda lands
-- on a lambda, body chain recovered) is the reusable supporting substrate.
#assert_no_axioms FX1Poly.Core.stepStarLamInversion
#assert_no_axioms FX1Poly.Core.stepStarLamBodyChain
#assert_no_axioms FX1Poly.Core.appLam_isStronglyNormalizing_of_contractum

-- The abstract Geser SN-of-union criterion: reduceLeft SN at a + reduceRight SN everywhere + reduceRight
-- quasi-commutes over reduceLeft implies (reduceLeft union reduceRight) SN at a.  Constructive, Init-only,
-- zero-axiom: nested Acc (outer on reduceLeft-Acc, inner on reduceRight-Acc with the outer IH carried in the
-- motive; quasi-commutation reconstructs the right-descendant's left-predecessors).  The crux for open beta-eta
-- SN, reusable for cubical SN-robustness.
#assert_no_axioms FX1Poly.Core.accDownwardUnionStar
#assert_no_axioms FX1Poly.Core.accUnionInner
#assert_no_axioms FX1Poly.Core.accUnion

-- Instantiation of the abstract criterion at the FX beta-eta relations.  Step.betaEtaSuccessor is
-- UnionSuccessor Step Step.eta by defeq (betaEtaSuccessor_eq_unionSuccessor = rfl), so accUnionBetaEta lands
-- the Geser criterion on Step.betaEtaStar.IsStronglyNormalizing: beta-SN + eta-SN + the
-- EtaQuasiCommutesOverBeta crux implies beta-eta-SN.  The crux is the eta-postponement family below.
#assert_no_axioms FX1Poly.Core.EtaQuasiCommutesOverBeta
#assert_no_axioms FX1Poly.Core.betaEtaSuccessor_eq_unionSuccessor
#assert_no_axioms FX1Poly.Core.accUnionBetaEta

-- The etaLam case of the eta-postponement crux.  A beta/iota-step inside the function lifts (Step.weaken +
-- Step.cong/StepChildren through lam composed with app) to a single step on the etaLam source
-- (etaLamSourceCongruence); then one etaLam eta-contraction reaches the original reduct, so etaLam eta-then-beta
-- reorders to beta-then-(one eta), inside beta-eta-star.  The etaLam obligation of EtaQuasiCommutesOverBeta.
#assert_no_axioms FX1Poly.Core.Step.etaLamSourceCongruence
#assert_no_axioms FX1Poly.Core.etaLamQuasiCommutesOverBeta

-- etaModIntro (single strip modIntro[modElim[_]], etaLam's shape minus the weaken) + etaPair (the
-- duplicating case).  The etaPair source pair[fst p, snd p] holds two copies of p, so one beta/iota-step reduces
-- only the fst copy (reduceFst); the beta-eta tail then beta-reduces the snd copy (reduceSnd) and eta-contracts,
-- a multi-step UnionStar (tailLeft + tailRight).  This is where the Geser criterion's multi-step
-- quasi-commutation is load-bearing (Klop-style duplication absorbed).
#assert_no_axioms FX1Poly.Core.Step.etaModIntroSourceCongruence
#assert_no_axioms FX1Poly.Core.etaModIntroQuasiCommutesOverBeta
#assert_no_axioms FX1Poly.Core.Step.etaPairSourceReduceFst
#assert_no_axioms FX1Poly.Core.Step.etaPairSourceReduceSnd
#assert_no_axioms FX1Poly.Core.etaPairQuasiCommutesOverBeta

-- The last two eta constructors, closing the five.  etaPathLam is etaLam's binder shape over
-- gen_pathLam/gen_pathApp (single copy, scope+1 ascription).  etaGlueIntro is the second duplicating case:
-- glueIntro[glueElim g, g] records g twice (the second directly), so it follows etaPair's
-- reduce-first/reduce-second/eta multi-step UnionStar pattern.  All five per-eta-constructor obligations are in
-- hand.
#assert_no_axioms FX1Poly.Core.Step.etaPathLamSourceCongruence
#assert_no_axioms FX1Poly.Core.etaPathLamQuasiCommutesOverBeta
#assert_no_axioms FX1Poly.Core.Step.etaGlueIntroReduceElim
#assert_no_axioms FX1Poly.Core.Step.etaGlueIntroReduceSecond
#assert_no_axioms FX1Poly.Core.etaGlueIntroQuasiCommutesOverBeta

-- The discharged crux.  `cases` on the indexed Step.eta with free-variable indices (pure-substitution
-- unification, no noConfusion) dispatches each of the five eta constructors to its postponement lemma,
-- propext-clean.  etaQuasiCommutesOverBeta proves EtaQuasiCommutesOverBeta as a theorem, so accUnionBetaEta's
-- hypothesis is discharged and open beta-eta-SN holds unconditionally.
#assert_no_axioms FX1Poly.Core.etaQuasiCommutesOverBeta

/-! ## RawTermSubstLiftWeaken — the double-weaken cancellation that cracks the symbolic-S / Church-sum wall

The single-weaken cancellation (weaken_subst_singleton) handles β-redexes where each bound variable is weakened
≤ once (the single-weaken case). A variable under TWO binders is weakened twice; the resulting subst (lift σ)(weaken² a)
= weaken a cancellation was the last deferred de Bruijn obstruction (symbolic S-rule, symbolic Church sums). It is
NOT a wall: subst_lift_weaken (★, the lift-weaken NATURALITY subst (lift σ)(weaken t) = weaken (subst σ t)) follows
from weaken_eq_rename + the shipped rename_subst_commute (LHS) + subst_rename_commute (RHS) + subst_pointwise (both
composites send k ↦ weaken(σ k)); subst_lift_singleton_weaken_weaken (the double-weaken cancellation) is then two
rw's (subst_lift_weaken peels one weaken, weaken_subst_singleton cancels the inner singleton). Zero-axiom. -/

#assert_no_axioms FX1Poly.Core.RawTerm.subst_lift_weaken
#assert_no_axioms FX1Poly.Core.RawTerm.subst_lift_singleton_weaken_weaken

/- `Conv` reflects an injective renaming (ConvRenameReflection): lift `Step.reflectRename` over a whole
`StepStar` chain, prove `weaken` injective from its partial left inverse `strengthen`, and reflect both
join-legs of a `Conv` through the renaming.  `Conv.reflectWeaken` is the reflection primitive grown
strengthening (the inverse of `weakenUnderBinding`, blocking grown η-contraction SR #477/PAR-2) needs in
every arm: strip a `weaken` off a `Conv` classifier to descend a scope.  Zero-axiom. -/

#assert_no_axioms FX1Poly.Core.StepStar.reflectRename
#assert_no_axioms FX1Poly.Core.RawTerm.weaken_injective
#assert_no_axioms FX1Poly.Core.Conv.reflectRename
#assert_no_axioms FX1Poly.Core.Conv.reflectWeaken
#assert_no_axioms FX1Poly.Core.RawRenaming.lift_injective

/- Term-level rename injectivity from Fin-injectivity (RawTermRenameInjective): the general statement
behind `weaken_injective` — a Fin-injective renaming is term-injective, by the term/spine mutual
structural induction (var heads via Fin-injectivity, non-var heads strip the scope-invariance payload
cast and recurse at the lifted renaming).  `Conv.reflectLiftRename` is the binder instance the route-H
pinned reflection's piIntro arm consumes (`Conv` reflects `lift rho`).  Zero-axiom. -/

#assert_no_axioms FX1Poly.Core.eqRecTypeCast_injective
#assert_no_axioms FX1Poly.Core.RawRenaming.iterateLiftRaw_injective
#assert_no_axioms FX1Poly.Core.RawTerm.rename_injective
#assert_no_axioms FX1Poly.Core.RawTermChildren.rename_injective
#assert_no_axioms FX1Poly.Core.Conv.reflectRenameOfFinInjective
#assert_no_axioms FX1Poly.Core.Conv.reflectLiftRename
-- STR-7: the Conv/NF renaming-EQUIVARIANCE bundle (ConvRenameEquivariance) — the two shipped halves
-- (preservation Conv.rename #370 + reflection Conv.reflectRename* #1167) assembled as iffs at the three
-- shapes the whnf-directed checker compares classifiers in (general Fin-injective / weaken / lift), plus
-- structural-normality invariance under EVERY renaming (Step.rename pushes a source step forward,
-- Step.reflectRename pulls an image step back — Bool case split, no excluded middle).
#assert_no_axioms FX1Poly.Core.Conv.rename_iff_ofFinInjective
#assert_no_axioms FX1Poly.Core.Conv.renameWeaken_iff
#assert_no_axioms FX1Poly.Core.Conv.renameLift_iff
#assert_no_axioms FX1Poly.Core.RawTerm.isStepNormalForm_rename_iff

/-! ### FireRootEtaRedex — the computable root η-firer + layered βη one-step reducer (ETA-2 core)

The ONE missing artifact the ETA-1 census identified: `fireRootEtaRedex?` fires the root η-redex
exactly when one exists (sound + EXACT-complete, since `Step.eta` is root-only), and
`reduceOnceBetaEta` layers it after the β/ι `reduceOnce` — sound + complete against the FULL
`Step.betaEta` union.  With the shipped metatheory bundle this completes the ingredient list for
the βη normalizer + decidable `BetaEtaConv` on the wf fragment. -/

#assert_no_axioms FX1Poly.Core.RawTerm.fireRootEtaRedex?
#assert_no_axioms FX1Poly.Core.RawTerm.fireRootEtaRedex?_etaLamSource
#assert_no_axioms FX1Poly.Core.RawTerm.fireRootEtaRedex?_etaPairSource
#assert_no_axioms FX1Poly.Core.RawTerm.fireRootEtaRedex?_etaPathLamSource
#assert_no_axioms FX1Poly.Core.RawTerm.fireRootEtaRedex?_etaModIntroSource
#assert_no_axioms FX1Poly.Core.RawTerm.fireRootEtaRedex?_etaGlueIntroSource
#assert_no_axioms FX1Poly.Core.RawTerm.fireRootEtaRedex?_complete
#assert_no_axioms FX1Poly.Core.RawTerm.fireRootEtaRedex?_sound
#assert_no_axioms FX1Poly.Core.RawTerm.reduceOnceBetaEta
#assert_no_axioms FX1Poly.Core.RawTerm.reduceOnceBetaEta_sound
#assert_no_axioms FX1Poly.Core.RawTerm.reduceOnceBetaEta_complete

/-! ### NormalizeBetaEta — the βη normalizer over the reducer (ETA-2 harvest, raw half)

The exact βη twin of `Core/Normalize`: iterate `reduceOnceBetaEta` along an
`Acc Step.betaEtaSuccessor` witness.  Output reached by a `betaEtaStar` chain and fully βη-normal
(no `Step.betaEta` step at all — `Step.eta` is root-only, so the root firer's completeness is full
η-completeness).  On the wf-typed fragment the accessibility witness is typed βη-SN (OSN-1). -/

#assert_no_axioms FX1Poly.Core.RawTerm.normalizeBetaEta
#assert_no_axioms FX1Poly.Core.RawTerm.normalizeBetaEta_unfold
#assert_no_axioms FX1Poly.Core.RawTerm.normalizeBetaEta_reducesTo
#assert_no_axioms FX1Poly.Core.RawTerm.normalizeBetaEta_isBetaEtaNormalForm

/-! ### The `unitCode` inert-leaf substrate (nullary formation row support)

The Unit type code `.mkGen .gen_unitCode () .childNil` is a normal leaf (no root rule, no
child steps), hence strongly normalizing, hence a reducible member of every universe code via
the generic `dataFormerInUniverse` (weak-head normal, non-Pi non-universe rooted) — the
reducibility-FT `genFormation`/`genFormationPi` arm for the nullary formation row. -/

#assert_no_axioms FX1Poly.Core.StepStar.noStep_unitTypeCode
#assert_no_axioms FX1Poly.Core.StepStar.unitTypeCode_isStronglyNormalizing
#assert_no_axioms FX1Poly.Core.IsReducibleMemberAt.unitFormerInUniverse
