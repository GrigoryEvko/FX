import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.TypingContext
import FX1Poly.Typed.HasType
import FX1Poly.Typed.HasTypeHonesty
import FX1Poly.Typed.WfContext
import FX1Poly.Typed.HasTypeWeakening
import FX1Poly.Typed.HasTypeSubstitution
import FX1Poly.Typed.HasTypeValidity
import FX1Poly.Typed.HasTypeStronglyNormalizing
import FX1Poly.Typed.HasTypeInversion
import FX1Poly.Typed.HasTypeDecidableConv
import FX1Poly.Typed.HasTypeSubjectReduction
import FX1Poly.Typed.UniverseCodeShape
import FX1Poly.Typed.SigmaCodeShape
import FX1Poly.Typed.IsTypeDecidable
import FX1Poly.Typed.HasTypeDecidable
import FX1Poly.Typed.HasTypeSmokeCorpus
import FX1Poly.Typed.HasTypeConsistency
import FX1Poly.Typed.HasTypeInfer
import FX1Poly.Typed.HasTypeCheck
import FX1Poly.Typed.HasTypePiSigmaFormationCheckingCertificate
import FX1Poly.Typed.HasTypeClosedForms
import FX1Poly.Typed.WfContextDecidable
import FX1Poly.Typed.HasTypeDesc
import FX1Poly.Typed.HasTypeDescSound
import FX1Poly.Typed.HasTypeDescDecidable
import FX1Poly.Typed.HasTypeDescElim
import FX1Poly.Typed.HasTypeDescValidity
import FX1Poly.Typed.HasTypeDescStronglyNormalizing
import FX1Poly.Typed.HasTypeDescClosedForms
import FX1Poly.Typed.HasTypeDescInversion
import FX1Poly.Typed.HasTypeDescUniqueness
import FX1Poly.Typed.HasTypeDescWeakening
import FX1Poly.Typed.HasTypeDescSubstitution
import FX1Poly.Typed.HasTypeDescElimWeakening
import FX1Poly.Typed.HasTypeDescElimSubstitution
import FX1Poly.Typed.HasTypeDescApplication
import FX1Poly.Typed.HasTypeDescPi
import FX1Poly.Typed.HasTypeDescPiWeakening
import FX1Poly.Typed.HasTypeDescPiSubstitution
import FX1Poly.Typed.HasTypeDescPiInversion
import FX1Poly.Typed.HasTypeDescPiApplication
import FX1Poly.Typed.HasTypeDescPiValidity
import FX1Poly.Typed.ConvCodeInjectivity
import FX1Poly.Typed.ReducibleEnv
import FX1Poly.Typed.ReducibleEnvAt
import FX1Poly.Typed.ReducibleEnvTypeVariable
import FX1Poly.Typed.SimplyTypedTypeExprFT
import FX1Poly.Typed.AbstractionNonDependentUnderSubstLevelFree
import FX1Poly.Typed.SimplyTypedTypeExprReducibleLevelFree
import FX1Poly.Typed.SimplyTypedTermFundamentalLevelFree
import FX1Poly.Typed.SimplyTypedTermConfluenceLevelFree
import FX1Poly.Typed.SimplyTypedTermInhabitationLevelFree
import FX1Poly.Typed.SimplyTypedTermInversionLevelFree
import FX1Poly.Typed.SimplyTypedTypeExprClosureLevelFree
import FX1Poly.Typed.SimplyTypedTermRenameLevelFree
import FX1Poly.Typed.SimplyTypedTermSubstLevelFree
import FX1Poly.Typed.SimplyTypedTermSubjectReductionLevelFree
import FX1Poly.Typed.SimplyTypedTermCanonicityLevelFree
import FX1Poly.Typed.SimplyTypedTermConsistencyLevelFree
import FX1Poly.Typed.SimplyTypedConvDecision
import FX1Poly.Typed.SimplyTypedNormalForm
import FX1Poly.Typed.SimplyTypedConvEquivalence
import FX1Poly.Typed.ReduceSmokeCorpus
import FX1Poly.Core.RedexExtraction
import FX1Poly.Core.RootStepDispatch
import FX1Poly.Core.FireRootRedex
import FX1Poly.Core.FireRootRedexComplete
import FX1Poly.Core.ReduceOnce
import FX1Poly.Core.ReduceOnceComplete
import FX1Poly.Core.Normalize
import FX1Poly.Core.NormalizeMeta
import FX1Poly.Core.StronglyNormalizingSubst
import FX1Poly.Core.ExistsStepOfNotNormal
import FX1Poly.Core.WeakNormalization
import FX1Poly.Core.NormalFormUnique
import FX1Poly.Core.StronglyNormalizingConvDecision
import FX1Poly.Typed.ReducibleEnvAtAllLevels
import FX1Poly.Typed.ReducibleEnvAtAllLevelsWithPositiveTypeCandidates
import FX1Poly.Typed.ReducibleEnvAtAllLevelsWithTypeValueCandidates
import FX1Poly.Typed.FundamentalWithPositiveTypeCandidates
import FX1Poly.Typed.FundamentalWithTypeValueCandidates
import FX1Poly.Typed.FundamentalAtAllLeafArms
import FX1Poly.Typed.FundamentalAtAllTelescope
import FX1Poly.Typed.FundamentalAtAllFormerChildren
import FX1Poly.Typed.FundamentalAtAllPiIntro
import FX1Poly.Typed.FundamentalAtAllPositiveArguments
import FX1Poly.Typed.StrongNormalizingAllLevelPiComponents
import FX1Poly.Typed.FundamentalAtAllTelescopePositiveArguments
import FX1Poly.Typed.FundamentalAtAllPositiveMemberExtension
import FX1Poly.Typed.FundamentalAtAllCanonicalCandidate
import FX1Poly.Typed.FundamentalAtAllVectorPremises
import FX1Poly.Typed.FundamentalAtAllNonDependentBinders
import FX1Poly.Typed.FundamentalAtUniformVectorPremises
import FX1Poly.Typed.HasTypeDescPiFundamentalVectorFromFormation
import FX1Poly.Typed.HasTypeDescFundamentalAtAllFromGenFormation
import FX1Poly.Typed.FundamentalLevelIndexed
import FX1Poly.Typed.ClosedLevelIndexed
import FX1Poly.Typed.TypeFundamentalLevelIndexed
import FX1Poly.Typed.LeveledContext
import FX1Poly.Typed.ClosedSNSmoke
import FX1Poly.Typed.ClosedConvDecision
import FX1Poly.Typed.HasTypeDescPiStronglyNormalizingFromFundamental
import FX1Poly.Typed.ReducibleEnvVec
import FX1Poly.Typed.ReducibleEnvVecTypeVariable
import FX1Poly.Typed.HasTypeDescPiConsistency
import FX1Poly.Typed.HasTypeFormationNoLambdaApplication
import FX1Poly.Typed.ReducibleSemanticRules
import FX1Poly.Typed.ReducibleMemberFormation
import FX1Poly.Typed.DescTelescopeInversion
import FX1Poly.Typed.PiFormerMembership
import FX1Poly.Typed.FormerChildrenReducible
import FX1Poly.Typed.TelescopeReducible
import FX1Poly.Typed.UniverseDomainMemberExtension
import FX1Poly.Typed.ReducibleTypeAtAllLevelsLeaves
import FX1Poly.Typed.ReducibleTypeAtAllLevelsInduction
import FX1Poly.Typed.ReducibleTypeAtAllLevelsPiNeutralDomain
import FX1Poly.Typed.ReducibleMemberAtAllPositiveLevelsLeaves
import FX1Poly.Typed.FundamentalTelescopeConsNeutralDomain
import FX1Poly.Typed.FundamentalTelescopeConsWhnfDomain
import FX1Poly.Typed.ReducibleTypeAtAllLevelsPiDomainMemberExtension
import FX1Poly.Typed.ReducibleMemberAtAllPositiveLevelsPiMemberExtension
import FX1Poly.Typed.ReducibleMemberAtAllPositiveLevelsHeadExpand
import FX1Poly.Typed.ReducibleMemberAtAllPositiveLevelsConv
import FX1Poly.Typed.ReducibleMemberAtAllPositiveLevelsStronglyNormalizing
import FX1Poly.Typed.ReducibleMemberAtAllPositiveLevelsNonDependentArrow
import FX1Poly.Typed.ReducibleTypeAtAllLevelsNonDependentArrow
import FX1Poly.Typed.FirstOrderSimplyTypedReducibility
import FX1Poly.Typed.HigherOrderSimplyTypedReducibility
import FX1Poly.Typed.SimplyTypedTermReducibility

/-! # Tools/AuditAll/AuditTyped
   — persistent per-declaration zero-axiom gate for the typed layer

The typed layer (polycell.md §11.8.5) is the dim-0 soundness stratum: the
`.context` / `.type` / `.term` cells that classify each other.  The native
`TypingContext` de Bruijn telescope is the `.context`-sort spine the `HasType`
engine consumes via the variable rule.

Every declaration here must elaborate without `propext`, `Classical.choice`,
`Quot.sound`, or `sorryAx` — so any future edit that introduces an axiom
dependency fails `lake build FX1PolyAudit` immediately.  The `lookup`
de Bruijn destructuring and `length_eq_scope` induction are the two places
a careless rewrite could pull `propext` through the match compiler; these
gates pin them shut.
-/

/-! ### TypingContext — native de Bruijn telescope + lookup + coherence -/

#assert_no_axioms FX1Poly.Typed.TypingContext
#assert_no_axioms FX1Poly.Typed.TypingContext.length
#assert_no_axioms FX1Poly.Typed.TypingContext.length_eq_scope
#assert_no_axioms FX1Poly.Typed.TypingContext.lookup
#assert_no_axioms FX1Poly.Typed.TypingContext.lookup_cons_zero
#assert_no_axioms FX1Poly.Typed.TypingContext.lookup_cons_succ

/-! ### HasType engine — type-formation arms (var / conv / universe / Π / Σ) + IsType -/

#assert_no_axioms FX1Poly.Typed.universeCodeCell
#assert_no_axioms FX1Poly.Typed.variableCell
#assert_no_axioms FX1Poly.Typed.piTyCodeCell
#assert_no_axioms FX1Poly.Typed.sigmaTyCodeCell
#assert_no_axioms FX1Poly.Typed.HasType
#assert_no_axioms FX1Poly.Typed.IsType

/-! ### Honesty — 0-false-positive probe (ill-typed cell has no derivation) -/

#assert_no_axioms FX1Poly.Typed.unitCell
#assert_no_axioms FX1Poly.Typed.appUnitUnit
#assert_no_axioms FX1Poly.Typed.RawTerm.headGenerator
#assert_no_axioms FX1Poly.Typed.HasType.subjectIsVariableOrTypeFormerCode
#assert_no_axioms FX1Poly.Typed.appUnitUnit_hasNoTyping

/-! ### WfContext — well-formedness predicate + inversions + non-vacuity witness -/

#assert_no_axioms FX1Poly.Typed.WfContext
#assert_no_axioms FX1Poly.Typed.WfContext.emptyIsWellFormed
#assert_no_axioms FX1Poly.Typed.WfContext.tailWellFormed
#assert_no_axioms FX1Poly.Typed.WfContext.headIsType
#assert_no_axioms FX1Poly.Typed.WfContext.cons
#assert_no_axioms FX1Poly.Typed.wfContext_universeBinding

/-! ### Typed renaming + weakening (the structural cartesian lift) -/

#assert_no_axioms FX1Poly.Typed.rename_variableCell
#assert_no_axioms FX1Poly.Typed.rename_universeCodeCell
#assert_no_axioms FX1Poly.Typed.HasType.renameRespectingContext
#assert_no_axioms FX1Poly.Typed.HasType.weakenUnderBinding

/-! ### Typed substitution (the β-engine) — `subst0` preserves typing -/

#assert_no_axioms FX1Poly.Typed.subst_variableCell
#assert_no_axioms FX1Poly.Typed.subst_universeCodeCell
#assert_no_axioms FX1Poly.Typed.subst_singleton_renameWeaken_cancel
#assert_no_axioms FX1Poly.Typed.HasType.substRespectingContext
#assert_no_axioms FX1Poly.Typed.HasType.substituteUnderBinding

/-! ### Validity (P3) — IsType stability + lookup-is-type + classifier-is-a-type -/

#assert_no_axioms FX1Poly.Typed.IsType.weakenUnderBinding
#assert_no_axioms FX1Poly.Typed.IsType.substituteUnderBinding
#assert_no_axioms FX1Poly.Typed.WfContext.lookupIsType
#assert_no_axioms FX1Poly.Typed.HasType.classifierIsType

/-! ### Fundamental theorem (typed SN, native pi/sigma-formation HasType core) + typed Conv.trans payoff -/

#assert_no_axioms FX1Poly.Typed.HasType.isStronglyNormalizing
#assert_no_axioms FX1Poly.Typed.IsType.isStronglyNormalizing
#assert_no_axioms FX1Poly.Typed.Conv.trans_of_typedMiddle

/-! ### INVERSION (#454, native pi/sigma-formation HasType core) — per-shape classifier characterization -/

#assert_no_axioms FX1Poly.Typed.HasType.inversionVariable
#assert_no_axioms FX1Poly.Typed.HasType.inversionUniverseCode
-- Π-formation inversion: a typed `piTyCodeCell` exposes both children's
-- universe typings (at one shared flag) + a `Conv` of the classifier to
-- `Type@(lmax …)`.  The decider's refutation arms + `uniqueness`'s Π case feed on
-- it.  Same equation-motive shape as the var / universe inversions, with the
-- `piFormation` arm closed by `piTyCodeCell_inj`.
#assert_no_axioms FX1Poly.Typed.HasType.inversionPiCode
-- Σ-formation inversion: the dual of `inversionPiCode`.  A typed
-- `sigmaTyCodeCell` exposes both children's universe typings (at one shared
-- flag) + a `Conv` of the classifier to `Type@(lmax …)`.  The Σ arms of the
-- decider + `uniqueness` feed on it.  Same equation-motive shape, with the
-- `piFormation` arm the impossible one (`Generator.noConfusion`) and the
-- `sigmaFormation` arm closed by `sigmaTyCodeCell_inj`.
#assert_no_axioms FX1Poly.Typed.HasType.inversionSigmaCode

/-! ### UNIQUENESS OF TYPING (#469, native pi/sigma-formation HasType core) -/

#assert_no_axioms FX1Poly.Typed.HasType.uniqueness

/-! ### DECIDABLE TYPE CONVERSION (native pi/sigma-formation HasType core) — normal-form rigidity →
    decidable Conv.  Core rigidity (`StepStar.eq_of_noStep`, `Conv.eq_of_noStep`,
    `Conv.iff_eq_of_noStep`) is swept by `#audit_namespace FX1Poly.Core` in
    `AuditCoreSubstrate.lean`; the typed payoff is pinned per-decl here. -/

#assert_no_axioms FX1Poly.Typed.IsType.hasNoStep
#assert_no_axioms FX1Poly.Typed.Conv.eq_of_isType
#assert_no_axioms FX1Poly.Typed.levelFlag_eq_of_conv_universeCodeCell
#assert_no_axioms FX1Poly.Typed.Conv.iff_eq_of_isType
#assert_no_axioms FX1Poly.Typed.Conv.decidableOfIsType

/-! ### Typed subject reduction (P4, native pi/sigma-formation HasType core) — `subjectHasNoStep`
    is the structural invariant (well-typed subjects are normal); SR itself
    holds vacuously over the redex-free fragment. -/

#assert_no_axioms FX1Poly.Typed.HasType.subjectHasNoStep
#assert_no_axioms FX1Poly.Typed.HasType.subjectReduction

/-! ### Universe-code cell destructor — recovers
    `universeCodeCell e flag` from `headGenerator = gen_universeCode` via the
    `RawTermChildren.eq_childNil` brick; the raw destructor `Decidable IsType`
    needs to apply `HasType.universeFormation`. -/

#assert_no_axioms FX1Poly.Typed.eq_universeCodeCell_of_headGenerator
#assert_no_axioms FX1Poly.Typed.eq_variableCell_of_headGenerator
#assert_no_axioms FX1Poly.Typed.headGenerator_universeCodeCell
#assert_no_axioms FX1Poly.Typed.headGenerator_variableCell
-- universe-code cell injectivity (no-Type-in-Type probe support): equal
-- universe codes have equal levels and flags, via `cases` on the cell equality
#assert_no_axioms FX1Poly.Typed.universeCodeCell_inj

/-! ### Π-formation shape bricks — `piTyCodeCell`
    smart ctor + head-generator computation + the two-child destructor that
    the `piFormation` arm + the decider consume. -/

#assert_no_axioms FX1Poly.Typed.headGenerator_piTyCodeCell
#assert_no_axioms FX1Poly.Typed.eq_piTyCodeCell_of_headGenerator
#assert_no_axioms FX1Poly.Typed.piTyCodeCell_noStep_of_childrenNoStep
-- `piTyCodeCell` is injective (domain/codomain recovered): the component extractor
-- the `piFormation` arm of `inversionPiCode` aligns the inducted arm's own
-- domain/codomain with the inversion target.  `cases` on the cell equality (the
-- propext-free substrate tactic), NOT `injection`.
#assert_no_axioms FX1Poly.Typed.piTyCodeCell_inj

/-! ### Π-cell rename/subst commutations —
    `rename`/`subst` distribute over a `piTyCodeCell` (domain at shift `0`,
    codomain at shift `1` under `iterateLiftRaw _ 1`), both `rfl` via the
    canonical fold.  The typed-weakening / typed-substitution Π cases
    chain these with the `RawTermSubst0Commute` `iterateLiftRaw` lemmas. -/

#assert_no_axioms FX1Poly.Typed.rename_piTyCodeCell
#assert_no_axioms FX1Poly.Typed.subst_piTyCodeCell

/-! ### Rename lift-weaken commutation — the
    naturality square `lift ρ ∘ weaken = weaken ∘ ρ` at the term level, the
    binder-crossing crux the `piFormation` case of `renameRespectingContext`
    discharges its lifted context-condition with. -/

#assert_no_axioms FX1Poly.Typed.rename_lift_weaken_commute
#assert_no_axioms FX1Poly.Typed.subst_lift_weaken_commute

/-! ### Π-cell size measure — domain and
    codomain are `RawTerm.size`-smaller than the `piTyCodeCell` containing them.
    The `decreasing_by` obligations a well-founded recursive Π-formation decider
    discharges, sidestepping the `RawTerm`/`RawTermChildren` mutual
    `termination_by` boundary gap with a plain `Nat` measure. -/

#assert_no_axioms FX1Poly.Typed.size_lt_piTyCodeCell_domain
#assert_no_axioms FX1Poly.Typed.size_lt_piTyCodeCell_codomain

/-! ### Σ-formation shape substrate — the complete
    raw-cell substrate for the Σ-formation arm, the dual of the Π substrate.
    `gen_sigmaTyCode` is structurally identical to `gen_piTyCode` ([0, 1] binder
    shifts, `Unit` payload), so each brick is the exact analog of its
    `piTyCodeCell` counterpart with the head generator swapped: the smart-ctor
    head computation, the two-child destructor, injectivity, non-stepping (pure
    type former), the `rename`/`subst` commutations (both `rfl`), and the
    `RawTerm.size` `decreasing_by` bricks.  The Σ arm + its decider consume
    these. -/

#assert_no_axioms FX1Poly.Typed.headGenerator_sigmaTyCodeCell
#assert_no_axioms FX1Poly.Typed.eq_sigmaTyCodeCell_of_headGenerator
#assert_no_axioms FX1Poly.Typed.sigmaTyCodeCell_inj
#assert_no_axioms FX1Poly.Typed.sigmaTyCodeCell_noStep_of_childrenNoStep
#assert_no_axioms FX1Poly.Typed.rename_sigmaTyCodeCell
#assert_no_axioms FX1Poly.Typed.subst_sigmaTyCodeCell
#assert_no_axioms FX1Poly.Typed.size_lt_sigmaTyCodeCell_domain
#assert_no_axioms FX1Poly.Typed.size_lt_sigmaTyCodeCell_codomain

/-! ### IsType characterization — the decision on the
    head generator that `Decidable IsType` assembles: universe codes are always
    types; a variable is a type iff its looked-up classifier is a universe code
    (forward by `inversionVariable` + rigidity); Π / Σ codes are types iff their
    children are; any other head is never a type
    (`subjectIsVariableOrTypeFormerCode`). -/

#assert_no_axioms FX1Poly.Typed.IsType.ofUniverseCodeCell
#assert_no_axioms FX1Poly.Typed.IsType.variableCell_iff_lookupIsUniverseCode
#assert_no_axioms FX1Poly.Typed.IsType.not_of_headGenerator

/-! ### Decidable IsType (native pi/sigma-formation HasType core) — the decision procedure
    assembled over the head-generator cases: case on the cell (payload = index as data),
    `dite` on the head generator (`DecidableEq Generator`, no `Classical`).  The
    Π arm makes the procedure RECURSIVE (well-founded on `RawTerm.size`); the
    data-returning core `decideWithWitness` (a `PSum` of a `Σ'` universe witness
    or a no-universe proof) carries the children's flag as DATA so the shared-flag
    side condition is decidable — an `Exists` could not eliminate into the
    `Type`-valued decision.  `decidableOfWellFormed` is a thin wrapper. -/

#assert_no_axioms FX1Poly.Typed.IsType.decideWithWitness
#assert_no_axioms FX1Poly.Typed.IsType.decidableOfWellFormed

/-! ### HasType characterization — typed checking collapses to
    classifier equality: validity makes the classifier normal, so the inversions
    + rigidity turn `HasType Γ subject T` into `T = (the unique classifier)`.
    No `Conv` decision / normalizer needed for this fragment. -/

#assert_no_axioms FX1Poly.Typed.HasType.variableCell_iff_classifierEqLookup
#assert_no_axioms FX1Poly.Typed.HasType.universeCodeCell_iff_classifierEqSucc
#assert_no_axioms FX1Poly.Typed.HasType.not_of_headGenerator

/-! ### Decidable HasType (native pi/sigma-formation HasType core) — typed checking decision
    procedure assembled over the classifier-equality characterization; mirror of
    `IsType.decidableOfWellFormed`, deciding via `DecidableEq RawTerm`. -/

#assert_no_axioms FX1Poly.Typed.HasType.decidableOfWellFormed

/-! ### Decidable typed Conv (native pi/sigma-formation HasType core) — convertibility
    of the classifiers of two well-typed terms, via validity + rigidity. -/

#assert_no_axioms FX1Poly.Typed.Conv.decidableOfTyped

/-! ### Typed smoke corpus (native pi/sigma-formation HasType core) — non-vacuity /
    regression witnesses pinning that the deciders DISCRIMINATE: one accepted +
    one rejected cell per outcome branch (universeCode-isTrue, var-isTrue,
    outer-reject, universeCode-isFalse). -/

#assert_no_axioms FX1Poly.Typed.headGenerator_unitCell
#assert_no_axioms FX1Poly.Typed.corpus_universeCode_typedBySucc
#assert_no_axioms FX1Poly.Typed.corpus_variable_typedByLookup
#assert_no_axioms FX1Poly.Typed.corpus_unitCell_rejected
#assert_no_axioms FX1Poly.Typed.corpus_universeCode_notTypedByUnit

/-! ### No-Type-in-Type probe — the headline universe-consistency
    guarantee: a universe code is NOT classified by itself (`Type@(e,f) :
    Type@(e,f)` rejected), so there is no `Type : Type` / Girard paradox at the
    universe level.  Routes through `universeCodeCell_iff_classifierEqSucc` (the
    classifier-equality characterization) + `universeCodeCell_inj` +
    `LevelExpr.ne_lsucc_self` (predicativity at the level algebra). -/

#assert_no_axioms FX1Poly.Typed.probe_universe_Type_in_Type_rejected

/-! ### Closed-typing characterization (P10 consistency precursor, native pi/sigma-formation HasType core) — every closed well-typed subject is itself a type.  The
    type-former-only fragment has NO closed proper terms (the closed `.term`
    layer below the universe is empty); `subjectIsVariableOrIsType` is the
    context-general induction engine (each non-`conv` arm witnesses `IsType` from
    its own conclusion), `closedSubjectIsType` the empty-context corollary
    (`Fin 0` kills the variable case). -/

#assert_no_axioms FX1Poly.Typed.HasType.subjectIsVariableOrIsType
#assert_no_axioms FX1Poly.Typed.HasType.closedSubjectIsType

/-! ### Closed-typing characterization, both halves (P10 precursor, native pi/sigma-formation HasType core) — the two complementary halves of "what is a closed typing
    judgment?".  `closedSubjectIsTypeFormer`: a closed well-typed subject is
    EXACTLY a universe / Π / Σ type-former code (canonical forms; the `var`
    disjunct of the 4-way shape classification is killed by `Fin 0`).
    `closedClassifierConvUniverseCode`: its classifier is Conv to a universe code
    (via `closedSubjectIsType` + `uniqueness` at the empty `WfContext`) — the
    consistency content (no closed inhabitant below the universe level), the
    precursor to ★ #460 (which additionally needs an `Empty` former). -/

#assert_no_axioms FX1Poly.Typed.HasType.closedSubjectIsTypeFormer
#assert_no_axioms FX1Poly.Typed.HasType.closedClassifierConvUniverseCode

/-! ### Context well-formedness decision
    — `WfContext.decidable` decides whether a raw `TypingContext` telescope is
    well-formed (every binding is a type in its prefix), by structural recursion
    on the telescope delegating each binding to `IsType.decidableOfWellFormed`
    under the prefix certificate.  The context-level checker complementing
    the term-level `Decidable IsType`/`HasType`/`Conv`.  Confirms the indexed
    two-constructor telescope match stays propext-clean into a `Decidable`
    motive. -/

#assert_no_axioms FX1Poly.Typed.WfContext.decidable

/-! ### Type synthesis / bidirectional `infer` (native pi/sigma-formation HasType core)
    — synthesise a subject's classifier + derivation (sound by construction);
    `var` direct, every other head delegates to `IsType.decideWithWitness`.
    `infer_succeeds` is totality on the typeable domain (via the
    `subjectIsVariableOrIsType` classification); `infer_complete` converts the
    synthesised type to any actual one via `uniqueness`.  The `simp only
    [HasType.infer, dif_pos/dif_neg]` reductions stay propext-clean (head
    `dite` on `DecidableEq Generator`, no indexed-match leak). -/

#assert_no_axioms FX1Poly.Typed.HasType.infer
#assert_no_axioms FX1Poly.Typed.HasType.infer_succeeds
#assert_no_axioms FX1Poly.Typed.HasType.infer_complete

/-! ### Type checking / bidirectional `check` (native pi/sigma-formation HasType core)
    — decide whether `subject` has the GIVEN `targetType`: synthesise with
    `infer`, confirm `targetType` is a type (`decideWithWitness`), decide
    `Conv synthType targetType`, coerce via the conversion rule on success.
    Returns `Decidable (HasType …)` (the faithful realisation of the spec's
    "`Option HasType`" — `Option` of a `Prop` is ill-typed), so it is sound AND
    complete by construction: `isTrue` carries the derivation, `isFalse` the
    refutation (`infer = none` ⊥ `infer_succeeds`; non-type target ⊥ validity;
    `Conv = isFalse` ⊥ uniqueness).  The general bidirectional method rests on
    `infer` + generic decidable `Conv`, not the fragment-specific collapse; on
    this fragment it agrees with the direct decider. -/

#assert_no_axioms FX1Poly.Typed.HasType.check

/-! ### Typed checking certificate (native pi/sigma-formation HasType / HasTypeDesc formation core)
    — explicit record packaging of the already-proved native-pi-sigma HasType typed
    checking (`decidableOfWellFormed` + bidirectional `check`), equivalent
    description-engine checking (`HasTypeDesc.decidableOfWellFormed` + the two
    translation maps), typed classifier conversion (`Conv.decidableOfTyped` /
    `Conv.decidableOfHasTypeDesc`), validity, and typed SN.
    This is deliberately scoped to the native pi/sigma-formation `HasType` core; the
    description-driven `HasTypeDescPi` reducibility assembly remains the next
    metatheory step. -/

#assert_no_axioms FX1Poly.Typed.HasTypePiSigmaFormationCheckingCertificate
#assert_no_axioms FX1Poly.Typed.HasTypePiSigmaFormationCheckingCertificate.decideHasTypeDesc
#assert_no_axioms FX1Poly.Typed.HasTypePiSigmaFormationCheckingCertificate.translateHasTypeToDesc
#assert_no_axioms FX1Poly.Typed.HasTypePiSigmaFormationCheckingCertificate.translateDescToHasType
#assert_no_axioms FX1Poly.Typed.HasTypePiSigmaFormationCheckingCertificate.decideHasTypeDescClassifierConv
#assert_no_axioms FX1Poly.Typed.HasTypePiSigmaFormationCheckingCertificate.proveHasTypeDescClassifierIsTypeDesc
#assert_no_axioms FX1Poly.Typed.HasTypePiSigmaFormationCheckingCertificate.proveHasTypeDescSubjectIsStronglyNormalizing
#assert_no_axioms FX1Poly.Typed.HasTypePiSigmaFormationCheckingCertificate.proveHasTypeDescClassifierIsStronglyNormalizing
#assert_no_axioms FX1Poly.Typed.HasTypePiSigmaFormationCheckingCertificate.proveHasTypeDescSubjectAndClassifierStronglyNormalizing
#assert_no_axioms FX1Poly.Typed.HasTypePiSigmaFormationCheckingCertificate.proveClassifierIsStronglyNormalizing
#assert_no_axioms FX1Poly.Typed.HasTypePiSigmaFormationCheckingCertificate.proveSubjectAndClassifierStronglyNormalizing
#assert_no_axioms FX1Poly.Typed.HasTypePiSigmaFormationCheckingCertificate.rejectHasTypeLambda
#assert_no_axioms FX1Poly.Typed.HasTypePiSigmaFormationCheckingCertificate.rejectHasTypeApplication
#assert_no_axioms FX1Poly.Typed.HasTypePiSigmaFormationCheckingCertificate.rejectHasTypeDescLambda
#assert_no_axioms FX1Poly.Typed.HasTypePiSigmaFormationCheckingCertificate.rejectHasTypeDescApplication
#assert_no_axioms FX1Poly.Typed.buildHasTypePiSigmaFormationCheckingCertificate
#assert_no_axioms FX1Poly.Typed.HasTypePiSigmaFormationCheckingCertificate.proveClosedSubjectIsType
#assert_no_axioms FX1Poly.Typed.HasTypePiSigmaFormationCheckingCertificate.proveClosedSubjectIsTypeFormer
#assert_no_axioms FX1Poly.Typed.HasTypePiSigmaFormationCheckingCertificate.proveClosedClassifierConvUniverseCode
#assert_no_axioms FX1Poly.Typed.HasTypePiSigmaFormationCheckingCertificate.proveClosedSubjectAndClassifierStronglyNormalizing
#assert_no_axioms FX1Poly.Typed.HasTypePiSigmaFormationCheckingCertificate.proveClosedHasTypeDescSubjectIsTypeDesc
#assert_no_axioms FX1Poly.Typed.HasTypePiSigmaFormationCheckingCertificate.proveClosedHasTypeDescSubjectIsTypeFormer
#assert_no_axioms FX1Poly.Typed.HasTypePiSigmaFormationCheckingCertificate.proveClosedHasTypeDescClassifierConvUniverseCode
#assert_no_axioms FX1Poly.Typed.HasTypePiSigmaFormationCheckingCertificate.proveClosedHasTypeDescSubjectAndClassifierStronglyNormalizing

/-! ### ★ MOONSHOT CORE — the description-driven generic typing engine
    (`HasTypeDesc`, polycell.md §11.8.5 / §5.2: the Natural-Model display map
    `Tm ↠ Ty` realized as a data-driven cascade-free `gen` arm).  `HasTypeDesc`
    = var + conv + nullary `universeFormation` + ONE generic `genFormation` arm
    consuming a per-generator `TypingRuleDesc` (the `typingRuleDescOf` table),
    typing the whole dependent-type-former family via the mutual `DescTelescope`
    spine with output = `rule.outputType scope levels flag` (for the type-formers,
    `universeFormerOutput = universeCodeCell (lmaxAll levels) flag`).  The
    `outputType` field realizes the §11.8.5 "non-uniform output" seam (output is
    rule-DATA, not hardwired).
    The two reconstruction theorems witness Π AND Σ through the SAME arm (P13
    cascade-freedom: a new dependent former is one `typingRuleDescOf` row, ZERO
    new arms).  Propext-free `lmaxFold`/`lmaxAll` (no overlapping patterns) +
    `typingRuleDescOf` (nested `if` over DecidableEq, no 194-ctor wildcard);
    `TypingRuleDesc` is pure syntax (no HasTypeDesc → genFormation strictly
    positive); output classifier an explicit INDEX (Prop, P14). -/

#assert_no_axioms FX1Poly.Typed.lmaxFold
#assert_no_axioms FX1Poly.Typed.lmaxAll
#assert_no_axioms FX1Poly.Typed.universeFormerOutput
#assert_no_axioms FX1Poly.Typed.TypingRuleDesc
#assert_no_axioms FX1Poly.Typed.typingRuleDescOf
#assert_no_axioms FX1Poly.Typed.typingRuleDescOf_piTyCode
#assert_no_axioms FX1Poly.Typed.typingRuleDescOf_sigmaTyCode
#assert_no_axioms FX1Poly.Typed.HasTypeDesc
#assert_no_axioms FX1Poly.Typed.DescTelescope
#assert_no_axioms FX1Poly.Typed.hasTypeDesc_piFormation_viaGenArm
#assert_no_axioms FX1Poly.Typed.hasTypeDesc_sigmaFormation_viaGenArm
-- COMPLETENESS: the description engine is at least as strong as the bespoke
-- HasType (every HasType derivation maps to HasTypeDesc; Π/Σ via the generic arm).
#assert_no_axioms FX1Poly.Typed.HasType.toHasTypeDesc
-- SOUNDNESS (0-FP wrt the trusted engine): every HasTypeDesc derivation maps back
-- to the bespoke HasType — the description engine derives NOTHING the hand-written
-- kernel wouldn't.  Mutual with the premise-spine map; the genFormation case's
-- exfalso branch proves a non-whitelisted generator cannot fire the generic arm.
-- Together with completeness this is the full HasTypeDesc ⟺ HasType equivalence on
-- the formation fragment — the cascade-free engine is a faithful replacement.
#assert_no_axioms FX1Poly.Typed.HasTypeTelescope
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.toHasType
#assert_no_axioms FX1Poly.Typed.DescTelescope.toHasTypeTelescope
-- DECIDABILITY (P11 0-FN) of the description engine, transported across the
-- proven ⟺ equivalence from the bespoke `HasType.decidableOfWellFormed`: the
-- cascade-free description-driven `gen` arm is a genuine DECIDABLE typechecker on
-- the native pi/sigma-formation HasType core.  Hand-built (match on the bespoke decision + the two
-- equivalence maps), no `decidable_of_iff`/`Iff`, so propext-free.
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.decidableOfWellFormed
#assert_no_axioms FX1Poly.Typed.Conv.decidableOfHasTypeDesc

/-! ### Eliminator-shape SUBSTRATE for the description engine (`HasTypeDescElim`).
    `DescTermTelescope` — the maximally-general typed-children spine over the
    PRIMARY engine `HasTypeDesc`: each child typed at an ARBITRARY classifier (the
    eliminator shape — scrutinee/motive/branches at motive-dependent types, NOT
    universes), the §11.8.5 PREMISE-side seam past formation (the output-side seam
    was opened by `outputType`).  Non-vacuous: `DescTelescope.toTermTelescope` shows
    the formation spine is an INSTANCE (so the substrate subsumes formation);
    `descTermTelescope_heterogeneous` witnesses a telescope at arbitrary classifiers
    the universe-only spine cannot express.  Standalone (HasTypeDesc positive in
    `cons` only); `toTermTelescope` is the propext-free term-mode `match` (mirrors
    `DescTelescope.toHasTypeTelescope`), self-recursive only. -/
#assert_no_axioms FX1Poly.Typed.DescTermTelescope
#assert_no_axioms FX1Poly.Typed.DescTelescope.toTermTelescope
#assert_no_axioms FX1Poly.Typed.descTermTelescope_heterogeneous

/-! ### Intrinsic VALIDITY of the description engine (`HasTypeDescValidity`) — a
    brick of the HasTypeDesc-from-HasType DECOUPLE.  The ⟺ equivalence
    (`HasTypeDesc.toHasType`) is total, so it forbids growing the engine with any
    `gen` row the bespoke `HasType` lacks (would break soundness ⇒ force a bespoke
    arm = the cascade we kill).  Decoupling = giving `HasTypeDesc` its OWN metatheory.
    `IsTypeDesc` = the intrinsic "inhabits a universe" (over `HasTypeDesc`, not
    `HasType`); `classifierIsTypeDesc` = validity (P3) proved by FULL-enumeration
    term-mode `match` on the engine (the propext-free form of
    `HasTypeDesc.toHasType`) — `var` lifts the context entry via completeness,
    `conv` reuses `reclassifierTyped` verbatim (no `Conv.trans`), formation arms
    re-fire `universeFormation` one level up (genFormation pinned by the same
    `by_cases`+`exfalso` generator-pin). -/
#assert_no_axioms FX1Poly.Typed.IsTypeDesc
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.classifierIsTypeDesc

/-! ### Strong normalization and typed conversion for the description formation engine.
    These are the `HasTypeDesc`-side consequences of the proven `HasTypeDesc -> HasType` soundness map:
    subject SN, type SN, and typed-middle conversion transitivity.  They are scoped to the description
    formation engine and do not claim the grown lambda/application reducibility theorem. -/
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.isStronglyNormalizing
#assert_no_axioms FX1Poly.Typed.IsTypeDesc.toIsType
#assert_no_axioms FX1Poly.Typed.IsTypeDesc.isStronglyNormalizing
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.classifierStronglyNormalizing
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.subjectAndClassifierStronglyNormalizing
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.closedSubjectAndClassifierStronglyNormalizing
#assert_no_axioms FX1Poly.Typed.Conv.trans_of_hasTypeDescMiddle

/-! ### Closed-form consequences for the description formation engine.  These expose the native
    closed-form facts through the proven `HasTypeDesc <-> HasType` bridge: closed subjects are intrinsic
    description types, have universe/Pi/Sigma type-former shape, and have classifiers convertible to
    universe codes. -/
#assert_no_axioms FX1Poly.Typed.IsType.toIsTypeDesc
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.closedSubjectIsTypeDesc
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.closedSubjectIsTypeFormer
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.closedClassifierConvUniverseCode

/-! ### INVERSION (P8 descent, premise half) for the description engine
    (`HasTypeDescInversion`).  polycell.md §11.8.5 P8: from a `piTyCodeCell`'s
    `HasTypeDesc`-typing recover the domain/codomain child typings (at a shared
    universe flag).  `Conv`-FREE: the children are fixed by the subject, so the
    `conv` arm forwards the child-typing IH verbatim (no `Conv.trans`, no
    `WfContext`) — isolating the descent content (the children's types, what the
    typechecker + canonicity consume) from the `Conv`-blocked classifier conjunct.
    Term-mode recursive `match` (NOT `induction`, which rejects the mutual
    `HasTypeDesc`) + `injection`/`subst_vars` + `congrArg RawTerm.headGenerator` +
    `Generator.noConfusion` (the propext-free recipe of the bespoke inversions).
    Covers BOTH the dependent-binary formers (Π over `gen_piTyCode`, Σ over
    `gen_sigmaTyCode`).  `…General` is the subject-generalized recursive workhorse;
    `inversion{Pi,Sigma}Code` the concrete `{pi,sigma}TyCodeCell` entry points. -/
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.inversionPiCodeGeneral
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.inversionPiCode
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.inversionSigmaCodeGeneral
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.inversionSigmaCode

/-! ### INVERSION (P8, FULL) for the description engine — premise telescope AND the
    classifier-`Conv` conjunct (`…WithConv`).  Wires typed `Conv.trans`
    into the description engine: `…WithConv` additionally concludes `Conv classifier
    (universeCodeCell (lmaxAll levels) flag)` — the cell's classifier converts to the
    canonical formation output.  This is the conjunct intrinsic UNIQUENESS (P7) and the
    typechecker's conv-check consume.  Three deltas over the premise half: a `WfContext`
    parameter (threaded as an OUTER argument — the term-mode `match` keeps the context
    index fixed, so it need not be reverted into the motive as the bespoke
    `induction`-based inversion must); the `conv` arm composes `Conv`s via
    `Conv.trans_of_typedMiddle`, the middle's `IsType` from `classifierIsType ∘
    toHasType` on the `conv` premise; the `genFormation` arm pins the `TypingRuleDesc`
    (`Option.some.inj`) so the output reduces to `universeCodeCell (lmaxAll …) …`, then
    `Conv.refl` closes the conjunct.  Both formers (Π + Σ). -/
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.inversionPiCodeWithConvGeneral
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.inversionPiCodeWithConv
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.inversionSigmaCodeWithConvGeneral
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.inversionSigmaCodeWithConv

/-! ### Leaf inversions (`var`, `universeCode`) for the description engine — the two
    NON-compound subjects, completing the per-shape inversion suite (var / universeCode
    / Π / Σ).  A variable cell's classifier is convertible to its context lookup; a
    universe-code cell's to the next universe.  Analogues of the bespoke
    `HasType.inversion{Variable,UniverseCode}`, via the term-mode recursive `match` (the
    mutual `HasTypeDesc` rejects `induction`): the `conv` arm composes through the
    premise's classifier (a type by validity) with `Conv.trans_of_typedMiddle`; the
    impossible `genFormation` arm is refuted by `subst`-ing the pinned non-formation
    generator and a `contradiction` against `typingRuleDescOf … = some rule` (the
    whitelist reduces to `none` for `gen_var` / `gen_universeCode`); the matching leaf
    arm closes by `Conv.refl` after `injection`.  These are the leaf cases intrinsic
    UNIQUENESS (P7) consumes when inverting the second derivation. -/
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.inversionVariableGeneral
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.inversionVariable
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.inversionUniverseCodeGeneral
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.inversionUniverseCode

/-! ### Component descent (P8) — projecting the typed CHILDREN of a Π/Σ formation cell
    (`HasTypeDescInversion`).  The `…WithConv` inversions yield the premise telescope; the
    typechecker / canonicity consume the DOMAIN and CODOMAIN typings directly.  These
    corollaries case the two-child `binderShape` telescope (the SAME shape the soundness
    map performs) to project `HasTypeDesc Γ domain Type@(dl,f)` ∧ `HasTypeDesc (Γ.cons
    domain) codomain Type@(cl,f)` ∧ `Conv classifier Type@(lmax dl cl, f)`.  Two definitional
    facts keep it transport-free: `scope + 0 ≡ scope` (binderShape's `Nat.add_zero ▸ domain`
    head is just `domain`) and `lmaxAll [dl, cl] ≡ lmax dl cl`.  The INTRINSIC analogue of
    the bespoke `HasType.inversionPiCode` in component form. -/
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.inversionPiCodeComponents
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.inversionSigmaCodeComponents

/-! ### UNIQUENESS of typing (P7) for the description engine
    (`HasTypeDescUniqueness`).  polycell.md §11.8.5 P7: any two classifiers a cell
    receives are convertible.  A recursion on `HasTypeDesc` ITSELF: the `var` /
    `universeFormation` arms invert the second derivation (INTRINSIC leaf inversions);
    the `conv` arm recurses INTRINSICALLY through `Conv.trans_of_typedMiddle`; the
    `genFormation` arm is intrinsic — it inverts the second derivation with the
    INTRINSIC `inversion{Pi,Sigma}CodeWithConvGeneral`, then forces the two formation
    telescopes to agree on `levels`/`flag` via `DescTelescope.uniquenessAgree`, after
    which both classifiers reduce to the SAME canonical universe code.  The ONE remaining
    leaf coupling is `uniquenessAgree` settling each HEAD CHILD's level/flag through the
    verified bespoke `HasType.uniqueness` (a standalone recursion cannot call the
    intrinsic uniqueness it precedes; a fully intrinsic version would make the two
    MUTUAL).  P7 makes `infer` well-defined and feeds canonicity. -/
#assert_no_axioms FX1Poly.Typed.DescTelescope.uniquenessAgree
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.uniqueness

/-! ### INTRINSIC renaming/weakening (P6, the β-engine) for the description engine
    (`HasTypeDescWeakening`).  polycell.md §11.8.5 P6: typing is preserved along a context
    morphism.  `HasTypeDesc.renameRespectingContext` (with its telescope companion
    `DescTelescope.renameRespectingTelescope`) preserves `HasTypeDesc` along any renaming
    respecting the context; `HasTypeDesc.weakenUnderBinding` is the weakening special case.
    An intrinsic-BY-INDUCTION `HasTypeDesc` metatheorem of the decouple (validity /
    inversion / uniqueness are case-analysis; this is genuine MUTUAL recursion) — proved
    NOT through the `⟺` maps.  Lands as a clean mutual recursion because it has NO
    second-derivation inversion (cross-calls on pristine `match`-bound subterms, like
    `toHasType`); the genFormation companion cross-call is HOISTED before the `by_cases` so
    `premises` stays pristine for the structural-recursion checker.  The telescope
    companion's lifted context-condition is the N-binder generalization of the bespoke
    `piFormation` codomain handling, reusing `rename_lift_weaken_commute` at every depth
    (`iterateLiftRaw ρ (cd+1) ≡ lift (iterateLiftRaw ρ cd)`). -/
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.renameRespectingContext
#assert_no_axioms FX1Poly.Typed.DescTelescope.renameRespectingTelescope
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.weakenUnderBinding

/-! ### INTRINSIC substitution (P6, the β-engine) for the description engine
    (`HasTypeDescSubstitution`).  polycell.md §11.8.5 P6: the SUBSTITUTION half of whiskering
    — the engine `app`'s β-reduction `b[a]` needs to preserve typing.
    `HasTypeDesc.substRespectingContext` (with companion `DescTelescope.substRespectingTelescope`)
    preserves `HasTypeDesc` along any substitution whose substituents are target-typed at the
    substituted source-binding types; `HasTypeDesc.substituteUnderBinding` is the `subst0`
    corollary the β-rule cites.  An intrinsic-by-induction mutual metatheorem — same
    clean shape as intrinsic weakening (no second-derivation inversion), and the decouple
    COMPOUNDS: the companion's successor case reuses the intrinsic
    `HasTypeDesc.weakenUnderBinding` to weaken the substituent across the binder.  `Conv.subst`
    (#370) rides the `conv` arm — no `Conv.trans`, so the β-engine does not depend on raw
    confluence.  NOT routed through the `⟺` maps. -/
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.substRespectingContext
#assert_no_axioms FX1Poly.Typed.DescTelescope.substRespectingTelescope
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.substituteUnderBinding

/-! ### INTRINSIC renaming/weakening (P6) for the ELIMINATOR-shape term spine
    (`HasTypeDescElimWeakening`).  polycell.md §11.8.5 P6 applied to `DescTermTelescope` — the
    maximally-general typed-children spine (each child at an ARBITRARY classifier) that the
    eliminator `gen`-arm (the non-uniform seam PAST formation) consumes.  This is the
    eliminator spine's cartesian-lift fibration leg.

    NON-breaking: `DescTermTelescope` is a STANDALONE inductive (`HasTypeDesc` appears only
    positively in `cons`'s `headTyped`), so this touches neither `HasTypeDesc`'s constructors
    nor the `toHasType` ⟺ soundness map.  SELF-recursive (not a mutual block): the head child's
    typing is re-renamed by `HasTypeDesc.renameRespectingContext` on the opaque
    `headTyped`; the only recursion is the strictly-smaller `restTyped`, so Lean's structural
    recursion lands it without `termination_by` — exactly like `DescTelescope.toTermTelescope`.
    The arbitrary classifier renames generically (no universe-code brick); the tail's lifted
    context-condition reuses `rename_lift_weaken_commute` at every depth.  `weakenUnderBinding`
    is the depth-0 corollary whose context-condition holds definitionally (`fun _ => rfl`, via
    `iterateLiftRaw _ 0 ≡ _` and `lookup_cons_succ`).  NOT routed through the `⟺` maps. -/
#assert_no_axioms FX1Poly.Typed.DescTermTelescope.renameRespectingTermTelescope
#assert_no_axioms FX1Poly.Typed.DescTermTelescope.weakenUnderBinding

/-! ### INTRINSIC substitution (P6, the β-engine) for the ELIMINATOR-shape term spine
    (`HasTypeDescElimSubstitution`).  polycell.md §11.8.5 P6 applied to `DescTermTelescope` —
    the SUBSTITUTION leg completing the pair with the renaming/weakening leg above.  Together
    they are the eliminator spine's two fibration legs (cartesian lift + β-substitution).

    SELF-recursive (not mutual): the head child's typing is re-substituted by
    `HasTypeDesc.substRespectingContext` on the opaque `headTyped`; only recursion is on
    `restTyped` ⇒ structural recursion w/o `termination_by`.  The arbitrary classifier
    substitutes generically (no `subst_universeCodeCell` brick).  The tail's lifted
    substitution-condition's `0`/successor split is IDENTICAL to the formation spine — `0` →
    fresh `var`, `k+1` → the substituent weakened across the binder via the intrinsic
    `HasTypeDesc.weakenUnderBinding` (the decouple COMPOUNDS: eliminator-spine subst stands on
    intrinsic HasTypeDesc weakening, no `HasType`).  `substituteUnderBinding` is the depth-0
    `subst0` corollary (singleton-cancel side-condition, symmetric to `weakenUnderBinding`).
    NON-breaking: `DescTermTelescope` standalone, touches neither `HasTypeDesc` ctors nor the
    `⟺` maps. -/
#assert_no_axioms FX1Poly.Typed.DescTermTelescope.substRespectingTermTelescope
#assert_no_axioms FX1Poly.Typed.DescTermTelescope.substituteUnderBinding

/-! ### DEPENDENT-ELIMINATOR OUTPUT VALIDITY (`HasTypeDescApplication`).  polycell.md §11.8.5
    non-uniform seam: an eliminator's output type is motive-dependent (it instantiates the
    codomain at the eliminated value).  These two lemmas prove the SOUNDNESS HEART of the
    `app`/`snd` rules — that the instantiated codomain is a well-formed type — by composing
    three intrinsic bricks: validity (`classifierIsTypeDesc`), Π/Σ inversion-components, and
    the β-engine `substituteUnderBinding`, feeding the intrinsic substitution into a
    dependent-elimination soundness fact.  POSITIVE construction
    (not a degenerate SR/Conv-stability collapse): `piApplicationOutputIsType` —
    `f : Π A.B`, `a : A` ⊢ `B[a]` IsType; `sigmaProjectionOutputIsType` — the Σ mirror.
    `subst0 (universeCodeCell ..) argument ≡ universeCodeCell ..` by defeq (subst0 reducible +
    subst_universeCodeCell rfl) closes the `IsTypeDesc` witness.  NON-breaking: standalone
    lemmas, touch neither `HasTypeDesc` ctors nor the `⟺` maps. -/
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.piApplicationOutputIsType
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.sigmaProjectionOutputIsType

/-! ### The engine past formation + first non-vacuous subject reduction
    (`HasTypeDescPi`).  polycell.md §11.8.5: 0-FP is FREE BY CONSTRUCTION (intrinsic intro rules
    ⇒ empty fiber over the unsound), so the `toHasType ⟺ HasType` map is a formation-fragment
    CROSS-CHECK, not the soundness source.  `HasTypeDescPi` ADDITIVELY embeds the formation
    fragment (`ofFormation`) and adds Π-introduction (λ) + Π-elimination (app) + its own `conv`
    — the first engine that expresses β-redexes.  NON-breaking: leaves `HasTypeDesc`,
    `toHasType`, `decidableOfWellFormed`, and the uniqueness proofs untouched (sidesteps the
    decidability/uniqueness cascade a direct `HasTypeDesc` extension would force); `HasTypeDesc`
    cannot type lamCell/appCell (no `typingRuleDescOf` row for gen_lam/gen_app), so `ofFormation`
    of a redex is impossible and the engine genuinely EXTENDS coverage.
    `betaCoherence_formationBody` is the first non-vacuous SR in the kernel: a β-redex
    `app(lam body) arg` and its β-reduct `subst0 body arg` BOTH type at `subst0 codomainCode arg`
    — redex by piElim∘piIntro, reduct by the intrinsic `substituteUnderBinding`.  Scope:
    preservation for component-derived redexes; fully-general inverted SR additionally needs
    Π-arm inversion + grown-engine substitution. -/
#assert_no_axioms FX1Poly.Typed.lamCell
#assert_no_axioms FX1Poly.Typed.appCell
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi
#assert_no_axioms FX1Poly.Typed.IsTypeDescPi
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.toHasTypeDescPi
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.betaCoherence_formationBody

/-! ### Grown-engine renaming/weakening (P6, the cartesian-lift leg) — `HasTypeDescPiWeakening`.
    polycell.md §11.8.5 P6 applied to the grown engine `HasTypeDescPi`: its cartesian-lift
    fibration leg.  Renaming PRESERVES formation-ness (introduces no eliminations), so the
    `ofFormation` arm delegates directly to `HasTypeDesc.renameRespectingContext` and
    re-wraps — no closure gap (term-substitution does not preserve formation-ness, which is why
    the grown engine carries the native `piFormation` / `genFormationPi` arms).  Self-recursive
    (not mutual): cross-call to the formation renamer on the opaque `formationTyped`; recursions
    on the strictly-smaller `HasTypeDescPi`
    sub-derivations ⇒ structural recursion w/o `termination_by`.  `piIntro` crosses one binder
    (one-binder context-condition via `rename_lift_weaken_commute`); `piElim`'s output commutes by
    `rename_subst0_commute`.  `weakenUnderBinding` is the `fun _ => rfl` corollary.  NON-breaking:
    leaves HasTypeDesc/toHasType/decidability/uniqueness untouched. -/
#assert_no_axioms FX1Poly.Typed.rename_lamCell
#assert_no_axioms FX1Poly.Typed.rename_appCell
#assert_no_axioms FX1Poly.Typed.renameContextCondition_cons
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.renameRespectingContext
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.weakenUnderBinding

/-! ### GENERIC GROWN FORMATION ARM — `genFormationPi` + `DescTelescopePi` (cascade-death at the
    grown layer, the §5-endgame direction).  `HasTypeDescPi` is a mutual block with the grown
    premise spine `DescTelescopePi`; its sole formation arm `genFormationPi` is generic over
    `typingRuleDescOf` (the grown mirror of `HasTypeDesc.genFormation`) — a new dependent former is
    ONE table row, ZERO new arms (P13).  The generic arm types a former with GROWN components (the
    `DescTelescopePi` heads are `HasTypeDescPi`, not just formation) with NO per-former dispatch,
    which is what makes the grown engine SUBSTITUTION-CLOSED generically — a per-former arm would
    force a partial-match on the child telescope (the indexed-inductive propext trap).
    `toDescTelescopePi` + `genFormationToHasTypeDescPi` exhibit that every formation Π/Σ is a
    `genFormationPi`.  The renaming leg `HasTypeDescPi.renameRespectingContext` is mutual with the
    spine companion `DescTelescopePi.renameRespectingTelescope`. -/
#assert_no_axioms FX1Poly.Typed.DescTelescopePi
#assert_no_axioms FX1Poly.Typed.DescTelescope.toDescTelescopePi
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.genFormationToHasTypeDescPi
#assert_no_axioms FX1Poly.Typed.DescTelescopePi.renameRespectingTelescope

/-! ### GROWN-ENGINE SUBSTITUTION — `ofFormation` leg.  `HasTypeDesc.substIntoGrown` carries a
    formation derivation along a substitution whose substituents are `HasTypeDescPi`-typed, into the
    grown engine (a formation subject substituted by a grown term is no longer a formation term, so
    the result lands in `HasTypeDescPi`).  Its `genFormation` case rebuilds through the generic
    `genFormationPi` from a substituted grown spine (`DescTelescope.substIntoGrown` → `DescTelescopePi`)
    with no per-former child projection.  Mutual structural recursion on the formation derivation; the
    recursion stays within the `HasTypeDesc`/`DescTelescope` family, so no cross-inductive boundary. -/
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.substIntoGrown
#assert_no_axioms FX1Poly.Typed.DescTelescope.substIntoGrown

/-! ### GROWN-ENGINE SUBSTITUTION — full leg (the β-engine "whiskering").
    `HasTypeDescPi.substRespectingContext` (mutual with `DescTelescopePi.substRespectingTelescope`)
    carries a GROWN derivation along ANY substitution whose substituents are `HasTypeDescPi`-typed at
    the substituted source bindings — the dual of the renaming `renameRespectingContext` (cartesian
    lift).  Substitution does NOT preserve formation-ness, so its `ofFormation` arm routes through the
    completed `HasTypeDesc.substIntoGrown` (returning a grown derivation) rather than a re-wrap; that
    keeps the recursion within the `HasTypeDescPi`/`DescTelescopePi` family (no cross-inductive
    boundary).  `subst_{lamCell,appCell}` are the rfl distribution bricks; `substContextCondition_cons`
    is the one-binder lifted grown substitution-condition the `piIntro` arm needs.  This is the
    substitution lemma typed β subject reduction consumes. -/
#assert_no_axioms FX1Poly.Typed.subst_lamCell
#assert_no_axioms FX1Poly.Typed.subst_appCell
#assert_no_axioms FX1Poly.Typed.substContextCondition_cons
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.substRespectingContext
#assert_no_axioms FX1Poly.Typed.DescTelescopePi.substRespectingTelescope

/-! ### GROWN β SUBJECT REDUCTION — the subst0 corollary + general β-coherence.
    `HasTypeDescPi.substituteUnderBinding` specializes `substRespectingContext` to the singleton
    substitution (substitute a grown-typed `argument` for de Bruijn 0) — the grown β-engine, mirror
    of the formation `HasTypeDesc.substituteUnderBinding`.  `HasTypeDescPi.betaCoherence` is the
    first FULLY-GENERAL non-vacuous β subject reduction: a redex `appCell (lamCell body) argument`
    from GROWN components and its β-reduct `subst0 body argument` are BOTH typed at the same
    `subst0 codomainCode argument` (redex by `piElim ∘ piIntro`, reduct by `substituteUnderBinding`).
    It strictly generalizes `betaCoherence_formationBody` to arbitrary grown body/argument/domain. -/
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.substituteUnderBinding
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.betaCoherence

/-! ### GROWN Π/Σ-CODE COMPONENT DESCENT — the inversion eliminator output-validity + canonicity
    consume.  `HasTypeDescPi.inversionPiCodeComponents` (resp. `…Sigma…`) recovers, from a
    `piTyCodeCell`/`sigmaTyCodeCell` SUBJECT's grown typing, that the domain is a grown type and the
    codomain is a grown type under the domain binder.  The grown analogue of the formation
    `HasTypeDesc.inversionPiCodeComponents`, with the classifier-`Conv` conjunct DROPPED: the grown
    engine has no `toHasType`, so the formation inversion's `Conv.trans_of_typedMiddle` route is
    unavailable — but the consumers `_`-discard that `Conv`, so dropping it lets the `conv` arm simply
    recurse (no `Conv.trans`).  The `ofFormation` arm routes through the formation workhorse +
    `toDescTelescopePi`; `genFormationPi` is the base (premise telescope verbatim); `piIntro`/`piElim`
    are refuted by `headGenerator` clash. -/
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.inversionPiCodeTelescopeGeneral
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.inversionPiCodeComponents
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.inversionSigmaCodeTelescopeGeneral
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.inversionSigmaCodeComponents

/-! ### GROWN DEPENDENT-ELIMINATOR OUTPUT-VALIDITY — the inversion composed with the β-engine.
    `HasTypeDescPi.piCodeInstantiationIsType` (resp. `…sigma…`) proves the motive-instantiated output
    `subst0 codomainCode argument` is a grown type, given the type-former's well-formedness and an
    argument of the domain.  Composes `inversionPiCodeComponents` + `substituteUnderBinding`; the
    universe classifier lands by the `subst0`/`subst_universeCodeCell` defeq.  The type-former
    well-formedness is a HYPOTHESIS (full grown validity is blocked at the `piIntro` domain/codomain
    flag — see the file docstring); it is exactly the witness SR/canonicity carry. -/
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.piCodeInstantiationIsType
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.sigmaCodeInstantiationIsType

/-! ### GROWN VALIDITY (P3) — every classifier is a well-formed grown type.
    `HasTypeDescPi.classifierIsTypeDesc` — the grown mirror of the formation `classifierIsTypeDesc`,
    UNBLOCKED by the strengthened `piIntro` (codomain a type at the domain's flag → the Π-formation is
    reconstructible via genFormationPi without a flag mismatch).  Structural recursion: ofFormation
    routes to formation validity; conv carries its witness; piIntro rebuilds the Π-code via
    genFormationPi from domainTyped/codomainTyped; piElim recurses (function validity) + the elimination
    output-validity; genFormationPi types the universe code one level up.  Gateway to canonicity (#459)
    + consistency (#460).  One of the three metatheory pillars. -/
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.classifierIsTypeDesc

/-! ### Π/Σ-CODE `Conv` STRUCTURAL CHARACTERIZATION (injectivity + congruence), SN-FREE.
    `Conv (piTyCodeCell A B) (piTyCodeCell A' B') ↔ Conv A A' ∧ Conv B B'` (Σ dual).  Since `Conv` is
    joinability and `gen_piTyCode` is not a redex root, a Π-code's head is STABLE under reduction
    (`shapeStable_piTyCode`, via `Step.from_piTyCode`); two joinable Π-codes thus share a `piTyCodeCell`
    common reduct, and the children join componentwise — NO confluence/SN/`Conv.trans`.  The injectivity
    direction is the ingredient typed SR consumes to peel a conv-disguised Π-type; the iff is the
    decidable-`Conv` recursion for the dependent type-code formers. -/
#assert_no_axioms FX1Poly.Typed.sigmaTyCodeCell_inj
#assert_no_axioms FX1Poly.Typed.StepStar.shapeStable_piTyCodeGeneral
#assert_no_axioms FX1Poly.Typed.StepStar.shapeStable_piTyCode
#assert_no_axioms FX1Poly.Typed.StepStar.shapeStable_sigmaTyCodeGeneral
#assert_no_axioms FX1Poly.Typed.StepStar.shapeStable_sigmaTyCode
#assert_no_axioms FX1Poly.Typed.Conv.piTyCode_inj
#assert_no_axioms FX1Poly.Typed.Conv.sigmaTyCode_inj
#assert_no_axioms FX1Poly.Typed.Conv.piTyCode_cong
#assert_no_axioms FX1Poly.Typed.Conv.sigmaTyCode_cong
#assert_no_axioms FX1Poly.Typed.Conv.piTyCode_iff
#assert_no_axioms FX1Poly.Typed.Conv.sigmaTyCode_iff

/-! ### TYPE-CODE DISJOINTNESS (rigidity), SN-FREE — distinct type formers are non-convertible.
    The companion to injectivity: together they give full type-code RIGIDITY (the canonicity
    ingredient — a Π-type is never a Σ-type, never a universe).  Same head-stability mechanism
    (`shapeStable` for Π/Σ, `StepStar.eq_of_noStep` + `noStep_universeCode` for the universe leaf): a
    shared common reduct's head is forced to two distinct generators, refuted by `Generator.noConfusion`. -/
#assert_no_axioms FX1Poly.Typed.Conv.piTyCode_not_sigmaTyCode
#assert_no_axioms FX1Poly.Typed.Conv.piTyCode_not_universeCode
#assert_no_axioms FX1Poly.Typed.Conv.sigmaTyCode_not_universeCode

/-! ### REDUCIBLE CLOSING-SUBSTITUTION ENVIRONMENT (the #425 fundamental-theorem environment).
    `ReducibleEnv context γ` says `γ` sends every context variable to an `IsReducibleMember` of its
    looked-up (γ-closed) type — the ∀-form makes the fundamental theorem's `var` case
    `lookupReducible`, and the dependent membership re-substitutes each variable's type (vs the
    superseded fixed-candidate `ReducibleSubst`).  `empty` is the closed-term base; `cons` is the
    Π-introduction binder extension, its weakened lookups cancelled by `RawTerm.weaken_subst_cons`. -/
#assert_no_axioms FX1Poly.Typed.ReducibleEnv
#assert_no_axioms FX1Poly.Typed.ReducibleEnv.lookupReducible
#assert_no_axioms FX1Poly.Typed.ReducibleEnv.empty
#assert_no_axioms FX1Poly.Typed.ReducibleEnv.cons

/-! ### LEVEL-INDEXED REDUCIBLE ENVIRONMENT (the conv-closing stratified port of the above).
    `ReducibleEnvAt level context γ` rides on `IsReducibleMemberAt level` instead of `IsReducibleMember`:
    its universe arm carries each type variable's candidate ONE LEVEL DOWN, closing the conv-invariance
    gap the pure-SN `ReducibleEnv` leaves open at a type variable `x : Type@k`.  The `level` is inert
    through the `cons` binder rewrites (they touch only the looked-up type and substituted term), so the
    `empty` / `cons` / `lookupReducible` proofs port character-identically.  This is the environment the
    fundamental theorem over `HasTypeDescPi` actually consumes. -/
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAt
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAt.lookupReducible
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAt.empty
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAt.cons

/-! ### ∀-LEVEL (Kripke) reducible environment — the off-by-one resolution for the dependent fundamental
    theorem's `var` arm.  A fixed-level `ReducibleEnvAt (predLevel+1)` cannot close `var` at a TYPE variable:
    the binder steps deposit each binding at the level its classifier supplies (`predLevel` after
    `tarskiDecode`), the universe candidate changes per fuel level (no monotonic cast), so `var`'s demanded
    `predLevel+1` never matches.  `ReducibleEnvAtAllLevels` certifies every variable at ALL positive levels
    (`∀ level, ReducibleEnvAt (level+1) …`) so `var` instantiates the family at the conclusion level.  Binder
    extension additionally needs the fresh semantic argument at all positive levels; the explicit
    all-positive argument bridges below isolate that remaining condition. -/
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAtAllLevels
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAtAllLevels.lookupReducible
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAtAllLevels.empty
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAtAllLevels.cons
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAtAllLevels.toVecPositive
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAtAllLevels.ofVecPositiveFamily
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAtAllLevels.consHeadToEnvAtPositive
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAtAllLevels.consHeadToVecPositive

/-! ### PROOF-RELEVANT ∀-LEVEL ENVIRONMENT with positive type-candidate companions.  This strengthens the
    all-level environment with the binder-facing fact that every substituted lookup type has the
    all-positive member predicate as a candidate at every positive fuel level.  The `cons` operation is the
    key checked bookkeeping step: old variables use the tail companion after the weakening/substitution
    cancellation, and variable zero uses the explicit head-type companion. -/
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAtAllLevelsWithPositiveTypeCandidates
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAtAllLevelsWithPositiveTypeCandidates.toAllLevels
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAtAllLevelsWithPositiveTypeCandidates.lookupPositiveCandidate
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAtAllLevelsWithPositiveTypeCandidates.empty
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAtAllLevelsWithPositiveTypeCandidates.cons
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAtAllLevelsWithPositiveTypeCandidates.consFromPositiveTypeCandidate
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAtAllLevelsWithPositiveTypeCandidates.lookupMemberExtendsToAllPositive

/-! ### PROOF-RELEVANT ∀-LEVEL ENVIRONMENT with type-value candidate companions.  The previous strengthened
    environment records candidates for looked-up BINDING TYPES.  The two-part dependent fundamental theorem
    also needs the type-variable payload: when the substituted lookup classifier is a universe code, the
    substituted VARIABLE VALUE itself must carry positive-fuel all-positive candidates.  The universe test is
    stated after substitution so `cons` is stable by `weaken_subst_cons`, avoiding a false syntactic
    rename-reflection assumption. -/
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAtAllLevelsWithTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAtAllLevelsWithTypeValueCandidates.toPositiveTypeCandidates
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAtAllLevelsWithTypeValueCandidates.toAllLevels
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAtAllLevelsWithTypeValueCandidates.lookupPositiveCandidate
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAtAllLevelsWithTypeValueCandidates.lookupTypeValuePositiveCandidate
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAtAllLevelsWithTypeValueCandidates.empty
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAtAllLevelsWithTypeValueCandidates.cons

/-! ### Dependent fundamental theorem — bundled type-value candidate motive.  This strengthens the
    positive-candidate arm layer by carrying the conditional type-variable payload in the theorem motive
    itself: if a substituted classifier is a universe code, the substituted subject must expose the
    all-positive member predicate as a positive-fuel candidate.  The bundled validity shape prevents later
    binder/type-variable arms from trying to recover this payload by false level irrelevance. -/
#assert_no_axioms FX1Poly.Typed.FundamentalConclusionWithTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.PositiveCandidateConclusionWithTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.TypeValueCandidateConclusionWithTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.FundamentalValidityWithTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.FundamentalValidityWithTypeValueCandidates.memberConclusion
#assert_no_axioms FX1Poly.Typed.FundamentalValidityWithTypeValueCandidates.typeValueCandidateConclusion
#assert_no_axioms FX1Poly.Typed.FundamentalConclusionWithPositiveTypeCandidates.toTypeValueCandidateEnv
#assert_no_axioms FX1Poly.Typed.PositiveCandidateConclusionWithPositiveTypeCandidates.toTypeValueCandidateEnv
#assert_no_axioms FX1Poly.Typed.PositiveCandidateConclusionWithTypeValueCandidates.toTypeValueCandidateConclusion
#assert_no_axioms FX1Poly.Typed.TypeValueCandidateConclusionWithTypeValueCandidates.toPositiveCandidateOfUniverseClassifier
#assert_no_axioms FX1Poly.Typed.FundamentalValidityWithTypeValueCandidates.toPositiveCandidateOfUniverseClassifier
#assert_no_axioms FX1Poly.Typed.TypeValueCandidateConclusionWithTypeValueCandidates.ofSubstitutedClassifierNeUniverse
#assert_no_axioms FX1Poly.Typed.PositiveCandidateConclusionWithTypeValueCandidates.memberExtendsToAllPositive
#assert_no_axioms FX1Poly.Typed.PositiveCandidateConclusionWithTypeValueCandidates.consEnvWithTypeValueCandidate
#assert_no_axioms FX1Poly.Typed.HasTypeValueCandidatesForAllPositiveUniverseMembers
#assert_no_axioms FX1Poly.Typed.HasTypeValueCandidatesForAllPositiveUniverseMembers.ofSubstitutedUniverseDomainMember
#assert_no_axioms FX1Poly.Typed.HasTypeValueCandidatesForAllReducibleTypesAtAllLevels
#assert_no_axioms FX1Poly.Typed.HasPositiveMemberExtensionForStronglyNormalizingAllLevelTypes
#assert_no_axioms FX1Poly.Typed.HasTypeValueCandidatesForAllReducibleTypesAtAllLevels.toUniverseMembers
#assert_no_axioms FX1Poly.Typed.HasTypeValueCandidatesForAllPositiveUniverseMembers.toAllReducibleTypesAtAllLevels
#assert_no_axioms FX1Poly.Typed.hasTypeValueCandidatesForAllPositiveUniverseMembers_iff_allReducibleTypesAtAllLevels
#assert_no_axioms FX1Poly.Typed.hasTypeValueCandidatesForAllReducibleTypesAtAllLevels_iff_positiveMemberExtension
#assert_no_axioms FX1Poly.Typed.HasTypeValueCandidatesForAllReducibleTypesAtAllLevels.reducibleTypeAtExtendsToAllLevels
#assert_no_axioms FX1Poly.Typed.HasPositiveMemberExtensionForStronglyNormalizingAllLevelTypes.toAllReducibleTypesHaveTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.HasPositiveMemberExtensionForStronglyNormalizingAllLevelTypes.reducibleTypeAtExtendsToAllLevels
#assert_no_axioms FX1Poly.Typed.FundamentalConclusionWithTypeValueCandidates.toTypeValueCandidateConclusionOfUniverseMembersHaveTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.FundamentalConclusionWithTypeValueCandidates.toTypeValueCandidateConclusionOfAllReducibleTypesHaveTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.FundamentalConclusionWithTypeValueCandidates.toValidityOfUniverseMembersHaveTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.FundamentalConclusionWithTypeValueCandidates.toValidityOfAllReducibleTypesHaveTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.fundamentalVarWithTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.positiveCandidateVarLookupWithTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.typeValueCandidateVarWithTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.fundamentalVarValidityWithTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.fundamentalUniverseFormationWithTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.positiveCandidateUniverseCodeWithTypeValueCandidatesOfLowerTypeExtendsToAllLevels
#assert_no_axioms FX1Poly.Typed.typeValueCandidateUniverseCodeWithTypeValueCandidatesOfLowerTypeExtendsToAllLevels
#assert_no_axioms FX1Poly.Typed.fundamentalUniverseValidityWithTypeValueCandidatesOfLowerTypeExtendsToAllLevels
#assert_no_axioms FX1Poly.Typed.positiveCandidateUniverseCodeWithTypeValueCandidatesOfAllReducibleTypesHaveTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.typeValueCandidateUniverseCodeWithTypeValueCandidatesOfAllReducibleTypesHaveTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.fundamentalUniverseValidityWithTypeValueCandidatesOfAllReducibleTypesHaveTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.positiveCandidateUniverseCodeWithTypeValueCandidatesOfPositiveMemberExtension
#assert_no_axioms FX1Poly.Typed.typeValueCandidateUniverseCodeWithTypeValueCandidatesOfPositiveMemberExtension
#assert_no_axioms FX1Poly.Typed.fundamentalUniverseValidityWithTypeValueCandidatesOfPositiveMemberExtension
#assert_no_axioms FX1Poly.Typed.fundamentalConvWithTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.fundamentalConvValidityWithTypeValueCandidatesFromTargetTypeValuePremise
#assert_no_axioms FX1Poly.Typed.fundamentalConvValidityWithTypeValueCandidatesOfPositiveMemberExtension
#assert_no_axioms FX1Poly.Typed.fundamentalPiElimWithTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.fundamentalPiElimValidityWithTypeValueCandidatesFromResultTypeValuePremise
#assert_no_axioms FX1Poly.Typed.fundamentalPiElimValidityWithTypeValueCandidatesOfPositiveMemberExtension
#assert_no_axioms FX1Poly.Typed.fundamentalPiIntroWithTypeValueCandidatesFromTypeValueArgumentPremise
#assert_no_axioms FX1Poly.Typed.substitutedPiTyCode_ne_universeCodeCell
#assert_no_axioms FX1Poly.Typed.substitutedSigmaTyCode_ne_universeCodeCell
#assert_no_axioms FX1Poly.Typed.fundamentalPiIntroValidityWithTypeValueCandidatesFromTypeValueArgumentPremise
#assert_no_axioms FX1Poly.Typed.fundamentalPiIntroWithTypeValueCandidatesFromTypedArgumentPremise
#assert_no_axioms FX1Poly.Typed.fundamentalPiIntroValidityWithTypeValueCandidatesFromTypedArgumentPremise
#assert_no_axioms FX1Poly.Typed.fundamentalPiIntroValidityWithTypeValueCandidatesFromUniverseDomain
#assert_no_axioms FX1Poly.Typed.fundamentalPiIntroValidityWithTypeValueCandidatesOfAllReducibleTypesHaveTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.fundamentalPiIntroValidityWithTypeValueCandidatesOfPositiveMemberExtension
#assert_no_axioms FX1Poly.Typed.positiveCandidatePiTypeWithTypeValueCandidatesFromTypeValueArgumentPremise
#assert_no_axioms FX1Poly.Typed.typeValueCandidatePiTypeWithTypeValueCandidatesFromTypeValueArgumentPremise
#assert_no_axioms FX1Poly.Typed.formerChildrenReducibleAtDispatchLevelsWithTypeValueCandidatesFromTypeValueArgumentPremise
#assert_no_axioms FX1Poly.Typed.fundamentalPiFormationWithTypeValueCandidatesFromTypeValueArgumentPremise
#assert_no_axioms FX1Poly.Typed.fundamentalSigmaFormationWithTypeValueCandidatesFromTypeValueArgumentPremise
#assert_no_axioms FX1Poly.Typed.fundamentalSigmaFormationWithTypeValueCandidatesFromPositiveDomainCandidate
#assert_no_axioms FX1Poly.Typed.fundamentalPiFormationValidityWithTypeValueCandidatesFromTypeValueArgumentPremise
#assert_no_axioms FX1Poly.Typed.positiveCandidateSigmaTypeWithTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.typeValueCandidateSigmaTypeWithTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.fundamentalSigmaFormationValidityWithTypeValueCandidatesFromPositiveDomainCandidate
#assert_no_axioms FX1Poly.Typed.fundamentalSigmaFormationValidityWithTypeValueCandidatesFromTypeValueArgumentPremise
#assert_no_axioms FX1Poly.Typed.fundamentalPiFormationValidityWithTypeValueCandidatesOfAllReducibleTypesHaveTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.fundamentalSigmaFormationValidityWithTypeValueCandidatesOfAllReducibleTypesHaveTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.fundamentalPiFormationValidityWithTypeValueCandidatesOfPositiveMemberExtension
#assert_no_axioms FX1Poly.Typed.fundamentalSigmaFormationValidityWithTypeValueCandidatesOfPositiveMemberExtension
#assert_no_axioms FX1Poly.Typed.codomainMemberAtDomainLevelWithTypeValueCandidatesFromUniverseDomain
#assert_no_axioms FX1Poly.Typed.formerChildrenReducibleAtDispatchLevelsWithTypeValueCandidatesFromUniverseDomain
#assert_no_axioms FX1Poly.Typed.fundamentalPiFormationWithTypeValueCandidatesFromUniverseDomain
#assert_no_axioms FX1Poly.Typed.fundamentalPiFormationValidityWithTypeValueCandidatesFromUniverseDomain
#assert_no_axioms FX1Poly.Typed.fundamentalPiFormationValidityWithTypeValueCandidatesFromUniverseDomainMembersHaveTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.fundamentalSigmaFormationValidityWithTypeValueCandidatesFromUniverseDomainMembersHaveTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.FundamentalConclusionWithTypeValueCandidates.typeInUniverse_hasStrongNormalizationAndAllLevelReducibility

/-! ### Dependent fundamental theorem — proof-relevant positive-candidate environment arm layer.  This is
    the recursor-facing strengthened motive: ordinary all-level membership plus positive type-candidate
    companions for looked-up binding types.  The non-binder arms project to the ordinary all-level layer; the
    lambda arm is the binder-critical proof that a decoded domain argument can be strengthened to
    all-positive membership, extending the strengthened environment before running the codomain/body
    recursive premises. -/
#assert_no_axioms FX1Poly.Typed.FundamentalConclusionWithPositiveTypeCandidates
#assert_no_axioms FX1Poly.Typed.PositiveCandidateConclusionWithPositiveTypeCandidates
#assert_no_axioms FX1Poly.Typed.PositiveCandidateConclusionWithPositiveTypeCandidates.memberExtendsToAllPositive
#assert_no_axioms FX1Poly.Typed.PositiveCandidateConclusionWithPositiveTypeCandidates.consEnv
#assert_no_axioms FX1Poly.Typed.FundamentalConclusionWithPositiveTypeCandidates.typeInUniverse_hasStrongNormalizationAndAllLevelReducibility
#assert_no_axioms FX1Poly.Typed.FundamentalConclusionAtAll.toPositiveTypeCandidateEnv
#assert_no_axioms FX1Poly.Typed.fundamentalVarWithPositiveTypeCandidates
#assert_no_axioms FX1Poly.Typed.fundamentalUniverseFormationWithPositiveTypeCandidates
#assert_no_axioms FX1Poly.Typed.positiveCandidateUniverseCodeWithPositiveTypeCandidatesOfLowerTypeExtendsToAllLevels
#assert_no_axioms FX1Poly.Typed.fundamentalConvWithPositiveTypeCandidates
#assert_no_axioms FX1Poly.Typed.fundamentalPiElimWithPositiveTypeCandidates
#assert_no_axioms FX1Poly.Typed.positiveCandidateVarWithPositiveTypeCandidates
#assert_no_axioms FX1Poly.Typed.positiveCandidateSigmaTypeWithPositiveTypeCandidates
#assert_no_axioms FX1Poly.Typed.positiveCandidatePiTypeWithPositiveTypeCandidates
#assert_no_axioms FX1Poly.Typed.fundamentalPiIntroWithPositiveTypeCandidatesFromPositiveDomainCandidate
#assert_no_axioms FX1Poly.Typed.fundamentalPiIntroWithPositiveTypeCandidates
#assert_no_axioms FX1Poly.Typed.formerChildrenReducibleAtDispatchLevelsWithPositiveTypeCandidates
#assert_no_axioms FX1Poly.Typed.fundamentalPiFormationWithPositiveTypeCandidates
#assert_no_axioms FX1Poly.Typed.fundamentalSigmaFormationWithPositiveTypeCandidates
#assert_no_axioms FX1Poly.Typed.codomainMemberAtDomainLevelWithPositiveTypeCandidatesFromUniverseDomain
#assert_no_axioms FX1Poly.Typed.formerChildrenReducibleAtDispatchLevelsWithPositiveTypeCandidatesFromUniverseDomain
#assert_no_axioms FX1Poly.Typed.fundamentalPiFormationWithPositiveTypeCandidatesFromUniverseDomain

/-! ### Dependent fundamental theorem — the NON-telescope arms over the ∀-level environment.  `var` (the arm
    the ∀-level env was built to unblock: closes by instantiating the all-levels family at the conclusion
    level, off-by-one-free), `universeFormation` (`Type@e : Type@(lsucc e)`), and `conv` (reclassifier IH one
    level up → `tarskiDecode` → `castAlongConvUnderSubst`) all close with zero axioms over
    `ReducibleEnvAtAllLevels`, validating the env on the leaf/conv fragment.  The `genFormation` / `piIntro`
    binder companions use the per-variable-level bridge for the fresh argument; their non-recursive packaging
    gates pin them shut. -/
#assert_no_axioms FX1Poly.Typed.FundamentalConclusionAtAll
#assert_no_axioms FX1Poly.Typed.fundamentalVarAtAll
#assert_no_axioms FX1Poly.Typed.fundamentalUniverseFormationAtAll
#assert_no_axioms FX1Poly.Typed.fundamentalConvAtAll
#assert_no_axioms FX1Poly.Typed.fundamentalPiElimAtAll
#assert_no_axioms FX1Poly.Typed.fundamentalPiIntroAtAll
#assert_no_axioms FX1Poly.Typed.fundamentalPiFormationAtAll
#assert_no_axioms FX1Poly.Typed.fundamentalSigmaFormationAtAll
#assert_no_axioms FX1Poly.Typed.fundamentalPiFormationAtDispatchLevelsAtAll
#assert_no_axioms FX1Poly.Typed.fundamentalSigmaFormationAtDispatchLevelsAtAll
#assert_no_axioms FX1Poly.Typed.formerChildrenReducibleNonDependentAtAll
#assert_no_axioms FX1Poly.Typed.fundamentalPiFormationNonDependentAtAll
#assert_no_axioms FX1Poly.Typed.fundamentalSigmaFormationNonDependentAtAll
#assert_no_axioms FX1Poly.Typed.fundamentalPiIntroNonDependentAtAll
#assert_no_axioms FX1Poly.Typed.fundamentalTelescopeNilAtAll
#assert_no_axioms FX1Poly.Typed.fundamentalTelescopeConsAtAll
#assert_no_axioms FX1Poly.Typed.formerChildrenReducibleAtAll
#assert_no_axioms FX1Poly.Typed.formerChildrenReducibleAtDispatchLevelsFromAtAllPremises
#assert_no_axioms FX1Poly.Typed.fundamentalPiIntroAtAllFromMemberPremises
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAtAllPositiveLevels
#assert_no_axioms FX1Poly.Typed.IsReducibleTypeAtAllLevels
#assert_no_axioms FX1Poly.Typed.IsReducibleTypeAtAllPositiveLevels
#assert_no_axioms FX1Poly.Typed.IsReducibleTypeAtAllLevels.atAllPositiveLevels
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAtAllPositiveLevels.atLevel
#assert_no_axioms FX1Poly.Typed.IsReducibleTypeAtAllLevels.ofWeakHeadReduct
#assert_no_axioms FX1Poly.Typed.IsReducibleTypeAtAllLevels.headExpand
#assert_no_axioms FX1Poly.Typed.IsReducibleTypeAtAllPositiveLevels.ofWeakHeadReduct
#assert_no_axioms FX1Poly.Typed.IsReducibleTypeAtAllPositiveLevels.headExpand
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAtAllPositiveLevels.headExpand
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.extendsToAllPositiveAtWeakHeadExpansion
#assert_no_axioms FX1Poly.Typed.IsReducibleTypeAtAllLevels.domainOfPiType
#assert_no_axioms FX1Poly.Typed.IsReducibleTypeAtAllLevels.codomainOfPiTypeAtAllPositiveArgument
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAtAllPositiveLevels.universeCode_iff
#assert_no_axioms FX1Poly.Typed.FundamentalConclusionAtAll.typeInUniverse_hasStrongNormalizationAndAllLevelReducibility
#assert_no_axioms FX1Poly.Typed.HasAllPositiveReducibleCandidateAt
#assert_no_axioms FX1Poly.Typed.HasAllPositiveReducibleCandidateUnderAllLevelSubstitution
#assert_no_axioms FX1Poly.Typed.HasAllPositiveReducibleCandidateAtPositiveLevelsUnderSubstitution
#assert_no_axioms FX1Poly.Typed.HasAllPositiveReducibleCandidateAt.memberExtendsToAllPositive
#assert_no_axioms FX1Poly.Typed.HasAllPositiveReducibleCandidateAt.ofMemberExtensionAtPositiveLevel
#assert_no_axioms FX1Poly.Typed.HasAllPositiveReducibleCandidateAt.atPositiveLevelsOfMemberExtension
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.extendsToAllPositiveOfAllPositiveCandidate
#assert_no_axioms FX1Poly.Typed.HasAllPositiveReducibleCandidateAt.ofNeutralClassifier
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.extendsToAllPositiveAtNeutralClassifier
#assert_no_axioms FX1Poly.Typed.HasAllPositiveReducibleCandidateAt.piType
#assert_no_axioms FX1Poly.Typed.HasAllPositiveReducibleCandidateAt.piTypeAtPositiveLevel
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.extendsToAllPositiveAtPiType
#assert_no_axioms FX1Poly.Typed.HasAllPositiveReducibleCandidateAt.piTypeUnderSubst
#assert_no_axioms FX1Poly.Typed.HasAllPositiveReducibleCandidateAt.piTypeUnderSubstAtPositiveLevel
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.extendsToAllPositiveAtPositivePiType
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.extendsToAllPositiveAtPiTypeOfComponentMemberExtensions
#assert_no_axioms FX1Poly.Typed.IsReducibleTypeAtAllLevels.domainDataOfStronglyNormalizingPiType
#assert_no_axioms FX1Poly.Typed.IsReducibleTypeAtAllLevels.codomainDataOfStronglyNormalizingPiTypeAtAllPositiveArgument
#assert_no_axioms FX1Poly.Typed.HasAllPositiveReducibleCandidateAt.sigmaType
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.extendsToAllPositiveAtSigmaType
#assert_no_axioms FX1Poly.Typed.HasAllPositiveReducibleCandidateAt.sigmaTypeUnderSubst
#assert_no_axioms FX1Poly.Typed.HasAllPositiveReducibleCandidateUnderAllLevelSubstitution.piType
#assert_no_axioms FX1Poly.Typed.HasAllPositiveReducibleCandidateUnderAllLevelSubstitution.sigmaType
#assert_no_axioms FX1Poly.Typed.HasAllPositiveReducibleCandidateAt.universeCodeOfLowerTypeExtendsToAllLevels
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.extendsToAllPositiveAtUniverseCodeOfLowerTypeExtendsToAllLevels
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.universeCodeHasNoMemberAtZero
#assert_no_axioms FX1Poly.Typed.HasAllPositiveReducibleCandidateAt.notSuccUniverseCodeAtZero
#assert_no_axioms FX1Poly.Typed.HasAllPositiveReducibleCandidateUnderAllLevelSubstitution.notSuccUniverseCode
#assert_no_axioms FX1Poly.Typed.HasAllPositiveReducibleCandidateAtPositiveLevelsUnderSubstitution.piType
#assert_no_axioms FX1Poly.Typed.HasAllPositiveReducibleCandidateAtPositiveLevelsUnderSubstitution.sigmaType
#assert_no_axioms FX1Poly.Typed.HasAllPositiveReducibleCandidateAtPositiveLevelsUnderSubstitution.universeCodeOfLowerTypeExtendsToAllLevels
#assert_no_axioms FX1Poly.Typed.HasAllPositiveReducibleCandidateAtPositiveLevelsUnderSubstitution.memberExtendsToAllPositive
#assert_no_axioms FX1Poly.Typed.fundamentalPiIntroAtAllFromAllPositiveArgumentPremises
#assert_no_axioms FX1Poly.Typed.fundamentalPiIntroAtAllFromAllPositiveDomainCandidate
#assert_no_axioms FX1Poly.Typed.fundamentalPiIntroAtAllFromPositiveDomainCandidateCompanion
#assert_no_axioms FX1Poly.Typed.fundamentalTelescopeConsAtAllFromAllPositiveArgumentPremises
#assert_no_axioms FX1Poly.Typed.fundamentalTelescopeConsAtAllFromAllLevelHeadCandidateCompanion
#assert_no_axioms FX1Poly.Typed.FundamentalConclusionAtAll.typeInUniverse_hasPositiveCandidateOfPositiveMemberExtension
#assert_no_axioms FX1Poly.Typed.FundamentalConclusionAtAll.typeInUniverse_positiveMemberExtendsToAllPositiveOfPositiveMemberExtension
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAtAllLevels.consArgumentAtPositiveMemberLevelOfHeadFundamental
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAtAllLevelsWithTypeValueCandidates.consArgumentAtPositiveMemberLevelOfHeadFundamental
#assert_no_axioms FX1Poly.Typed.FundamentalConclusionWithTypeValueCandidates.typeInUniverse_hasPositiveCandidateOfPositiveMemberExtension
#assert_no_axioms FX1Poly.Typed.FundamentalConclusionWithTypeValueCandidates.typeInUniverse_positiveMemberExtendsToAllPositiveOfPositiveMemberExtension
#assert_no_axioms FX1Poly.Typed.fundamentalTelescopeConsAtAllFromPositiveMemberExtensionAndZeroMemberTail
#assert_no_axioms FX1Poly.Typed.HasAllPositiveReducibleCandidateUnderAllLevelSubstitution.memberExtendsToAllPositive
#assert_no_axioms FX1Poly.Typed.formerChildrenReducibleAtDispatchLevelsFromAllPositiveArgumentPremises
#assert_no_axioms FX1Poly.Typed.formerChildrenReducibleAtDispatchLevelsFromAllPositiveDomainCandidate
#assert_no_axioms FX1Poly.Typed.formerChildrenReducibleAtDispatchLevelsFromAllLevelDomainCandidateCompanion
#assert_no_axioms FX1Poly.Typed.formerChildrenReducibleAtDispatchLevelsFromPositiveDomainCandidateAndBaseLevelPremise
#assert_no_axioms FX1Poly.Typed.codomainMemberAtDomainLevelFromUniverseDomainPositiveCandidate
#assert_no_axioms FX1Poly.Typed.formerChildrenReducibleAtDispatchLevelsFromUniverseDomainPositiveCandidate
#assert_no_axioms FX1Poly.Typed.fundamentalPiFormationAtAllFromAllLevelDomainCandidateCompanion
#assert_no_axioms FX1Poly.Typed.fundamentalPiFormationAtAllFromPositiveDomainCandidateAndBaseLevelPremise
#assert_no_axioms FX1Poly.Typed.fundamentalPiFormationAtAllFromUniverseDomainPositiveCandidate
#assert_no_axioms FX1Poly.Typed.fundamentalSigmaFormationAtAllFromAllLevelDomainCandidateCompanion
#assert_no_axioms FX1Poly.Typed.fundamentalSigmaFormationAtAllFromPositiveDomainCandidate

-- Canonical per-level candidate companion extracted from an all-level `T : Type@u` fundamental result.  This
-- is weaker than the all-positive candidate discipline and avoids assuming stratified level-irrelevance.
#assert_no_axioms FX1Poly.Typed.HasCanonicalReducibleCandidateUnderAllLevelSubstitution
#assert_no_axioms FX1Poly.Typed.HasCanonicalReducibleCandidateAtPositiveLevelsUnderSubstitution
#assert_no_axioms FX1Poly.Typed.HasCanonicalReducibleCandidateUnderAllLevelSubstitution.atPositiveLevels
#assert_no_axioms FX1Poly.Typed.FundamentalConclusionAtAll.typeInUniverse_hasCanonicalReducibleCandidateUnderSubstitution
#assert_no_axioms FX1Poly.Typed.FundamentalConclusionAtAll.typeInUniverse_hasCanonicalReducibleCandidateAtPositiveLevels
#assert_no_axioms FX1Poly.Typed.IsFundamentalConclusionAtVector
#assert_no_axioms FX1Poly.Typed.fundamentalVarAtVectorMatchingLevel
#assert_no_axioms FX1Poly.Typed.fundamentalConclusionAtAllOfVector
#assert_no_axioms FX1Poly.Typed.fundamentalPiIntroAtAllFromVectorPremises
#assert_no_axioms FX1Poly.Typed.fundamentalPiIntroNonDependentAtAllFromVectorPremise
#assert_no_axioms FX1Poly.Typed.formerChildrenReducibleAtAllFromVectorPremise
#assert_no_axioms FX1Poly.Typed.formerChildrenReducibleAtDispatchLevelsFromVectorPremise
#assert_no_axioms FX1Poly.Typed.positiveUniformLevels
#assert_no_axioms FX1Poly.Typed.positiveUniformLevels_eq
#assert_no_axioms FX1Poly.Typed.IsFundamentalConclusionAtUniformVector
#assert_no_axioms FX1Poly.Typed.fundamentalVarAtUniformVector
#assert_no_axioms FX1Poly.Typed.fundamentalConclusionAtAllOfUniformVector
#assert_no_axioms FX1Poly.Typed.fundamentalPiIntroNonDependentAtAllFromUniformVectorPremise
#assert_no_axioms FX1Poly.Typed.IsTelescopeReducibleAtVector
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.fundamentalVectorFromFormation
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.fundamentalAtAllFromFormation
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.subjectStronglyNormalizingFromFormation
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.classifierStronglyNormalizingFromFormation
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedSubjectReducibleUnderSubstFromFormation
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedSubjectSubstStronglyNormalizingFromFormation
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedClassifierSubstStronglyNormalizingFromFormation
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedSubjectStronglyNormalizingFromFormation
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedClassifierStronglyNormalizingFromFormation

-- ALL-LEVEL FORMATION FT, var/conv/universeFormation discharged, genFormation factored (#496 progress).
-- The downstream SN chain (the FromFormation block above) is conditional on the formation engine HasTypeDesc
-- satisfying the FT.  This peels the three NON-former formation arms off that obligation: over the all-level
-- environment, var is off-by-one-free (fundamentalVarAtAll), conv/universeFormation dispatch to their AtAll
-- arms; the genFormation former arm (whose telescope binder obligation = the recursive
-- codomain-under-argument premise) is the sole explicit hypothesis.  Reduces the formation FT to the
-- genFormation former arm alone — the formation-engine analog of fundamentalVectorFromFormation.
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.fundamentalAtAllFromGenFormation

-- DECOUPLED-subjectLevel FT CONCLUSION (#496 — the var-level wall resolution).  IsFundamentalConclusionAtVector
-- fixes the conclusion at a uniform predLevel+1 decoupled from the env's per-variable levels, so var (reducible
-- only at its own level contextLevels index) is unprovable for arbitrary vectors; uniform-vector handles var but
-- not the dependent binder (codomain one rung lower via tarskiDecode). FundamentalConclusionLevelIndexed
-- concludes at a SEPARATE subjectLevel = the subject's level, so var = lookupReducible directly (off-by-one-free),
-- and the level-preserving arms (universeFormation, piElim — application is uniform-level via applicationUnderSubst)
-- thread it unchanged. The level-CHANGING arms now ALSO land: conv carries the tarskiDecode +1 (reclassifier run
-- one level up, decoded down to a reducible type, then castAlongConvUnderSubst); piIntro (the dependent binder, the
-- crux that walled the FT) is uniform-level via abstractionCanonicalUnderSubst with the bound arg deposited at
-- predLevel+1 via levelCons (positive level needed for CR1 on the domain candidate). genFormation (the dependent
-- type-former telescope) + the HasTypeDescPi.rec assembly with consistency hypotheses are the remaining Route-2 work.
#assert_no_axioms FX1Poly.Typed.fundamentalVarLevelIndexed
#assert_no_axioms FX1Poly.Typed.fundamentalUniverseFormationLevelIndexed
#assert_no_axioms FX1Poly.Typed.fundamentalPiElimLevelIndexed
#assert_no_axioms FX1Poly.Typed.fundamentalConvLevelIndexed
#assert_no_axioms FX1Poly.Typed.fundamentalPiIntroLevelIndexed
-- The dependent type-FORMER arms (the level-indexed twins of PiFormerMembership): the Π/Σ type-code
-- cell is a reducible universe member, from its children's QUANTIFIED-over-head-level fundamentals.
-- These are the membership dispatch the generic genFormation/genFormationPi arm calls; the remaining
-- Route-2 work is the DescTelescope(Pi) inversion feeding these the domain/codomain fundamentals + the
-- HasTypeDescPi.rec assembly.
#assert_no_axioms FX1Poly.Typed.fundamentalPiFormationLevelIndexed
#assert_no_axioms FX1Poly.Typed.fundamentalSigmaFormationLevelIndexed
-- The GENERIC genFormation/genFormationPi former arm: dispatches piTyCode/sigmaTyCode, inverts the two-child
-- spine, reads the FormerChildrenReducible bundle off the level-indexed telescope IH. The level-indexed twin
-- of fundamentalVectorFromFormation's genFormationPi arm — the FORMER half of the recursor assembly. Remaining:
-- the motive threading subjectLevel/contextLevels + the telescope motive_2 producing telescopeFundamental.
#assert_no_axioms FX1Poly.Typed.fundamentalGenFormationFormerLevelIndexed
-- CLOSED-TERM HANDOFF (#497/#498): at the empty context the per-variable-level env is vacuous
-- (ReducibleEnvVec.empty), so a level-indexed fundamental conclusion specializes to closed reducibility
-- under any closing substitution, and via CR1 (positive level) + the empty-renaming SN reflection to closed
-- strong normalization. Conditional on the level-indexed fundamental conclusion for the closed term (an
-- explicit argument, as the committed *FromFormation handoffs are conditional on the formation premise);
-- unconditional once the HasTypeDescPi.rec level-indexed assembly supplies that conclusion.
#assert_no_axioms FX1Poly.Typed.closedSubjectReducibleFromLevelIndexed
#assert_no_axioms FX1Poly.Typed.closedSubjectStronglyNormalizingFromLevelIndexed
-- Closed-type twin: a closed type code (given its type-FT) is a reducible TYPE at its level under any closing
-- substitution, via ReducibleEnvVec.empty. The handoff a closed-former canonicity argument consumes.
#assert_no_axioms FX1Poly.Typed.closedTypeReducibleFromTypeFundamental
-- BRIDGE to the committed vector machinery: IsFundamentalConclusionAtVector ≡ the level-indexed conclusion
-- at every (envLevels, predLevel+1). Makes precise why var fails at vector (forces predLevel+1 for the var's
-- env-fixed level) and lets vector-proved grown arms be read as level-indexed conclusions (toLevelIndexed).
#assert_no_axioms FX1Poly.Typed.isFundamentalConclusionAtVector_iff_forall_levelIndexed
#assert_no_axioms FX1Poly.Typed.IsFundamentalConclusionAtVector.toLevelIndexed
-- TYPE-FT (the type half of the mutual fundamental theorem): the formation type-subjects (universe code +
-- Pi/Sigma formers) are reducible TYPES (ReducibleTypeAt, not just members) at their level, via tarskiDecode
-- of the shipped term-FT arms. This is the ReducibleTypeAt form the conv arm consumes for its classifier;
-- the type-variable case + context-validity threading remain for the full mutual relation.
-- The GENERIC type-FT bridge: type-FT = tarskiDecode ∘ term-FT. Collapses the type half of the mutual FT
-- into a projection of the term FT (no separate induction); the three former type-FT lemmas below route
-- through it. The recursor's conv arm draws its reclassifier's type validity from the reclassifier's term IH.
#assert_no_axioms FX1Poly.Typed.typeFundamentalOfTermFundamental
#assert_no_axioms FX1Poly.Typed.universeCodeIsTypeFundamentalLevelIndexed
#assert_no_axioms FX1Poly.Typed.piFormerIsTypeFundamentalLevelIndexed
#assert_no_axioms FX1Poly.Typed.sigmaFormerIsTypeFundamentalLevelIndexed
-- type-FT var case: a type variable (looked-up type a universe code, env level positive) is a reducible TYPE
-- at its env level, via tarskiDecode of the env's membership. Completes the type-FT for all formation
-- type-subjects (universe code + Pi/Sigma formers + var) modulo conv (mutual with the term FT).
#assert_no_axioms FX1Poly.Typed.varIsTypeFundamentalLevelIndexed
-- LEVELED VALID CONTEXT (the validity-context structure for the term-FT recursor motive): context is a
-- telescope of types each typed at a universe code, contextLevels recording each entry's positive membership
-- level via levelCons. allLevelsPositive (induction on the inductive; propext-clean Fin split) is the
-- positivity invariant the recursor relies on (CR1 + conv tarskiDecode one-up both need positive levels).
#assert_no_axioms FX1Poly.Typed.LeveledContext.allLevelsPositive
-- FIRST UNCONDITIONAL SN results via the level-indexed FT: concrete closed terms whose FT conclusion is built
-- directly from the shipped arms at the empty context (no recursor), discharged to plain IsStronglyNormalizing
-- by the closed-SN handoff. End-to-end validation that the arms + handoff compose into hypothesis-free SN.
#assert_no_axioms FX1Poly.Typed.universeCode_stronglyNormalizing
#assert_no_axioms FX1Poly.Typed.closedPiBetweenUniverses_stronglyNormalizing
-- The closed identity λx.x : Π Type@e. Type@e is unconditionally SN — first such result with a LAMBDA +
-- BOUND VARIABLE, composing piIntro + var arms end-to-end (the heart of the FT). Fin-1 index via ⟨0,_⟩.
#assert_no_axioms FX1Poly.Typed.closedIdentityOnUniverse_stronglyNormalizing
-- The closed β-redex (λx.x) Type@e is unconditionally SN — first such result with an APPLICATION, composing
-- piElim over (piIntro + var) and universeFormation; exercises the subst0 in piElim's conclusion end-to-end.
#assert_no_axioms FX1Poly.Typed.closedIdentityApplication_stronglyNormalizing
-- FIRST LANE CROSSING: the FT-derived SN results discharge the SN-fragment conversion decider
-- (Conv.decidableOfStronglyNormalizing — normalize each, compare NF), yielding UNCONDITIONAL decidable Conv
-- for concrete closed terms (β-redex vs reduct, β-redex vs identity). The general bridge is conditional on the
-- FT conclusion (becomes unconditional with the recursor). betaRedexConvertsToReduct is the non-vacuity witness
-- (the redex really converts to its reduct). Concrete realization of raw decidable Conv (#267 / #503).
#assert_no_axioms FX1Poly.Typed.closedConvDecidableFromLevelIndexed
#assert_no_axioms FX1Poly.Typed.decidableConvBetaRedexAndReduct
#assert_no_axioms FX1Poly.Typed.decidableConvBetaRedexAndIdentity
#assert_no_axioms FX1Poly.Typed.betaRedexConvertsToReduct
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiSubstitutedStrongNormalizationTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiClosedStrongNormalizationTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.subjectStronglyNormalizingFromFundamentalAtAll
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedSubjectReducibleUnderSubstFromFundamentalAtAll
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedSubjectSubstStronglyNormalizingFromFundamentalAtAll
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedSubjectStronglyNormalizingFromFundamentalAtAll
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiAllLevelFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiPositiveCandidateFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiTypeValueCandidateFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiPositiveCandidateSubstitutedStrongNormalizationTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiTypeValueCandidateSubstitutedStrongNormalizationTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiTypeValueReducibilityAndStrongNormalizationTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiTypeValueReducibilityAndStrongNormalizationTheorem.fundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiTypeValueReducibilityAndStrongNormalizationTheorem.substitutedStrongNormalizationTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiTypeValueReducibilityAndStrongNormalizationTheorem.closedStrongNormalizationTheorem
#assert_no_axioms FX1Poly.Typed.FundamentalConclusionAtAll.toTypeValueCandidateValidityOfAllReducibleTypesHaveTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiAllLevelFundamentalTheorem.toTypeValueCandidateFundamentalTheoremOfAllReducibleTypesHaveTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiAllLevelFundamentalTheorem.toTypeValueCandidateFundamentalTheoremOfPositiveMemberExtension
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.subjectStronglyNormalizingFromAllLevelFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.classifierStronglyNormalizingFromAllLevelFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.subjectStronglyNormalizingFromPositiveCandidateFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.classifierStronglyNormalizingFromPositiveCandidateFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.subjectStronglyNormalizingFromTypeValueCandidateFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.classifierStronglyNormalizingFromTypeValueCandidateFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedSubjectReducibleUnderSubstFromAllLevelFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedSubjectSubstStronglyNormalizingFromAllLevelFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedClassifierSubstStronglyNormalizingFromAllLevelFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedSubjectStronglyNormalizingFromAllLevelFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedClassifierStronglyNormalizingFromAllLevelFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedSubjectReducibleUnderSubstFromPositiveCandidateFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedSubjectSubstStronglyNormalizingFromPositiveCandidateFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedClassifierSubstStronglyNormalizingFromPositiveCandidateFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedSubjectStronglyNormalizingFromPositiveCandidateFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedClassifierStronglyNormalizingFromPositiveCandidateFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedSubjectReducibleUnderSubstFromTypeValueCandidateFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedSubjectSubstStronglyNormalizingFromTypeValueCandidateFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedClassifierSubstStronglyNormalizingFromTypeValueCandidateFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedSubjectStronglyNormalizingFromTypeValueCandidateFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedClassifierStronglyNormalizingFromTypeValueCandidateFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiAllLevelFundamentalTheorem.toSubstitutedStrongNormalizationTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiPositiveCandidateFundamentalTheorem.toSubstitutedStrongNormalizationTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiTypeValueCandidateFundamentalTheorem.toSubstitutedStrongNormalizationTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiAllLevelFundamentalTheorem.toTypeValueCandidateSubstitutedStrongNormalizationTheoremOfAllReducibleTypesHaveTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiAllLevelFundamentalTheorem.toTypeValueCandidateSubstitutedStrongNormalizationTheoremOfPositiveMemberExtension
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiTypeValueCandidateFundamentalTheorem.toReducibilityAndStrongNormalizationTheorem
#assert_no_axioms FX1Poly.Typed.hasTypeDescPiTypeValueReducibilityAndStrongNormalizationTheorem_iff_typeValueCandidateFundamentalTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiAllLevelFundamentalTheorem.toTypeValueReducibilityAndStrongNormalizationTheoremOfAllReducibleTypesHaveTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiAllLevelFundamentalTheorem.toTypeValueReducibilityAndStrongNormalizationTheoremOfPositiveMemberExtension
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.allLevelFundamentalTheoremFromFormationVector
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.typeValueReducibilityAndStrongNormalizationTheoremFromFormationVectorAndAllReducibleTypesHaveTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.typeValueReducibilityAndStrongNormalizationTheoremFromFormationVectorAndPositiveMemberExtension
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiAllLevelFundamentalTheorem.toClosedStrongNormalizationTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiPositiveCandidateFundamentalTheorem.toClosedStrongNormalizationTheorem
#assert_no_axioms FX1Poly.Typed.HasTypeDescPiTypeValueCandidateFundamentalTheorem.toClosedStrongNormalizationTheorem

/-! ### PER-VARIABLE-LEVEL reducible environment (the Kripke refinement for the dependent fundamental
    theorem).  `ReducibleEnvAt`'s single global level cannot serve a context that mixes variables at
    different typing-tower rungs (each rung sits one fuel higher via `tarskiDecode`, and upward
    level-cumulativity is false).  `ReducibleEnvVec` indexes each variable by its OWN tower level via a
    `Fin scope → Nat` vector; `levelCons` is the propext-free fresh-level cons. -/
#assert_no_axioms FX1Poly.Typed.levelCons
#assert_no_axioms FX1Poly.Typed.ReducibleEnvVec
#assert_no_axioms FX1Poly.Typed.ReducibleEnvVec.lookupReducible
#assert_no_axioms FX1Poly.Typed.ReducibleEnvVec.empty
#assert_no_axioms FX1Poly.Typed.ReducibleEnvVec.cons
#assert_no_axioms FX1Poly.Typed.ReducibleEnvVec.typeVariableReducible

/-! ### SEMANTIC TYPING RULES UNDER A CLOSING SUBSTITUTION (the fundamental theorem's arm bodies).
    The Girard-Tait fundamental theorem over `HasTypeDescPi` is a thin induction whose arms dispatch to
    these substitution-closed semantic rules.  `applicationUnderSubst` is the `piElim` arm: it lifts the
    raw `IsReducibleMemberAt.application` through the β-substitution commutation
    `RawTerm.subst0_subst_commute` (which lines up `subst γ (subst0 codomainCode argument)` with the
    dependent output of the substituted pieces), at a FIXED `level` (elimination introduces no universe
    nesting).  Future arms (conv / piIntro / formation) append here. -/
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.applicationUnderSubst

/-! ### CONV ARM under a closing substitution.  Transports membership across the substituted conversion
    (`Conv.subst`) via the shipped `castAlongConv`; the target type-reducibility is supplied by the
    fundamental theorem via `tarskiDecode` of the `reclassifier : Type@e` premise's IH at `level + 1`. -/
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.castAlongConvUnderSubst

/-! ### NON-DEPENDENT (simply-typed) Π-INTRODUCTION arm under a closing substitution.  Lifts the raw
    `abstractionNonDependent` (the choice-free no-large-elim piIntro) through the cell-substitution
    commutations: `subst_lamCell`/`subst_piTyCodeCell` (rfl) + `subst_lift_weaken_commute` (the codomain
    weakening commutes out through the binder lift).  The binder arm of the simply-typed fundamental
    theorem. -/
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.abstractionNonDependentUnderSubst

/-! ### DEPENDENT Π-introduction + both Π-formation arms under a closing substitution.  The dependent
    `piIntro` (`abstractionUnderSubst`) and `Π`-formation (`piTypeUnderSubst`) twins lift the raw
    `abstraction` / `piType` through the rfl cell-substitutions (dependent codomain stays in the extended
    scope — no weakening-commutation); the simple-arrow formation (`arrowTypeUnderSubst`) lifts
    `arrowType` through the same `typeEq` re-expression as the non-dependent `piIntro` arm.  Choice-free as
    semantic rules (the per-argument candidate is given); the dependent arms are the full-FT (large
    elimination) introduction/formation rules. -/
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.abstractionUnderSubst
#assert_no_axioms FX1Poly.Typed.ReducibleTypeAt.arrowTypeUnderSubst
#assert_no_axioms FX1Poly.Typed.ReducibleTypeAt.piTypeUnderSubst

/-! ### CHOICE-FREE dependent Π formation + introduction under a closing substitution (the Path-A
    fundamental-theorem binder arms).  The canonical-codomain twins of `piTypeUnderSubst` /
    `abstractionUnderSubst`: they feed the FIXED `fun arg => IsReducibleMemberAt level (subst0 (subst
    (lift γ) cod) arg)` codomain and discharge the per-argument codomain premise from mere EXISTENCE via
    the Core engine `reducibleMemberCandidate` — no candidate is chosen, so the choice wall the dependent
    fundamental theorem hit at `piIntro`/`piType` is dissolved. -/
#assert_no_axioms FX1Poly.Typed.ReducibleTypeAt.piTypeCanonicalUnderSubst
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.abstractionCanonicalUnderSubst

/-! ### genFormationPi former weak-head-normality — the `genFormationPi` arm's WHN obligation.
    `typingRuleDescOf` is `some` only for `gen_piTyCode` / `gen_sigmaTyCode` (the dependent type-formers),
    both weak-head normal, so the fundamental theorem's generic formation arm discharges the
    `reducibleOfWeakHeadNormalFormer` weak-head-normality hypothesis with no per-former proof at the
    induction site. -/
#assert_no_axioms FX1Poly.Typed.formationGenerator_noWeakHeadStep
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.sigmaFormationUnderSubst
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.piFormationUnderSubst

/-! ### Grown-engine closed-subject shape characterization (the consistency-spine inversion leg).
    A well-typed grown subject is rooted at one of the six grown-engine generators; in the empty context
    consistency reduces to the `gen_app` case the fundamental theorem's SN rules out.  Term-mode structural
    recursion sidesteps the HasTypeDescPi/DescTelescopePi mutual-induction rejection. -/
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.subjectRootGenerator
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.subjectRootGenerator
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.closedSubjectRootGenerator
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.subjectRootGenerator_ne_lam
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.subjectRootGenerator_ne_app
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.subjectCannotBeLambda
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.subjectCannotBeApplication
#assert_no_axioms FX1Poly.Typed.HasType.subjectRootGenerator_ne_lam
#assert_no_axioms FX1Poly.Typed.HasType.subjectRootGenerator_ne_app
#assert_no_axioms FX1Poly.Typed.HasType.subjectCannotBeLambda
#assert_no_axioms FX1Poly.Typed.HasType.subjectCannotBeApplication

/-! ### FORMATION-ARM BRIDGE: membership at a universe-code classifier ⟺ strong normalization.
    A universe code is a normal leaf (`noStep_universeCode`), hence neutral, so the dependent
    reducibility relation assigns it the SN candidate and `IsReducibleMember (universeCodeCell ..) t ↔
    IsStronglyNormalizing t` (via the Core `IsReducibleMember.atNeutralClassifier`).  This is the
    fundamental theorem's formation/universe arm bridge between a well-formed type term and its SN. -/
#assert_no_axioms FX1Poly.Typed.universeCodeCell_noWeakHeadStep
#assert_no_axioms FX1Poly.Typed.IsReducibleMember.atUniverseCode
#assert_no_axioms FX1Poly.Typed.DescTelescope.consInversion
#assert_no_axioms FX1Poly.Typed.DescTelescope.twoChildLevels
#assert_no_axioms FX1Poly.Typed.DescTelescopePi.consInversion
#assert_no_axioms FX1Poly.Typed.DescTelescopePi.twoChildLevels
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.piFormerOfChildMembershipsAtRequiredLevels
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.piFormerOfChildMemberships
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.sigmaFormerOfChildMembershipsAtRequiredLevel
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.sigmaFormerOfChildMemberships
#assert_no_axioms FX1Poly.Typed.FormerChildrenReducibleAtDispatchLevels
#assert_no_axioms FX1Poly.Typed.FormerChildrenReducible.toDispatchLevels
#assert_no_axioms FX1Poly.Typed.FormerChildrenReducible.toPiMember
#assert_no_axioms FX1Poly.Typed.FormerChildrenReducibleAtDispatchLevels.toPiMember
#assert_no_axioms FX1Poly.Typed.FormerChildrenReducible.toSigmaMember
#assert_no_axioms FX1Poly.Typed.FormerChildrenReducibleAtDispatchLevels.toSigmaMember
#assert_no_axioms FX1Poly.Typed.FormerChildrenReducible.ofTelescopeReducible
#assert_no_axioms FX1Poly.Typed.FormerChildrenReducibleAtDispatchLevels.ofTelescopeReducible
#assert_no_axioms FX1Poly.Typed.consecutiveShifts
#assert_no_axioms FX1Poly.Typed.TelescopeReducible
#assert_no_axioms FX1Poly.Typed.Generator.gen_piTyCode_binderShifts_eq
#assert_no_axioms FX1Poly.Typed.Generator.gen_sigmaTyCode_binderShifts_eq

-- Universe-domain member-extension reduction: the cons-arm's last hard case (the type-polymorphic binder
-- `Π (A : Type@e). …`) is EXACTLY type-level positive level-irrelevance — the membership/SN layer stripped
-- off via the Tarski universe decode/encode, exposing the pure type-level lift the level-congruence
-- inductive step (`ReducibleTypeStep.existsCongr`) is built to thread.
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAtAllPositiveLevels.ofUniverseMemberUnderTypeLevelIrrelevance
#assert_no_axioms FX1Poly.Typed.universeDomainMemberExtension_ofTypeLevelIrrelevance
#assert_no_axioms FX1Poly.Typed.typeLevelIrrelevance_ofUniverseDomainMemberExtension

-- Non-Π type leaves are reducible at ALL levels UNCONDITIONALLY (candidate `IsStronglyNormalizing` /
-- per-level universe candidate), discharging the type-level-irrelevance obligation for every cons-arm
-- universe-domain argument except a Π-TYPE argument — the sole remaining cons-arm gap, now isolated.
#assert_no_axioms FX1Poly.Typed.IsReducibleTypeAtAllLevels.ofWeakHeadNormalNonPiNonUniverse
#assert_no_axioms FX1Poly.Typed.IsReducibleTypeAtAllLevels.ofUniverseCode
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAtAllPositiveLevels.ofUniverseMemberNonPiNonUniverseArgument
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAtAllPositiveLevels.ofUniverseMemberUniverseCodeArgument

-- Level-irrelevance INDUCTION over the whole reducibility derivation: every `ReducibleTypeStep` arm but
-- `piType` discharged unconditionally (redex via `headExpand` — extending the non-Π discharge to
-- redex-carrying args — neutral/universe via the leaves, congruence via the IH).  The entire type-level
-- level-irrelevance obstruction is reduced to ONE hypothesis, the `piArm` (Π-former case).
#assert_no_axioms FX1Poly.Typed.IsReducibleTypeAtAllLevels.ofReducibleTypeStep
#assert_no_axioms FX1Poly.Typed.IsReducibleTypeAtAllLevels.ofReducibleAtLevel

-- The `piArm` CLOSES for a neutral / data-former domain: such a domain's reducible-type candidate is
-- `IsStronglyNormalizing` at EVERY level, so the domain-candidate level-mismatch dissolves and the Π type
-- rebuilds at every level (canonical codomain candidate, choice-free).  Level-irrelevance now holds
-- unconditionally for every Π type whose domain is neutral / a data former — residual gap: Π- or
-- universe-rooted domains.
#assert_no_axioms FX1Poly.Typed.IsReducibleTypeAtAllLevels.piTypeOfNeutralDomain
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAtAllPositiveLevels.ofUniverseMemberPiNeutralDomainArgument

-- Member-side leaf (dual of the type leaves): membership in a neutral / data-former classifier is
-- `IsStronglyNormalizing` (level-independent), so a one-level member extends to all positive levels — the
-- cons-arm `headMemberExtendsToAllPositive` premise for a neutral-domain former.
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAtAllPositiveLevels.ofNeutralClassifier
#assert_no_axioms FX1Poly.Typed.headMemberExtendsToAllPositive_ofNeutralClassifier

-- ASSEMBLY: the formation-FT telescope-cons (binder) arm CLOSES for a neutral / data-former domain — the
-- member-side leaf composed with the all-positive-argument cons companion.  The binder arm that has carried
-- the lone all-level-assembly `sorry` is discharged for every non-type-polymorphic former, given only the
-- tail recursion (supplied by the FT's own IH).
#assert_no_axioms FX1Poly.Typed.fundamentalTelescopeConsAtAllNeutralDomain

-- ASSEMBLY: the same binder arm CLOSES for a weak-head-reducible domain — the member-side `whnfExpand` arm
-- (this iteration) composed with the all-positive-argument cons companion.  Sibling of the neutral-domain
-- lemma; chaining the two covers every former whose substituted domain weak-head-normalises to neutral/data.
#assert_no_axioms FX1Poly.Typed.fundamentalTelescopeConsAtAllWhnfDomain

-- The Π `piType` arm of type-level level-irrelevance, generalized from a neutral domain to ANY domain that
-- admits MEMBER-EXTENSION: the domain-candidate level-mismatch dissolves under domain member-extension
-- (rebuild with the domain's fixed canonical member-predicate).  The type leg of the mutual type+member
-- irrelevance — residual obstruction now purely member-side (member-extension for Π/universe domains).
#assert_no_axioms FX1Poly.Typed.IsReducibleTypeAtAllLevels.piTypeOfDomainMemberExtension

-- The MEMBER leg of the Π `piType` arm: a positive-level Π member extends to all positive levels via the
-- application chain (domain member-ext → `application` → codomain member-ext), run entirely at positive
-- levels (the degenerate fuel-0 base untouched).  With the type leg, the full `piType` arm of mutual
-- type+member level-irrelevance is reduced to domain+codomain member-extension.
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAtAllPositiveLevels.piTypeMemberExtension

-- The TIGHT primary form: the domain/codomain member-extension premises need only hold from POSITIVE source
-- levels (the proof never invokes them at the degenerate fuel-0), and the all-source-level
-- `piTypeMemberExtension` is now the trivial weakening that delegates to it.  This tightening is what lets the
-- member-extension family ASSEMBLE over nested non-dependent arrows (a sub-arrow supplies only positive-source
-- member-extension, which now suffices to feed the enclosing arrow).
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAtAllPositiveLevels.piTypeMemberExtensionPositive

-- The member-side `whnfExpand` arm of mutual type+member level-irrelevance: member-extension lifts backward
-- across one weak-head step of the classifier (peel the member to the shared-candidate contractum, strengthen
-- by the contractum's member-extension, head-expand back).  With `ofNeutralClassifier` this completes the
-- member-side arm family for the non-Π / non-universe cases — the structurally-recursive part.
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAtAllPositiveLevels.extensionHeadExpand

-- The CONVERSION arm of the member-extension family: member-extension transports across an arbitrary kernel
-- `Conv` of the classifier (target reducible at all positive levels), via the single-level `castAlongConv` /
-- `ReducibleTypeAt.convTransfer`.  More flexible than the single-step whnfExpand arm; the conv arm of the
-- strengthened formation-FT motive.  `castAlongConvOfAllLevels` is the all-levels-target convenience form.
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAtAllPositiveLevels.castAlongConv
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAtAllPositiveLevels.castAlongConvOfAllLevels

-- CR1 for the all-positive member family: every all-positive member is strongly normalizing (read at the
-- bottom positive fuel via `atLevel 0`, then single-level CR1).  The SN bridge the strong-normalization /
-- canonicity corollaries consume once a binder/telescope arm strengthens a one-level member to all-positive.
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAtAllPositiveLevels.stronglyNormalizing

-- Member-extension for a NON-DEPENDENT arrow `A → B`: the dependent `piTypeMemberExtension`'s argument-indexed
-- codomain hypotheses collapse to the CONSTANT base-codomain facts via weaken-cancellation
-- (`subst0 (weaken B) arg = B`).  The member-side twin of `formerChildrenReducibleNonDependentAtAll`; the
-- premise-(2) recursion step for the simply-typed fragment (no dependent-Π codomain growth).
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAtAllPositiveLevels.nonDependentArrow

-- TYPE-side twin: all-levels type reducibility for a non-dependent arrow `A → B`.  The dependent
-- `piTypeOfDomainMemberExtension`'s argument-indexed codomain premise collapses to the constant base-codomain
-- all-levels fact via weaken-cancellation.  With the member-side twin this is the full non-dependent-arrow
-- reducibility pair — the simply-typed step where the dependent-Π codomain-growth obstruction is absent.
#assert_no_axioms FX1Poly.Typed.IsReducibleTypeAtAllLevels.nonDependentArrow

-- TYPE-side crack past the universe-domain wall: a non-dependent arrow is all-levels reducible from domain +
-- codomain all-levels reducibility ALONE — NO domain member-extension (the codomain candidate is constant in
-- the argument when the codomain is `weaken`-ed, so the argument membership is never consumed).  This reaches
-- a non-dependent arrow over a UNIVERSE domain (`Type@e → B`), which the member-extension-requiring
-- `nonDependentArrow` cannot — only the dependent and member legs of a universe domain stay open.
#assert_no_axioms FX1Poly.Typed.IsReducibleTypeAtAllLevels.nonDependentArrowOfAllLevelsDomain
#assert_no_axioms FX1Poly.Typed.IsReducibleTypeAtAllLevels.universeDomainNonDependentArrow

-- ASSEMBLY CAPSTONE: the universe member-extension principle (open in general at the fuel-0 universe wall) is
-- proved UNCONDITIONALLY for the FIRST-ORDER simply-typed fragment — types built from neutral/data leaves and
-- non-dependent arrows with neutral DOMAINS (curried first-order functions over base types).  This is the
-- classic Tait reducibility result realized on FX's stratified Tarski substrate: the first non-trivial
-- fragment where the reducibility machinery closes end-to-end, assembling the neutral-leaf, non-dependent-
-- arrow (type + positive-source member), and ofNeutralClassifier arms by induction on a 2-ctor witness.
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAtAllPositiveLevels.nonDependentArrowPositive
#assert_no_axioms FX1Poly.Typed.IsFirstOrderSimplyTyped
#assert_no_axioms FX1Poly.Typed.IsFirstOrderSimplyTyped.reducibleAndMemberExtension

-- Smart constructors making the first-order fragment CONSTRUCTIBLE for concrete types (via the
-- canonical-form weak-head-normality lemmas), plus the end-to-end corollary that a variable type is
-- reducible-at-all-levels and member-extending — a closed demonstration that the Tait machinery applies
-- concretely, not merely to an abstract fragment.
#assert_no_axioms FX1Poly.Typed.IsFirstOrderSimplyTyped.ofVariable
#assert_no_axioms FX1Poly.Typed.IsFirstOrderSimplyTyped.ofSigmaTyCode
#assert_no_axioms FX1Poly.Typed.IsFirstOrderSimplyTyped.arrowOfVariableDomain
#assert_no_axioms FX1Poly.Typed.IsFirstOrderSimplyTyped.variableReducibleAndMemberExtension

-- The general neutral-leaf principle: every neutral type (variable / neutral application / projection /
-- stuck eliminator) is first-order simply-typed, lifting the leaf class from bare variables to the full
-- Tait neutral family.  Backed by the Core `IsNeutral.rootGenerator_ne_piTyCode` / `…_ne_universeCode`
-- root-disequality lemmas (swept by `#audit_namespace FX1Poly.Core`).  The end-to-end corollary exercises
-- reducibility + member-extension on a NON-variable neutral type (a type-family application `f a`).
#assert_no_axioms FX1Poly.Typed.IsFirstOrderSimplyTyped.ofNeutral
#assert_no_axioms FX1Poly.Typed.IsFirstOrderSimplyTyped.ofNeutralApplication
#assert_no_axioms FX1Poly.Typed.IsFirstOrderSimplyTyped.neutralApplicationReducibleAndMemberExtension

-- FULL HIGHER-ORDER simply-typed fragment: the certified Tait fragment extended from first-order to the whole
-- simply-typed lambda calculus over neutral/data base types — arrows closed on BOTH domain and codomain (an
-- arrow domain `(A → B) → C` recurses, NOT blocked).  The arrow-domain recursion is unblocked precisely by the
-- member-extension-free type-side arrow `nonDependentArrowOfAllLevelsDomain` (the IH supplies only
-- positive-source member-extension, which the member-side `nonDependentArrowPositive` accepts).  Corrects the
-- first-order file's docstring claim that higher-order domains hit the fuel-0 wall — only UNIVERSE domains do.
#assert_no_axioms FX1Poly.Typed.IsSimplyTyped.reducibleAndMemberExtension
#assert_no_axioms FX1Poly.Typed.IsSimplyTyped.ofFirstOrder
#assert_no_axioms FX1Poly.Typed.IsSimplyTyped.ofNeutral
#assert_no_axioms FX1Poly.Typed.IsSimplyTyped.higherOrderArrow
#assert_no_axioms FX1Poly.Typed.IsSimplyTyped.higherOrderArrowReducibleAndMemberExtension

-- TERM-level reducibility of the simply-typed fragment: the term-formation rules (abstraction / application)
-- made concrete + the SN payoff on a REDUCING term.  `lambdaNeutralArrow` / `applicationNonDependentArrow`
-- are the candidate-free piIntro/piElim specializations; `polymorphicIdentity` is `λx.x : A→A`; and
-- `polymorphicIdentityRedexStronglyNormalizing` proves the β-redex `(λx.x) y` strongly normalizes — strong
-- normalization of an actually-reducing term (CR1 on a non-normal form), the genuine Tait payoff.
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.lambdaNeutralArrow
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.applicationNonDependentArrow
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.polymorphicIdentity
#assert_no_axioms FX1Poly.Typed.polymorphicIdentityRedexStronglyNormalizing

-- HIGHER-ORDER term reducibility: `lambdaNeutralDomain` generalizes the abstraction rule from a neutral
-- codomain to ANY reducible codomain (candidate = the codomain's own member-predicate, so the body condition
-- is "body lands as a member" — the form functions-returning-functions and the FT λ arm need).
-- `constantIdentity` demonstrates it on an ARROW codomain: `λx.(λy.y) : A → (B → B)`.
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.lambdaNeutralDomain
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.constantIdentity

-- The K combinator `λx.λy.x : A → (B → A)` — the hardest concrete simply-typed term, where the inner body
-- CAPTURES the outer bound variable.  `subst0_lamCellVarOne_eq_lamWeaken` is the binder-crossing substitution
-- computation behind it (`subst0 (λy.var 1) arg = λy.weaken arg`), proven fold-`rfl`-free (no propext /
-- Quot.sound) with a Nat-arithmetic Fin bound (no omega).
#assert_no_axioms FX1Poly.Typed.subst0_lamCellVarOne_eq_lamWeaken
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.kCombinator

-- Abstraction rule-family completion: `lambdaLeafDomain` is the maximally-general form — a LEAF domain
-- (weak-head-normal, non-Π, non-universe: data formers, not only neutrals) + any reducible codomain — matching
-- the `IsSimplyTyped.leaf` class and subsuming `lambdaNeutralArrow` / `lambdaNeutralDomain`.  `sigmaIdentity`
-- (`λx.x : (Σ A. B) → (Σ A. B)`) is the identity over a Σ-code DATA-FORMER base type, reachable only via it.
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.lambdaLeafDomain
#assert_no_axioms FX1Poly.Typed.IsReducibleMemberAt.sigmaIdentity

-- The FT crux that sidesteps the universe wall: a type-VARIABLE domain (a context binding `α : Type@e`) is a
-- reducible TYPE under a reducible environment, read off the environment via the universe-membership decode
-- (`universeMembership_iff`).  The wall blocks TYPE abstraction (`λA:Type.…`), not term abstraction over type
-- variables — so the simply-typed fundamental theorem is NOT wall-blocked, only awaiting the judgment+env
-- assembly.
#assert_no_axioms FX1Poly.Typed.ReducibleEnvAt.typeVariableReducible

-- The TYPE-LEVEL half of the simply-typed fundamental theorem.  `IsSimplyTypedTypeExpr` classifies the pure
-- STLC type expressions over a context (type variable bound at a universe, or non-dependent arrow of such), and
-- `reducibleAtAllLevels` proves every one substitutes to an all-levels reducible type under an all-levels
-- reducible closing environment.  The type-variable arm reads reducibility off the environment (sidestepping
-- the universe wall via `typeVariableReducible`); the arrow arm is `nonDependentArrowOfAllLevelsDomain` on the
-- induction hypotheses.  This is the domain/codomain reducibility the term FT's λ-introduction arm consumes.
#assert_no_axioms FX1Poly.Typed.IsSimplyTypedTypeExpr
#assert_no_axioms FX1Poly.Typed.IsSimplyTypedTypeExpr.reducibleAtAllLevels

-- The simply-typed lambda arm of the LEVEL-FREE term fundamental theorem: the non-dependent specialization
-- of the dependent `abstractionUnderSubst`, pre-cancelling the codomain weakening
-- (`subst0 (subst (lift σ) (weaken codomainBase)) arg = subst σ codomainBase`).  The simply-typed term FT
-- assembles over the level-free layer (not the stratified one): level-free `ReducibleEnv.cons` extends from
-- a single `IsReducibleMember`, so the lam binder needs no all-levels argument — the stratified universe wall
-- is structurally absent for a non-dependent codomain.
#assert_no_axioms FX1Poly.Typed.IsReducibleMember.abstractionNonDependentUnderSubst

-- The domain supplier for the level-free simply-typed term FT: the non-dependent arrow type builder
-- (`ReducibleType.nonDependentArrow`, level-free twin of the stratified `IsReducibleTypeAtAllLevels.nonDependentArrow`),
-- the directly-reducible type-expression class (`IsReducibleTypeExprLF` = universe codes + non-dependent
-- arrows; no type-variable leaves, which decode only to SN level-free), and the supplier proper
-- (`reducibleUnderSubst`) — every such expression substitutes to a directly-reducible level-free type, the
-- domain reducibility the lam arm consumes.
#assert_no_axioms FX1Poly.Typed.ReducibleType.nonDependentArrow
#assert_no_axioms FX1Poly.Typed.IsReducibleTypeExprLF
#assert_no_axioms FX1Poly.Typed.IsReducibleTypeExprLF.reducibleUnderSubst

-- THE LEVEL-FREE SIMPLY-TYPED TERM FUNDAMENTAL THEOREM (#502): the well-scoped term judgment
-- `SimplyTypedTermLF` (var/app/lam) + `reducibleUnderSubst` (every simply-typed term, closed by a reducible
-- substitution, is a reducible member of its type — var→lookupReducible, app→applicationUnderSubst,
-- lam→abstractionNonDependentUnderSubst fed reducibleUnderSubst) + the strong-normalization corollaries.
-- `stronglyNormalizingClosed` is the tangible payoff: every closed simply-typed term strongly normalizes
-- (SN-for-well-typed on the wall-free simply-typed fragment).
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.reducibleUnderSubst
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.stronglyNormalizingUnderSubst
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.reducibleClosed
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.stronglyNormalizingClosed

-- CHURCH-ROSSER + NORMAL-FORM UNIQUENESS for simply-typed terms: the SN result fed the per-term Newman bridge
-- (`confluence_of_localJoin_and_accessible`) gives confluence (`reductsJoinUnderSubst`), and `eq_of_noStep`
-- gives normal-form uniqueness (`normalFormUnique{UnderSubst,Closed}`) — the foundation for deciding conversion
-- on the simply-typed fragment.
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.reductsJoinUnderSubst
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.normalFormUniqueUnderSubst
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.normalFormUniqueClosed

-- INHABITATION CORPUS for the simply-typed term FT (the fundamental theorem is non-vacuous): concrete
-- `SimplyTypedTermLF` derivations of the polymorphic identity at a universe base type and at an arrow type,
-- with their strong normalization as fundamental-theorem corollaries.  Simply-typed analogue of TY-honesty.
#assert_no_axioms FX1Poly.Typed.identityIsSimplyTyped
#assert_no_axioms FX1Poly.Typed.identityStronglyNormalizing
#assert_no_axioms FX1Poly.Typed.arrowIdentityIsSimplyTyped
#assert_no_axioms FX1Poly.Typed.arrowIdentityStronglyNormalizing

-- PRODUCTIVE REDEX EXTRACTION (toward weak normalization, #267/#374): the converse of
-- `isStepNormalForm_blocks_step` per root-redex shape — a fired root check yields an actual `Step`, witness
-- produced.  This batch covers the FUNCTION (beta) and PRODUCT (fst/snd) redexes (+ the shallow source
-- inversions); inductive-eliminator iotas are deferred to subsequent bricks.
#assert_no_axioms FX1Poly.Core.isLamSource_eq_lam
#assert_no_axioms FX1Poly.Core.hasAppBetaRoot_exists_step
#assert_no_axioms FX1Poly.Core.isPairSource_eq_pair
#assert_no_axioms FX1Poly.Core.hasPairProjectionIotaRoot_exists_step_fst
#assert_no_axioms FX1Poly.Core.hasPairProjectionIotaRoot_exists_step_snd

-- Redex-extraction bricks: BOOLEAN (boolElim) + NATURAL (natElim/natRec).  The two-constructor eliminators'
-- disjunctive root check is split propext-free (`cases h : isXxxSource`, NOT `rw [Bool.or_eq_true]`).
#assert_no_axioms FX1Poly.Core.isBoolTrueSource_eq_boolTrue
#assert_no_axioms FX1Poly.Core.isBoolFalseSource_eq_boolFalse
#assert_no_axioms FX1Poly.Core.hasBoolElimIotaRoot_exists_step
#assert_no_axioms FX1Poly.Core.isNatZeroSource_eq_natZero
#assert_no_axioms FX1Poly.Core.isNatSuccSource_eq_natSucc
#assert_no_axioms FX1Poly.Core.hasNatElimIotaRoot_exists_step_natElim
#assert_no_axioms FX1Poly.Core.hasNatElimIotaRoot_exists_step_natRec

-- Redex-extraction bricks completing the per-redex layer: LIST + OPTION + EITHER + IDENTITY eliminators.
-- listCons is the first BINARY-constructor inversion; eitherMatch has two unary scrutinees; idJ/idStrictRec
-- have a single (non-disjunctive) isReflSource check on the witness child.  With every root-redex shape
-- covered, `hasRootStepSource → ∃ step` is now assemblable.
#assert_no_axioms FX1Poly.Core.isListNilSource_eq_listNil
#assert_no_axioms FX1Poly.Core.isListConsSource_eq_listCons
#assert_no_axioms FX1Poly.Core.isOptionNoneSource_eq_optionNone
#assert_no_axioms FX1Poly.Core.isOptionSomeSource_eq_optionSome
#assert_no_axioms FX1Poly.Core.isEitherInlSource_eq_eitherInl
#assert_no_axioms FX1Poly.Core.isEitherInrSource_eq_eitherInr
#assert_no_axioms FX1Poly.Core.isReflSource_eq_refl
#assert_no_axioms FX1Poly.Core.hasListElimIotaRoot_exists_step
#assert_no_axioms FX1Poly.Core.hasOptionMatchIotaRoot_exists_step
#assert_no_axioms FX1Poly.Core.hasEitherMatchIotaRoot_exists_step
#assert_no_axioms FX1Poly.Core.hasIdElimIotaRoot_exists_step_idJ
#assert_no_axioms FX1Poly.Core.hasIdElimIotaRoot_exists_step_idStrictRec

-- The ROOT-REDEX DISPATCH: `hasRootStepSource source = true → ∃ target, Step source target`, assembling all
-- 11 per-redex bricks via a generator case-split mirroring `hasRootStepSource`'s definition.  The missing
-- root ingredient for weak normalization (the Acc descent's step-extraction at a non-normal term).
#assert_no_axioms FX1Poly.Core.hasRootStepSource_exists_step

-- The COMPUTABLE root-redex firing FUNCTION + its soundness: `fireRootRedex generator payload children`
-- returns `some reduct` exactly on a root redex, exhibiting the reduct as a concrete RawTerm (vs the
-- existential `hasRootStepSource_exists_step`).  The reduct-supplier the weak-normalization normalizer
-- FUNCTION (#261/#480) needs to make `decidableOfNormalForms_of_isStronglyNormalizing` parameter-free.
-- Propext-clean over the 194-ctor table via DecidableEq dite-chains + ▸-casts + full spine destructure.
#assert_no_axioms FX1Poly.Core.RawTerm.fireRootRedex
#assert_no_axioms FX1Poly.Core.RawTerm.fireRootRedex_sound

-- COMPLETENESS of root-redex firing: fireRootRedex fires on EXACTLY the redexes hasRootStepSource detects
-- (the 11-generator dite-chains agree, via the RedexExtraction source-inversions + rfl firings).  The
-- contrapositive `fireRootRedex = none → hasRootStepSource = false` is the root half of structural normality
-- that reduceOnce completeness consumes.
#assert_no_axioms FX1Poly.Core.RawTerm.hasRootStepSource_imp_fireRootRedex_isSome
#assert_no_axioms FX1Poly.Core.RawTerm.fireRootRedex_eq_none_imp_hasRootStepSource_false

-- One deterministic reduction step as a TOTAL FUNCTION + soundness: `reduceOnce` fires a root redex
-- (fireRootRedex) or descends the child spine to the first reducible child; `reduceOnce_sound` /
-- `reduceOnceSpine_sound` show every produced reduct is a genuine Step / StepChildren.  The descent engine
-- the WN normalizer FUNCTION (#261/#480) iterates along Acc StepSuccessor.
#assert_no_axioms FX1Poly.Core.RawTerm.reduceOnce
#assert_no_axioms FX1Poly.Core.RawTerm.reduceOnce_sound
#assert_no_axioms FX1Poly.Core.RawTermChildren.reduceOnceSpine_sound

-- COMPLETENESS of reduceOnce: it halts (returns none) EXACTLY at structural normal forms.  With soundness
-- this pins reduceOnce's halting set to isStepNormalForm.  reduceOnce_eq_none_iff_isStepNormalForm packages
-- the biconditional; not_isStepNormalForm_imp_reduceOnce_isSome is the descent guarantee (a non-normal term
-- genuinely reduces) the Acc StepSuccessor normalizer FUNCTION steps along.
#assert_no_axioms FX1Poly.Core.RawTerm.reduceOnce_complete
#assert_no_axioms FX1Poly.Core.RawTermChildren.reduceOnceSpine_complete
#assert_no_axioms FX1Poly.Core.RawTerm.reduceOnce_eq_none_iff_isStepNormalForm
#assert_no_axioms FX1Poly.Core.RawTerm.not_isStepNormalForm_imp_reduceOnce_isSome

-- THE NORMALIZER FUNCTION + its correctness, and the parameter-free SN-fragment decidable Conv it unlocks.
-- normalize iterates reduceOnce along Acc StepSuccessor (Acc.rec — the descent shrinks the accessibility
-- proof, not the term); normalize_reducesTo / normalize_isStepNormalForm are its soundness/normality.
-- Conv.decidableOfStronglyNormalizing: two SN terms → Decidable (Conv ..), no NF witnesses / Normalizer /
-- global confluence.  The culmination of the WN grind (#503) — raw redex detection to a real decider.
#assert_no_axioms FX1Poly.Core.RawTerm.normalize
#assert_no_axioms FX1Poly.Core.RawTerm.normalize_unfold
#assert_no_axioms FX1Poly.Core.RawTerm.normalize_reducesTo
#assert_no_axioms FX1Poly.Core.RawTerm.normalize_isStepNormalForm
#assert_no_axioms FX1Poly.Core.Conv.decidableOfStronglyNormalizing

-- NORMALIZER METATHEORY: fixed-point-at-NF, idempotence, term↔NF conversion, and the headline
-- normalize_eq_iff_conv (two terms convert iff their normal forms coincide — the normal form is a complete
-- conversion invariant on the SN fragment, the explicit biconditional behind decidableOfStronglyNormalizing).
#assert_no_axioms FX1Poly.Core.RawTerm.normalize_eq_self_of_isStepNormalForm
#assert_no_axioms FX1Poly.Core.RawTerm.normalize_idempotent
#assert_no_axioms FX1Poly.Core.RawTerm.conv_normalize
#assert_no_axioms FX1Poly.Core.RawTerm.normalize_eq_iff_conv

-- DECIDABLE CONV ON THE SIMPLY-TYPED FRAGMENT WITH SN DISCHARGED.  Composing the normalizer's
-- decidableOfStronglyNormalizing with the simply-typed fundamental theorem's stronglyNormalizing* — typing
-- alone decides convertibility (no SN hypothesis), joining the FT (#502) and WN-normalizer (#503) lines.
#assert_no_axioms FX1Poly.Typed.Conv.decidableOfSimplyTypedUnderSubst
#assert_no_axioms FX1Poly.Typed.Conv.decidableOfSimplyTypedClosed

-- SN REFLECTED BY SUBSTITUTION: SN of `subst σ term` ⇒ SN of bare `term` (Acc reflected along `subst σ` via
-- Step.subst + Subrelation.accessible ∘ InvImage.accessible).  This pulls the FT's SN-of-substituted back to
-- SN-of-bare, removing the closing-substitution wart: decidableOfSimplyTypedBareClosed decides conversion of
-- the BARE closed terms themselves — the cleanest "simply-typed fragment has decidable conversion".
#assert_no_axioms FX1Poly.Core.StepStar.stronglyNormalizing_of_subst
#assert_no_axioms FX1Poly.Typed.emptyClosingSubst
#assert_no_axioms FX1Poly.Typed.Conv.decidableOfSimplyTypedBareClosed

-- CANONICAL NORMAL FORM for closed simply-typed terms — the NORMALIZE companion to the bare-closed DECIDE.
-- stronglyNormalizingBare: bare SN (the sole use site of stronglyNormalizing_of_subst); normalForm: the
-- computable RawTerm 0; conv_normalForm / normalForm_isStepNormalForm: term ↝* its NF and NF is normal;
-- normalForm_eq_self_of_isStepNormalForm: no spurious rewriting on a normal input; conv_iff_normalForm_eq:
-- two terms convert IFF their NFs coincide (the canonical NF is a complete conversion invariant — the
-- explicit characterization behind decidableOfSimplyTypedBareClosed).
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.stronglyNormalizingBare
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.normalForm
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.conv_normalForm
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.normalForm_isStepNormalForm
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.normalForm_eq_self_of_isStepNormalForm
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.conv_iff_normalForm_eq

-- REDUCER SMOKE CORPUS — the WN-grind reducer COMPUTES on concrete closed terms (each `by rfl`, no decide).
-- Demonstrates non-vacuity of reduceOnce / fireRootRedex / isStepNormalFormBool: β fires with the right
-- reduct (identity + binder-ignoring bodies), the reducer halts on normal forms, a two-step normalization
-- trace reaches `unit`, the detector agrees, and the root engine fires directly.  The 8 theorem gates
-- transitively certify the 5 fixture defs are axiom-free too.
#assert_no_axioms FX1Poly.Typed.reduceOnce_betaIdentity_fires
#assert_no_axioms FX1Poly.Typed.reduceOnce_betaConstant_fires
#assert_no_axioms FX1Poly.Typed.reduceOnce_identityLambda_halts
#assert_no_axioms FX1Poly.Typed.reduceOnce_unit_halts
#assert_no_axioms FX1Poly.Typed.reduceOnce_nestedRedex_fires
#assert_no_axioms FX1Poly.Typed.isStepNormalFormBool_betaRedex_false
#assert_no_axioms FX1Poly.Typed.isStepNormalFormBool_identityLambda_true
#assert_no_axioms FX1Poly.Typed.fireRootRedex_betaIdentity_fires

-- SIMPLY-TYPED GENERATION (INVERSION) LEMMAS — the "extract the premises" foundation of subject reduction.
-- SimplyTypedTermLF has no conv arm, so inversions conclude EQUALITIES: a variable's type IS its lookup, an
-- application's type IS the function's arrow codomain, a lambda's type IS a Π-code over a weakened codomain.
-- Proven by the cell-index inversion recipe (generalize subject + thread Eq + headGenerator/noConfusion +
-- injection past the mkGen/childCons index-eqs).  SR-β consumes inversionApplication then inversionLambda.
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.inversionVariable
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.inversionApplication
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.inversionLambda

-- REDUCIBLE TYPE-EXPR CLOSURE under renaming and substitution — the SR arc's type-side substrate.  The
-- lam rule of SimplyTypedTermLF carries IsReducibleTypeExprLF premises on domain/codomain; the (downstream)
-- renaming/substitution-preservation lemmas transport those premises across the action via these closure
-- lemmas (universe-code leaves are action-invariant; arrows thread *_lift_weaken_commute through the codomain).
#assert_no_axioms FX1Poly.Typed.IsReducibleTypeExprLF.subst
#assert_no_axioms FX1Poly.Typed.IsReducibleTypeExprLF.rename

-- SIMPLY-TYPED RENAMING PRESERVATION — the SR arc's term-side substrate.  SimplyTypedTermLF survives any
-- context-respecting renaming (var/app/lam, no conv arm); the lam arm transports its IsReducibleTypeExprLF
-- premises via IsReducibleTypeExprLF.rename and lifts the body IH via renameContextCondition_cons.
-- weakenUnderBinding is the one-fresh-binder corollary the substitution lemma's binder-lift consumes.
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.renameRespectingContext
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.weakenUnderBinding

-- SIMPLY-TYPED SUBSTITUTION PRESERVATION — the SR arc's β-engine.  SimplyTypedTermLF survives any well-typed
-- substitution; the lam arm transports IsReducibleTypeExprLF premises via .subst and lifts the body IH with
-- the 0/succ split (var at 0, weakenUnderBinding at k+1).  substituteUnderBinding is the subst0 corollary
-- β-reduction cites: (λ.body) arg ↝ body[arg] preserves type.
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.substRespectingContext
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.substituteUnderBinding

-- SUBJECT REDUCTION + TYPE-PRESERVING NORMALIZATION — the SR arc CULMINATION.  Reduction preserves typing
-- (single-step inverts Step per shape via StepInversion: var refuted, app = β/cong-fn/cong-arg with the
-- β-engine substituteUnderBinding + weaken_subst_singleton, lam = cong-body); multi-step iterates it; and
-- normalForm_typed (the gold payoff) threads the normalizer's reduction chain through SR* so the canonical
-- normal form of a closed simply-typed term is itself simply-typed at the same type.
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.subjectReduction
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.subjectReductionStar
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.normalForm_typed

-- CANONICITY (PROGRESS) — the classic STLC capstone, completing the simply-typed metatheory.  Closed normal
-- forms are lambdas: a LnNeutral term (var-headed app spine) is impossible at scope 0, the canonicalSplit
-- inducts on typing (β-redex case killed by Step.beta + blocks_step, child-normality via cong), and
-- normalFormIsLambda composes it with type-preserving normalization — every closed simply-typed term
-- normalizes to a lambda.
#assert_no_axioms FX1Poly.Typed.lnNeutral_scopeZero_absurd
#assert_no_axioms FX1Poly.Typed.isStepNormalForm_appCell_function
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.canonicalSplit
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.closedNormalIsLambda
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.normalFormIsLambda

-- INHABITATION / CONSISTENCY — the final theorem of the simply-typed metatheory.  Every closed simply-typed
-- term has an arrow type (canonicity says its NF is a lambda, type-preserving normalization keeps the type,
-- lambda inversion makes the type an arrow); hence universe codes are uninhabited by closed terms (arrow vs
-- universe-code head generators differ) — the fragment's consistency.
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.closedTermHasArrowType
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.noClosedTermAtUniverseCode

-- CONV EQUIVALENCE PACKAGE (#421) — convertibility is a DECIDABLE EQUIVALENCE RELATION on closed simply-
-- typed terms.  Raw Conv.refl/sym are unconditional but Conv.trans needs Church-Rosser for the chains
-- leaving the shared middle term, which at the raw layer requires that middle term to be strongly
-- normalizing (raw Step is NOT globally SN).  On the simply-typed fragment the fundamental theorem supplies
-- exactly that SN, so conv_trans (= trans_of_middle_accessible ∘ stronglyNormalizingBare) holds; bundled
-- with refl/sym it gives convertsTo_equivalence, and decidableOfSimplyTypedBareClosed makes it decidable.
-- This is the honest locus where the Conv equivalence structure becomes provable — the unconditional raw
-- Conv.trans remains genuinely unavailable.
#assert_no_axioms FX1Poly.Typed.SimplyTypedTermLF.conv_trans
#assert_no_axioms FX1Poly.Typed.SimplyTypedClosedTerm.convertsTo_equivalence
#assert_no_axioms FX1Poly.Typed.SimplyTypedClosedTerm.decidableConvertsTo

-- The PRODUCTIVE MIRROR of `isStepNormalForm_blocks_step`: a non-normal term genuinely reduces, with the
-- reduct exhibited.  Mutual term + child-spine halves.  Combines the root-redex dispatch (root conjunct) with
-- a structural recursion into the child spine (`Step.cong` / `StepChildren.here` / `StepChildren.there`).
-- The step-extraction the `Acc StepSuccessor` weak-normalization descent calls at every non-normal node.
#assert_no_axioms FX1Poly.Core.exists_step_of_not_isStepNormalForm
#assert_no_axioms FX1Poly.Core.exists_stepChildren_of_not_areStepNormalForms

-- WEAK NORMALIZATION: a strongly-normalizing term reaches a structural normal form, with the reduction
-- chain produced by descending the `Acc StepSuccessor` witness and extracting a real Step at every
-- non-normal node.  The StepStar-existence half of normalization (uniqueness comes from confluence) —
-- the strongly-normalizing-fragment door to decidable Conv (#267) and the WHNF migration (#374).
#assert_no_axioms FX1Poly.Core.exists_normalForm_of_isStronglyNormalizing

-- NORMAL-FORM UNIQUENESS: confluence forces two normal reducts of one SN term to coincide, so the SN
-- fragment has a UNIQUE normal form (existence from WN + this uniqueness clause).  The "the normal form"
-- handle a normalizer function realizes and SN-fragment decidable Conv (#267) rests on.
#assert_no_axioms FX1Poly.Core.normalForm_unique
#assert_no_axioms FX1Poly.Core.exists_unique_normalForm_of_isStronglyNormalizing

-- SN-FRAGMENT DECIDABLE CONV: Conv = normal-form equality on the strongly-normalizing fragment, with the
-- global StepStar.HasConfluence hypothesis of PolygraphConvergentDecision DISCHARGED per-term from the SN
-- witnesses (confluence_of_localJoin_and_accessible).  The honest raw-layer decider modulo the normalizer
-- function (#261/#480) that supplies the normal-form witnesses.
#assert_no_axioms FX1Poly.Core.Conv.iff_normalForms_eq_of_isStronglyNormalizing
#assert_no_axioms FX1Poly.Core.Conv.decidableOfNormalForms_of_isStronglyNormalizing
