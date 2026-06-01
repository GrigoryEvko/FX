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
#assert_no_axioms FX1Poly.Typed.HasTypePiSigmaFormationCheckingCertificate.rejectHasTypeLambda
#assert_no_axioms FX1Poly.Typed.HasTypePiSigmaFormationCheckingCertificate.rejectHasTypeApplication
#assert_no_axioms FX1Poly.Typed.HasTypePiSigmaFormationCheckingCertificate.rejectHasTypeDescLambda
#assert_no_axioms FX1Poly.Typed.HasTypePiSigmaFormationCheckingCertificate.rejectHasTypeDescApplication
#assert_no_axioms FX1Poly.Typed.buildHasTypePiSigmaFormationCheckingCertificate
#assert_no_axioms FX1Poly.Typed.HasTypePiSigmaFormationCheckingCertificate.proveClosedSubjectIsType
#assert_no_axioms FX1Poly.Typed.HasTypePiSigmaFormationCheckingCertificate.proveClosedSubjectIsTypeFormer
#assert_no_axioms FX1Poly.Typed.HasTypePiSigmaFormationCheckingCertificate.proveClosedClassifierConvUniverseCode
#assert_no_axioms FX1Poly.Typed.HasTypePiSigmaFormationCheckingCertificate.proveClosedHasTypeDescSubjectIsTypeDesc
#assert_no_axioms FX1Poly.Typed.HasTypePiSigmaFormationCheckingCertificate.proveClosedHasTypeDescSubjectIsTypeFormer
#assert_no_axioms FX1Poly.Typed.HasTypePiSigmaFormationCheckingCertificate.proveClosedHasTypeDescClassifierConvUniverseCode

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
#assert_no_axioms FX1Poly.Typed.fundamentalConvValidityWithTypeValueCandidatesOfAllReducibleTypesHaveTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.fundamentalConvValidityWithTypeValueCandidatesOfPositiveMemberExtension
#assert_no_axioms FX1Poly.Typed.fundamentalPiElimWithTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.fundamentalPiElimValidityWithTypeValueCandidatesFromResultTypeValuePremise
#assert_no_axioms FX1Poly.Typed.fundamentalPiElimValidityWithTypeValueCandidatesOfAllReducibleTypesHaveTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.fundamentalPiElimValidityWithTypeValueCandidatesOfPositiveMemberExtension
#assert_no_axioms FX1Poly.Typed.fundamentalPiIntroWithTypeValueCandidatesFromTypeValueArgumentPremise
#assert_no_axioms FX1Poly.Typed.substitutedPiTyCode_ne_universeCodeCell
#assert_no_axioms FX1Poly.Typed.substitutedSigmaTyCode_ne_universeCodeCell
#assert_no_axioms FX1Poly.Typed.fundamentalPiIntroValidityWithTypeValueCandidatesFromTypeValueArgumentPremise
#assert_no_axioms FX1Poly.Typed.fundamentalPiIntroWithTypeValueCandidatesFromTypedArgumentPremise
#assert_no_axioms FX1Poly.Typed.fundamentalPiIntroValidityWithTypeValueCandidatesFromTypedArgumentPremise
#assert_no_axioms FX1Poly.Typed.fundamentalPiIntroValidityWithTypeValueCandidatesFromUniverseDomain
#assert_no_axioms FX1Poly.Typed.fundamentalPiIntroValidityWithTypeValueCandidatesFromUniverseDomainAllReducibleTypesHaveTypeValueCandidates
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
#assert_no_axioms FX1Poly.Typed.codomainMemberAtDomainLevelWithTypeValueCandidatesFromNoZeroDomain
#assert_no_axioms FX1Poly.Typed.fundamentalPiFormationValidityWithTypeValueCandidatesFromNoZeroDomainAllReducibleTypesHaveTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.codomainMemberAtDomainLevelWithTypeValueCandidatesFromUniverseDomain
#assert_no_axioms FX1Poly.Typed.formerChildrenReducibleAtDispatchLevelsWithTypeValueCandidatesFromUniverseDomain
#assert_no_axioms FX1Poly.Typed.fundamentalPiFormationWithTypeValueCandidatesFromUniverseDomain
#assert_no_axioms FX1Poly.Typed.fundamentalPiFormationValidityWithTypeValueCandidatesFromUniverseDomain
#assert_no_axioms FX1Poly.Typed.fundamentalPiFormationValidityWithTypeValueCandidatesFromUniverseDomainMembersHaveTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.fundamentalSigmaFormationValidityWithTypeValueCandidatesFromUniverseDomainMembersHaveTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.fundamentalPiFormationValidityWithTypeValueCandidatesFromUniverseDomainAllReducibleTypesHaveTypeValueCandidates
#assert_no_axioms FX1Poly.Typed.fundamentalSigmaFormationValidityWithTypeValueCandidatesFromUniverseDomainAllReducibleTypesHaveTypeValueCandidates
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
