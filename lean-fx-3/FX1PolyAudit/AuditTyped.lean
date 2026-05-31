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
import FX1Poly.Typed.HasTypeClosedForms
import FX1Poly.Typed.WfContextDecidable
import FX1Poly.Typed.HasTypeGen
import FX1Poly.Typed.DependentTelescopeSpike
import FX1Poly.Typed.HasTypeDesc
import FX1Poly.Typed.HasTypeDescSound
import FX1Poly.Typed.HasTypeDescDecidable

/-! # Tools/AuditAll/AuditTyped
   — persistent per-declaration zero-axiom gate for the typed layer

The typed layer (polycell.md §11.8.5) is the dim-0 soundness stratum: the
`.context` / `.type` / `.term` cells that classify each other.  Its first
brick is the native `TypingContext` de Bruijn telescope (TY-CTX, the
lean-fx-3 re-port of lean-fx-2's M31/M32) — the `.context`-sort spine the
`HasType` engine consumes via the variable rule.

Every declaration here must elaborate without `propext`, `Classical.choice`,
`Quot.sound`, or `sorryAx` — so any future edit that introduces an axiom
dependency fails `lake build FX1PolyAudit` immediately.  The `lookup`
de Bruijn destructuring and `length_eq_scope` induction are the two places
a careless rewrite could pull `propext` through the match compiler; these
gates pin them shut.
-/

/-! ### TY-CTX #467 — native TypingContext telescope + lookup + coherence -/

#assert_no_axioms FX1Poly.Typed.TypingContext
#assert_no_axioms FX1Poly.Typed.TypingContext.length
#assert_no_axioms FX1Poly.Typed.TypingContext.length_eq_scope
#assert_no_axioms FX1Poly.Typed.TypingContext.lookup
#assert_no_axioms FX1Poly.Typed.TypingContext.lookup_cons_zero
#assert_no_axioms FX1Poly.Typed.TypingContext.lookup_cons_succ

/-! ### TY-ENGINE #282 first slice — HasType var + conv core + IsType -/

#assert_no_axioms FX1Poly.Typed.universeCodeCell
#assert_no_axioms FX1Poly.Typed.variableCell
#assert_no_axioms FX1Poly.Typed.piTyCodeCell
#assert_no_axioms FX1Poly.Typed.sigmaTyCodeCell
#assert_no_axioms FX1Poly.Typed.HasType
#assert_no_axioms FX1Poly.Typed.IsType

/-! ### TY-honesty #470 first slice — 0-false-positive probe (ill-typed cell has no derivation) -/

#assert_no_axioms FX1Poly.Typed.unitCell
#assert_no_axioms FX1Poly.Typed.appUnitUnit
#assert_no_axioms FX1Poly.Typed.RawTerm.headGenerator
#assert_no_axioms FX1Poly.Typed.HasType.typedSubjectIsVariableOrUniverseCode
#assert_no_axioms FX1Poly.Typed.appUnitUnit_hasNoTyping

/-! ### TY-WF #468 — WfContext predicate + inversions + non-vacuity witness -/

#assert_no_axioms FX1Poly.Typed.WfContext
#assert_no_axioms FX1Poly.Typed.WfContext.emptyIsWellFormed
#assert_no_axioms FX1Poly.Typed.WfContext.tailWellFormed
#assert_no_axioms FX1Poly.Typed.WfContext.headIsType
#assert_no_axioms FX1Poly.Typed.WfContext.cons
#assert_no_axioms FX1Poly.Typed.wfContext_universeBinding

/-! ### TY-SR-cong #456 — typed renaming + weakening (structural cartesian lift) -/

#assert_no_axioms FX1Poly.Typed.rename_variableCell
#assert_no_axioms FX1Poly.Typed.rename_universeCodeCell
#assert_no_axioms FX1Poly.Typed.HasType.renameRespectingContext
#assert_no_axioms FX1Poly.Typed.HasType.weakenUnderBinding

/-! ### TY-SR-beta engine #457 — typed single-substitution (subst0 preserves typing) -/

#assert_no_axioms FX1Poly.Typed.subst_variableCell
#assert_no_axioms FX1Poly.Typed.subst_universeCodeCell
#assert_no_axioms FX1Poly.Typed.subst_singleton_renameWeaken_cancel
#assert_no_axioms FX1Poly.Typed.HasType.substRespectingContext
#assert_no_axioms FX1Poly.Typed.HasType.substituteUnderBinding

/-! ### TY-VALIDITY (P3) #468 — IsType stability + lookup-is-type + classifier-is-a-type -/

#assert_no_axioms FX1Poly.Typed.IsType.weakenUnderBinding
#assert_no_axioms FX1Poly.Typed.IsType.substituteUnderBinding
#assert_no_axioms FX1Poly.Typed.WfContext.lookupIsType
#assert_no_axioms FX1Poly.Typed.HasType.classifierIsType

/-! ### FUNDAMENTAL THEOREM (M10, current fragment) + typed Conv.trans payoff -/

#assert_no_axioms FX1Poly.Typed.HasType.isStronglyNormalizing
#assert_no_axioms FX1Poly.Typed.IsType.isStronglyNormalizing
#assert_no_axioms FX1Poly.Typed.Conv.trans_of_typedMiddle

/-! ### INVERSION (#454, current fragment) — per-shape classifier characterization -/

#assert_no_axioms FX1Poly.Typed.HasType.inversionVariable
#assert_no_axioms FX1Poly.Typed.HasType.inversionUniverseCode
-- Π-formation inversion (#443): a typed `piTyCodeCell` exposes both children's
-- universe typings (at one shared flag) + a `Conv` of the classifier to
-- `Type@(lmax …)`.  The decider's refutation arms + `uniqueness`'s Π case feed on
-- it.  Same equation-motive shape as the var / universe inversions, with the
-- `piFormation` arm closed by `piTyCodeCell_inj`.
#assert_no_axioms FX1Poly.Typed.HasType.inversionPiCode
-- Σ-formation inversion (#445): the dual of `inversionPiCode`.  A typed
-- `sigmaTyCodeCell` exposes both children's universe typings (at one shared
-- flag) + a `Conv` of the classifier to `Type@(lmax …)`.  The Σ arms of the
-- decider cascade + `uniqueness` feed on it.  Same equation-motive shape, with
-- the `piFormation` arm now the impossible one (`Generator.noConfusion`) and the
-- `sigmaFormation` arm closed by `sigmaTyCodeCell_inj`.
#assert_no_axioms FX1Poly.Typed.HasType.inversionSigmaCode

/-! ### UNIQUENESS OF TYPING (#469, current fragment) -/

#assert_no_axioms FX1Poly.Typed.HasType.uniqueness

/-! ### DECIDABLE TYPE CONVERSION (current fragment) — normal-form rigidity →
    decidable Conv.  Core rigidity (`StepStar.eq_of_noStep`, `Conv.eq_of_noStep`,
    `Conv.iff_eq_of_noStep`) is swept by `#audit_namespace FX1Poly.Core` in
    `AuditCoreSubstrate.lean`; the typed payoff is pinned per-decl here. -/

#assert_no_axioms FX1Poly.Typed.IsType.hasNoStep
#assert_no_axioms FX1Poly.Typed.Conv.eq_of_isType
#assert_no_axioms FX1Poly.Typed.levelFlag_eq_of_conv_universeCodeCell
#assert_no_axioms FX1Poly.Typed.Conv.iff_eq_of_isType
#assert_no_axioms FX1Poly.Typed.Conv.decidableOfIsType

/-! ### TYPED SUBJECT REDUCTION (P4 #458, current fragment) — `subjectHasNoStep`
    is the real structural invariant (well-typed subjects are normal leaves);
    SR itself holds vacuously over the leaf-only fragment until app/iota arms
    land (#444), then routes through the substitution lemma (#457). -/

#assert_no_axioms FX1Poly.Typed.HasType.subjectHasNoStep
#assert_no_axioms FX1Poly.Typed.HasType.subjectReduction

/-! ### UNIVERSE-CODE CELL DESTRUCTOR (#303 groundwork) — recovers
    `universeCodeCell e flag` from `headGenerator = gen_universeCode` via the
    `RawTermChildren.eq_childNil` brick; the raw destructor `Decidable IsType`
    needs to apply `HasType.universeFormation`. -/

#assert_no_axioms FX1Poly.Typed.eq_universeCodeCell_of_headGenerator
#assert_no_axioms FX1Poly.Typed.eq_variableCell_of_headGenerator
#assert_no_axioms FX1Poly.Typed.headGenerator_universeCodeCell
#assert_no_axioms FX1Poly.Typed.headGenerator_variableCell
-- universe-code cell injectivity (#442 no-Type-in-Type probe support): equal
-- universe codes have equal levels and flags, via `cases` on the cell equality
#assert_no_axioms FX1Poly.Typed.universeCodeCell_inj

/-! ### Π-FORMATION SHAPE BRICKS (#443 stage 1, non-breaking) — `piTyCodeCell`
    smart ctor + head-generator computation + the two-child destructor that
    stage 2's `piFormation` arm + the decider cascade will consume. -/

#assert_no_axioms FX1Poly.Typed.headGenerator_piTyCodeCell
#assert_no_axioms FX1Poly.Typed.eq_piTyCodeCell_of_headGenerator
#assert_no_axioms FX1Poly.Typed.piTyCodeCell_noStep_of_childrenNoStep
-- `piTyCodeCell` is injective (domain/codomain recovered): the component extractor
-- the `piFormation` arm of `inversionPiCode` aligns the inducted arm's own
-- domain/codomain with the inversion target.  `cases` on the cell equality (the
-- propext-free substrate tactic), NOT `injection`.
#assert_no_axioms FX1Poly.Typed.piTyCodeCell_inj

/-! ### Π-CELL RENAME/SUBST COMMUTATIONS (#443 stage 2 prereq, non-breaking) —
    `rename`/`subst` distribute over a `piTyCodeCell` (domain at shift `0`,
    codomain at shift `1` under `iterateLiftRaw _ 1`), both `rfl` via the
    canonical fold.  The typed-weakening / typed-substitution Π cases will
    chain these with the `RawTermSubst0Commute` `iterateLiftRaw` lemmas. -/

#assert_no_axioms FX1Poly.Typed.rename_piTyCodeCell
#assert_no_axioms FX1Poly.Typed.subst_piTyCodeCell

/-! ### RENAME LIFT-WEAKEN COMMUTATION (#443 stage 2 prereq, non-breaking) — the
    naturality square `lift ρ ∘ weaken = weaken ∘ ρ` at the term level, the
    binder-crossing crux the `piFormation` case of `renameRespectingContext`
    (first binder-introducing arm) discharges its lifted context-condition with. -/

#assert_no_axioms FX1Poly.Typed.rename_lift_weaken_commute
#assert_no_axioms FX1Poly.Typed.subst_lift_weaken_commute

/-! ### Π-CELL SIZE MEASURE (#443 stage 2 prereq, non-breaking) — domain and
    codomain are `RawTerm.size`-smaller than the `piTyCodeCell` containing them.
    The `decreasing_by` obligations a well-founded recursive Π-formation decider
    discharges, sidestepping the `RawTerm`/`RawTermChildren` mutual
    `termination_by` boundary gap with a plain `Nat` measure. -/

#assert_no_axioms FX1Poly.Typed.size_lt_piTyCodeCell_domain
#assert_no_axioms FX1Poly.Typed.size_lt_piTyCodeCell_codomain

/-! ### Σ-FORMATION SHAPE SUBSTRATE (#445 stage 1, non-breaking) — the complete
    raw-cell substrate for the Σ-formation arm, the dual of #443's Π substrate.
    `gen_sigmaTyCode` is structurally identical to `gen_piTyCode` ([0, 1] binder
    shifts, `Unit` payload), so each brick is the exact analog of its
    `piTyCodeCell` counterpart with the head generator swapped: the smart-ctor
    head computation, the two-child destructor, injectivity, non-stepping (pure
    type former), the `rename`/`subst` commutations (both `rfl`), and the
    `RawTerm.size` `decreasing_by` bricks.  The Σ arm + its decider cascade
    (next iteration) consume these. -/

#assert_no_axioms FX1Poly.Typed.headGenerator_sigmaTyCodeCell
#assert_no_axioms FX1Poly.Typed.eq_sigmaTyCodeCell_of_headGenerator
#assert_no_axioms FX1Poly.Typed.sigmaTyCodeCell_inj
#assert_no_axioms FX1Poly.Typed.sigmaTyCodeCell_noStep_of_childrenNoStep
#assert_no_axioms FX1Poly.Typed.rename_sigmaTyCodeCell
#assert_no_axioms FX1Poly.Typed.subst_sigmaTyCodeCell
#assert_no_axioms FX1Poly.Typed.size_lt_sigmaTyCodeCell_domain
#assert_no_axioms FX1Poly.Typed.size_lt_sigmaTyCodeCell_codomain

/-! ### IsType CHARACTERIZATION (#303 heart) — the decidable trichotomy on the
    head generator that `Decidable IsType` assembles: universe codes are always
    types; a variable is a type iff its looked-up classifier is a universe code
    (forward by `inversionVariable` + rigidity); any other head is never a type
    (`typedSubjectIsVariableOrUniverseCode`). -/

#assert_no_axioms FX1Poly.Typed.IsType.ofUniverseCodeCell
#assert_no_axioms FX1Poly.Typed.IsType.variableCell_iff_lookupIsUniverseCode
#assert_no_axioms FX1Poly.Typed.IsType.not_of_headGenerator

/-! ### DECIDABLE IsType (#303 + #443, current fragment) — the decision procedure
    assembled over the trichotomy: case on the cell (payload = index as data),
    `dite` on the head generator (`DecidableEq Generator`, no `Classical`).  The
    Π arm makes the procedure RECURSIVE (well-founded on `RawTerm.size`); the
    data-returning core `decideWithWitness` (a `PSum` of a `Σ'` universe witness
    or a no-universe proof) carries the children's flag as DATA so the shared-flag
    side condition is decidable — an `Exists` could not eliminate into the
    `Type`-valued decision.  `decidableOfWellFormed` is a thin wrapper. -/

#assert_no_axioms FX1Poly.Typed.IsType.decideWithWitness
#assert_no_axioms FX1Poly.Typed.IsType.decidableOfWellFormed

/-! ### HasType CHARACTERIZATION (#461 heart) — typed checking collapses to
    classifier equality: validity makes the classifier normal, so the inversions
    + rigidity turn `HasType Γ subject T` into `T = (the unique classifier)`.
    No `Conv` decision / normalizer needed for this fragment. -/

#assert_no_axioms FX1Poly.Typed.HasType.variableCell_iff_classifierEqLookup
#assert_no_axioms FX1Poly.Typed.HasType.universeCodeCell_iff_classifierEqSucc
#assert_no_axioms FX1Poly.Typed.HasType.not_of_headGenerator

/-! ### DECIDABLE HasType (#461/#302, current fragment) — typed checking decision
    procedure assembled over the classifier-equality characterization; mirror of
    `IsType.decidableOfWellFormed`, deciding via `DecidableEq RawTerm`. -/

#assert_no_axioms FX1Poly.Typed.HasType.decidableOfWellFormed

/-! ### DECIDABLE TYPED CONV (#462 ★ A-core, current fragment) — convertibility
    of the classifiers of two well-typed terms, via validity + rigidity. -/

#assert_no_axioms FX1Poly.Typed.Conv.decidableOfTyped

/-! ### TYPED SMOKE CORPUS (#470/#308, current fragment) — non-vacuity /
    regression witnesses pinning that the deciders DISCRIMINATE: one accepted +
    one rejected cell per outcome branch (universeCode-isTrue, var-isTrue,
    outer-reject, universeCode-isFalse). -/

#assert_no_axioms FX1Poly.Typed.headGenerator_unitCell
#assert_no_axioms FX1Poly.Typed.corpus_universeCode_typedBySucc
#assert_no_axioms FX1Poly.Typed.corpus_variable_typedByLookup
#assert_no_axioms FX1Poly.Typed.corpus_unitCell_rejected
#assert_no_axioms FX1Poly.Typed.corpus_universeCode_notTypedByUnit

/-! ### NO-TYPE-IN-TYPE PROBE (#442, M35-T1) — the headline universe-consistency
    guarantee: a universe code is NOT classified by itself (`Type@(e,f) :
    Type@(e,f)` rejected), so there is no `Type : Type` / Girard paradox at the
    universe level.  Routes through `universeCodeCell_iff_classifierEqSucc` (the
    classifier-equality characterization) + `universeCodeCell_inj` +
    `LevelExpr.ne_lsucc_self` (predicativity at the level algebra). -/

#assert_no_axioms FX1Poly.Typed.probe_universe_Type_in_Type_rejected

/-! ### CLOSED-TYPING CHARACTERIZATION (P10 consistency precursor, #460, current
    fragment) — every closed well-typed subject is itself a type.  The
    type-former-only fragment has NO closed proper terms yet (the closed `.term`
    layer below the universe is empty); `subjectIsVariableOrIsType` is the
    context-general induction engine (each non-`conv` arm witnesses `IsType` from
    its own conclusion), `closedSubjectIsType` the empty-context corollary
    (`Fin 0` kills the variable case). -/

#assert_no_axioms FX1Poly.Typed.HasType.subjectIsVariableOrIsType
#assert_no_axioms FX1Poly.Typed.HasType.closedSubjectIsType

/-! ### CLOSED-TYPING CHARACTERIZATION COMPLETED (#460 / P10 precursor, current
    fragment) — the two complementary halves of "what is a closed typing
    judgment?".  `closedSubjectIsTypeFormer`: a closed well-typed subject is
    EXACTLY a universe / Π / Σ type-former code (canonical forms; the `var`
    disjunct of the 4-way shape classification is killed by `Fin 0`).
    `closedClassifierConvUniverseCode`: its classifier is Conv to a universe code
    (via `closedSubjectIsType` + `uniqueness` at the empty `WfContext`) — the
    consistency content (no closed inhabitant below the universe level), the
    honest precursor to ★ #460 (which additionally needs an `Empty` former). -/

#assert_no_axioms FX1Poly.Typed.HasType.closedSubjectIsTypeFormer
#assert_no_axioms FX1Poly.Typed.HasType.closedClassifierConvUniverseCode

/-! ### CONTEXT WELL-FORMEDNESS DECISION (completes the decidable-checking story)
    — `WfContext.decidable` decides whether a raw `TypingContext` telescope is
    well-formed (every binding is a type in its prefix), by structural recursion
    on the telescope delegating each binding to `IsType.decidableOfWellFormed`
    (#303) under the prefix certificate.  The context-level checker complementing
    the term-level `Decidable IsType`/`HasType`/`Conv`.  Confirms the indexed
    two-constructor telescope match stays propext-clean into a `Decidable`
    motive. -/

#assert_no_axioms FX1Poly.Typed.WfContext.decidable

/-! ### TYPE SYNTHESIS / bidirectional `infer` (#478 / #300 M51, current fragment)
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

/-! ### TYPE CHECKING / bidirectional `check` (#479 / #301 M52, current fragment)
    — decide whether `subject` has the GIVEN `targetType`: synthesise with
    `infer`, confirm `targetType` is a type (`decideWithWitness`), decide
    `Conv synthType targetType`, coerce via the conversion rule on success.
    Returns `Decidable (HasType …)` (the faithful realisation of the spec's
    "`Option HasType`" — `Option` of a `Prop` is ill-typed), so it is sound AND
    complete by construction: `isTrue` carries the derivation, `isFalse` the
    refutation (`infer = none` ⊥ `infer_succeeds`; non-type target ⊥ validity;
    `Conv = isFalse` ⊥ uniqueness).  The general bidirectional method (rests on
    `infer` + generic decidable `Conv`, not the #461 collapse); on this fragment
    it necessarily agrees with the direct decider but survives fragment growth. -/

#assert_no_axioms FX1Poly.Typed.HasType.check

/-! ### CASCADE-FREE TYPING ENGINE s1 (#483, parallel-build) — the dependent-binary
    type-FORMATION shape-arm.  `HasTypeGen` is a NEW mutual inductive built
    ALONGSIDE the shipped `HasType` (additive; the eventual migration proves
    `HasTypeGen ⟺ HasType` then retires the per-former arms).  Three arms: `var`,
    `conv`, and ONE per-shape `dependentBinaryFormation` arm generic over the
    Generator via the `isDependentBinaryFormer` whitelist (gen_piTyCode /
    gen_sigmaTyCode) — the FIRST of Decision 4's ~6 shape-arms (P13:
    cascade-free; a second [0,1] former is one whitelist disjunct, zero new
    arms — witnessed by the two smoke lemmas).  SOUNDNESS (P1): the whitelist is
    an explicit Π/Σ enumeration, NOT a `binderShifts == [0,1]` proxy (which would
    wrongly admit gen_polyFunctor).  The spine `DependentBinaryFormationChildren`
    is mutual with `HasTypeGen`, its index sig free of `HasTypeGen` (mutual-index
    rule, StepChildren precedent); output level is an explicit INDEX (Prop-valued,
    P14 erasure). -/

#assert_no_axioms FX1Poly.Typed.isDependentBinaryFormer
#assert_no_axioms FX1Poly.Typed.isDependentBinaryFormer_piTyCode
#assert_no_axioms FX1Poly.Typed.isDependentBinaryFormer_sigmaTyCode
#assert_no_axioms FX1Poly.Typed.HasTypeGen
#assert_no_axioms FX1Poly.Typed.DependentBinaryFormationChildren
#assert_no_axioms FX1Poly.Typed.hasTypeGen_piFormation_viaShapeArm
#assert_no_axioms FX1Poly.Typed.hasTypeGen_sigmaFormation_viaShapeArm

/-! ### MOONSHOT FOUNDATION — generic variadic dependent-telescope typed-children
    spine (the description-universe's `premisesHold`).  `DependentTelescopeChildren`
    is the cumulative `[0,1,…,n-1]` dependent telescope of children-as-types
    (validated: reconstructs Π/Σ formation as its [0,1] instance + a [0,1,2]
    3-ary witness).  `DependentTelescopeTyped` is the MAXIMAL generalization —
    each child typed at an ARBITRARY per-step classifier (a telescope of typed
    TERMS, not just types — the shape an eliminator rule's premises take).  Both
    solve the shift-rebasing crux by indexing children at a fixed `baseScope`
    while only the context grows (`currentDepth`), making
    `(baseScope+currentDepth)+1 = baseScope+(currentDepth+1)` definitional.  This
    is the foundation stone for the description-driven generic `gen` arm. -/

#assert_no_axioms FX1Poly.Typed.DependentTelescopeChildren
#assert_no_axioms FX1Poly.Typed.dependentTelescope_reconstructs_piFormation
#assert_no_axioms FX1Poly.Typed.dependentTelescope_threeAry
#assert_no_axioms FX1Poly.Typed.DependentTelescopeTyped
#assert_no_axioms FX1Poly.Typed.dependentTelescopeTyped_reconstructs_piFormation
#assert_no_axioms FX1Poly.Typed.dependentTelescopeTyped_heterogeneous

/-! ### ★ MOONSHOT CORE — the description-driven generic typing engine
    (`HasTypeDesc`, polycell.md §11.8.5 / §5.2: the Natural-Model display map
    `Tm ↠ Ty` realized as a data-driven cascade-free `gen` arm).  `HasTypeDesc`
    = var + conv + nullary `universeFormation` + ONE generic `genFormation` arm
    consuming a per-generator `TypingRuleDesc` (the `typingRuleDescOf` table),
    typing the whole dependent-type-former family via the mutual `DescTelescope`
    spine with output = `rule.outputType scope levels flag` (for the type-formers,
    `universeFormerOutput = universeCodeCell (lmaxAll levels) flag`).  The
    `outputType` field generalizes the earlier level-only `combineLevel`, opening
    the §11.8.5 "non-uniform output" seam (output is rule-DATA, not hardwired).
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
-- the current fragment.  Hand-built (match on the bespoke decision + the two
-- equivalence maps), no `decidable_of_iff`/`Iff`, so propext-free.
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.decidableOfWellFormed
