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
import FX1Poly.Typed.HasTypeDescElim
import FX1Poly.Typed.HasTypeDescValidity
import FX1Poly.Typed.HasTypeDescInversion
import FX1Poly.Typed.HasTypeDescUniqueness
import FX1Poly.Typed.HasTypeDescWeakening
import FX1Poly.Typed.HasTypeDescSubstitution
import FX1Poly.Typed.HasTypeDescElimWeakening
import FX1Poly.Typed.HasTypeDescElimSubstitution
import FX1Poly.Typed.HasTypeDescApplication
import FX1Poly.Typed.HasTypeDescPi
import FX1Poly.Typed.HasTypeDescPiWeakening

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
    the shipped `DescTelescope.toHasTypeTelescope`), self-recursive only. -/
#assert_no_axioms FX1Poly.Typed.DescTermTelescope
#assert_no_axioms FX1Poly.Typed.DescTelescope.toTermTelescope
#assert_no_axioms FX1Poly.Typed.descTermTelescope_heterogeneous

/-! ### Intrinsic VALIDITY of the description engine (`HasTypeDescValidity`) — the
    FIRST BRICK of the HasTypeDesc-from-HasType DECOUPLE.  The ⟺ equivalence
    (`HasTypeDesc.toHasType`) is total, so it forbids growing the engine with any
    `gen` row the bespoke `HasType` lacks (would break soundness ⇒ force a bespoke
    arm = the cascade we kill).  Decoupling = giving `HasTypeDesc` its OWN metatheory.
    `IsTypeDesc` = the intrinsic "inhabits a universe" (over `HasTypeDesc`, not
    `HasType`); `classifierIsTypeDesc` = validity (P3) proved by FULL-enumeration
    term-mode `match` on the engine (the propext-free form of the shipped
    `HasTypeDesc.toHasType`) — `var` lifts the context entry via completeness,
    `conv` reuses `reclassifierTyped` verbatim (no `Conv.trans`), formation arms
    re-fire `universeFormation` one level up (genFormation pinned by the same
    `by_cases`+`exfalso` generator-pin). -/
#assert_no_axioms FX1Poly.Typed.IsTypeDesc
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.classifierIsTypeDesc

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
    Shipped for BOTH the dependent-binary formers (Π over `gen_piTyCode`, Σ over
    `gen_sigmaTyCode`).  `…General` is the subject-generalized recursive workhorse;
    `inversion{Pi,Sigma}Code` the concrete `{pi,sigma}TyCodeCell` entry points. -/
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.inversionPiCodeGeneral
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.inversionPiCode
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.inversionSigmaCodeGeneral
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.inversionSigmaCode

/-! ### INVERSION (P8, FULL) for the description engine — premise telescope AND the
    classifier-`Conv` conjunct (`…WithConv`).  The first wiring of typed `Conv.trans`
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
    UNIQUENESS (P7) will consume when inverting the second derivation. -/
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
    `genFormation` arm is now ALSO intrinsic — it inverts the second derivation with the
    INTRINSIC `inversion{Pi,Sigma}CodeWithConvGeneral`, then forces the two formation
    telescopes to agree on `levels`/`flag` via `DescTelescope.uniquenessAgree`, after
    which both classifiers reduce to the SAME canonical universe code.  The ONE remaining
    leaf coupling is `uniquenessAgree` settling each HEAD CHILD's level/flag through the
    verified bespoke `HasType.uniqueness` (a standalone recursion cannot yet call the
    intrinsic uniqueness it precedes; the fully intrinsic version makes the two MUTUAL —
    the decouple's next target).  P7 makes `infer` well-defined and feeds canonicity. -/
#assert_no_axioms FX1Poly.Typed.DescTelescope.uniquenessAgree
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.uniqueness

/-! ### INTRINSIC renaming/weakening (P6, the β-engine) for the description engine
    (`HasTypeDescWeakening`).  polycell.md §11.8.5 P6: typing is preserved along a context
    morphism.  `HasTypeDesc.renameRespectingContext` (with its telescope companion
    `DescTelescope.renameRespectingTelescope`) preserves `HasTypeDesc` along any renaming
    respecting the context; `HasTypeDesc.weakenUnderBinding` is the weakening special case.
    The FIRST intrinsic-BY-INDUCTION `HasTypeDesc` metatheorem of the decouple (validity /
    inversion / uniqueness were case-analysis; this is genuine MUTUAL recursion) — proved
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
    corollary the β-rule cites.  The SECOND intrinsic-by-induction mutual metatheorem — same
    clean shape as intrinsic weakening (no second-derivation inversion), and the decouple
    COMPOUNDS: the companion's successor case reuses the intrinsic
    `HasTypeDesc.weakenUnderBinding` to weaken the substituent across the binder.  `Conv.subst`
    (#370) rides the `conv` arm — no `Conv.trans`, so the β-engine is unblocked ahead of raw
    confluence.  NOT routed through the `⟺` maps. -/
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.substRespectingContext
#assert_no_axioms FX1Poly.Typed.DescTelescope.substRespectingTelescope
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.substituteUnderBinding

/-! ### INTRINSIC renaming/weakening (P6) for the ELIMINATOR-shape term spine
    (`HasTypeDescElimWeakening`).  polycell.md §11.8.5 P6 applied to `DescTermTelescope` — the
    maximally-general typed-children spine (each child at an ARBITRARY classifier) that the
    future eliminator `gen`-arm (the non-uniform seam PAST formation) consumes.  This is the
    eliminator spine's cartesian-lift fibration leg, regardless of how the arm lands.

    NON-breaking: `DescTermTelescope` is a STANDALONE inductive (`HasTypeDesc` appears only
    positively in `cons`'s `headTyped`), so this touches neither `HasTypeDesc`'s constructors
    nor the `toHasType` ⟺ soundness map.  SELF-recursive (not a mutual block): the head child's
    typing is re-renamed by the SHIPPED `HasTypeDesc.renameRespectingContext` on the opaque
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

    SELF-recursive (not mutual): the head child's typing is re-substituted by the SHIPPED
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
    future `app`/`snd` arms AHEAD of the arms — that the instantiated codomain is a well-formed
    type — by composing three shipped intrinsic bricks: validity (`classifierIsTypeDesc`),
    Π/Σ inversion-components, and the β-engine `substituteUnderBinding`.  The FIRST place the
    intrinsic substitution feeds a dependent-elimination soundness fact.  POSITIVE construction
    (not a degenerate SR/Conv-stability collapse): `piApplicationOutputIsType` —
    `f : Π A.B`, `a : A` ⊢ `B[a]` IsType; `sigmaProjectionOutputIsType` — the Σ mirror.
    `subst0 (universeCodeCell ..) argument ≡ universeCodeCell ..` by defeq (subst0 reducible +
    subst_universeCodeCell rfl) closes the `IsTypeDesc` witness.  NON-breaking: standalone
    lemmas, touch neither `HasTypeDesc` ctors nor the `⟺` maps. -/
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.piApplicationOutputIsType
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.sigmaProjectionOutputIsType

/-! ### GROWING THE ENGINE PAST FORMATION + FIRST NON-VACUOUS SUBJECT REDUCTION
    (`HasTypeDescPi`).  polycell.md §11.8.5: 0-FP is FREE BY CONSTRUCTION (intrinsic intro rules
    ⇒ empty fiber over the unsound), so the `toHasType ⟺ HasType` map was only ever a
    formation-fragment CROSS-CHECK, not the soundness source.  `HasTypeDescPi` ADDITIVELY embeds
    the formation fragment (`ofFormation`) and adds Π-introduction (λ) + Π-elimination (app) +
    its own `conv` — the first engine that expresses β-redexes.  NON-breaking: leaves
    `HasTypeDesc`, `toHasType`, `decidableOfWellFormed`, and the uniqueness proofs untouched
    (sidesteps the decidability/uniqueness cascade a direct `HasTypeDesc` extension forces);
    `HasTypeDesc` cannot type lamCell/appCell (no `typingRuleDescOf` row for gen_lam/gen_app),
    so `ofFormation` of a redex is impossible and the engine genuinely EXTENDS coverage.
    `betaCoherence_formationBody` is the FIRST non-vacuous SR in the kernel: a β-redex
    `app(lam body) arg` and its β-reduct `subst0 body arg` BOTH type at `subst0 codomainCode arg`
    — redex by piElim∘piIntro, reduct by the shipped intrinsic `substituteUnderBinding`.  Honest:
    preservation for component-derived redexes; fully-general inverted SR follows once Π-arm
    inversion + grown-engine substitution land. -/
#assert_no_axioms FX1Poly.Typed.lamCell
#assert_no_axioms FX1Poly.Typed.appCell
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi
#assert_no_axioms FX1Poly.Typed.IsTypeDescPi
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.toHasTypeDescPi
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.betaCoherence_formationBody

/-! ### GROWN-ENGINE RENAMING/WEAKENING (P6, the first fibration leg) — `HasTypeDescPiWeakening`.
    polycell.md §11.8.5 P6 applied to the grown engine `HasTypeDescPi`: its cartesian-lift
    fibration leg.  Renaming PRESERVES formation-ness (introduces no eliminations), so the
    `ofFormation` arm delegates directly to the shipped `HasTypeDesc.renameRespectingContext` and
    re-wraps — no substitution-closure gap (that gap only bites term-substitution, which awaits a
    native Π-formation arm).  Self-recursive (not mutual): cross-call to the shipped formation
    renamer on the opaque `formationTyped`; recursions on the strictly-smaller `HasTypeDescPi`
    sub-derivations ⇒ structural recursion w/o `termination_by`.  `piIntro` crosses one binder
    (one-binder context-condition via `rename_lift_weaken_commute`); `piElim`'s output commutes by
    `rename_subst0_commute`.  `weakenUnderBinding` is the `fun _ => rfl` corollary.  NON-breaking:
    leaves HasTypeDesc/toHasType/decidability/uniqueness untouched. -/
#assert_no_axioms FX1Poly.Typed.rename_lamCell
#assert_no_axioms FX1Poly.Typed.rename_appCell
#assert_no_axioms FX1Poly.Typed.renameContextCondition_cons
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.renameRespectingContext
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.weakenUnderBinding

/-! ### NATIVE Π/Σ-FORMATION ARMS for the grown engine (substitution-closure prerequisite).
    `HasTypeDescPi` gains `piFormation` + `sigmaFormation` (native dependent type-former
    formation: domain:Type@dl, codomain:Type@cl under the binder ⊢ Π/Σ : Type@(dl⊔cl)).  These
    make the engine SUBSTITUTION-CLOSED: substituting a grown term into a `piTyCodeCell` component
    yields a Π type with a non-formation component, which `ofFormation` cannot type but
    `piFormation` can — the prerequisite for the grown-engine substitution leg.  The
    `renameRespectingContext` gate above re-verifies with the two new arms (the binder-crossing
    condition factored into `renameContextCondition_cons`, shared by piIntro/piFormation/
    sigmaFormation).  NON-breaking: additive constructors; HasTypeDesc/toHasType/decidability/
    uniqueness untouched. -/

/-! ### GENERIC GROWN FORMATION ARM — `genFormationPi` + `DescTelescopePi` (cascade-death at the
    grown layer, the §5-endgame direction).  `HasTypeDescPi` becomes a mutual block with the grown
    premise spine `DescTelescopePi`, gaining ONE generic `genFormationPi` arm over `typingRuleDescOf`
    (the grown mirror of `HasTypeDesc.genFormation`) — a new dependent former is ONE table row, ZERO
    new arms (P13).  Unlike the binary `piFormation`/`sigmaFormation` it subsumes, the generic arm
    types a former with GROWN components (the `DescTelescopePi` heads are `HasTypeDescPi`, not just
    formation) with NO per-former dispatch — this is exactly what makes the grown engine
    SUBSTITUTION-CLOSED generically (the binary arms would force a partial-match on the child
    telescope, the indexed-inductive propext trap).  `toDescTelescopePi` + `genFormationToHasTypeDescPi`
    are the subsumption witnesses (formation formation is grown formation, through the generic arm).
    The renaming leg `HasTypeDescPi.renameRespectingContext` becomes mutual with the spine companion
    `DescTelescopePi.renameRespectingTelescope` (the `renameRespectingContext` gate above re-verifies
    with the new generic arm).  NON-breaking: additive constructor + mutual wrap; HasTypeDesc/
    toHasType/decidability/uniqueness untouched. -/
#assert_no_axioms FX1Poly.Typed.DescTelescopePi
#assert_no_axioms FX1Poly.Typed.DescTelescope.toDescTelescopePi
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.genFormationToHasTypeDescPi
#assert_no_axioms FX1Poly.Typed.DescTelescopePi.renameRespectingTelescope
