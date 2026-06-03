import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.CellSort
import FX1Poly.Typed.HasType
import FX1Poly.Core.GeneratorTagRoundTrip
import FX1Poly.Core.GeneratorFinitePolygraph
import FX1Poly.Core.GeneratorPolygraphMap
import FX1Poly.Core.RawCellWordEncoding
import FX1Poly.Core.StepRewriteRuleMap
import FX1Poly.Core.StepWordRewriteSoundness
import FX1Poly.Core.StepWordRewriteEquivariance
import FX1Poly.Core.ConvWordJoinableBridge
import FX1Poly.Core.BetaEtaWordSystem
import FX1Poly.Core.MultisetOrder
import FX1Poly.Core.TerminationOrders
import FX1Poly.Core.ReducibleTypeClosed
import FX1Poly.Core.PointwiseIffAlgebra
import FX1Poly.Core.StratifiedReducibleLevelCongr
import FX1Poly.Core.StratifiedReducibleMemberNeutral
import FX1Poly.Core.StratifiedReducibleMemberStepClosure
import FX1Poly.Core.StrongNormalizationSubterm

/-! # FX1PolyAudit/AuditCore — zero-axiom gate for the cell-calculus core

Persistent per-declaration `#assert_no_axioms` gate for the FX1Poly
cell substrate.

`CellSort` — the seven-sort vocabulary
(context / type / term / mode / effect / grade / protocol) over which
every PolyCell morphism (the dim-1 `FXStep sort` cells) ranges.  This
is the spine of the "morphisms on terms, types, contexts, grades"
design: a 1-cell is `PolyCell fxProfile sort 1 …` for any `sort`, so
the sort vocabulary is the foundational brick.

Typed sort markers: `FX1Poly.Typed.hasType*Sort` pin the native
cells-classify-cells typing discipline (a `.term` subject classified by
a `.type` classifier) and guard against reintroducing an MLTT
`Foundation.Ty` classifier.  (The `HasType` inductive itself is gated in
`AuditTyped.lean`.)
-/

#assert_no_axioms FX1Poly.Core.CellSort
#assert_no_axioms FX1Poly.Core.CellSort.all
#assert_no_axioms FX1Poly.Core.CellSort.toCode
#assert_no_axioms FX1Poly.Core.CellSort.ofCode?
#assert_no_axioms FX1Poly.Core.CellSort.ofCode?_toCode
#assert_no_axioms FX1Poly.Core.CellSort.all_length

-- Typed-layer sort markers (cells classify cells: .term subject, .type classifier)
#assert_no_axioms FX1Poly.Typed.hasTypeSubjectSort
#assert_no_axioms FX1Poly.Typed.hasTypeClassifierSort
#assert_no_axioms FX1Poly.Typed.hasTypeContextBindingSort
#assert_no_axioms FX1Poly.Typed.hasType_classifies_term_by_type

-- §11.6.4 Generator-table validation (#230): the FX0 prefix-code tag assignment
-- `Generator.toNat` is collision-free (injective), proved via the explicit left
-- inverse `Generator.fromTag` and its per-constructor round-trip.  The head byte
-- of the cell serialization therefore uniquely identifies the generator.
#assert_no_axioms FX1Poly.Core.Generator.fromTag
#assert_no_axioms FX1Poly.Core.Generator.fromTag_toNat
#assert_no_axioms FX1Poly.Core.Generator.toNat_injective

-- SN-123 (#626): the FX kernel as a FINITE POLYGRAPH over the 194-Generator table. The generators are indexed
-- injectively (toNat_injective) + boundedly (toNat_lt, NEW) into Fin 194, with the total inverse table fromTag
-- (round-trip fromTag_toNat + range-totality fromTag_total_on_range, NEW); each carries its dimension (arity) and
-- boundary (binderShifts), coherently (binderShifts_length_eq_arity). fxKernelPolygraph bundles all of it — the
-- Leg-3 anchor for SN-124 (Generator→polygraph-gen map) + SN-125 (RawCell→OmegacEWord). Zero-axiom (cases+decide,
-- bounded-decide with raised maxRecDepth — plain decide NOT native_decide).
#assert_no_axioms FX1Poly.Core.Generator.toNat_lt
#assert_no_axioms FX1Poly.Core.Generator.fromTag_total_on_range
#assert_no_axioms FX1Poly.Core.fxKernelPolygraph

-- SN-124 (#627): the explicit Generator -> polygraph-generator map. PolygraphGenerator presents each former with
-- its boundary (tag + child arity + child boundary shifts, coherently); toPolygraphGenerator is the presentation
-- map; _injective is FAITHFUL (distinct gens present distinctly, via toNat_injective); _boundary/_tag confirm the
-- presented data IS binderShifts/toNat (rfl); _recoversGenerator is INVERTIBLE (fromTag round-trips the presented
-- tag). The per-generator object SN-125's RawCell->OmegacEWord encoding lifts the dim-1 free monoid over. Zero-axiom
-- (record literal over shipped toNat/arity/binderShifts; rfl projections; congrArg into toNat_injective).
#assert_no_axioms FX1Poly.Core.Generator.toPolygraphGenerator
#assert_no_axioms FX1Poly.Core.Generator.toPolygraphGenerator_injective
#assert_no_axioms FX1Poly.Core.Generator.toPolygraphGenerator_boundary
#assert_no_axioms FX1Poly.Core.Generator.toPolygraphGenerator_tag
#assert_no_axioms FX1Poly.Core.Generator.toPolygraphGenerator_recoversGenerator

-- SN-125 (#628): the dim-1 free-monoid rule-word encoding of the RawCell composite layer — the FX-Conv-to-word
-- bridge START. encodeRuleWord reads off the ordered generating-cell rule ids (the dim-1 REWRITE-rule alphabet,
-- distinct from SN-124's 194 term-formers): objects/identities to the empty word, generatingCell to [ruleId],
-- composites to ++. The per-ctor rules are rfl; _assoc + _identity_left/_right are the MONOID HOMOMORPHISM onto
-- the free monoid (List ++ / [] with assoc + 2-sided unit); length_eq_generatingCellCount is FAITHFULNESS to the
-- rewrite content. Zero-axiom (structural recursion + local propext-free list/Nat lemmas). SN-126 maps each
-- generatingCell to a source-word ⇒ target-word rule on top of this.
#assert_no_axioms FX1Poly.Core.RawCell.encodeRuleWord
#assert_no_axioms FX1Poly.Core.encodeRuleWord_termBase
#assert_no_axioms FX1Poly.Core.encodeRuleWord_generatingCell
#assert_no_axioms FX1Poly.Core.encodeRuleWord_verticalComposite
#assert_no_axioms FX1Poly.Core.encodeRuleWord_horizontalComposite
#assert_no_axioms FX1Poly.Core.encodeRuleWord_identityCell
#assert_no_axioms FX1Poly.Core.encodeRuleWord_assoc
#assert_no_axioms FX1Poly.Core.encodeRuleWord_identity_left
#assert_no_axioms FX1Poly.Core.encodeRuleWord_identity_right
#assert_no_axioms FX1Poly.Core.RawCell.generatingCellCount
#assert_no_axioms FX1Poly.Core.encodeRuleWord_length_eq_generatingCellCount

-- SN-126 (#629): each FX reduction as a rewrite rule over the term-code word monoid. Uses the SHIPPED faithful
-- RawTerm.toCode (head tag + payload + children) as the bridge encode. toCode_mkGen (rfl head-tag rule) +
-- toCode_ne_nil (every code begins with the head tag, so non-degenerate rules). Step.inducedRewriteRule maps a
-- reduction to the rule (redex.toCode, reduct.toCode); projections rfl + both-sides-non-empty. fxStepSystem is
-- the generated rule system (a rule is in it iff it is some reduction's code-pair); inducedRewriteRule_mem proves
-- every Step lands in it by construction -- the fxSystem SN-127's bridge soundness ranges over. Zero-axiom
-- (rfl / cases+cons_ne_nil / existential-intro with rfl witnesses).
#assert_no_axioms FX1Poly.Core.toCode_mkGen
#assert_no_axioms FX1Poly.Core.toCode_ne_nil
#assert_no_axioms FX1Poly.Core.Step.inducedRewriteRule
#assert_no_axioms FX1Poly.Core.Step.inducedRewriteRule_leftHandSide
#assert_no_axioms FX1Poly.Core.Step.inducedRewriteRule_rightHandSide
#assert_no_axioms FX1Poly.Core.Step.inducedRewriteRule_leftHandSide_ne_nil
#assert_no_axioms FX1Poly.Core.Step.inducedRewriteRule_rightHandSide_ne_nil
#assert_no_axioms FX1Poly.Core.fxStepSystem
#assert_no_axioms FX1Poly.Core.Step.inducedRewriteRule_mem_fxStepSystem

-- SN-127 (#630): the FORWARD half of the Leg-3 bridge -- FX reduction embeds into word rewriting over the
-- term-code monoid. FxWordRewritesOneStep is one-step word rewriting (List Nat) under an FxTermRewriteRule system
-- (fire + left/right context closure). Step.toWordRewrite is single-step SOUNDNESS (the fire of the SN-126 system
-- rule -- NOT gated on typed SN, since fxStepSystem holds every instantiated reduction as a top-level rule).
-- FxWordRewritesMany is the refl-trans closure with single/trans + context lifts (a congruence preorder);
-- StepStar.toWordRewrites is many-step SOUNDNESS by induction over the chain. Zero-axiom (Prop inductives +
-- constructor application + structural inductions).
#assert_no_axioms FX1Poly.Core.FxWordRewritesOneStep
#assert_no_axioms FX1Poly.Core.Step.toWordRewrite
#assert_no_axioms FX1Poly.Core.FxWordRewritesMany
#assert_no_axioms FX1Poly.Core.FxWordRewritesMany.single
#assert_no_axioms FX1Poly.Core.FxWordRewritesMany.trans
#assert_no_axioms FX1Poly.Core.FxWordRewritesMany.underLeftContext
#assert_no_axioms FX1Poly.Core.FxWordRewritesMany.underRightContext
#assert_no_axioms FX1Poly.Core.StepStar.toWordRewrites

-- SN-128 (#631): rename/subst-equivariance of the Step->word bridge + system-level inversion. The soundness
-- commutes with the term rename/subst actions (Step.toWordRewrite_rename/_subst, StepStar.toWordRewrites_rename,
-- via the shipped Step.rename/Step.subst/StepStar.rename) and the generated system is closed under both
-- (fxStepSystem_rename_mem/_subst_mem). fxStepSystem_imp_step inverts the system (every rule comes from a Step) +
-- _leftHandSide/_rightHandSide_ne_nil (no degenerate rules). FULL word->Step completeness is BLOCKED (free word
-- monoid + toCode payload-collapse on universe codes), honestly deferred -- not faked. Zero-axiom.
#assert_no_axioms FX1Poly.Core.Step.toWordRewrite_rename
#assert_no_axioms FX1Poly.Core.StepStar.toWordRewrites_rename
#assert_no_axioms FX1Poly.Core.Step.toWordRewrite_subst
#assert_no_axioms FX1Poly.Core.fxStepSystem_rename_mem
#assert_no_axioms FX1Poly.Core.fxStepSystem_subst_mem
#assert_no_axioms FX1Poly.Core.fxStepSystem_imp_step
#assert_no_axioms FX1Poly.Core.fxStepSystem_leftHandSide_ne_nil
#assert_no_axioms FX1Poly.Core.fxStepSystem_rightHandSide_ne_nil

-- SN-129 (#632): Conv -> word-joinability bridge (FORWARD half). Conv is term joinability (StepStar.Join =
-- common reduct); FxWordJoinable is the ConvertibleModulo for the FX term-code word monoid (common word reduct).
-- Conv.toWordJoinable maps both StepStar legs via SN-127's StepStar.toWordRewrites with common = commonTerm.toCode.
-- refl/symm shipped (a reflexive-symmetric relation); trans NOT claimed (needs word confluence SN-132/133).
-- REVERSE blocked by SN-128's word->term completeness gap, honestly deferred. Zero-axiom.
#assert_no_axioms FX1Poly.Core.FxWordJoinable
#assert_no_axioms FX1Poly.Core.FxWordJoinable.refl
#assert_no_axioms FX1Poly.Core.FxWordJoinable.symm
#assert_no_axioms FX1Poly.Core.FxWordJoinable.ofWordRewritesMany
#assert_no_axioms FX1Poly.Core.Conv.toWordJoinable
#assert_no_axioms FX1Poly.Core.Step.toWordJoinable

-- SN-130 (#633): the certified beta/iota/eta word-rewrite system. fxStepSystem (SN-126) was beta/iota only (over
-- Step); eta lives in Step.eta, so this enumerates the FULL system fxBetaEtaStepSystem over Step.betaEta (= Step
-- or Step.eta). Generic membership + single-step soundness (fire) reuse SN-127's generic FxWordRewrites*;
-- fxStepSystem_imp_fxBetaEtaStepSystem embeds the beta/iota system (Or.inl); Step/Step.eta.toBetaEtaWordRewrite
-- certify beta/iota (Or.inl) AND eta (Or.inr) rules -- the eta half is NEW. Step.betaEtaStar.toWordRewrites is the
-- many-step eta-inclusive soundness. Zero-axiom.
#assert_no_axioms FX1Poly.Core.fxBetaEtaStepSystem
#assert_no_axioms FX1Poly.Core.Step.betaEta.inducedRewriteRule
#assert_no_axioms FX1Poly.Core.Step.betaEta.inducedRewriteRule_mem_fxBetaEtaStepSystem
#assert_no_axioms FX1Poly.Core.Step.betaEta.toWordRewrite
#assert_no_axioms FX1Poly.Core.fxStepSystem_imp_fxBetaEtaStepSystem
#assert_no_axioms FX1Poly.Core.Step.toBetaEtaWordRewrite
#assert_no_axioms FX1Poly.Core.Step.eta.toBetaEtaWordRewrite
#assert_no_axioms FX1Poly.Core.Step.betaEtaStar.toWordRewrites

-- SN-116 (#619): the Dershowitz-Manna multiset ordering + its well-foundedness, the foundational termination
-- order (RPO multiset-status SN-115, ι-eliminator termination SN-131). Mechanized zero-axiom over Init only: a
-- true multiset is the quotient of List by permutation, but Quot.sound is banned, so MultisetRedOne is an
-- EXISTENTIAL on plain List (prefix ++ removed :: suffix shrinks to prefix ++ added ++ suffix, added all below
-- removed). isWellFounded is the DM theorem via the nested-Acc argument (emptyAccessible + consAccessible with
-- the accAppendBelow inner helper). Inversion by obtain + cases prefixList (clean List split, no indexed-cases
-- propext leak). replaceHead/underContext make the order constructible. Zero-axiom.
#assert_no_axioms FX1Poly.Core.MultisetRedOne
#assert_no_axioms FX1Poly.Core.MultisetRedOne.replaceHead
#assert_no_axioms FX1Poly.Core.MultisetRedOne.underContext
#assert_no_axioms FX1Poly.Core.MultisetRedOne.emptyAccessible
#assert_no_axioms FX1Poly.Core.MultisetRedOne.consAccessible
#assert_no_axioms FX1Poly.Core.MultisetRedOne.isWellFounded

-- SN-117 (#620): the lexicographic list order + WF (the lex companion to SN-116's multiset order — the comparison
-- LPO uses for arguments, RPO for lex-status symbols) + measure-based termination certificates over BOTH orders.
-- LexListStep is the existential-on-List lex single step (length-matched tails); isWellFounded via length-indexed
-- nested accessibility. wellFounded_of_multisetMeasure/_lexMeasure turn a measure-decrease into WellFounded via
-- InvImage.wf. Zero-axiom: List-existential inversion (cases commonPrefix), defeq length + local length_append,
-- Nat.noConfusion DIRECTLY (absurd+succ_ne_zero leaks propext). The recursive path ordering on FX terms is the
-- downstream SN-131 composition.
#assert_no_axioms FX1Poly.Core.LexListStep
#assert_no_axioms FX1Poly.Core.LexListStep.length_eq
#assert_no_axioms FX1Poly.Core.LexListStep.emptyAccessible
#assert_no_axioms FX1Poly.Core.LexListStep.consAccessible
#assert_no_axioms FX1Poly.Core.LexListStep.accessibleByLength
#assert_no_axioms FX1Poly.Core.LexListStep.isWellFounded
#assert_no_axioms FX1Poly.Core.wellFounded_of_multisetMeasure
#assert_no_axioms FX1Poly.Core.wellFounded_of_lexMeasure

-- Pointwise-saturation of the dependent reducibility relation (the level-free FT's choice-free piIntro
-- keystone): `ReducibleTypeClosed` is closed under pointwise-iff by construction, so it carries the
-- canonical member-predicate candidate that bare `ReducibleType` cannot.  (New file outside the
-- AuditCoreSubstrate sweep's import closure, so gated per-declaration here.)
#assert_no_axioms FX1Poly.Core.ReducibleTypeClosed
#assert_no_axioms FX1Poly.Core.ReducibleType.toClosed
#assert_no_axioms FX1Poly.Core.ReducibleType.closedAtMemberPredicate

-- Equivalence-relation algebra of candidate pointwise-iff (the transport algebra the reducibility
-- model threads through every `ReducibleType.deterministic` candidate transfer, and the pending
-- `ReducibleType.ofPointwiseIff` congruence-closure cascade).
#assert_no_axioms FX1Poly.Core.PointwiseIff.refl
#assert_no_axioms FX1Poly.Core.PointwiseIff.symm
#assert_no_axioms FX1Poly.Core.PointwiseIff.trans

-- Candidate-congruence of the stratified reducibility step-functor under lower-existence-equivalence: the
-- inductive STEP of level-irrelevance (Π case via ofPointwiseIff, universe case via the lower-existence
-- equivalence).  Does NOT bootstrap full irrelevance alone (level-0 degenerate base) — see the module
-- docstring; reusable as the hard core of any future level argument.
#assert_no_axioms FX1Poly.Core.ReducibleTypeStep.existsCongr

-- Fuel-zero boundary witness: unlike universe-code domains, neutral classifiers can genuinely have
-- members at fuel zero, so the dependent-formation telescope's base-level branch cannot be discharged by
-- a generic contradiction.
#assert_no_axioms FX1Poly.Core.IsReducibleMemberAt.variableClassifierHasVariableMemberAtZero

-- Strong-normalization inverse lemmas for dependent type-code children.  These are the subterm
-- accessibility projections needed by structural arguments over reducible Pi/Sigma type values.
#assert_no_axioms FX1Poly.Core.StepStar.domain_isStronglyNormalizing_of_piTyCode
#assert_no_axioms FX1Poly.Core.StepStar.codomain_isStronglyNormalizing_of_piTyCode
#assert_no_axioms FX1Poly.Core.StepStar.domain_isStronglyNormalizing_of_sigmaTyCode
#assert_no_axioms FX1Poly.Core.StepStar.codomain_isStronglyNormalizing_of_sigmaTyCode

-- CR2 / CR3 closure lifted to the semantic-membership layer (the forward-Step, forward-StepStar, and
-- neutral-backward companions of the shipped CR1 membership corollary; the Tait closure bricks the
-- fundamental theorem's neutral and reduction-stable cases consume).
#assert_no_axioms FX1Poly.Core.IsReducibleMemberAt.closedUnderStep
#assert_no_axioms FX1Poly.Core.IsReducibleMemberAt.closedUnderStepStar
#assert_no_axioms FX1Poly.Core.IsReducibleMemberAt.neutralExpansion
