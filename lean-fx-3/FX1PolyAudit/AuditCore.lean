import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.CellSort
import FX1Poly.Typed.HasType
import FX1Poly.Core.GeneratorTagRoundTrip
import FX1Poly.Core.GeneratorFinitePolygraph
import FX1Poly.Core.GeneratorPolygraphMap
import FX1Poly.Core.RawCellWordEncoding
import FX1Poly.Core.StepRewriteRuleMap
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
