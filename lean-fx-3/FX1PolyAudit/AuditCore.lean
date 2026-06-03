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
import FX1Poly.Core.RecursivePathOrder
import FX1Poly.Core.Newman
import FX1Poly.Core.DiamondConfluence
import FX1Poly.Core.StepParallelConfluence
import FX1Poly.Core.TakahashiTriangle
import FX1Poly.Core.ParallelReduction
import FX1Poly.Core.CompleteDevelopment
import FX1Poly.Core.ParStepSubstRename
import FX1Poly.Core.ParStepSubstPointwise
import FX1Poly.Core.CommutationConfluence
import FX1Poly.Core.DeterministicConfluence
import FX1Poly.Core.KripkeReducibilityCandidate
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

-- SN-115 (#618): the RPO termination certificate -- precedence x argument-order, lexicographically. LexPair is the
-- lex product of two relations as a DISJUNCTION (not the indexed Prod.Lex, whose cases leaks propext via the
-- pair-index); isWellFounded by nested Acc with rcases on the Or. wellFounded_of_precedenceMultisetMeasure /
-- _LexMeasure are the RPO certificates for multiset-status (SN-116) / lex-status (SN-117) symbols: a step
-- terminates if the precedence rank decreases OR stays equal while the argument measure decreases. The full
-- recursive path ordering on FX terms is the downstream SN-131 composition. Zero-axiom (Or-inversion + InvImage.wf).
#assert_no_axioms FX1Poly.Core.LexPair
#assert_no_axioms FX1Poly.Core.LexPair.pairAccessible
#assert_no_axioms FX1Poly.Core.LexPair.isWellFounded
#assert_no_axioms FX1Poly.Core.wellFounded_of_lexPairMeasure
#assert_no_axioms FX1Poly.Core.wellFounded_of_precedenceMultisetMeasure
#assert_no_axioms FX1Poly.Core.wellFounded_of_precedenceLexMeasure

-- SN-046 core (#549): the ABSTRACT Newman's lemma -- terminating + weakly confluent ⟹ confluent -- the
-- confluence analogue of the termination orders, generic over any relation. ReflTransClosure (own RTC, since
-- Relation.ReflTransGen is Mathlib-only) + single/trans; Joinable/WeaklyConfluent/Confluent vocabulary; newmanAux
-- is the WF-induction tiling (WCR on the two first steps, IH at each reduct, compose); newman is the headline.
-- The confluence arc instantiates this: SN-046 typed fragment, SN-133 fxSystem (both gated on typed SN). Zero-axiom
-- (cases on RTC is propext-clean since its indices are free vars, not ctor patterns).
#assert_no_axioms FX1Poly.Core.ReflTransClosure
#assert_no_axioms FX1Poly.Core.ReflTransClosure.single
#assert_no_axioms FX1Poly.Core.ReflTransClosure.trans
#assert_no_axioms FX1Poly.Core.Joinable
#assert_no_axioms FX1Poly.Core.WeaklyConfluent
#assert_no_axioms FX1Poly.Core.Confluent
#assert_no_axioms FX1Poly.Core.newmanAux
#assert_no_axioms FX1Poly.Core.newman

-- M8-S1 core (#420): the diamond ⟹ confluence route (strip lemma), the SECOND abstract confluence path
-- complementing Newman -- confluence from the DIAMOND property alone, no termination. ReflTransClosure.monotone/
-- collapse (the sandwich glue) + DiamondProperty + stripLemma (single strips against many) + diamondConfluence +
-- confluentOfDiamondSimulation (the parallel-reduction recipe: rel ⊆ parRel ⊆ RTC rel + parRel diamond ⟹ rel
-- confluent -- how single-step β, which lacks the diamond, is proved confluent via parallel reduction). The
-- generic core of #420 parStar.confluence. NOTE the shipped cd_lemma (#256) is LOCAL confluence (feeds Newman /
-- the strip property), NOT this parallel diamond; the diamond needs a concrete FX parallel reduction (deferred).
-- Zero-axiom.
#assert_no_axioms FX1Poly.Core.ReflTransClosure.monotone
#assert_no_axioms FX1Poly.Core.ReflTransClosure.collapse
#assert_no_axioms FX1Poly.Core.DiamondProperty
#assert_no_axioms FX1Poly.Core.stripLemma
#assert_no_axioms FX1Poly.Core.diamondConfluenceAux
#assert_no_axioms FX1Poly.Core.diamondConfluence
#assert_no_axioms FX1Poly.Core.confluentOfDiamondSimulation

-- M8-S1 FX-layer wiring (#420): connects the abstract diamond/strip confluence to the concrete raw `StepStar`.
-- StepStar ≅ ReflTransClosure Step (toReflTransClosure / ofReflTransClosure), then hasConfluence_of_parallelDiamond
-- (route A via confluentOfDiamondSimulation) and hasStrip_of_parallelDiamond (route B via stripLemma, realizing
-- StepStarConfluence's `confluence_of_strip`). A sandwiched parallel relation (Step ⊆ ParStep ⊆ StepStar) with the
-- diamond yields raw global confluence; the concrete FX parallel reduction + its diamond is the deferred content.
#assert_no_axioms FX1Poly.Core.StepStar.toReflTransClosure
#assert_no_axioms FX1Poly.Core.StepStar.ofReflTransClosure
#assert_no_axioms FX1Poly.Core.StepStar.hasConfluence_of_parallelDiamond
#assert_no_axioms FX1Poly.Core.StepStar.hasStrip_of_parallelDiamond

-- Takahashi triangle lemma (toward #420): the linear route to the parallel-reduction diamond. A
-- completeDevelopment function with the TriangleProperty (every reduct steps to the source's complete
-- development) yields DiamondProperty.ofTriangle and Confluent.ofTriangle, reducing the deferred parallel
-- diamond above from a quadratic redex-pair join to the single linear "exhibit completeDevelopment + its
-- triangle" obligation (Takahashi 1995). Composes with diamondConfluence + hasConfluence_of_parallelDiamond.
#assert_no_axioms FX1Poly.Core.DiamondProperty.ofTriangle
#assert_no_axioms FX1Poly.Core.Confluent.ofTriangle
-- The existential per-source form (HasMaximalReduct): generalizes the function-based TriangleProperty
-- (HasMaximalReduct.ofTriangle) and is the form the concrete FX parallel reduction discharges by structural
-- recursion on the source (no separately-defined total completeDevelopment function over RawTerm needed).
-- ofMaximalReduct yields the diamond; Confluent.ofMaximalReduct composes with diamondConfluence.
#assert_no_axioms FX1Poly.Core.HasMaximalReduct.ofTriangle
#assert_no_axioms FX1Poly.Core.DiamondProperty.ofMaximalReduct
#assert_no_axioms FX1Poly.Core.Confluent.ofMaximalReduct

-- The concrete FX parallel reduction (toward #420): ParStep contracts any set of redexes simultaneously
-- (Takahashi), mirroring all 18 Step rules with parallel sub-reduction of the surviving sub-terms; the pointwise
-- ParStepChildren reduces every child at once. ParStep.refl / ParStepChildren.refl give reflexivity by mutual
-- structural recursion (term-mode match, no termination_by — avoids the v4.29.1 WF substitution gap). This is the
-- relation that will discharge HasMaximalReduct -> the diamond -> raw confluence (the prize SN cannot supply).
#assert_no_axioms FX1Poly.Core.ParStep.refl
#assert_no_axioms FX1Poly.Core.ParStepChildren.refl
-- Step subset ParStep (the lower sandwich bound = stepToPar for hasConfluence_of_parallelDiamond): every single
-- reduction is a parallel reduction firing only that redex, surviving sub-terms reflexive; cong maps the
-- single-child StepChildren to a pointwise ParStepChildren. Mutual term-mode structural recursion on the
-- derivation. One of the two arguments the raw-confluence adapter needs; the upper bound ParStep subset StepStar
-- is the next increment.
#assert_no_axioms FX1Poly.Core.Step.toParStep
#assert_no_axioms FX1Poly.Core.StepChildren.toParStepChildren
-- ParStep subset StepStar (the upper sandwich bound = parToStepStar): every parallel reduction is a finite
-- sequence of single steps. Each arm reduces the redex's surviving sub-terms via StepStar.ofChildrenStar (the
-- child-spine congruence lifter) then fires the matching root Step; cong lifts the pointwise ParStepChildren
-- through ofChildrenStar. With Step.toParStep above, this COMPLETES the sandwich Step subset ParStep subset
-- StepStar that StepStar.hasConfluence_of_parallelDiamond needs -- only the ParStep DiamondProperty (via
-- HasMaximalReduct) remains for unconditional raw confluence.
#assert_no_axioms FX1Poly.Core.ParStep.toStepStar
#assert_no_axioms FX1Poly.Core.ParStepChildren.toStepChildrenStar

-- Takahashi complete development (the maximal-reduct witness toward #420): contract every redex present
-- at once but NOT the redexes created by contraction. Propext-clean because the ~18-redex-shape detection is
-- delegated to the already-clean fireRootRedex (a direct overlapping-nested-pattern match leaks propext and
-- defeats the equation compiler); completeDevelopment itself does only flat mkGen / childNil-childCons matches.
-- completeDevelopment_stepStar = the soundness half (the development is reachable by StepStar): develop the
-- children via ofChildrenStar, then fire the root via fireRootRedex_sound. This is the function the eventual
-- HasMaximalReduct ParStep (triangle) proof maximizes against -> the ParStep diamond -> raw confluence.
#assert_no_axioms FX1Poly.Core.RawTerm.fireRootRedexOrSelf
-- fireRootRedexOrSelfGated: fire on developed children only when the ORIGINAL children form a syntactic
-- redex. This GATE makes completeDevelopment the standard (non-over-firing) Takahashi development: firing
-- on developed children alone would contract redexes CREATED by developing (an inner redex whose
-- contractum is a lam turns a non-lam-headed app into a beta-redex), breaking the triangle's ParStep a (cd a).
#assert_no_axioms FX1Poly.Core.RawTerm.fireRootRedexOrSelfGated
#assert_no_axioms FX1Poly.Core.RawTerm.completeDevelopment
#assert_no_axioms FX1Poly.Core.RawTerm.completeDevelopmentChildren
#assert_no_axioms FX1Poly.Core.RawTerm.fireRootRedexOrSelf_stepStar
#assert_no_axioms FX1Poly.Core.RawTerm.fireRootRedexOrSelfGated_stepStar
#assert_no_axioms FX1Poly.Core.RawTerm.completeDevelopment_stepStar
#assert_no_axioms FX1Poly.Core.RawTerm.completeDevelopmentChildren_stepChildrenStar
-- cd_app_lam_eq: the gated beta-redex develops to subst0 of the developed components, by rfl -- the exact
-- equation the Takahashi triangle's beta arm needs, witnessing triangle-readiness of the gated development.
#assert_no_axioms FX1Poly.Core.cd_app_lam_eq

-- ParStep stable under substitution + renaming (toward the #420 triangle): the parallel-substitution
-- lemma the triangle ParStep a b -> ParStep b (completeDevelopment a) needs at its beta/iota arms is built
-- on these. ParStep.subst mirrors Step.subst's recursor idiom (all-substitutions motive; beta via
-- subst0_subst_commute, cong via the gen_var split, every iota arm applies its premises' IHs at sigma,
-- the spine lifts sigma by the child binder shift). ParStep.rename is the corollary via the Step.rename
-- rename->subst trick. These are the renaming/substitution substrate the binder case of the eventual
-- parallel substitution lemma requires.
#assert_no_axioms FX1Poly.Core.ParStep.subst
#assert_no_axioms FX1Poly.Core.ParStepChildren.subst
#assert_no_axioms FX1Poly.Core.ParStep.rename
#assert_no_axioms FX1Poly.Core.ParStepChildren.rename

-- Parallel substitution lemma (the #420 triangle's beta/iota engine): substituting a parallel-reduced
-- argument into a parallel-reduced body parallel-reduces. ParStep is a single parallel step (not
-- transitive), so the diagonal cannot be composed from two one-sided ParStep.subst applications -- it
-- needs the combined induction varying BOTH the substitution (sigma => tau, related by PointwiseParStep,
-- lifted under binders by ParStep.weaken) AND the term. ParStep.subst0_diagonal instantiates substPointwise
-- at the two singleton substitutions; this is what the triangle's beta arm fires with (and the recursive
-- iota arms whose contractums embed subst0 of developed components).
#assert_no_axioms FX1Poly.Core.ParStep.weaken
#assert_no_axioms FX1Poly.Core.RawTermSubst.lift_pointwiseParStep
#assert_no_axioms FX1Poly.Core.iterateLiftRaw_RawTermSubst_pointwiseParStep
#assert_no_axioms FX1Poly.Core.ParStep.substPointwise
#assert_no_axioms FX1Poly.Core.RawTermSubst.singleton_pointwiseParStep
#assert_no_axioms FX1Poly.Core.ParStep.subst0_diagonal

-- Hindley-Rosen via the diamond (abstract toolkit): the THIRD confluence route after Newman (terminating)
-- and DiamondConfluence (single diamond). Modular -- combines two separately-confluent relations whose
-- diamonds COMMUTE into a confluent union (the intended FX use: beta-parallel diamond + iota-parallel
-- diamond + beta/iota commute, without one monolithic 20-arm ParStep). StronglyCommutes + DiamondProperty.union
-- (4-way case split) + confluentOfUnionDiamonds + confluentUnionOfParallelDiamonds (2-relation generalization
-- of confluentOfDiamondSimulation). Zero-axiom.
#assert_no_axioms FX1Poly.Core.StronglyCommutes
#assert_no_axioms FX1Poly.Core.DiamondProperty.union
#assert_no_axioms FX1Poly.Core.confluentOfUnionDiamonds
#assert_no_axioms FX1Poly.Core.confluentUnionOfParallelDiamonds

-- Deterministic confluence (abstract toolkit, FOURTH route): a deterministic (functional) relation is confluent
-- -- its reflexive-transitive reducts from a common source are linearly ordered. Determinism does NOT give the
-- strict diamond (a normal form breaks it), so this is its own linear-chain induction. The route for
-- deterministic reduction strategies (weak-head here, the deterministic NbE evaluator M12 downstream).
-- IsDeterministic + confluentOfDeterministic + the concrete WeakHeadStep.hasConfluence (weak-head reduction is
-- Church-Rosser, from WeakHeadStep.deterministic). Zero-axiom.
#assert_no_axioms FX1Poly.Core.IsDeterministic
#assert_no_axioms FX1Poly.Core.confluentOfDeterministicAux
#assert_no_axioms FX1Poly.Core.confluentOfDeterministic
#assert_no_axioms FX1Poly.Core.WeakHeadStep.hasConfluence

-- SN-040, HONEST unconditional Kripke form: a reducibility candidate is closed under renaming. The bare
-- ReducibleTypeStep SN-040 is FALSE (the piType same-scope argument quantifier has a real counterexample at a
-- renamed Pi-type). The TRUE statement lives at the Kripke-indexed candidate: IsKripkeReducibilityCandidate
-- (CR1 members-SN + CR2 closed-under-Step) survives KripkeCand.transport along ANY renaming with NO hypothesis
-- (the index precomposes; laws read off at the composed index). Predicate-level companion is the shipped
-- kripkeArrowDep_transport_pointwise. Off the SN-043 critical path (that gate is fuel-stability, not renaming).
#assert_no_axioms FX1Poly.Core.IsKripkeReducibilityCandidate
#assert_no_axioms FX1Poly.Core.IsKripkeReducibilityCandidate.transport

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
