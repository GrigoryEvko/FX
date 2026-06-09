import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.CellSort
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
import FX1Poly.Core.RecursiveEliminatorTermination
import FX1Poly.Core.IotaNonRecursiveTermination
import FX1Poly.Core.RecursiveIotaSizeGrowth
import FX1Poly.Core.RecursivePathOrderInductive
import FX1Poly.Core.RawIotaRpoBridge
import FX1Poly.Core.RawIotaRpoAssembly
import FX1Poly.Core.RawIotaFullStepSN
import FX1Poly.Core.EraseToRoseRenameInvariant
import FX1Poly.Core.Newman
import FX1Poly.Core.DiamondConfluence
import FX1Poly.Core.StepParallelConfluence
import FX1Poly.Core.TakahashiTriangle
import FX1Poly.Core.ParallelReduction
import FX1Poly.Core.CompleteDevelopment
import FX1Poly.Core.ParStepSubstRename
import FX1Poly.Core.ParStepSubstPointwise
import FX1Poly.Core.ParStepInversion
import FX1Poly.Core.CompleteDevelopmentParStep
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

/-! # FX1PolyAudit/AuditCore — zero-axiom gate for the cell-calculus core

Persistent per-declaration `#assert_no_axioms` gate for the FX1Poly
cell substrate.

`CellSort` — the seven-sort vocabulary
(context / type / term / mode / effect / grade / protocol) over which
every PolyCell morphism (the dim-1 `FXStep sort` cells) ranges.  This
is the spine of the "morphisms on terms, types, contexts, grades"
design: a 1-cell is `PolyCell fxProfile sort 1 …` for any `sort`, so
the sort vocabulary is the foundational brick.

The native typing discipline — `HasTypeDesc` (formation) and
`HasTypeDescPi` (grown) — classifies cells by cells: a `.term` subject by
a `.type` classifier over `CellSort`, with no MLTT `Foundation.Ty`
classifier.  Those engines are audit-gated in `AuditTyped.lean`.
-/

#assert_no_axioms FX1Poly.Core.CellSort
#assert_no_axioms FX1Poly.Core.CellSort.all
#assert_no_axioms FX1Poly.Core.CellSort.toCode
#assert_no_axioms FX1Poly.Core.CellSort.ofCode?
#assert_no_axioms FX1Poly.Core.CellSort.ofCode?_toCode
#assert_no_axioms FX1Poly.Core.CellSort.all_length


-- §11.6.4 Generator-table validation: the FX0 prefix-code tag assignment
-- `Generator.toNat` is collision-free (injective), proved via the explicit left
-- inverse `Generator.fromTag` and its per-constructor round-trip.  The head byte
-- of the cell serialization therefore uniquely identifies the generator.
#assert_no_axioms FX1Poly.Core.Generator.fromTag
#assert_no_axioms FX1Poly.Core.Generator.fromTag_toNat
#assert_no_axioms FX1Poly.Core.Generator.toNat_injective

-- The FX kernel as a finite polygraph over the 197-Generator table.  The generators are indexed injectively
-- (toNat_injective) and boundedly (toNat_lt) into Fin 197, with the total inverse table fromTag (round-trip
-- fromTag_toNat + range-totality fromTag_total_on_range); each carries its dimension (arity) and boundary
-- (binderShifts), coherently (binderShifts_length_eq_arity).  fxKernelPolygraph bundles all of it.  Zero-axiom
-- via cases + bounded decide with raised maxRecDepth (plain decide, not native_decide).
#assert_no_axioms FX1Poly.Core.Generator.toNat_lt
#assert_no_axioms FX1Poly.Core.Generator.fromTag_total_on_range
#assert_no_axioms FX1Poly.Core.fxKernelPolygraph

-- The explicit Generator-to-polygraph-generator map.  PolygraphGenerator presents each former with its
-- boundary (tag + child arity + child boundary shifts, coherently); toPolygraphGenerator is the presentation
-- map; _injective is faithful (distinct generators present distinctly, via toNat_injective); _boundary/_tag
-- confirm the presented data is binderShifts/toNat (rfl); _recoversGenerator is invertible (fromTag
-- round-trips the presented tag).  Zero-axiom: record literal over toNat/arity/binderShifts; rfl projections;
-- congrArg into toNat_injective.
#assert_no_axioms FX1Poly.Core.Generator.toPolygraphGenerator
#assert_no_axioms FX1Poly.Core.Generator.toPolygraphGenerator_injective
#assert_no_axioms FX1Poly.Core.Generator.toPolygraphGenerator_boundary
#assert_no_axioms FX1Poly.Core.Generator.toPolygraphGenerator_tag
#assert_no_axioms FX1Poly.Core.Generator.toPolygraphGenerator_recoversGenerator

-- The dim-1 free-monoid rule-word encoding of the RawCell composite layer, the start of the FX-Conv-to-word
-- bridge.  encodeRuleWord reads off the ordered generating-cell rule ids (the dim-1 rewrite-rule alphabet,
-- distinct from the term-formers): objects/identities to the empty word, generatingCell to [ruleId],
-- composites to ++.  The per-constructor rules are rfl; _assoc + _identity_left/_right are the monoid
-- homomorphism onto the free monoid (List ++ / [] with assoc + two-sided unit); length_eq_generatingCellCount
-- is faithfulness to the rewrite content.  Zero-axiom: structural recursion + local propext-free list/Nat lemmas.
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

-- Each FX reduction as a rewrite rule over the term-code word monoid.  Uses the faithful RawTerm.toCode
-- (head tag + payload + children) as the bridge encode.  toCode_mkGen (rfl head-tag rule) + toCode_ne_nil
-- (every code begins with the head tag, so non-degenerate rules).  Step.inducedRewriteRule maps a reduction to
-- the rule (redex.toCode, reduct.toCode); projections rfl + both-sides-non-empty.  fxStepSystem is the
-- generated rule system (a rule is in it iff it is some reduction's code-pair); inducedRewriteRule_mem proves
-- every Step lands in it by construction.  Zero-axiom: rfl / cases + cons_ne_nil / existential-intro with rfl
-- witnesses.
#assert_no_axioms FX1Poly.Core.toCode_mkGen
#assert_no_axioms FX1Poly.Core.toCode_ne_nil
#assert_no_axioms FX1Poly.Core.Step.inducedRewriteRule
#assert_no_axioms FX1Poly.Core.Step.inducedRewriteRule_leftHandSide
#assert_no_axioms FX1Poly.Core.Step.inducedRewriteRule_rightHandSide
#assert_no_axioms FX1Poly.Core.Step.inducedRewriteRule_leftHandSide_ne_nil
#assert_no_axioms FX1Poly.Core.Step.inducedRewriteRule_rightHandSide_ne_nil
#assert_no_axioms FX1Poly.Core.fxStepSystem
#assert_no_axioms FX1Poly.Core.Step.inducedRewriteRule_mem_fxStepSystem

-- The forward half of the term-code-word bridge: FX reduction embeds into word rewriting over the
-- term-code monoid.  FxWordRewritesOneStep is one-step word rewriting (List Nat) under an FxTermRewriteRule
-- system (fire + left/right context closure).  Step.toWordRewrite is single-step soundness (the fire of the
-- system rule, with no typed-SN side condition since fxStepSystem holds every instantiated reduction as a
-- top-level rule).  FxWordRewritesMany is the refl-trans closure with single/trans + context lifts (a
-- congruence preorder); StepStar.toWordRewrites is many-step soundness by induction over the chain.
-- Zero-axiom: Prop inductives + constructor application + structural inductions.
#assert_no_axioms FX1Poly.Core.FxWordRewritesOneStep
#assert_no_axioms FX1Poly.Core.Step.toWordRewrite
#assert_no_axioms FX1Poly.Core.FxWordRewritesMany
#assert_no_axioms FX1Poly.Core.FxWordRewritesMany.single
#assert_no_axioms FX1Poly.Core.FxWordRewritesMany.trans
#assert_no_axioms FX1Poly.Core.FxWordRewritesMany.underLeftContext
#assert_no_axioms FX1Poly.Core.FxWordRewritesMany.underRightContext
#assert_no_axioms FX1Poly.Core.StepStar.toWordRewrites

-- Rename/subst-equivariance of the Step-to-word bridge + system-level inversion.  The soundness commutes
-- with the term rename/subst actions (Step.toWordRewrite_rename/_subst, StepStar.toWordRewrites_rename, via
-- Step.rename/Step.subst/StepStar.rename) and the generated system is closed under both
-- (fxStepSystem_rename_mem/_subst_mem).  fxStepSystem_imp_step inverts the system (every rule comes from a
-- Step) + _leftHandSide/_rightHandSide_ne_nil (no degenerate rules).  The reverse word-to-Step direction is
-- not part of this gate (the free word monoid and toCode payload-collapse on universe codes make full
-- completeness non-derivable here).  Zero-axiom.
#assert_no_axioms FX1Poly.Core.Step.toWordRewrite_rename
#assert_no_axioms FX1Poly.Core.StepStar.toWordRewrites_rename
#assert_no_axioms FX1Poly.Core.Step.toWordRewrite_subst
#assert_no_axioms FX1Poly.Core.fxStepSystem_rename_mem
#assert_no_axioms FX1Poly.Core.fxStepSystem_subst_mem
#assert_no_axioms FX1Poly.Core.fxStepSystem_imp_step
#assert_no_axioms FX1Poly.Core.fxStepSystem_leftHandSide_ne_nil
#assert_no_axioms FX1Poly.Core.fxStepSystem_rightHandSide_ne_nil

-- The Conv-to-word-joinability bridge (forward half).  Conv is term joinability (StepStar.Join = common
-- reduct); FxWordJoinable is the ConvertibleModulo for the FX term-code word monoid (common word reduct).
-- Conv.toWordJoinable maps both StepStar legs via StepStar.toWordRewrites with common = commonTerm.toCode.
-- refl/symm establish a reflexive-symmetric relation; this gate does not include trans (which needs word
-- confluence) or the reverse direction (the word-to-term completeness gap).  Zero-axiom.
#assert_no_axioms FX1Poly.Core.FxWordJoinable
#assert_no_axioms FX1Poly.Core.FxWordJoinable.refl
#assert_no_axioms FX1Poly.Core.FxWordJoinable.symm
#assert_no_axioms FX1Poly.Core.FxWordJoinable.ofWordRewritesMany
#assert_no_axioms FX1Poly.Core.Conv.toWordJoinable
#assert_no_axioms FX1Poly.Core.Step.toWordJoinable

-- The certified beta/iota/eta word-rewrite system.  fxStepSystem covers beta/iota (over Step); eta lives in
-- Step.eta, so fxBetaEtaStepSystem enumerates the full system over Step.betaEta (= Step or Step.eta).  Generic
-- membership + single-step soundness (fire) reuse the generic FxWordRewrites*; fxStepSystem_imp_fxBetaEtaStepSystem
-- embeds the beta/iota system (Or.inl); Step/Step.eta.toBetaEtaWordRewrite certify beta/iota (Or.inl) and eta
-- (Or.inr) rules.  Step.betaEtaStar.toWordRewrites is the many-step eta-inclusive soundness.  Zero-axiom.
#assert_no_axioms FX1Poly.Core.fxBetaEtaStepSystem
#assert_no_axioms FX1Poly.Core.Step.betaEta.inducedRewriteRule
#assert_no_axioms FX1Poly.Core.Step.betaEta.inducedRewriteRule_mem_fxBetaEtaStepSystem
#assert_no_axioms FX1Poly.Core.Step.betaEta.toWordRewrite
#assert_no_axioms FX1Poly.Core.fxStepSystem_imp_fxBetaEtaStepSystem
#assert_no_axioms FX1Poly.Core.Step.toBetaEtaWordRewrite
#assert_no_axioms FX1Poly.Core.Step.eta.toBetaEtaWordRewrite
#assert_no_axioms FX1Poly.Core.Step.betaEtaStar.toWordRewrites

-- The Dershowitz-Manna multiset ordering + its well-foundedness, the foundational termination order.
-- Mechanized zero-axiom over Init only: a true multiset is the quotient of List by permutation, but Quot.sound
-- is banned, so MultisetRedOne is an existential on plain List (prefix ++ removed :: suffix shrinks to
-- prefix ++ added ++ suffix, added all below removed).  isWellFounded is the Dershowitz-Manna theorem via the
-- nested-Acc argument (emptyAccessible + consAccessible with the accAppendBelow inner helper).  Inversion by
-- obtain + cases prefixList (clean List split, no indexed-cases propext leak).  replaceHead/underContext make
-- the order constructible.  Zero-axiom.
#assert_no_axioms FX1Poly.Core.MultisetRedOne
#assert_no_axioms FX1Poly.Core.MultisetRedOne.replaceHead
#assert_no_axioms FX1Poly.Core.MultisetRedOne.underContext
#assert_no_axioms FX1Poly.Core.MultisetRedOne.emptyAccessible
#assert_no_axioms FX1Poly.Core.MultisetRedOne.consAccessible
#assert_no_axioms FX1Poly.Core.MultisetRedOne.isWellFounded

-- The lexicographic list order + well-foundedness (the lex companion to the multiset order, the comparison
-- LPO uses for arguments and RPO for lex-status symbols) + measure-based termination certificates over both
-- orders.  LexListStep is the existential-on-List lex single step (length-matched tails); isWellFounded via
-- length-indexed nested accessibility.  wellFounded_of_multisetMeasure/_lexMeasure turn a measure-decrease
-- into WellFounded via InvImage.wf.  Zero-axiom: List-existential inversion (cases commonPrefix), defeq length
-- + local length_append, Nat.noConfusion directly (absurd + succ_ne_zero leaks propext).
#assert_no_axioms FX1Poly.Core.LexListStep
#assert_no_axioms FX1Poly.Core.LexListStep.length_eq
#assert_no_axioms FX1Poly.Core.LexListStep.emptyAccessible
#assert_no_axioms FX1Poly.Core.LexListStep.consAccessible
#assert_no_axioms FX1Poly.Core.LexListStep.accessibleByLength
#assert_no_axioms FX1Poly.Core.LexListStep.isWellFounded
#assert_no_axioms FX1Poly.Core.wellFounded_of_multisetMeasure
#assert_no_axioms FX1Poly.Core.wellFounded_of_lexMeasure

-- The RPO termination certificate: precedence times argument-order, lexicographically.  LexPair is the lex
-- product of two relations as a disjunction (not the indexed Prod.Lex, whose cases leaks propext via the
-- pair-index); isWellFounded by nested Acc with rcases on the Or.  wellFounded_of_precedenceMultisetMeasure /
-- _LexMeasure are the RPO certificates for multiset-status / lex-status symbols: a step terminates if the
-- precedence rank decreases or stays equal while the argument measure decreases.  Zero-axiom: Or-inversion +
-- InvImage.wf.
#assert_no_axioms FX1Poly.Core.LexPair
#assert_no_axioms FX1Poly.Core.LexPair.pairAccessible
#assert_no_axioms FX1Poly.Core.LexPair.isWellFounded
#assert_no_axioms FX1Poly.Core.wellFounded_of_lexPairMeasure
#assert_no_axioms FX1Poly.Core.wellFounded_of_precedenceMultisetMeasure
#assert_no_axioms FX1Poly.Core.wellFounded_of_precedenceLexMeasure
-- ★ #1139 SPIKE: the RECURSIVE-eliminator ι-pattern terminates via the shipped multiset RPO certificate,
-- INDEPENDENT of β and typed-SN (the Leg-3 "β-imported boundary"). The fxSystem termination (SN-131) imports
-- typed-SN because it encodes β (raw β is non-terminating, SN-NECESSITY); η-SN is shipped; the open ι piece
-- splits — non-recursive ι is size-decreasing, the RECURSIVE eliminator (natElim-succ DUPLICATES the recursive
-- call on a SMALLER scrutinee) needs the multiset (Dershowitz-Manna) RPO. This models that hard core: ElimStep
-- elim(k+1) ↝ branch(elim k, elim k), terminated by recScrutineeMultiset over Nat.lt via
-- wellFounded_of_precedenceMultisetMeasure — NO β, NO Tait. listAppendAssoc is propext-free (List.append_assoc
-- DEPENDS ON propext). De-risking model; the real Step ι-arms over RawTerm are the multi-firing follow-on.
#assert_no_axioms FX1Poly.Core.listAppendAssoc
#assert_no_axioms FX1Poly.Core.MultisetRedOne.appendRight
#assert_no_axioms FX1Poly.Core.MultisetRedOne.appendLeft
#assert_no_axioms FX1Poly.Core.elimStep_decreasesMultiset
#assert_no_axioms FX1Poly.Core.recursiveEliminatorTerminates
#assert_no_axioms FX1Poly.Core.recursiveEliminatorTerminates.smoke
-- ★ #1139 (Leg 3): the NON-recursive ι fragment over the REAL kernel terminates by RawTerm.size,
-- INDEPENDENT of β and typed-SN. The 13 non-recursive ι arms (branch-selection bool/nat/list/option-none,
-- fst/snd projection, idJ/idStrictRec base, optionSome/eitherInl/eitherInr applied-branch) strictly
-- decrease size; toStep ties the fragment to the live Step relation (NOT a toy like the recursive RecTerm
-- model); SN via Subrelation.wf + InvImage.wf RawTerm.size — the EXACT shape of the shipped η-SN. The 3
-- recursive arms (RecursiveEliminatorTermination above) and η-SN (Step.etaStar) complete Leg-3 ι/η; the β
-- boundary stays honestly Tait-imported. AC-normalization is explicit Nat.add_right_comm (simp-AC + ac_rfl
-- both leak propext).
#assert_no_axioms FX1Poly.Core.IotaNonRecursiveStep.toStep
#assert_no_axioms FX1Poly.Core.IotaNonRecursiveStep.size_decreases
#assert_no_axioms FX1Poly.Core.iotaNonRecursiveStep_wellFounded
#assert_no_axioms FX1Poly.Core.IotaNonRecursiveStep.isStronglyNormalizing
#assert_no_axioms FX1Poly.Core.IotaNonRecursiveStep.isStronglyNormalizing.smoke
-- ★ #1139 (Leg 3) contrast: the RECURSIVE ι arm natElimSucc INCREASES RawTerm.size by branchSize + 5
-- (grows with the branch) over the REAL kernel, because it DUPLICATES the arbitrary branch s. So the
-- firing-67 size route (IotaNonRecursiveStep.size_decreases) does NOT extend to the recursive arms, and
-- NO flat measure dominated by size survives branch-duplication. Honest correction: firing-66's RecTerm
-- model duplicated only the recursive CALL (flat scrutinee-multiset sufficed); the real arm duplicates an
-- independent branch eliminator of arbitrary size. The resolution is a full recursive RPO (precedence
-- eliminator > app); the shipped single-level lex/multiset certificates do not recurse into subterms, so
-- they are insufficient for the congruence-closed recursive ι (the named multi-firing build). β stays
-- Tait-imported (SN-NECESSITY #950).
#assert_no_axioms FX1Poly.Core.natElimSucc_isRealStep
#assert_no_axioms FX1Poly.Core.natElimSuccReduct_size_eq
#assert_no_axioms FX1Poly.Core.natElimSucc_size_increases
#assert_no_axioms FX1Poly.Core.natElimSucc_size_increase_at_least_branch

-- The genuine INDUCTIVE recursive path order (firing-69): the generic rose-tree RPO with multiset status,
-- positivity-accepted (subterm clause split into subtermEq/subtermStrict to avoid the kernel's nested-Or
-- rejection; multiset witnesses inlined to avoid passing the inductive to the external MultisetRedOne).
-- rpo_orients_natElim ORIENTS the firing-68 obstruction arm — redex ≻ reduct for natElim(succ n) z s with
-- an ARBITRARY duplicated branch s — exactly what every flat measure failed (firing-68); the subterm
-- property tames the duplication. fxPrecedence_wellFounded is the first WF ingredient. The full RPO
-- well-foundedness (Nipkow/Buchholz nested accessibility, fed by MultisetRedOne.consAccessible) is the
-- named multi-firing crux.
#assert_no_axioms FX1Poly.Core.RpoInductive.rpo_orients_natElim
#assert_no_axioms FX1Poly.Core.RpoInductive.fxPrecedence_wellFounded

-- RPO well-foundedness (firing-70): the Nipkow/Buchholz nested-accessibility theorem, zero-axiom and with
-- NO size measure. acc_node uses the rose-tree recursor twice (top-level wrapper + the predecessor's
-- predAcc, which supplies the precedence/multiset cases their children accessible — breaking the apparent
-- circularity); the four-clause Rpo inversion via `cases` is propext-clean. rpoWellFounded :
-- WellFounded prec → WellFounded (RpoBelow prec); fxRpoWellFounded instantiates it at fxPrecedence, so the
-- firing-68 obstruction arm (oriented by rpo_orients_natElim) sits in a genuine well-founded order.
#assert_no_axioms FX1Poly.Core.RpoInductive.rpoWellFounded
#assert_no_axioms FX1Poly.Core.RpoInductive.fxRpoWellFounded

-- RPO congruence (firing-72): the order is a CONGRUENCE — replacing one child by an RPO-smaller child makes
-- the node RPO-smaller (via the multiset clause: a single Dershowitz-Manna decrease, unchanged children
-- dominated as subterms, the replacement dominated through the larger child). This is the monotonicity /
-- compatibility-with-contexts that turns the root-redex order into a genuine REWRITE order — the load-bearing
-- ingredient that lifts a child-context ι step to a node-level RPO decrease. The four List append/membership
-- helpers it consumes are propext-clean re-proofs (Init's List.append_assoc and friends leak propext).
#assert_no_axioms FX1Poly.Core.RpoInductive.rpo_congruence
#assert_no_axioms FX1Poly.Core.RpoInductive.rpo_congruence_head

-- RawTerm RPO bridge (firing-71): the generic rose-tree RPO instantiated at the REAL kernel. eraseToRose
-- forgets RawTerm's scope/binder-shift structure to a RoseTerm Generator; realGenPrecedence ranks the three
-- recursive eliminators above gen_app. The three recursive ι arms (Step.iotaNatElimSucc / iotaNatRecSucc /
-- iotaListElimCons — the firing-68 obstruction that defeats every flat measure) have their erased redex
-- RPO-dominate their erased reduct, and realGenRpoWellFounded gives the order is well-founded — the complete
-- termination certificate for those arms on the real kernel. The <arm>Raw_isStep witnesses confirm the
-- redex/reduct pairs really are the live Step constructors. β stays Tait-imported (raw β non-SN, #950).
#assert_no_axioms FX1Poly.Core.RawIotaRpo.natElimSuccRaw_isStep
#assert_no_axioms FX1Poly.Core.RawIotaRpo.natRecSuccRaw_isStep
#assert_no_axioms FX1Poly.Core.RawIotaRpo.listElimConsRaw_isStep
#assert_no_axioms FX1Poly.Core.RawIotaRpo.rpo_orients_iotaNatElimSucc
#assert_no_axioms FX1Poly.Core.RawIotaRpo.rpo_orients_iotaNatRecSucc
#assert_no_axioms FX1Poly.Core.RawIotaRpo.rpo_orients_iotaListElimCons
#assert_no_axioms FX1Poly.Core.RawIotaRpo.realGenRpoWellFounded

-- Full root-ι SN assembly (firing-73): unify firing-67's 13 non-recursive arms + firing-71's 3 recursive
-- arms into ONE order over the CANONICAL FX1Poly.Core.IotaHeadStep (no duplicate relation — it already
-- carries toStep + deterministic; this adds the missing SN leg). iotaGenRank bumps optionMatch/eitherMatch
-- to rank 2 (their reduct app(branch,value) has head gen_app, which outranks the redex head under firing-71's
-- realGenPrecedence — wrong direction; the bump fixes it); the other 11 arms need no rank change (recursive
-- already ranked, 10 subterm-reduct arms need no precedence). rpoOrientsAppliedFirst/Second orient the 3
-- applied-branch arms; IotaHeadStep.rpoEmbeds covers all 16. iotaHeadStep_wellFounded: the canonical root-ι
-- fragment is SN by ONE RPO via Subrelation.wf + InvImage.wf eraseToRose, Tait-free (the unification).
#assert_no_axioms FX1Poly.Core.RawIotaRpo.iotaGenPrecedence_wellFounded
#assert_no_axioms FX1Poly.Core.RawIotaRpo.rpoOrientsAppliedFirst
#assert_no_axioms FX1Poly.Core.RawIotaRpo.rpoOrientsAppliedSecond
#assert_no_axioms FX1Poly.Core.RawIotaRpo.iotaGenRpoWellFounded
#assert_no_axioms FX1Poly.Core.IotaHeadStep.rpoEmbeds
#assert_no_axioms FX1Poly.Core.iotaHeadStep_wellFounded

-- Full ι-reduction SN (firing-74): lift root-ι SN (firing-73) to the COMPATIBLE CLOSURE of IotaHeadStep —
-- ι at the root OR ι inside ANY child context (IotaStep/IotaStepChildren, mirroring Step/StepChildren). The
-- congruence case finally CONSUMES firing-72's rpo_congruence: an ι step inside child position i changes
-- eraseChildren only at that position (prefix ++ child :: suffix → prefix ++ child' :: suffix, the child
-- RPO-decreasing by IH), and rpo_congruence lifts that to a node RPO-decrease. The here/there spine walk
-- builds the prefix ([] at head, eraseToRose head :: prefix one step in). Proven via the explicit mutual
-- recursor IotaStep.rec (the Step.subst pattern). IotaStep.toStep: sound sub-relation of the live Step.
-- iotaFullStep_wellFounded: the GENUINE ι-fragment SN (not just root), Tait-free (β imported, η shipped #357).
#assert_no_axioms FX1Poly.Core.IotaStep.rpoEmbeds
#assert_no_axioms FX1Poly.Core.IotaStep.toStep
#assert_no_axioms FX1Poly.Core.iotaFullStep_wellFounded
#assert_no_axioms FX1Poly.Core.IotaStep.congSmoke

-- eraseToRose rename-invariance (the eta-embedding substrate): `eraseToRose` forgets the payload and every
-- binder shift, so a rename (which only rewrites the var-arm payload + renames children) leaves the rose
-- image unchanged.  This is what lets eta-reduction RPO-decrease the SAME eraseToRose order the ι fragment
-- uses: each eta-contraction leaves a SUBTERM of the source modulo a weakening rename (etaLam/etaPathLam put
-- the inner function under one extra binder, reached by RawTerm.weaken), and weaken-invariance erases that
-- gap.  Proven by the mutual term+children recursion mirroring RawTerm.rename_pointwise (var arm closes
-- definitionally; non-var via rename_mkGen_of_ne_var + the children IH).  eraseToRose_weaken is the corollary
-- the binder eta arms consume directly.
#assert_no_axioms FX1Poly.Core.eraseToRose_rename
#assert_no_axioms FX1Poly.Core.eraseChildren_rename
#assert_no_axioms FX1Poly.Core.eraseToRose_weaken

-- The abstract Newman's lemma: terminating + weakly confluent implies confluent, the confluence analogue of
-- the termination orders, generic over any relation.  ReflTransClosure (an own RTC, since
-- Relation.ReflTransGen is Mathlib-only) + single/trans; Joinable/WeaklyConfluent/Confluent vocabulary;
-- newmanAux is the WF-induction tiling (WCR on the two first steps, IH at each reduct, compose); newman is the
-- headline.  Zero-axiom: cases on RTC is propext-clean since its indices are free vars, not ctor patterns.
#assert_no_axioms FX1Poly.Core.ReflTransClosure
#assert_no_axioms FX1Poly.Core.ReflTransClosure.single
#assert_no_axioms FX1Poly.Core.ReflTransClosure.trans
#assert_no_axioms FX1Poly.Core.Joinable
#assert_no_axioms FX1Poly.Core.WeaklyConfluent
#assert_no_axioms FX1Poly.Core.Confluent
#assert_no_axioms FX1Poly.Core.newmanAux
#assert_no_axioms FX1Poly.Core.newman

-- The diamond-implies-confluence route (strip lemma), the second abstract confluence path complementing
-- Newman: confluence from the diamond property alone, no termination.  ReflTransClosure.monotone/collapse
-- (the sandwich glue) + DiamondProperty + stripLemma (single strips against many) + diamondConfluence +
-- confluentOfDiamondSimulation (the parallel-reduction recipe: rel subset parRel subset RTC rel + parRel
-- diamond implies rel confluent, the route by which single-step beta, which lacks the diamond, is proved
-- confluent via parallel reduction).  Zero-axiom.
#assert_no_axioms FX1Poly.Core.ReflTransClosure.monotone
#assert_no_axioms FX1Poly.Core.ReflTransClosure.collapse
#assert_no_axioms FX1Poly.Core.DiamondProperty
#assert_no_axioms FX1Poly.Core.stripLemma
#assert_no_axioms FX1Poly.Core.diamondConfluenceAux
#assert_no_axioms FX1Poly.Core.diamondConfluence
#assert_no_axioms FX1Poly.Core.confluentOfDiamondSimulation

-- FX-layer wiring connecting the abstract diamond/strip confluence to the concrete raw `StepStar`.
-- StepStar is isomorphic to ReflTransClosure Step (toReflTransClosure / ofReflTransClosure), then
-- hasConfluence_of_parallelDiamond (route A via confluentOfDiamondSimulation) and hasStrip_of_parallelDiamond
-- (route B via stripLemma, realizing StepStarConfluence's `confluence_of_strip`).  A sandwiched parallel
-- relation (Step subset ParStep subset StepStar) with the diamond yields raw global confluence.
#assert_no_axioms FX1Poly.Core.StepStar.toReflTransClosure
#assert_no_axioms FX1Poly.Core.StepStar.ofReflTransClosure
#assert_no_axioms FX1Poly.Core.StepStar.hasConfluence_of_parallelDiamond
#assert_no_axioms FX1Poly.Core.StepStar.hasStrip_of_parallelDiamond

-- The Takahashi triangle lemma: the linear route to the parallel-reduction diamond.  A completeDevelopment
-- function with the TriangleProperty (every reduct steps to the source's complete development) yields
-- DiamondProperty.ofTriangle and Confluent.ofTriangle, reducing the parallel diamond from a quadratic
-- redex-pair join to the single linear "exhibit completeDevelopment + its triangle" obligation (Takahashi
-- 1995).  Composes with diamondConfluence + hasConfluence_of_parallelDiamond.
#assert_no_axioms FX1Poly.Core.DiamondProperty.ofTriangle
#assert_no_axioms FX1Poly.Core.Confluent.ofTriangle
-- The existential per-source form (HasMaximalReduct): generalizes the function-based TriangleProperty
-- (HasMaximalReduct.ofTriangle) and is the form the concrete FX parallel reduction discharges by structural
-- recursion on the source (no separately-defined total completeDevelopment function over RawTerm needed).
-- ofMaximalReduct yields the diamond; Confluent.ofMaximalReduct composes with diamondConfluence.
#assert_no_axioms FX1Poly.Core.HasMaximalReduct.ofTriangle
#assert_no_axioms FX1Poly.Core.DiamondProperty.ofMaximalReduct
#assert_no_axioms FX1Poly.Core.Confluent.ofMaximalReduct

-- The concrete FX parallel reduction: ParStep contracts any set of redexes simultaneously (Takahashi),
-- mirroring all 18 Step rules with parallel sub-reduction of the surviving sub-terms; the pointwise
-- ParStepChildren reduces every child at once.  ParStep.refl / ParStepChildren.refl give reflexivity by mutual
-- structural recursion (term-mode match, no termination_by).  This is the relation that discharges
-- HasMaximalReduct, hence the diamond, hence raw confluence.
#assert_no_axioms FX1Poly.Core.ParStep.refl
#assert_no_axioms FX1Poly.Core.ParStepChildren.refl
-- Step subset ParStep (the lower sandwich bound = stepToPar for hasConfluence_of_parallelDiamond): every
-- single reduction is a parallel reduction firing only that redex, surviving sub-terms reflexive; cong maps
-- the single-child StepChildren to a pointwise ParStepChildren.  Mutual term-mode structural recursion on the
-- derivation.  One of the two sandwich bounds the raw-confluence adapter needs.
#assert_no_axioms FX1Poly.Core.Step.toParStep
#assert_no_axioms FX1Poly.Core.StepChildren.toParStepChildren
-- ParStep subset StepStar (the upper sandwich bound = parToStepStar): every parallel reduction is a finite
-- sequence of single steps.  Each arm reduces the redex's surviving sub-terms via StepStar.ofChildrenStar (the
-- child-spine congruence lifter) then fires the matching root Step; cong lifts the pointwise ParStepChildren
-- through ofChildrenStar.  With Step.toParStep, this completes the sandwich Step subset ParStep subset StepStar
-- that StepStar.hasConfluence_of_parallelDiamond consumes.
#assert_no_axioms FX1Poly.Core.ParStep.toStepStar
#assert_no_axioms FX1Poly.Core.ParStepChildren.toStepChildrenStar

-- The Takahashi complete development (the maximal-reduct witness): contract every redex present at once but
-- not the redexes created by contraction.  Propext-clean because the redex-shape detection is delegated to
-- fireRootRedex (a direct overlapping-nested-pattern match leaks propext and defeats the equation compiler);
-- completeDevelopment itself does only flat mkGen / childNil-childCons matches.  completeDevelopment_stepStar
-- is the soundness half (the development is reachable by StepStar): develop the children via ofChildrenStar,
-- then fire the root via fireRootRedex_sound.  This is the function the HasMaximalReduct ParStep (triangle)
-- proof maximizes against, hence the ParStep diamond, hence raw confluence.
#assert_no_axioms FX1Poly.Core.RawTerm.fireRootRedexOrSelf
-- fireRootRedexOrSelfGated: fire on developed children only when the original children form a syntactic
-- redex.  This gate makes completeDevelopment the standard (non-over-firing) Takahashi development: firing on
-- developed children alone would contract redexes created by developing (an inner redex whose contractum is a
-- lam turns a non-lam-headed app into a beta-redex), breaking the triangle's ParStep a (cd a).
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
-- ι reduction-rule equations: per-redex definitional characterization of the gated complete development
-- (all rfl), the companions of cd_app_lam_eq the triangle's 16 ι arms rewrite with before firing.
#assert_no_axioms FX1Poly.Core.cd_boolElimTrue_eq
#assert_no_axioms FX1Poly.Core.cd_boolElimFalse_eq
#assert_no_axioms FX1Poly.Core.cd_fstPair_eq
#assert_no_axioms FX1Poly.Core.cd_sndPair_eq
#assert_no_axioms FX1Poly.Core.cd_natElimZero_eq
#assert_no_axioms FX1Poly.Core.cd_natRecZero_eq
#assert_no_axioms FX1Poly.Core.cd_listElimNil_eq
#assert_no_axioms FX1Poly.Core.cd_optionMatchNone_eq
#assert_no_axioms FX1Poly.Core.cd_optionMatchSome_eq
#assert_no_axioms FX1Poly.Core.cd_eitherMatchInl_eq
#assert_no_axioms FX1Poly.Core.cd_eitherMatchInr_eq
#assert_no_axioms FX1Poly.Core.cd_natElimSucc_eq
#assert_no_axioms FX1Poly.Core.cd_natRecSucc_eq
#assert_no_axioms FX1Poly.Core.cd_listElimCons_eq
#assert_no_axioms FX1Poly.Core.cd_idJRefl_eq
#assert_no_axioms FX1Poly.Core.cd_idStrictRecRefl_eq

-- ParStep stable under substitution + renaming: the parallel-substitution lemma the triangle
-- ParStep a b -> ParStep b (completeDevelopment a) uses at its beta/iota arms is built on these.  ParStep.subst
-- mirrors Step.subst's recursor idiom (all-substitutions motive; beta via subst0_subst_commute, cong via the
-- gen_var split, every iota arm applies its premises' IHs at sigma, the spine lifts sigma by the child binder
-- shift).  ParStep.rename is the corollary via the Step.rename rename-to-subst trick.  These are the
-- renaming/substitution substrate the binder case of the parallel substitution lemma requires.
#assert_no_axioms FX1Poly.Core.ParStep.subst
#assert_no_axioms FX1Poly.Core.ParStepChildren.subst
#assert_no_axioms FX1Poly.Core.ParStep.rename
#assert_no_axioms FX1Poly.Core.ParStepChildren.rename

-- The parallel substitution lemma (the triangle's beta/iota engine): substituting a parallel-reduced
-- argument into a parallel-reduced body parallel-reduces.  ParStep is a single parallel step (not transitive),
-- so the diagonal cannot be composed from two one-sided ParStep.subst applications: it needs the combined
-- induction varying both the substitution (sigma to tau, related by PointwiseParStep, lifted under binders by
-- ParStep.weaken) and the term.  ParStep.subst0_diagonal instantiates substPointwise at the two singleton
-- substitutions; this is what the triangle's beta arm fires with (and the recursive iota arms whose contractums
-- embed subst0 of developed components).
#assert_no_axioms FX1Poly.Core.ParStep.weaken
#assert_no_axioms FX1Poly.Core.RawTermSubst.lift_pointwiseParStep
#assert_no_axioms FX1Poly.Core.iterateLiftRaw_RawTermSubst_pointwiseParStep
#assert_no_axioms FX1Poly.Core.ParStep.substPointwise
#assert_no_axioms FX1Poly.Core.RawTermSubst.singleton_pointwiseParStep
#assert_no_axioms FX1Poly.Core.ParStep.subst0_diagonal

-- ParStep cong-inversion at the non-redex-head constructors: a parallel reduct of mkGen C .. keeps the head
-- C with components reduced (only the cong arm's source unifies; the beta/iota arms have app/eliminator
-- sources).  These extract the developed sub-components the triangle's beta/iota arms need from the
-- cong-reduced children: completeDevelopment dispatches on the generator by by_cases (hiding deep subterms
-- from structural recursion), so completeDevelopment_parStep recurses only on the direct children spine and
-- extracts per-component ParSteps by these inversions.
#assert_no_axioms FX1Poly.Core.ParStep.lam_inv
#assert_no_axioms FX1Poly.Core.ParStep.pair_inv
#assert_no_axioms FX1Poly.Core.ParStep.natSucc_inv
#assert_no_axioms FX1Poly.Core.ParStep.listCons_inv
#assert_no_axioms FX1Poly.Core.ParStep.optionSome_inv
#assert_no_axioms FX1Poly.Core.ParStep.eitherInl_inv
#assert_no_axioms FX1Poly.Core.ParStep.eitherInr_inv
-- Nullary scrutinee / witness inversions completing the 13-constructor set: the triangle's cong arm learns
-- from e.g. ParStep boolTrue sc' that sc' = boolTrue, so a cong-reduced redex is still a redex.
#assert_no_axioms FX1Poly.Core.ParStep.boolTrue_inv
#assert_no_axioms FX1Poly.Core.ParStep.boolFalse_inv
#assert_no_axioms FX1Poly.Core.ParStep.natZero_inv
#assert_no_axioms FX1Poly.Core.ParStep.listNil_inv
#assert_no_axioms FX1Poly.Core.ParStep.optionNone_inv
#assert_no_axioms FX1Poly.Core.ParStep.refl_inv

-- completeDevelopment_parStep: every term parallel-reduces to its complete development.  The correctness
-- witness for the gated cd (an over-firing cd would fail it, since a created redex cannot be fired in the same
-- single parallel step) and the triangle's b := a instance.  Via RawTerm.rec (the by_cases generator dispatch
-- hides deep subterms from structural recursion, so it routes through the recursor's children-spine IH):
-- none implies cong, some implies per-redex fire with the child IHs extracted by cases.  Propext-clean.
#assert_no_axioms FX1Poly.Core.RawTerm.completeDevelopment_parStep

-- The Takahashi triangle: every parallel reduct b of a further parallel-reduces to completeDevelopment a,
-- the maximal-reduct property that discharges the ParStep DiamondProperty and hence (through the
-- Step subset ParStep subset StepStar sandwich) unconditional raw confluence.  Proved by induction on the
-- ParStep a b derivation (ParStep.rec, termination-free): beta/branch-selection iota arms close by IHs through
-- the cd_<redex>_eq defeq, recursive iota by nested cong, cong by triangleCongFires.  triangleCongFires is the
-- cong-some workhorse: it dispatches on the 11 redex generators, inverts the cong-reduced scrutinee/function
-- child to learn the post-cong head shape, extracts the per-component development steps from the children IH,
-- and fires the matching ParStep ctor (whose contractum is definitionally fireRootRedexOrSelf's output);
-- non-firing branches reuse fireRootRedex_sound's keys.
#assert_no_axioms FX1Poly.Core.ParStep.triangleCongFires
#assert_no_axioms FX1Poly.Core.ParStep.triangle

-- Unconditional raw confluence.  ParStep.diamond instantiates DiamondProperty.ofTriangle at
-- ParStep.triangle; StepStar.rawConfluence feeds that diamond + the Step subset ParStep subset StepStar
-- sandwich (Step.toParStep / ParStep.toStepStar) to StepStar.hasConfluence_of_parallelDiamond, yielding global
-- Church-Rosser for the raw StepStar relation with no strong-normalization assumption (raw beta+iota is not
-- SN).
#assert_no_axioms FX1Poly.Core.ParStep.diamond
#assert_no_axioms FX1Poly.Core.StepStar.rawConfluence

-- The Newman-precursor strip property, unconditional via the ParStep diamond (route B,
-- hasStrip_of_parallelDiamond): a single Step out of a source joins against any StepStar chain out of it.
-- A distinct statement from rawConfluence (one-vs-many vs many-vs-many); confluence_of_strip turns it into the
-- same Church-Rosser result.  No SN assumption.
#assert_no_axioms FX1Poly.Core.StepStar.rawStrip

-- Raw Conv (= StepStar.Join) is an unconditional equivalence relation.  Conv.refl / Conv.sym are structural;
-- Conv.trans is the consequence of Church-Rosser, discharged by StepStar.rawConfluence (which supplies the
-- confluence hypothesis), so Conv.trans + Conv.equivalence + the calc-enabling Trans instance hold
-- unconditionally, with no strong-normalization premise (raw beta+iota is not SN).  This is the foundation the
-- raw-layer conversion checker rests on.
#assert_no_axioms FX1Poly.Core.Conv.trans
#assert_no_axioms FX1Poly.Core.Conv.equivalence
#assert_no_axioms FX1Poly.Core.Conv.instTrans

-- Uniqueness of normal forms with no termination hypothesis.  StepStar.rawConfluence joins any two
-- reductions of a common source, so two normal reducts coincide whether or not the source terminates, making
-- "the normal form" a well-defined partial function on all raw terms.  The proof reuses Conv.eq_of_noStep +
-- isStepNormalForm_blocks_step, joining via rawConfluence.
#assert_no_axioms FX1Poly.Core.normalForm_unique_of_confluence

-- Conv equals normal-form equality with no SN hypothesis.  rawConfluence + normalForm_unique_of_confluence
-- discharge the per-term confluence witnesses, so the iff holds for any two terms that reduce to normal forms.
-- This separates decidable Conv into existence-of-normal-forms (the SN obligation, gated) and
-- correctness-of-normal-form-comparison (pure confluence, unconditional).  The decidable wrapper decides Conv
-- via instDecidableEqRawTerm given the normal-form witnesses, no SN premise.
#assert_no_axioms FX1Poly.Core.Conv.iff_normalForms_eq_of_confluence
#assert_no_axioms FX1Poly.Core.Conv.decidableOfNormalForms

-- The Path-B decider (polycell.md §2.3) with the confluence hypothesis discharged.  Conv.iff_normalForm_eq /
-- Conv.decidableOfNormalizer take a Normalizer and StepStar.HasConfluence; rawConfluence discharges the latter,
-- so a Normalizer alone decides Conv as normal-form equality.  The Normalizer (a total normal-form function)
-- remains the SN obligation (raw beta+iota has no global normalizer); the separate confluence assumption a
-- normalizer construction would otherwise also supply is what this discharges.
#assert_no_axioms FX1Poly.Core.Normalizer.conv_iff_normalForm_eq
#assert_no_axioms FX1Poly.Core.Normalizer.decidableConv

-- Hindley-Rosen via the diamond (abstract toolkit): the third confluence route after Newman (terminating)
-- and DiamondConfluence (single diamond).  Modular: it combines two separately-confluent relations whose
-- diamonds commute into a confluent union (the intended FX use: beta-parallel diamond + iota-parallel diamond +
-- beta/iota commute, without one monolithic 20-arm ParStep).  StronglyCommutes + DiamondProperty.union (4-way
-- case split) + confluentOfUnionDiamonds + confluentUnionOfParallelDiamonds (the two-relation generalization of
-- confluentOfDiamondSimulation).  Zero-axiom.
#assert_no_axioms FX1Poly.Core.StronglyCommutes
#assert_no_axioms FX1Poly.Core.DiamondProperty.union
#assert_no_axioms FX1Poly.Core.confluentOfUnionDiamonds
#assert_no_axioms FX1Poly.Core.confluentUnionOfParallelDiamonds

-- Deterministic confluence (abstract toolkit, fourth route): a deterministic (functional) relation is
-- confluent, since its reflexive-transitive reducts from a common source are linearly ordered.  Determinism
-- does not give the strict diamond (a normal form breaks it), so this is its own linear-chain induction.  The
-- route for deterministic reduction strategies (weak-head here, the deterministic NbE evaluator downstream).
-- IsDeterministic + confluentOfDeterministic + the concrete WeakHeadStep.hasConfluence (weak-head reduction is
-- Church-Rosser, from WeakHeadStep.deterministic).  Zero-axiom.
#assert_no_axioms FX1Poly.Core.IsDeterministic
#assert_no_axioms FX1Poly.Core.confluentOfDeterministicAux
#assert_no_axioms FX1Poly.Core.confluentOfDeterministic
#assert_no_axioms FX1Poly.Core.WeakHeadStep.hasConfluence

-- A reducibility candidate is closed under renaming, in the Kripke-indexed form: IsKripkeReducibilityCandidate
-- (CR1 members-SN + CR2 closed-under-Step) survives KripkeCand.transport along any renaming with no hypothesis
-- (the index precomposes; laws read off at the composed index).  The bare same-scope ReducibleTypeStep form is
-- false (the piType same-scope argument quantifier has a counterexample at a renamed Pi-type), so the Kripke
-- index is what carries renaming-closure.  Predicate-level companion is kripkeArrowDep_transport_pointwise.
#assert_no_axioms FX1Poly.Core.IsKripkeReducibilityCandidate
#assert_no_axioms FX1Poly.Core.IsKripkeReducibilityCandidate.transport

-- Pointwise-saturation of the dependent reducibility relation (the level-free fundamental theorem's
-- choice-free piIntro keystone): `ReducibleTypeClosed` is closed under pointwise-iff by construction, so it
-- carries the canonical member-predicate candidate that bare `ReducibleType` does not.  Gated per-declaration
-- here, outside the AuditCoreSubstrate sweep's import closure.
#assert_no_axioms FX1Poly.Core.ReducibleTypeClosed
#assert_no_axioms FX1Poly.Core.ReducibleType.toClosed
#assert_no_axioms FX1Poly.Core.ReducibleType.closedAtMemberPredicate

-- Equivalence-relation algebra of candidate pointwise-iff (the transport algebra the reducibility model
-- threads through every `ReducibleType.deterministic` candidate transfer and the `ReducibleType.ofPointwiseIff`
-- congruence-closure cascade).
#assert_no_axioms FX1Poly.Core.PointwiseIff.refl
#assert_no_axioms FX1Poly.Core.PointwiseIff.symm
#assert_no_axioms FX1Poly.Core.PointwiseIff.trans

-- Candidate-congruence of the stratified reducibility step-functor under lower-existence-equivalence: the
-- inductive step of level-irrelevance (Pi case via ofPointwiseIff, universe case via the lower-existence
-- equivalence).  The level-0 degenerate base means it does not bootstrap full irrelevance alone (see the module
-- docstring); it is the hard core a level argument reuses.
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
-- neutral-backward companions of the CR1 membership corollary; the Tait closure bricks the fundamental
-- theorem's neutral and reduction-stable cases consume).
#assert_no_axioms FX1Poly.Core.IsReducibleMemberAt.closedUnderStep
#assert_no_axioms FX1Poly.Core.IsReducibleMemberAt.closedUnderStepStar
#assert_no_axioms FX1Poly.Core.IsReducibleMemberAt.neutralExpansion

-- Structural SN closure completing the universe-code former family: the one-child listCode/optionCode
-- congruence inversions + SN, the three-child idCode inversion + SN, and the reusable three-child congruence
-- SN combinator (the three-child analogue of the one/two-child versions).  The SN half of "the code is a
-- reducible member of El"; SN is fuel-independent.
#assert_no_axioms FX1Poly.Core.Step.from_listCode
#assert_no_axioms FX1Poly.Core.Step.from_optionCode
#assert_no_axioms FX1Poly.Core.Step.from_idCode
#assert_no_axioms FX1Poly.Core.StepStar.isStronglyNormalizing_of_threeChildCong
#assert_no_axioms FX1Poly.Core.StepStar.listCode_isStronglyNormalizing_of_element
#assert_no_axioms FX1Poly.Core.StepStar.optionCode_isStronglyNormalizing_of_element
#assert_no_axioms FX1Poly.Core.StepStar.idCode_isStronglyNormalizing_of_type_endpoints
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
≤ once (the #1009 case). A variable under TWO binders is weakened twice; the resulting subst (lift σ)(weaken² a)
= weaken a cancellation was the last deferred de Bruijn obstruction (symbolic S-rule, symbolic Church sums). It is
NOT a wall: subst_lift_weaken (★, the lift-weaken NATURALITY subst (lift σ)(weaken t) = weaken (subst σ t)) follows
from weaken_eq_rename + the shipped rename_subst_commute (LHS) + subst_rename_commute (RHS) + subst_pointwise (both
composites send k ↦ weaken(σ k)); subst_lift_singleton_weaken_weaken (the double-weaken cancellation) is then two
rw's (subst_lift_weaken peels one weaken, weaken_subst_singleton cancels the inner singleton). Zero-axiom. -/

#assert_no_axioms FX1Poly.Core.RawTerm.subst_lift_weaken
#assert_no_axioms FX1Poly.Core.RawTerm.subst_lift_singleton_weaken_weaken
