import FX1PolyAudit.DependencyAudit
import FX1Poly.Universe.LevelExpr
import FX1Poly.Universe.UniverseFlag
import FX1Poly.Universe.UniverseFlagStrength
import FX1Poly.Universe.LevelExprSimplify
import FX1Poly.Universe.LevelExprSerialize
import FX1Poly.Universe.UniverseFlagSerialize
import FX1Poly.Universe.UniversePayloadSerialize

/-! # Tools/AuditAll/AuditUniverse
   — persistent per-declaration zero-axiom gate for the Phase Z₀
     universe layer

The universe layer (LevelExpr inductive, UniverseFlag enum, and the
full LevelExprSimplify normalization / canonical-form / decision-
procedure cascade) is the substrate of FX's first-class universe
polymorphism (polycell.md §11.8.2, §11.8.7).  Its correctness rests on
the zero-axiom discipline: every declaration must elaborate without
depending on `propext`, `Classical.choice`, `Quot.sound`, or `sorryAx`.

## Why this file exists

This file makes the zero-axiom check PERSISTENT: every universe
declaration is gated by `#assert_no_axioms` (the throwing variant from
`FX1PolyAudit/DependencyAudit`), so any future edit that introduces an
axiom dependency fails `lake build FX1PolyAudit` immediately.

`#assert_no_axioms` takes a fully-qualified name and errors at
elaboration if the named constant depends on any axiom, so no
namespace wrapper is needed here — the file is a flat census of the
universe surface.

## Coverage

The universe modules:
* `Universe/LevelExpr.lean` — the 5-ctor inductive + per-ctor
  canonical-form smokes + DecidableEq smokes.
* `Universe/UniverseFlag.lean` — the Setzer-Rathjen closed enum +
  per-flag canonical-form + DecidableEq + ctor-count.
* `Universe/LevelExprSimplify.lean` — the normalization cascade:
  Phase-A `simplify` + `size` + `denote` + the levelMax/lmax/lsucc
  algebraic laws + `compare` total order + the `MaxPlusForm` max-plus
  canonical form (toMaxPlusForm soundness, canonicalize/normalizeBase/
  fullCanonicalize, the lookupOffset extensionality tower,
  canonicalForm_unique) + the predicative `denoteEquiv` decision
  procedure (`denoteEquiv_iff_fullCanonicalize_eq`,
  `decideDenoteEquiv`) + the 14-fixture behavioral smoke corpus + its
  count/behavior ratchet (`predicativeSmokeCorpus_count`/`_behavior`,
  the silent-shrink + verdict-flip guard) + the
  complexity working-set bounds (`toMaxPlusForm_varOffsets_length_le_size`,
  `canonicalizeVarOffsets_length_le`,
  `fullCanonicalize_toMaxPlusForm_varOffsets_length_le_size`).

## Discovery

Auto-included in the `FX1PolyAudit` lean_lib via its
`.submodules \`FX1PolyAudit` glob (lakefile.lean) — no manual
registration required.  Run `lake build FX1Poly FX1PolyAudit` for the
full strict-zero-axiom sweep.
-/

/-! ### LevelExpr inductive + per-ctor canonical-form + DecidableEq smokes -/

#assert_no_axioms FX1Poly.Universe.LevelExpr
#assert_no_axioms FX1Poly.Universe.LevelExpr.lzero_canonical
#assert_no_axioms FX1Poly.Universe.LevelExpr.lsucc_lzero_canonical
#assert_no_axioms FX1Poly.Universe.LevelExpr.lmax_lzero_lzero_canonical
#assert_no_axioms FX1Poly.Universe.LevelExpr.limax_lzero_lzero_canonical
#assert_no_axioms FX1Poly.Universe.LevelExpr.lvar_zero_canonical
#assert_no_axioms FX1Poly.Universe.LevelExpr.decEq_refl_lzero
-- structural distinctness `e ≠ lsucc e` (no-Type-in-Type probe support):
-- size-free structural induction, the predicativity guard at the level algebra
#assert_no_axioms FX1Poly.Universe.LevelExpr.ne_lsucc_self

/-! ### UniverseFlag Setzer-Rathjen closed enum + canonical-form + DecidableEq -/

#assert_no_axioms FX1Poly.Universe.UniverseFlag
#assert_no_axioms FX1Poly.Universe.UniverseFlag.standard_canonical
#assert_no_axioms FX1Poly.Universe.UniverseFlag.inaccessible_canonical
#assert_no_axioms FX1Poly.Universe.UniverseFlag.mahlo_canonical
#assert_no_axioms FX1Poly.Universe.UniverseFlag.superMahlo_canonical
#assert_no_axioms FX1Poly.Universe.UniverseFlag.nMahlo_zero_canonical
#assert_no_axioms FX1Poly.Universe.UniverseFlag.hyperMahlo_canonical
#assert_no_axioms FX1Poly.Universe.UniverseFlag.weaklyCompact_canonical
#assert_no_axioms FX1Poly.Universe.UniverseFlag.indescribable_zero_canonical
#assert_no_axioms FX1Poly.Universe.UniverseFlag.reflecting_canonical
#assert_no_axioms FX1Poly.Universe.UniverseFlag.vopenka_canonical
#assert_no_axioms FX1Poly.Universe.UniverseFlag.decEq_refl_standard
#assert_no_axioms FX1Poly.Universe.UniverseFlag.ctorCount
#assert_no_axioms FX1Poly.Universe.UniverseFlag.ctorCount_correct

/-! ### Normalization cascade: Phase-A simplify / size / denote / algebraic laws / compare / MaxPlusForm canonical form / predicative decision procedure / smokes / complexity working-set bounds -/

#assert_no_axioms FX1Poly.Universe.LevelExpr.simplify
#assert_no_axioms FX1Poly.Universe.LevelExpr.simplify_lmax_idempotent
#assert_no_axioms FX1Poly.Universe.LevelExpr.simplify_lmax_idempotent_nonzero
#assert_no_axioms FX1Poly.Universe.LevelExpr.simplify_lmax_left_identity
#assert_no_axioms FX1Poly.Universe.LevelExpr.simplify_lmax_right_identity
#assert_no_axioms FX1Poly.Universe.LevelExpr.simplify_limax_left_identity
#assert_no_axioms FX1Poly.Universe.LevelExpr.simplify_limax_right_collapse
#assert_no_axioms FX1Poly.Universe.LevelExpr.simplify_limax_both_zero
#assert_no_axioms FX1Poly.Universe.LevelExpr.simplify_lzero
#assert_no_axioms FX1Poly.Universe.LevelExpr.simplify_lsucc_lzero
#assert_no_axioms FX1Poly.Universe.LevelExpr.simplify_lvar_zero
#assert_no_axioms FX1Poly.Universe.LevelExpr.simplify_lmax_distinct
#assert_no_axioms FX1Poly.Universe.LevelExpr.simplify_limax_non_lzero_codomain
#assert_no_axioms FX1Poly.Universe.LevelExpr.simplify_lzero_idempotent
#assert_no_axioms FX1Poly.Universe.LevelExpr.simplify_lvar_zero_idempotent
#assert_no_axioms FX1Poly.Universe.LevelExpr.size
#assert_no_axioms FX1Poly.Universe.LevelExpr.size_pos
#assert_no_axioms FX1Poly.Universe.LevelExpr.simplify_size_le
#assert_no_axioms FX1Poly.Universe.LevelExpr.size_lzero
#assert_no_axioms FX1Poly.Universe.LevelExpr.size_lvar
#assert_no_axioms FX1Poly.Universe.LevelExpr.size_lsucc
#assert_no_axioms FX1Poly.Universe.LevelExpr.size_lmax
#assert_no_axioms FX1Poly.Universe.LevelExpr.size_limax
#assert_no_axioms FX1Poly.Universe.LevelExpr.simplify_idempotent
#assert_no_axioms FX1Poly.Universe.LevelExpr.IsPhaseANormalForm
#assert_no_axioms FX1Poly.Universe.LevelExpr.simplify_produces_normal_form
#assert_no_axioms FX1Poly.Universe.LevelExpr.lzero_isNormalForm
#assert_no_axioms FX1Poly.Universe.LevelExpr.lvar_isNormalForm
#assert_no_axioms FX1Poly.Universe.LevelExpr.IsStructurallyNormalForm
#assert_no_axioms FX1Poly.Universe.LevelExpr.simplify_produces_isStructurallyNormalForm
#assert_no_axioms FX1Poly.Universe.LevelExpr.IsStructurallyNormalForm.toFixedPoint
#assert_no_axioms FX1Poly.Universe.LevelExpr.simplify_isStructurallyNormal_and_fixed
#assert_no_axioms FX1Poly.Universe.LevelExpr.size_lt_lmax_left
#assert_no_axioms FX1Poly.Universe.LevelExpr.size_lt_lmax_right
#assert_no_axioms FX1Poly.Universe.LevelExpr.size_lt_limax_left
#assert_no_axioms FX1Poly.Universe.LevelExpr.size_lt_limax_right
#assert_no_axioms FX1Poly.Universe.LevelExpr.lzero_size_lt_limax
#assert_no_axioms FX1Poly.Universe.LevelExpr.IsPhaseANormalForm.toStructurallyNormal
#assert_no_axioms FX1Poly.Universe.LevelExpr.isPhaseANormalForm_iff_isStructurallyNormalForm
#assert_no_axioms FX1Poly.Universe.LevelExpr.levelMax
#assert_no_axioms FX1Poly.Universe.LevelExpr.levelMax_self
#assert_no_axioms FX1Poly.Universe.LevelExpr.levelMax_zero_left
#assert_no_axioms FX1Poly.Universe.LevelExpr.levelMax_zero_right
#assert_no_axioms FX1Poly.Universe.LevelExpr.denote
#assert_no_axioms FX1Poly.Universe.LevelExpr.denote_lzero
#assert_no_axioms FX1Poly.Universe.LevelExpr.denote_lvar
#assert_no_axioms FX1Poly.Universe.LevelExpr.denote_lsucc
#assert_no_axioms FX1Poly.Universe.LevelExpr.denote_lmax
#assert_no_axioms FX1Poly.Universe.LevelExpr.denote_limax
#assert_no_axioms FX1Poly.Universe.LevelExpr.simplify_denote_eq
#assert_no_axioms FX1Poly.Universe.LevelExpr.levelMax_comm
#assert_no_axioms FX1Poly.Universe.LevelExpr.levelMax_assoc
#assert_no_axioms FX1Poly.Universe.LevelExpr.levelMax_succ_distrib
#assert_no_axioms FX1Poly.Universe.LevelExpr.lmax_denote_comm
#assert_no_axioms FX1Poly.Universe.LevelExpr.lmax_denote_assoc
#assert_no_axioms FX1Poly.Universe.LevelExpr.lsucc_lmax_distrib_denote
#assert_no_axioms FX1Poly.Universe.LevelExpr.denoteEquiv
#assert_no_axioms FX1Poly.Universe.LevelExpr.denoteEquiv.refl
#assert_no_axioms FX1Poly.Universe.LevelExpr.denoteEquiv.symm
#assert_no_axioms FX1Poly.Universe.LevelExpr.denoteEquiv.trans
#assert_no_axioms FX1Poly.Universe.LevelExpr.lmax_comm_denoteEquiv
#assert_no_axioms FX1Poly.Universe.LevelExpr.lmax_assoc_denoteEquiv
#assert_no_axioms FX1Poly.Universe.LevelExpr.lsucc_lmax_distrib_denoteEquiv
#assert_no_axioms FX1Poly.Universe.LevelExpr.lmax_idempotent_denoteEquiv
#assert_no_axioms FX1Poly.Universe.LevelExpr.lmax_lzero_left_denoteEquiv
#assert_no_axioms FX1Poly.Universe.LevelExpr.lmax_lzero_right_denoteEquiv
#assert_no_axioms FX1Poly.Universe.LevelExpr.simplify_denoteEquiv
#assert_no_axioms FX1Poly.Universe.LevelExpr.lsucc_denoteEquiv_congr
#assert_no_axioms FX1Poly.Universe.LevelExpr.lmax_denoteEquiv_congr
#assert_no_axioms FX1Poly.Universe.LevelExpr.limax_denoteEquiv_congr
#assert_no_axioms FX1Poly.Universe.LevelExpr.limax_denote_lzero_right
#assert_no_axioms FX1Poly.Universe.LevelExpr.limax_denote_lzero_left
#assert_no_axioms FX1Poly.Universe.LevelExpr.limax_denote_eq_lmax_when_codomain_nonzero
#assert_no_axioms FX1Poly.Universe.LevelExpr.limax_lzero_right_denoteEquiv
#assert_no_axioms FX1Poly.Universe.LevelExpr.limax_lzero_left_denoteEquiv
#assert_no_axioms FX1Poly.Universe.LevelExpr.compareNat
#assert_no_axioms FX1Poly.Universe.LevelExpr.compareNat_refl
#assert_no_axioms FX1Poly.Universe.LevelExpr.compareNat_swap
#assert_no_axioms FX1Poly.Universe.LevelExpr.compareNat_lt_trans
#assert_no_axioms FX1Poly.Universe.LevelExpr.compareNat_gt_trans
#assert_no_axioms FX1Poly.Universe.LevelExpr.ctorIndex
#assert_no_axioms FX1Poly.Universe.LevelExpr.orderingThen
#assert_no_axioms FX1Poly.Universe.LevelExpr.orderingThen_eq_eq_of_both
#assert_no_axioms FX1Poly.Universe.LevelExpr.orderingThen_eq_eq_inv
#assert_no_axioms FX1Poly.Universe.LevelExpr.orderingThen_swap
#assert_no_axioms FX1Poly.Universe.LevelExpr.compare
#assert_no_axioms FX1Poly.Universe.LevelExpr.compare_refl
#assert_no_axioms FX1Poly.Universe.LevelExpr.compare_swap
#assert_no_axioms FX1Poly.Universe.LevelExpr.compareNat_eq_imp_eq
#assert_no_axioms FX1Poly.Universe.LevelExpr.compareNat_eq_iff_eq
#assert_no_axioms FX1Poly.Universe.LevelExpr.compare_eq_imp_eq
#assert_no_axioms FX1Poly.Universe.LevelExpr.compare_eq_iff_eq
#assert_no_axioms FX1Poly.Universe.LevelExpr.compare_cross_ctor
#assert_no_axioms FX1Poly.Universe.LevelExpr.compare_lt_imp_ctorIndex_not_gt
#assert_no_axioms FX1Poly.Universe.LevelExpr.orderingThen_eq_lt_iff
#assert_no_axioms FX1Poly.Universe.LevelExpr.orderingThen_eq_gt_iff
#assert_no_axioms FX1Poly.Universe.LevelExpr.compare_lt_of_ctorIndex_lt
#assert_no_axioms FX1Poly.Universe.LevelExpr.compare_lt_trans_step
#assert_no_axioms FX1Poly.Universe.LevelExpr.compare_lt_trans
#assert_no_axioms FX1Poly.Universe.LevelExpr.swapToCanonicalLmax
#assert_no_axioms FX1Poly.Universe.LevelExpr.canonicalizeLmaxPair
#assert_no_axioms FX1Poly.Universe.LevelExpr.swapToCanonicalLmax_denoteEquiv
#assert_no_axioms FX1Poly.Universe.LevelExpr.canonicalizeLmaxPair_denoteEquiv
#assert_no_axioms FX1Poly.Universe.LevelExpr.canonicalizeLmaxPair_swapToCanonicalLmax
#assert_no_axioms FX1Poly.Universe.LevelExpr.canonicalizeLmaxPair_idempotent
#assert_no_axioms FX1Poly.Universe.LevelExpr.lmaxAtoms
#assert_no_axioms FX1Poly.Universe.LevelExpr.foldLmax
#assert_no_axioms FX1Poly.Universe.LevelExpr.foldLmax_append_denoteEquiv
#assert_no_axioms FX1Poly.Universe.LevelExpr.foldLmax_lmaxAtoms_denoteEquiv
#assert_no_axioms FX1Poly.Universe.LevelExpr.dropLzeroAtoms
#assert_no_axioms FX1Poly.Universe.LevelExpr.foldLmax_dropLzeroAtoms_denoteEquiv
#assert_no_axioms FX1Poly.Universe.LevelExpr.foldLmax_swap_denoteEquiv
#assert_no_axioms FX1Poly.Universe.LevelExpr.insertStep
#assert_no_axioms FX1Poly.Universe.LevelExpr.insertByCompare
#assert_no_axioms FX1Poly.Universe.LevelExpr.foldLmax_insertByCompare_denoteEquiv
#assert_no_axioms FX1Poly.Universe.LevelExpr.insertionSortByCompare
#assert_no_axioms FX1Poly.Universe.LevelExpr.foldLmax_insertionSortByCompare_denoteEquiv
#assert_no_axioms FX1Poly.Universe.LevelExpr.foldLmax_dup_head_denoteEquiv
#assert_no_axioms FX1Poly.Universe.LevelExpr.dedupStep
#assert_no_axioms FX1Poly.Universe.LevelExpr.dedupAdjacent
#assert_no_axioms FX1Poly.Universe.LevelExpr.foldLmax_dedupAdjacent_denoteEquiv
#assert_no_axioms FX1Poly.Universe.LevelExpr.canonicalize
#assert_no_axioms FX1Poly.Universe.LevelExpr.canonicalize_denoteEquiv
#assert_no_axioms FX1Poly.Universe.LevelExpr.denoteAtomList
#assert_no_axioms FX1Poly.Universe.LevelExpr.denoteAtomList_append
#assert_no_axioms FX1Poly.Universe.LevelExpr.foldLmax_denote
#assert_no_axioms FX1Poly.Universe.LevelExpr.lmaxAtoms_denote
#assert_no_axioms FX1Poly.Universe.LevelExpr.IsLowerBound
#assert_no_axioms FX1Poly.Universe.LevelExpr.IsSorted
#assert_no_axioms FX1Poly.Universe.LevelExpr.IsLowerBound_insertByCompare
#assert_no_axioms FX1Poly.Universe.LevelExpr.insertByCompare_sorted
#assert_no_axioms FX1Poly.Universe.LevelExpr.insertionSortByCompare_sorted
#assert_no_axioms FX1Poly.Universe.LevelExpr.IsLowerBound_dedupAdjacent
#assert_no_axioms FX1Poly.Universe.LevelExpr.dedupAdjacent_sorted
#assert_no_axioms FX1Poly.Universe.LevelExpr.compare_lzero_ne_gt
#assert_no_axioms FX1Poly.Universe.LevelExpr.compare_le_lzero_imp_eq
#assert_no_axioms FX1Poly.Universe.LevelExpr.lzero_isLowerBound
#assert_no_axioms FX1Poly.Universe.LevelExpr.IsLowerBound_dropLzeroAtoms
#assert_no_axioms FX1Poly.Universe.LevelExpr.dropLzeroAtoms_sorted
#assert_no_axioms FX1Poly.Universe.LevelExpr.IsStrictLowerBound
#assert_no_axioms FX1Poly.Universe.LevelExpr.IsStrictlySorted
#assert_no_axioms FX1Poly.Universe.LevelExpr.IsStrictLowerBound_dedupAdjacent
#assert_no_axioms FX1Poly.Universe.LevelExpr.dedupAdjacent_strictlySorted
#assert_no_axioms FX1Poly.Universe.LevelExpr.OccursIn
#assert_no_axioms FX1Poly.Universe.LevelExpr.strictlySorted_head_lt
#assert_no_axioms FX1Poly.Universe.LevelExpr.compare_lt_imp_ne
#assert_no_axioms FX1Poly.Universe.LevelExpr.compare_lt_asymm
#assert_no_axioms FX1Poly.Universe.LevelExpr.strictlySorted_unique
#assert_no_axioms FX1Poly.Universe.LevelExpr.levelMax_ge_left
#assert_no_axioms FX1Poly.Universe.LevelExpr.levelMax_ge_right
#assert_no_axioms FX1Poly.Universe.LevelExpr.denote_le_denoteAtomList_of_occurs
#assert_no_axioms FX1Poly.Universe.LevelExpr.denoteAtomList_eq_zero_of_all_zero
#assert_no_axioms FX1Poly.Universe.LevelExpr.denoteAtomList_eq_zero_iff
#assert_no_axioms FX1Poly.Universe.LevelExpr.pointEnvironment
#assert_no_axioms FX1Poly.Universe.LevelExpr.denote_lvar_pointEnvironment
#assert_no_axioms FX1Poly.Universe.LevelExpr.denote_lvar_pointEnvironment_self
#assert_no_axioms FX1Poly.Universe.LevelExpr.denoteAtomList_pointEnvironment_ne_zero_of_occursLvar
#assert_no_axioms FX1Poly.Universe.LevelExpr.AllAtomsAreVariables
#assert_no_axioms FX1Poly.Universe.LevelExpr.isLvar_of_occursIn_allVariables
#assert_no_axioms FX1Poly.Universe.LevelExpr.denoteAtomList_pointEnvironment_eq_zero_of_not_occursLvar
#assert_no_axioms FX1Poly.Universe.LevelExpr.occursLvar_iff_denoteAtomList_pointEnvironment_ne_zero
#assert_no_axioms FX1Poly.Universe.LevelExpr.canonicalAtoms
#assert_no_axioms FX1Poly.Universe.LevelExpr.canonicalize_eq_foldLmax_canonicalAtoms
#assert_no_axioms FX1Poly.Universe.LevelExpr.denote_eq_denoteAtomList_canonicalAtoms
#assert_no_axioms FX1Poly.Universe.LevelExpr.canonicalAtoms_sameLvarMembership_of_denoteEquiv
#assert_no_axioms FX1Poly.Universe.LevelExpr.compare_right_lzero_ne_lt
#assert_no_axioms FX1Poly.Universe.LevelExpr.IsStrictLowerBound_dropLzeroAtoms
#assert_no_axioms FX1Poly.Universe.LevelExpr.dropLzeroAtoms_strictlySorted
#assert_no_axioms FX1Poly.Universe.LevelExpr.canonicalAtoms_strictlySorted
#assert_no_axioms FX1Poly.Universe.LevelExpr.sameMembership_of_sameLvarMembership
#assert_no_axioms FX1Poly.Universe.LevelExpr.canonicalize_eq_of_denoteEquiv_onVariableFragment
#assert_no_axioms FX1Poly.Universe.LevelExpr.IsVariableJoin
#assert_no_axioms FX1Poly.Universe.LevelExpr.AllAtomsAreVarsOrLzero
#assert_no_axioms FX1Poly.Universe.LevelExpr.AllAtomsAreVarsOrLzero_append
#assert_no_axioms FX1Poly.Universe.LevelExpr.lmaxAtoms_allVarsOrLzero_of_isVariableJoin
#assert_no_axioms FX1Poly.Universe.LevelExpr.AllAtomsAreVarsOrLzero_insertByCompare
#assert_no_axioms FX1Poly.Universe.LevelExpr.AllAtomsAreVarsOrLzero_insertionSortByCompare
#assert_no_axioms FX1Poly.Universe.LevelExpr.AllAtomsAreVarsOrLzero_dedupAdjacent
#assert_no_axioms FX1Poly.Universe.LevelExpr.AllAtomsAreVariables_dropLzeroAtoms
#assert_no_axioms FX1Poly.Universe.LevelExpr.canonicalAtoms_allVariables_of_isVariableJoin
#assert_no_axioms FX1Poly.Universe.LevelExpr.canonicalize_eq_of_denoteEquiv_of_isVariableJoin
#assert_no_axioms FX1Poly.Universe.LevelExpr.denoteEquiv_of_canonicalize_eq
#assert_no_axioms FX1Poly.Universe.LevelExpr.decidableDenoteEquivOfVariableJoin
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.denoteVarOffsets
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.denote
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.incrementOffsets
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.shiftSucc
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.denoteVarOffsets_incrementOffsets_shift
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.shiftSucc_denote
#assert_no_axioms FX1Poly.Universe.LevelExpr.levelMax_interchange
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.denoteVarOffsets_append
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.merge
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.merge_denote
#assert_no_axioms FX1Poly.Universe.LevelExpr.and_eq_true_imp_left
#assert_no_axioms FX1Poly.Universe.LevelExpr.and_eq_true_imp_right
#assert_no_axioms FX1Poly.Universe.LevelExpr.isPredicative
#assert_no_axioms FX1Poly.Universe.LevelExpr.isPredicative_lmax_smoke
#assert_no_axioms FX1Poly.Universe.LevelExpr.isPredicative_limax_smoke
#assert_no_axioms FX1Poly.Universe.LevelExpr.toMaxPlusForm
#assert_no_axioms FX1Poly.Universe.LevelExpr.toMaxPlusForm_denote
#assert_no_axioms FX1Poly.Universe.LevelExpr.levelMax_add_left_distrib
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.denoteVarOffsets_swap_adjacent
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.denoteVarOffsets_absorb_adjacent
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.insertByVariable
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.denoteVarOffsets_insertByVariable
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.sortByVariable
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.denoteVarOffsets_sortByVariable
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.absorbFrom
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.denoteVarOffsets_absorbFrom
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.absorbAdjacent
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.denoteVarOffsets_absorbAdjacent
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.canonicalizeVarOffsets
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.denoteVarOffsets_canonicalizeVarOffsets
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.canonicalize
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.canonicalize_denote
#assert_no_axioms FX1Poly.Universe.LevelExpr.canonicalize_toMaxPlusForm_denote
#assert_no_axioms FX1Poly.Universe.LevelExpr.levelMax_offset_dominatedRight
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.maxOffset
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.maxOffset_dominated
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.normalizeBase
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.normalizeBase_denote
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.fullCanonicalize
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.fullCanonicalize_denote
#assert_no_axioms FX1Poly.Universe.LevelExpr.fullCanonicalize_toMaxPlusForm_denote
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.zeroEnvironment
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.denoteVarOffsets_zeroEnvironment
#assert_no_axioms FX1Poly.Universe.LevelExpr.levelMax_reabsorb_right
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.normalizeBase_baseConstant_eq_denote_zeroEnvironment
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.allVariablesAtLeast
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.isSortedByVariable
#assert_no_axioms FX1Poly.Universe.LevelExpr.and_eq_true_of_both
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.insertByVariable_preserves_allVariablesAtLeast
#assert_no_axioms FX1Poly.Universe.LevelExpr.ble_trans
#assert_no_axioms FX1Poly.Universe.LevelExpr.ble_false_swap
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.allVariablesAtLeast_mono
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.insertByVariable_preserves_isSortedByVariable
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.sortByVariable_produces_sorted
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.isStrictlySortedByVariable
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.absorbFrom_preserves_allVariablesAtLeast
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.absorbAdjacent_preserves_allVariablesAtLeast
#assert_no_axioms FX1Poly.Universe.LevelExpr.ble_succ_of_beq_false_of_ble
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.absorbFrom_strictlySorted
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.absorbAdjacent_produces_strictlySorted
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.canonicalizeVarOffsets_produces_strictlySorted
#assert_no_axioms FX1Poly.Universe.LevelExpr.or_eq_false_imp_left
#assert_no_axioms FX1Poly.Universe.LevelExpr.or_eq_false_imp_right
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.scaledPointEnvironment
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.occursAsVariable
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.denoteVarOffsets_scaledPointEnvironment_of_not_occurs
#assert_no_axioms FX1Poly.Universe.LevelExpr.levelMax_eq_left_of_right_le
#assert_no_axioms FX1Poly.Universe.LevelExpr.levelMax_eq_right_of_left_le
#assert_no_axioms FX1Poly.Universe.LevelExpr.beq_false_of_ble_succ
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.allVariablesAtLeast_imp_not_occurs
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.offsetOf
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.denoteVarOffsets_scaledPointEnvironment_of_occurs
#assert_no_axioms FX1Poly.Universe.LevelExpr.beq_self
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.lookupOffset
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.lookupOffset_cons_self
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.lookupOffset_cons_of_beq_false
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.lookupOffset_eq_none_of_allVariablesAtLeast
#assert_no_axioms FX1Poly.Universe.LevelExpr.ble_antisymm
#assert_no_axioms FX1Poly.Universe.LevelExpr.ble_succ_le_of_ble_false
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.lookupOffset_pointwise_tail
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.lookupOffset_ext
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.lookupOffset_eq_none_of_not_occurs
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.lookupOffset_eq_some_offsetOf_of_occurs
#assert_no_axioms FX1Poly.Universe.LevelExpr.levelMax_le
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.denote_scaledPointEnvironment_of_occurs
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.denote_scaledPointEnvironment_of_not_occurs
#assert_no_axioms FX1Poly.Universe.LevelExpr.add_left_cancel
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.lookupOffset_of_denote_eq
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.canonicalForm_unique
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.fullCanonicalize_isStrictlySortedByVariable
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.fullCanonicalize_baseConstant_eq_denote_zeroEnvironment
#assert_no_axioms FX1Poly.Universe.LevelExpr.denoteEquiv_iff_fullCanonicalize_eq
#assert_no_axioms FX1Poly.Universe.LevelExpr.decideDenoteEquiv
#assert_no_axioms FX1Poly.Universe.LevelExpr.smoke_denoteEquiv_idempotentDedup
#assert_no_axioms FX1Poly.Universe.LevelExpr.smoke_denoteEquiv_leftUnitLzero
#assert_no_axioms FX1Poly.Universe.LevelExpr.smoke_denoteEquiv_rightUnitLzero
#assert_no_axioms FX1Poly.Universe.LevelExpr.smoke_denoteEquiv_commutativeMax
#assert_no_axioms FX1Poly.Universe.LevelExpr.smoke_denoteEquiv_associativeMax
#assert_no_axioms FX1Poly.Universe.LevelExpr.smoke_denoteEquiv_succDominatesVar
#assert_no_axioms FX1Poly.Universe.LevelExpr.smoke_denoteEquiv_succAbsorbsBareVar
#assert_no_axioms FX1Poly.Universe.LevelExpr.smoke_denoteEquiv_constantCollapse
#assert_no_axioms FX1Poly.Universe.LevelExpr.smoke_denoteEquiv_succZeroDominates
#assert_no_axioms FX1Poly.Universe.LevelExpr.smoke_denoteEquiv_nestedDedupReorder
#assert_no_axioms FX1Poly.Universe.LevelExpr.smoke_denoteEquiv_threeVariableSort
#assert_no_axioms FX1Poly.Universe.LevelExpr.smoke_denoteEquiv_constVarCommute
#assert_no_axioms FX1Poly.Universe.LevelExpr.smoke_notDenoteEquiv_distinctVars
#assert_no_axioms FX1Poly.Universe.LevelExpr.smoke_notDenoteEquiv_varVsSucc
#assert_no_axioms FX1Poly.Universe.LevelExpr.predicativeSmokeCorpus
#assert_no_axioms FX1Poly.Universe.LevelExpr.predicativeSmokeCorpus_count
#assert_no_axioms FX1Poly.Universe.LevelExpr.predicativeSmokeCorpus_behavior
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.length_append
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.incrementOffsets_length
#assert_no_axioms FX1Poly.Universe.LevelExpr.toMaxPlusForm_varOffsets_length_le_size
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.insertByVariable_length
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.sortByVariable_length
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.absorbFrom_length_le
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.absorbAdjacent_length_le
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.canonicalizeVarOffsets_length_le
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.fullCanonicalize_toMaxPlusForm_varOffsets_length_le_size
#assert_no_axioms FX1Poly.Universe.LevelExpr.decidableOccursIn

/-! ### Complexity witness — single-pass comparison-count costs -/

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.insertByVariableSteps
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.insertByVariableSteps_le_length
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.absorbFromSteps
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.absorbFromSteps_le_length
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.absorbAdjacentSteps
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.absorbAdjacentSteps_le_length

/-! ### Complexity witness — quadratic sort accumulation -/

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.sortByVariableSteps
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.mulSelf_add_self_le_succ_mul_succ
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.sortByVariableSteps_le

/-! ### Complexity witness — total offset-canonicalizer cost -/

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.canonicalizeVarOffsetsSteps
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.canonicalizeVarOffsetsSteps_le
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.canonicalizeVarOffsetsSteps_toMaxPlusForm_le_size

/-! ### Complexity witness — END-TO-END fullCanonicalize cost (canonicalize + normalizeBase fold), QUADRATIC -/

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.maxOffsetSteps
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.maxOffsetSteps_eq_length
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.fullCanonicalizeSteps
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.fullCanonicalizeSteps_toMaxPlusForm_le_size
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.maxOffsetSteps_smoke_twoEntries

/-! ### Complexity witness — cost-counter non-vacuity corpus -/

#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.insertByVariableSteps_smoke_empty
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.insertByVariableSteps_smoke_stopAtHead
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.insertByVariableSteps_smoke_walkToEnd
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.sortByVariableSteps_smoke_reversedPair
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.sortByVariableSteps_smoke_reversedTriple
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.absorbFromSteps_smoke_fuseThenSkip
#assert_no_axioms FX1Poly.Universe.LevelExpr.MaxPlusForm.canonicalizeVarOffsetsSteps_smoke_reversedPair

/-! ### LevelExpr prefix serializer + round-trip

The `LevelExpr → List Nat` prefix encoder (accumulator form, no list
concatenation), its fuel-bounded decoder, and the round-trip left-inverse
proof at the natural `nodeCount` fuel.  Feeds the FX0 certificate format
and the universe-payload serializer. -/

#assert_no_axioms FX1Poly.Universe.LevelExpr.nodeCount
#assert_no_axioms FX1Poly.Universe.LevelExpr.encodeOnto
#assert_no_axioms FX1Poly.Universe.LevelExpr.encodePrefix
#assert_no_axioms FX1Poly.Universe.LevelExpr.decodeOnto
#assert_no_axioms FX1Poly.Universe.LevelExpr.decodeOnto_encodeOnto_lsucc
#assert_no_axioms FX1Poly.Universe.LevelExpr.decodeOnto_encodeOnto_lmax
#assert_no_axioms FX1Poly.Universe.LevelExpr.decodeOnto_encodeOnto_limax
#assert_no_axioms FX1Poly.Universe.LevelExpr.decodeOnto_encodeOnto
#assert_no_axioms FX1Poly.Universe.LevelExpr.decodeOnto_nodeCount_encodePrefix

/-! ### UniverseFlag prefix serializer + round-trip

The `UniverseFlag → List Nat` flat tag encoder, its fuel-free decoder, and
the `cases`-+-`rfl` round-trip.  Companion to the LevelExpr serializer; the
two together feed the universe-payload (`LevelExpr × UniverseFlag`)
serializer. -/

#assert_no_axioms FX1Poly.Universe.UniverseFlag.encodeOnto
#assert_no_axioms FX1Poly.Universe.UniverseFlag.encodePrefix
#assert_no_axioms FX1Poly.Universe.UniverseFlag.decode
#assert_no_axioms FX1Poly.Universe.UniverseFlag.decode_encodeOnto
#assert_no_axioms FX1Poly.Universe.UniverseFlag.decode_encodePrefix

/-! ### Universe-payload (`LevelExpr × UniverseFlag`) serializer

Composes the LevelExpr and UniverseFlag serializers into the
universe-payload serializer — the function the `gen_universeCode`
payload-serializer arm calls for a `LevelExpr × UniverseFlag` payload.
Round-trip at LevelExpr fuel. -/

#assert_no_axioms FX1Poly.Universe.UniversePayload.encodeOnto
#assert_no_axioms FX1Poly.Universe.UniversePayload.encodePrefix
#assert_no_axioms FX1Poly.Universe.UniversePayload.decodeOnto
#assert_no_axioms FX1Poly.Universe.UniversePayload.decodeOnto_encodeOnto_reduce
#assert_no_axioms FX1Poly.Universe.UniversePayload.decodeOnto_encodeOnto
#assert_no_axioms FX1Poly.Universe.UniversePayload.decodeOnto_nodeCount_encodePrefix

/-! ### UNIVERSE-FLAG CONSISTENCY-STRENGTH TOTAL ORDER (the Setzer-Rathjen ladder, §11.8.2 / §3.16.3).
    The decidable total order on universe admission predicates: `strengthBand`/`strengthDegree`
    lexicographic rank (placing unbounded `nMahlo`/`indescribable` between fixed neighbours), its injective
    left inverse, the `LE` + `Decidable` instances, the four order laws, and the ladder non-degeneracy
    smokes.  Realizes the spec's "strictly stronger admission predicate" + "admission decidable in O(flag
    enum position)" as theorems. -/
#assert_no_axioms FX1Poly.Universe.UniverseFlag.strengthBand
#assert_no_axioms FX1Poly.Universe.UniverseFlag.strengthDegree
#assert_no_axioms FX1Poly.Universe.UniverseFlag.decodeStrengthRank_strength
#assert_no_axioms FX1Poly.Universe.UniverseFlag.eq_of_strengthRank
#assert_no_axioms FX1Poly.Universe.UniverseFlag.le
#assert_no_axioms FX1Poly.Universe.UniverseFlag.le_refl
#assert_no_axioms FX1Poly.Universe.UniverseFlag.le_trans
#assert_no_axioms FX1Poly.Universe.UniverseFlag.le_antisymm
#assert_no_axioms FX1Poly.Universe.UniverseFlag.le_total
#assert_no_axioms FX1Poly.Universe.UniverseFlag.standard_le_vopenka
#assert_no_axioms FX1Poly.Universe.UniverseFlag.not_vopenka_le_standard
#assert_no_axioms FX1Poly.Universe.UniverseFlag.nMahlo_le_hyperMahlo
#assert_no_axioms FX1Poly.Universe.UniverseFlag.nMahlo_mono
