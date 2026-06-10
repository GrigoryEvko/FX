import FX1PolyAudit.DependencyAudit
import FX1Poly.Universe.LevelExpr
import FX1Poly.Universe.UniverseFlag
import FX1Poly.Universe.UniverseFlagStrength
import FX1Poly.Universe.LevelExprSimplify
import FX1Poly.Universe.LevelExprSerialize
import FX1Poly.Universe.UniverseFlagSerialize
import FX1Poly.Universe.UniversePayloadSerialize
import FX1Poly.Universe.LevelExprImpredicativeClosure
import FX1Poly.Universe.LevelExprComplexity

/-! # FX1PolyAudit/AuditUniverseLevelAlgebra03 — universe-layer zero-axiom gates, shard 3 of 3
(split from the AuditUniverse monolith for parallel gate elaboration; the full import block is preserved verbatim so the per-decl `#assert_no_axioms` gates resolve every universe-layer name). -/

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

/-! ### Complexity witness — level-equivalence DECIDER capstone (quadratic, the tractability certificate) -/

#assert_no_axioms FX1Poly.Universe.LevelExpr.decideDenoteEquivSteps
#assert_no_axioms FX1Poly.Universe.LevelExpr.decideDenoteEquivSteps_le_size

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

/-! ### LevelExprComplexity — the M22-A11 STRICT-COMPLEXITY witness (DecisionComplexity instance)

The level decider's shadow comparison counter packaged through the generic `DecisionComplexity`
schema with the machine-checked HONEST quadratic bound `≤ 4·(size² + size²) + 4` (the sort is an
insertion sort — degree 2 is the real worst case, not an `O(n·log n)` overclaim). -/

#assert_no_axioms FX1Poly.Universe.pow_one_eq_self
#assert_no_axioms FX1Poly.Universe.addSelf_le_mulSelf_add_two
#assert_no_axioms FX1Poly.Universe.mulSelf_add_self_add_self_le_doubleSquare
#assert_no_axioms FX1Poly.Universe.addSelf_add_addSelf_eq_four_mul
#assert_no_axioms FX1Poly.Universe.add_two_add_add_two_eq_add_four
#assert_no_axioms FX1Poly.Universe.LevelExpr.decideDenoteEquivSteps_isPolynomial
#assert_no_axioms FX1Poly.Universe.levelDenoteEquivDecisionComplexity
#assert_no_axioms FX1Poly.Universe.levelDenoteEquivDecisionComplexity_stepCount_smoke
#assert_no_axioms FX1Poly.Universe.levelDenoteEquivDecisionComplexity_stepCount_smoke_larger
