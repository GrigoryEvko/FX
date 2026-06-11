import FX1PolyAudit.DependencyAudit
import FX1Poly.Modal.ResourceGraded
import FX1Poly.Modal.GradeVector
import FX1Poly.Modal.GradeVectorGeneric
import FX1Poly.Modal.UsageDiscipline
import FX1Poly.Modal.GradedTypingGeneric
import FX1Poly.Modal.GradedBinaryParametricity
import FX1Poly.Modal.GradedGradeExactness
import FX1Poly.Modal.GradeErasureGeneric
import FX1Poly.Modal.GradedWeakeningGeneric
import FX1Poly.Modal.GradedSubstitutionGeneric
import FX1Poly.Modal.GradedSubjectReductionGeneric
import FX1Poly.Modal.GradedCompositionGeneric
import FX1Poly.Modal.GradeSemiringProduct
import FX1Poly.Modal.GradeSemiringMonoidal
import FX1Poly.Modal.GradeSemiringFunctorial
import FX1Poly.Modal.SimpleStrongNormalization
import FX1Poly.Modal.GradedSubstitutionAlgebra
import FX1Poly.Modal.GradedReductionSubstitution
import FX1Poly.Modal.GradedFundamentalTheorem
import FX1Poly.Modal.GradedReductionConfluence
import FX1Poly.Modal.GradedNormalization
import FX1Poly.Modal.ComplexitySemiring
import FX1Poly.Modal.EffectLatticeClassification
import FX1Poly.Modal.OverflowLatticeDimension
import FX1Poly.Modal.PrecisionOverflowCollision
import FX1Poly.Modal.SoundnessCollisionSchema
import FX1Poly.Modal.ThreeWayCollisionClassifiedAsyncSession
import FX1Poly.Modal.FlagshipMultiDimensionSignature
import FX1Poly.Modal.SoundnessCollisionCatalog
import FX1Poly.Modal.SoundnessCollisionCatalogComplete
import FX1Poly.Modal.BoundedJoinSemilatticeUniversal
import FX1Poly.Modal.BoundedJoinSemilatticeProductOrder
import FX1Poly.Modal.UnifiedGradeMonoid
import FX1Poly.Modal.FractionalPermission
import FX1Poly.Modal.ClockDomainLatticeDimension
import FX1Poly.Modal.ProvenanceLatticeDimension
import FX1Poly.Modal.MutationChainLatticeDimension
import FX1Poly.Modal.PreorderDimension
import FX1Poly.Modal.DimensionRepetitionContrast
import FX1Poly.Modal.DimensionMultiplicationContrast
import FX1Poly.Modal.LatticeDistributivityClassification
import FX1Poly.Modal.SessionDualityDimension
import FX1Poly.Modal.SessionCommunication
import FX1Poly.Modal.SelfApplicationUntypable
import FX1Poly.Modal.GradedProgress
import FX1Poly.Modal.GradedEvaluation
import FX1Poly.Modal.GradedLogicalConsistency
import FX1Poly.Modal.VersionCategoryDimension
import FX1Poly.Modal.GradedNormalizerValue

/-! # FX1PolyAudit/AuditModalGradedSubstitution — modal/dimension-layer zero-axiom gates, shard 3 of 4 (split from the AuditModal monolith for parallel gate elaboration) -/

/-! ### Generic substitution + β subject reduction for HasGradeOver R (security + dims 6–21)

The headline of the generic reduction metatheory: substituting at a cut preserves typing with the grade
vector transformed by `substInto`, and β `(λ.body) arg ↝ body[0:=arg]` preserves typing AND the EXACT
grade vector — the corrected Wood/Atkey App scaling making the judgment sound under reduction, for ANY
dimension R.  The security witness exercises β SR in a second dimension. -/

#assert_no_axioms FX1Poly.Modal.hasGradeOver_substitution
#assert_no_axioms FX1Poly.Modal.hasGradeOver_betaPreservation
#assert_no_axioms FX1Poly.Modal.securityBeta_smoke

/-! ### Generic composition ledger for HasGradeOver R (security + dims 6–21)

Graded subject reduction over the FULL β-reduction `Reduces`, and the metatheory bundle (SN ∧ graded-SR
on the same relation, for any dimension R).  The usage ω-witness routes the decisive `ρ + r·σ` regression
(r=ω) through the GENERIC preservedByReduces.  Mirrors the usage `GradedComposition`; completes the
generic reduction metatheory (semiring → vector → judgment → erasure+SN → weakening → substInto →
subst+β-SR → composition). -/

#assert_no_axioms FX1Poly.Modal.HasGradeOver.preservedByReduces
#assert_no_axioms FX1Poly.Modal.HasGradeOver.metatheoryBundle
#assert_no_axioms FX1Poly.Modal.appliedIdentityOver_typed
#assert_no_axioms FX1Poly.Modal.appliedIdentityOver_reductKeepsGrade
#assert_no_axioms FX1Poly.Modal.securityAppliedIdentity_reductKeepsGrade
#assert_no_axioms FX1Poly.Modal.usageAppliedIdentity_reductKeepsGrade
#assert_no_axioms FX1Poly.Modal.securityMetatheoryBundle_smoke
#assert_no_axioms FX1Poly.Modal.omegaScalingBinaryTypeUsage
#assert_no_axioms FX1Poly.Modal.usageOmegaScalingRedex_typed
#assert_no_axioms FX1Poly.Modal.usageOmegaScalingRedex_reductKeepsGrade

/-! ### Grade-free simple typing: the type dimension underneath the graded judgments -/

#assert_no_axioms FX1Poly.Modal.SimpleType
#assert_no_axioms FX1Poly.Modal.SimpleType.lookup
#assert_no_axioms FX1Poly.Modal.HasSimpleType

/-! ### STLC strong normalization substrate: β-reduction + Acc-SN + structural lemmas -/

#assert_no_axioms FX1Poly.Modal.GradedLambda.Reduces
#assert_no_axioms FX1Poly.Modal.GradedLambda.IsStronglyNormalizing
#assert_no_axioms FX1Poly.Modal.GradedLambda.IsNeutral
#assert_no_axioms FX1Poly.Modal.GradedLambda.IsStronglyNormalizing.var
#assert_no_axioms FX1Poly.Modal.GradedLambda.IsStronglyNormalizing.ofAppLeft
#assert_no_axioms FX1Poly.Modal.GradedLambda.IsStronglyNormalizing.ofAppRight
#assert_no_axioms FX1Poly.Modal.GradedLambda.IsStronglyNormalizing.ofLam
#assert_no_axioms FX1Poly.Modal.GradedLambda.IsStronglyNormalizing.ofReduces

/-! ### Tait reducibility candidates: Reducible + CR1/CR2/CR3 -/

#assert_no_axioms FX1Poly.Modal.GradedLambda.Reducible
#assert_no_axioms FX1Poly.Modal.GradedLambda.reducibilityConditions
#assert_no_axioms FX1Poly.Modal.GradedLambda.Reducible.sn
#assert_no_axioms FX1Poly.Modal.GradedLambda.Reducible.ofReduces
#assert_no_axioms FX1Poly.Modal.GradedLambda.Reducible.ofNeutral
#assert_no_axioms FX1Poly.Modal.GradedLambda.Reducible.var

/-! ### Parallel-substitution σ-algebra: renaming + substitution fusion laws

The funext-free de Bruijn substitution infrastructure for the STLC-SN fundamental theorem: a renaming
sublayer makes `lift` compose definitionally, and the four σ-monoid fusion laws + identity drop out
by structural induction with pointwise-agreement congruences (never `funext`/`Quot.sound`). -/

#assert_no_axioms FX1Poly.Modal.incrementIndex
#assert_no_axioms FX1Poly.Modal.liftRenaming
#assert_no_axioms FX1Poly.Modal.GradedLambda.renameTerm
#assert_no_axioms FX1Poly.Modal.liftSubstitution
#assert_no_axioms FX1Poly.Modal.GradedLambda.applySubstitution
#assert_no_axioms FX1Poly.Modal.GradedLambda.renameTerm_congr
#assert_no_axioms FX1Poly.Modal.GradedLambda.applySubstitution_congr
#assert_no_axioms FX1Poly.Modal.GradedLambda.renameTerm_renameTerm
#assert_no_axioms FX1Poly.Modal.GradedLambda.applySubstitution_renameTerm
#assert_no_axioms FX1Poly.Modal.GradedLambda.renameTerm_applySubstitution
#assert_no_axioms FX1Poly.Modal.GradedLambda.applySubstitution_applySubstitution
#assert_no_axioms FX1Poly.Modal.GradedLambda.applySubstitution_id

/-! ### Reduction is substitutive: kernel substAt/shift bridge + Reduces.substAt

The kernel `shift`/`substAt` bridged to the σ-algebra, the β-composition (★), and the abstraction-
lemma engine `Reduces.substAt` (single-step β preserved under substitution) + SN-reflection.  Going
through the σ-algebra (rather than a direct de Bruijn substitution-swap) keeps it short: `lift`
composition handles the binder bookkeeping once. -/

#assert_no_axioms FX1Poly.Modal.shiftRenaming
#assert_no_axioms FX1Poly.Modal.shift_eq_renameTerm
#assert_no_axioms FX1Poly.Modal.shift_zero_eq_renameTerm
#assert_no_axioms FX1Poly.Modal.singleSubstitution
#assert_no_axioms FX1Poly.Modal.substAt_eq_applySubstitution
#assert_no_axioms FX1Poly.Modal.consSubstitution
#assert_no_axioms FX1Poly.Modal.substAt_zero_applySubstitution_lift
#assert_no_axioms FX1Poly.Modal.GradedLambda.Reduces.applySubstitution
#assert_no_axioms FX1Poly.Modal.GradedLambda.Reduces.substAt
#assert_no_axioms FX1Poly.Modal.GradedLambda.IsStronglyNormalizing.ofSubstAt

/-! ### Tait SN: the STLC fundamental theorem

The STLC fundamental theorem (abstraction lemma → fundamental → every well-typed term reducible →
SN) proved ONCE.  Graded-SN transfers from this type-dimension SN through grade erasure with no
graded-reducibility re-proof — for ANY dimension R, via the generic `HasGradeOver.stronglyNormalizing`
gated in the generic erasure section above. -/

#assert_no_axioms FX1Poly.Modal.GradedLambda.IsStronglyNormalizing.lam
#assert_no_axioms FX1Poly.Modal.GradedLambda.Reducible.abstraction
#assert_no_axioms FX1Poly.Modal.ReducibleSubstitution
#assert_no_axioms FX1Poly.Modal.ReducibleSubstitution.cons
#assert_no_axioms FX1Poly.Modal.HasSimpleType.fundamental
#assert_no_axioms FX1Poly.Modal.HasSimpleType.reducible
#assert_no_axioms FX1Poly.Modal.HasSimpleType.stronglyNormalizing

/-! ### Binary parametricity over the grade discipline (OP1-M0)

The binary logical relation `ParametricRel` over the GRADED types, the fundamental theorem over the
GRADED judgment `HasGradeOver R` (the binder grade flows through inertly — the Milestone-0 GO
verdict), the closed abstraction theorem, and the linear-usage free-theorem demonstration (every
closed `base -(1)-> base` function over the usage semiring maps β-joinable arguments to β-joinable
results).  The grade-AWARE relation-scaling refinement is OP1-M1. -/

#assert_no_axioms FX1Poly.Modal.RespectsExpansion
#assert_no_axioms FX1Poly.Modal.ParametricRel
#assert_no_axioms FX1Poly.Modal.ParametricRel.expandLeft
#assert_no_axioms FX1Poly.Modal.ParametricRel.expandRight
#assert_no_axioms FX1Poly.Modal.ParametricSubstitution
#assert_no_axioms FX1Poly.Modal.ParametricSubstitution.cons
#assert_no_axioms FX1Poly.Modal.HasGradeOver.parametric
#assert_no_axioms FX1Poly.Modal.HasGradeOver.parametricClosed
#assert_no_axioms FX1Poly.Modal.joinabilityRespectsExpansion
#assert_no_axioms FX1Poly.Modal.linearUsageFunction_mapsJoinable

-- The usage composition ledger (graded-SR over full β + the SN∧graded-SR metatheory bundle + the ω-scaling
-- regression witnesses) is subsumed by the GENERIC HasGradeOver.preservedByReduces / .metatheoryBundle +
-- the usage{Applied,OmegaScaling}* witnesses gated in the generic composition section above.

/-! ### β-confluence infrastructure: reduction-substitutivity for GradedLambda

Part of the full reference STLC (SN + SR + confluence → unique NF).  Reduction under renaming/shift (via
`Reduces.applySubstitution`), multi-step congruence closures, and argument-substitutivity — the inputs to
the local-confluence critical-pair analysis. -/

#assert_no_axioms FX1Poly.Modal.GradedLambda.renameTerm_eq_applySubstitution_var
#assert_no_axioms FX1Poly.Modal.GradedLambda.Reduces.renameTerm
#assert_no_axioms FX1Poly.Modal.GradedLambda.Reduces.shift
#assert_no_axioms FX1Poly.Modal.GradedLambda.ReducesStar.congLam
#assert_no_axioms FX1Poly.Modal.GradedLambda.ReducesStar.congAppLeft
#assert_no_axioms FX1Poly.Modal.GradedLambda.ReducesStar.congAppRight
#assert_no_axioms FX1Poly.Modal.GradedLambda.Reduces.substReducedArg

/-! ### β-confluence: local confluence + Newman → confluence on the typed fragment

The 9-case β critical-pair analysis (`WeaklyConfluent Reduces`), then the relation-generic `newmanAux`
(per-term `Acc` = `IsStronglyNormalizing`) gives confluence on the SN fragment — and hence on every
well-simply-typed `GradedLambda` term (SN from the Tait fundamental theorem). -/

#assert_no_axioms FX1Poly.Modal.GradedLambda.Reduces.localConfluent
#assert_no_axioms FX1Poly.Modal.GradedLambda.Reduces.weaklyConfluent
#assert_no_axioms FX1Poly.Modal.GradedLambda.IsStronglyNormalizing.confluent
#assert_no_axioms FX1Poly.Modal.HasSimpleType.confluent

/-! ### Unique normal forms

Confluence + "a normal form admits no step" ⟹ a strongly-normalizing term has at most one β-NF; hence
every well-simply-typed `GradedLambda` term has a unique normal form (the bridge to decidable
conversion). -/

#assert_no_axioms FX1Poly.Modal.GradedLambda.IsNormalForm
#assert_no_axioms FX1Poly.Modal.GradedLambda.var_isNormalForm
#assert_no_axioms FX1Poly.Modal.GradedLambda.IsNormalForm.eq_of_reducesStar
#assert_no_axioms FX1Poly.Modal.GradedLambda.IsStronglyNormalizing.uniqueNormalForm
#assert_no_axioms FX1Poly.Modal.HasSimpleType.uniqueNormalForm

/-! ### The verified β-normalizer

`stepOrNormal` (β-progress: every term steps-with-witness or is normal) drives `normalize` via `Acc.rec`
on the SN accessibility, producing the unique β-NF bundled with `ReducesStar` reachability and
`IsNormalForm` irreducibility — toward decidable conversion (`normalize a = normalize b`). -/

#assert_no_axioms FX1Poly.Modal.GradedLambda.lam_isNormalForm
#assert_no_axioms FX1Poly.Modal.GradedLambda.var_app_isNormalForm
#assert_no_axioms FX1Poly.Modal.GradedLambda.app_app_isNormalForm
#assert_no_axioms FX1Poly.Modal.GradedLambda.stepOrNormal
#assert_no_axioms FX1Poly.Modal.GradedLambda.normalizeWithProof
#assert_no_axioms FX1Poly.Modal.GradedLambda.normalize
#assert_no_axioms FX1Poly.Modal.GradedLambda.normalize_reducesStar
#assert_no_axioms FX1Poly.Modal.GradedLambda.normalize_isNormalForm

/-! ### Decidable β-conversion (completes the substrate)

Conversion (`Joinable Reduces`) = normal-form equality on the SN fragment, so it is decidable via
`GradedLambda`'s `DecidableEq` on normal forms.  Every well-simply-typed term pair has decidable
convertibility — the GradedLambda STLC is a full reference calculus with decidable definitional
equality. -/

#assert_no_axioms FX1Poly.Modal.GradedLambda.IsStronglyNormalizing.ofReducesStar
#assert_no_axioms FX1Poly.Modal.GradedLambda.normalize_of_isNormalForm
#assert_no_axioms FX1Poly.Modal.GradedLambda.joinable_iff_normalize_eq
#assert_no_axioms FX1Poly.Modal.GradedLambda.decidableJoinable
#assert_no_axioms FX1Poly.Modal.HasSimpleType.decidableConv
#assert_no_axioms FX1Poly.Modal.GradedLambda.var_notJoinable_of_ne

/-! ### β-conversion is an equivalence relation (definitional-equality justification)

`Joinable Reduces` is reflexive + symmetric unconditionally, transitive when the middle term is SN
(confluence), and contains reduction — a genuine decidable equivalence on the typed fragment. -/

#assert_no_axioms FX1Poly.Modal.GradedLambda.Reduces.joinable_refl
#assert_no_axioms FX1Poly.Modal.GradedLambda.Reduces.joinable_symm
#assert_no_axioms FX1Poly.Modal.GradedLambda.ReducesStar.joinable
#assert_no_axioms FX1Poly.Modal.GradedLambda.IsStronglyNormalizing.joinable_trans
#assert_no_axioms FX1Poly.Modal.GradedLambda.Reduces.beta_joinable
#assert_no_axioms FX1Poly.Modal.HasSimpleType.joinable_trans

/-! ## §6.4 separation-logic permission algebra — the first PARTIAL grade structure (`FractionalPermission`)

§6.4 makes separation logic an instance of the usage grade: ownership is a fractional share `Frac of p :
rational {0 < p ≤ 1}`, and `Frac(p) + Frac(q) = Frac(p+q)` when `p+q ≤ 1`, else CONFLICT (over-allocation).
This is the FIRST partial grade structure (the shipped graded dims are total ordered semirings / bounded
join-semilattices).  `Permission` (carrier) + the guarded partial `add` + the unguarded buggy `naiveAdd` +
`fitsWhole`; the lawful-monoid fragment (`zero_add` / `add_zero` / `conflict_add` / `add_conflict` /
`add_comm`); the SOUNDNESS theorem `add_neverOverallocates` (combining two fitting shares never yields an
over-full share — the guard prevents over-allocation); and the §27.2 / Boyland-2003 over-allocation BUG
(`naiveAddOverallocates` / `naiveOverallocationDoesNotFit`) vs its REJECTION
(`soundAddRejectsOverallocation`).  ASSOCIATIVITY-where-defined (`add_assoc`, gated by positive outer
denominators `hasPositiveDenom`) closes the fractional core into a genuine lawful PARTIAL commutative monoid
— proved by a triple normal-form argument (both association orders reduce to `bif (triple fits) then triple
else conflict`), with a non-vacuity smoke (`add_assoc_smoke`, `1/4+1/4+1/4`).  All propext-free
(full-enumeration matches, Bool-`bif` guard, `Nat.add_comm`/`Nat.mul_comm`, `injection`/`noConfusion`, `rfl`
witnesses; the cross-multiplied Nat algebra reuses `ComplexitySemiring`'s clean `natMulAssoc`/`natRightDistrib`
— `Nat.mul_assoc`/right-`Nat.add_mul` themselves leak propext). -/

#assert_no_axioms FX1Poly.Modal.Permission.fitsWhole
#assert_no_axioms FX1Poly.Modal.Permission.add
#assert_no_axioms FX1Poly.Modal.Permission.naiveAdd
#assert_no_axioms FX1Poly.Modal.Permission.zero_add
#assert_no_axioms FX1Poly.Modal.Permission.add_zero
#assert_no_axioms FX1Poly.Modal.Permission.conflict_add
#assert_no_axioms FX1Poly.Modal.Permission.add_conflict
#assert_no_axioms FX1Poly.Modal.Permission.add_comm
#assert_no_axioms FX1Poly.Modal.Permission.add_neverOverallocates
#assert_no_axioms FX1Poly.Modal.Permission.naiveAddOverallocates
#assert_no_axioms FX1Poly.Modal.Permission.naiveOverallocationDoesNotFit
#assert_no_axioms FX1Poly.Modal.Permission.soundAddRejectsOverallocation
#assert_no_axioms FX1Poly.Modal.Permission.fracExactlyFullAdmitted
#assert_no_axioms FX1Poly.Modal.Permission.fracExactlyFullFits
#assert_no_axioms FX1Poly.Modal.Permission.fracPartialAdmitted
#assert_no_axioms FX1Poly.Modal.Permission.hasPositiveDenom
#assert_no_axioms FX1Poly.Modal.Permission.add_assoc
#assert_no_axioms FX1Poly.Modal.Permission.add_assoc_smoke

/-! ## §6.3 Dim 12 / §18.7 clock-domain dimension — the first PARAMETERIZED (infinite-carrier) lattice
(`ClockDomainLatticeDimension`)

Every prior lattice dimension (effect/trust/security 2-chains, overflow's finite diamond M3) has a FINITE
enum carrier.  The clock domain `{combinational (bottom), sync (clockId : Nat), crossDomainError (top)}` is
the FIRST with an INFINITE carrier, hence the first INFINITE ANTICHAIN (`sync a` / `sync b` pairwise
incomparable for all distinct clocks).  The parameterized `sync`-`sync` join laws need the three propext-clean
`Nat.beq` facts (`natBeqReflexive` / `natEqOfBeqTrue` / `natBeqCommutes`, hand-rolled by structural
recursion); `clockJoinCommutes` / `clockJoinAssociates` route through them (`Bool.cond_true`/`_false` discharge
the guard residues).  `clockSyncIncomparableOfDistinct` is the genuinely-new infinite-antichain content;
`clockOverflowProductIsLawful` composes the infinite-antichain dimension with the finite diamond via the
shipped `productIsLawful` (cardinality-agnostic composition).  All propext-free; the Nat helpers are gated
transitively by the lattice/antichain theorems but listed explicitly for provenance. -/

#assert_no_axioms FX1Poly.Modal.natBeqReflexive
#assert_no_axioms FX1Poly.Modal.natEqOfBeqTrue
#assert_no_axioms FX1Poly.Modal.natBeqCommutes
#assert_no_axioms FX1Poly.Modal.ClockGrade.join
#assert_no_axioms FX1Poly.Modal.clockJoinSyncWithSelf
#assert_no_axioms FX1Poly.Modal.clockLattice
#assert_no_axioms FX1Poly.Modal.clockJoinCommutes
#assert_no_axioms FX1Poly.Modal.clockJoinAssociates
#assert_no_axioms FX1Poly.Modal.clockIsLawfulBoundedJoinSemilattice
#assert_no_axioms FX1Poly.Modal.clockSyncIncomparableOfDistinct
#assert_no_axioms FX1Poly.Modal.clockSyncJoinDistinctIsCrossDomain
#assert_no_axioms FX1Poly.Modal.clockSync01Incomparable
#assert_no_axioms FX1Poly.Modal.clockCombinationalIsLeast
#assert_no_axioms FX1Poly.Modal.clockCrossDomainIsGreatest
#assert_no_axioms FX1Poly.Modal.clockOverflowProductIsLawful

/-! ## §6.3 Dim 18 mutation dimension — the first proper TOTAL-ORDER chain (`MutationChainLatticeDimension`)

Completes the lattice-shape spanning set: alongside the trivial 2-chains (effect/trust/security), the finite
antichain (overflow M3) and the infinite antichain (clock), mutation `immutable < appendOnly < monotonic <
readWrite` is the FIRST proper total-order chain.  Its distinct content is `mutationIsTotalOrder` (every pair
comparable — NO antichain, the structural opposite of overflow/clock); the covering chain + four-distinct
witness a genuine four-element chain; `mutationClockProductIsLawful` composes the proper chain with the
infinite-antichain clock (two opposite order shapes) via the shipped `productIsLawful`.  All finite-enum
`cases <;> rfl` (the total order via `first | Or.inl rfl | Or.inr rfl`), propext-free. -/

#assert_no_axioms FX1Poly.Modal.MutationGrade.join
#assert_no_axioms FX1Poly.Modal.mutationLattice
#assert_no_axioms FX1Poly.Modal.mutationIsLawfulBoundedJoinSemilattice
#assert_no_axioms FX1Poly.Modal.mutationIsTotalOrder
#assert_no_axioms FX1Poly.Modal.mutationImmutableBelowAppendOnly
#assert_no_axioms FX1Poly.Modal.mutationAppendOnlyBelowMonotonic
#assert_no_axioms FX1Poly.Modal.mutationMonotonicBelowReadWrite
#assert_no_axioms FX1Poly.Modal.mutationChainHasFourDistinct
#assert_no_axioms FX1Poly.Modal.mutationImmutableIsLeast
#assert_no_axioms FX1Poly.Modal.mutationReadWriteIsGreatest
#assert_no_axioms FX1Poly.Modal.mutationClockProductIsLawful

/-! ## The PREORDER structural class + §6.3 Dim 7 lifetime (`PreorderDimension`) — the THIRD dimension shape

After the ordered semirings (HasGradeOver) and the bounded join-semilattices (all antisymmetric partial
orders), the preorder is the third structural class FX dimensions take: order-only (le_refl + le_trans), NOT
necessarily antisymmetric.  `PreorderDimension` + the induced equivalence KERNEL (equiv_refl/symm/trans = the
kernel is an equivalence relation) + IsAntisymmetric + product.  `boundedJoinSemilatticeToPreorder` +
`latticePreorderIsAntisymmetric` show every lattice forgets to a PARTIAL order (antisymmetric); the §6.3 Dim7
LIFETIME instance (regions ordered by outlives, static outlives all) is the FIRST dimension that is NOT a
partial order — `lifetimeRegionsEquivalentButDistinct` (distinct equal-extent regions mutually outlive) ⟹
`lifetimeIsNotAntisymmetric`.  Completes FX's dimension structural taxonomy.  All term-proofs over
le_refl/le_trans/le_antisymm + Nat.le_refl/le_trans + injection/noConfusion, propext-free. -/

#assert_no_axioms FX1Poly.Modal.PreorderDimension.equiv
#assert_no_axioms FX1Poly.Modal.PreorderDimension.equiv_refl
#assert_no_axioms FX1Poly.Modal.PreorderDimension.equiv_symm
#assert_no_axioms FX1Poly.Modal.PreorderDimension.equiv_trans
#assert_no_axioms FX1Poly.Modal.PreorderDimension.IsAntisymmetric
#assert_no_axioms FX1Poly.Modal.PreorderDimension.product
#assert_no_axioms FX1Poly.Modal.boundedJoinSemilatticeToPreorder
#assert_no_axioms FX1Poly.Modal.latticePreorderIsAntisymmetric
#assert_no_axioms FX1Poly.Modal.effectInducedPreorderIsAntisymmetric
#assert_no_axioms FX1Poly.Modal.LifetimeGrade.outlives
#assert_no_axioms FX1Poly.Modal.lifetimeOutlivesRefl
#assert_no_axioms FX1Poly.Modal.lifetimeOutlivesTrans
#assert_no_axioms FX1Poly.Modal.lifetimePreorder
#assert_no_axioms FX1Poly.Modal.lifetimeStaticOutlivesAll
#assert_no_axioms FX1Poly.Modal.lifetimeRegionsEquivalentButDistinct
#assert_no_axioms FX1Poly.Modal.lifetimeIsNotAntisymmetric
#assert_no_axioms FX1Poly.Modal.lifetimeProductPreorder

