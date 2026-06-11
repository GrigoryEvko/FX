import FX1Poly.Typed.HasTypeNativeUnionInversion
import FX1Poly.Typed.HasTypeNativeUnionSubstitution
import FX1Poly.Typed.HasTypeNativeUnionSubjectReduction
import FX1Poly.Typed.HasTypeNativeUnionReverseAdequacy
import FX1Poly.Typed.HasTypeNativeUnionTwoPathVerdict
import FX1Poly.Typed.HasTypeNativeUnionMatchInversion
import FX1Poly.Typed.HasTypeNativeUnionPathProjInversion
import FX1Poly.Typed.HasTypeNativeUnionRecursiveInversion
import FX1Poly.Typed.TypedByTableUnion
import FX1Poly.Typed.HasTypeDescPiRootGeneric
import FX1Poly.Typed.HasTypeNativeUnionWeakening

/-! # FX1Poly/Typed/UnionParitySurpassLedger — the honest PARITY-AND-SURPASS ledger for `HasTypeNativeUnion`

The kernel retired ~23 bespoke `HasTypeDesc*` typing engines (graded intro, base type, data intro,
term-indexed former, the per-family data eliminators / introductions, …) and replaced them with ONE
unified judgment `HasTypeNativeUnion` (the embedding arms + the table-driven native arms + the
recursive-eliminator rows + the conversion arm).  This file is the living, machine-anchored gap ledger
answering, capability by capability:

  * **PARITY** — for every metatheory capability ANY bespoke engine carried, does the union have a
    same-or-stronger theorem, witnessed by a CITED decl?
  * **SURPASS** — which capabilities did NO bespoke engine ever have, that the union now carries?

The ledger is HONEST.  A `proven` cell binds a real shipped theorem by reference (the §27.3-L3
cross-reference idiom: the file fails to compile if the cited theorem is renamed/deleted, and each
anchor's `#assert_no_axioms` gate re-certifies that proof is itself zero-axiom).  A `bridged` cell
records that the union's result holds only up to a Conv-modulo classifier or with deferred shapes
(NOT a false unconditional `proven`).  An `open` cell names the missing theorem and the task that
will close it — it carries NO anchor, because none exists yet.

## The parity picture (capability rows)

| Capability                | Status   | Union witness (cited)                                                |
| ------------------------- | -------- | -------------------------------------------------------------------- |
| typing / adequacy         | proven   | `HasTypeDescBridge.toNativeUnion` (every Bridge derivation → union)  |
| inversion (per head)      | proven   | the `invertAt*Head` family + `cellHasNoTypingWhenRootGenericallyExcluded` |
| substitution              | proven   | `HasTypeNativeUnion.substRespectingContext` (unconditional)         |
| root subject reduction    | bridged  | `unionRootStepSubjectReduction` (Conv-modulo + deferred β/ι shapes)  |
| reverse adequacy          | proven   | `nativeUnionReverseAdequacyCoverageWitness`                          |
| honesty classifier        | proven   | `hasTableTypingRule` + `hasSomeTypingRule_eq_hasTableTypingRule`     |
| affine rejection          | proven   | `HasTypeNativeUnion.unionRejectsAffineDoubleUse`                     |
| weakening                 | proven   | `HasTypeNativeUnion.renameRespectingContext` (all 25 arms, unconditional)   |
| uniqueness                | open     | union has no classifier-uniqueness theorem yet (union-uniqueness task) |
| reducibility / SN         | open     | no union-level SN theorem; bespoke SN lives on the grown engine (union-reducibility task) |
| canonicity                | open     | no union-level canonicity theorem; closed-form canonicity is per-engine (union-canonicity task) |
| context conversion        | open     | no union-level context-conversion theorem (union-context-conversion task) |

## The surpass picture (capabilities NO bespoke engine had)

  1. **union-wide affine rejection** — `unionRejectsAffineDoubleUse`: NO per-engine had an affine
     double-use guard; the union refutes `pathLam(pair(var 0, var 0))` across every arm.
  2. **two-path strict subsumption** — `natSuccRowStrictlyMoreGeneralThanEmbedding`: the recursive
     row TYPES `natSucc(computedNumber)` where the intro embedding is DEAD; the row strictly subsumes
     the embedding.  No bespoke engine could compare two derivation paths inside one judgment.
  3. **the conversion arm + Conv-closure** — `HasTypeNativeUnion.conv` (the 25th arm): NO bespoke
     DATA engine carried a conv rule; the union reclassifies along raw definitional equality.
  4. **table-driven static-typing classifier + cross-table equivalence** —
     `hasTableTypingRule` / `hasSomeTypingRule_eq_hasTableTypingRule`: a single Boolean static
     classifier over EVERY generator, proven extensionally equal to the engine-disjunction.  No
     bespoke engine exposed a decidable head-classifier folding all families.
  5. **cross-family single-judgment root-SR dispatcher** — `unionRootStepSubjectReduction` over core
     `Step`'s constructors: ONE dispatcher routes every root reduction (β + all ι + congruence) for a
     union-typed redex.  No bespoke engine had subject reduction spanning all families in one theorem.

## Honest finding

The five SURPASS items are all SHIPPED and CITED.  On the PARITY side, EIGHT of the twelve capability
rows are positive (seven `proven` + one `bridged`); FOUR are honestly `open` (uniqueness,
reducibility/SN, canonicity, context conversion — the union does NOT yet carry these, they live on
the bespoke / grown engines and have not been restated union-wide).  The ledger does NOT mark a
single one of those four as proven.  This is the present, honest state — a criterion, not a closure
claim.

## Zero-axiom verification

`UnionCapability` / `SurpassCapability` / `ParityStatus` are plain enums with full-enumeration status
projections (no wildcards over the 197-ctor tables).  The anchors are proof-term aliases of shipped
zero-axiom theorems; the ledger facts close by `rfl`; the coverage gate and discriminations close by
`decide` over `Nat`-deceq / enum `noConfusion`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditUnionParitySurpassLedger.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Modal

/-! ## The capability rows -/

/-- The metatheory capabilities a bespoke `HasTypeDesc*` engine could carry; each row asks "does the
unified judgment `HasTypeNativeUnion` have a same-or-stronger theorem?". -/
inductive UnionCapability where
  | typingAdequacy
  | inversion
  | substitution
  | rootSubjectReduction
  | reverseAdequacy
  | honestyClassifier
  | affineRejection
  | weakening
  | uniqueness
  | reducibilityStrongNormalization
  | canonicity
  | contextConversion
  deriving DecidableEq

/-- Honest per-capability status:
* `proven` — a shipped zero-axiom union theorem carries the capability at full strength; the cell is
  anchored to that theorem by reference.
* `bridged` — the union carries the capability only up to a Conv-modulo classifier or with deferred
  shapes (an honest qualifier, NOT a false unconditional claim); the cell is still anchored.
* `open` — the union does NOT yet carry the capability; the cell names the pending task and carries no
  anchor. -/
inductive ParityStatus where
  | proven
  | bridged
  | open
  deriving DecidableEq

/-- The honest parity status of each capability (full enumeration, no wildcard). -/
def UnionCapability.parityStatus : UnionCapability → ParityStatus
  | .typingAdequacy => .proven
  | .inversion => .proven
  | .substitution => .proven
  | .rootSubjectReduction => .bridged
  | .reverseAdequacy => .proven
  | .honestyClassifier => .proven
  | .affineRejection => .proven
  | .weakening => .proven
  | .uniqueness => .open
  | .reducibilityStrongNormalization => .open
  | .canonicity => .open
  | .contextConversion => .open

/-! ## Capability anchors (the teeth)

Each `proven`/`bridged` cell binds its shipped union theorem by reference; the file breaks if the
theorem is renamed, and each anchor's `#assert_no_axioms` gate re-certifies that proof is zero-axiom.
No `open` capability is anchored — because no union theorem exists for it. -/

/-- Typing / adequacy: every Bridge derivation translates to a union typing at the same subject. -/
def unionAnchor_typingAdequacy := @HasTypeDescBridge.toNativeUnion
/-- Inversion, pathLam head — the master per-head inversion (representative of the `invertAt*Head`
family). -/
def unionAnchor_inversion_pathLamHead := @HasTypeNativeUnion.invertAtPathLamHead
/-- Inversion, lambda head. -/
def unionAnchor_inversion_lamHead := @HasTypeNativeUnion.invertAtLamHead
/-- Inversion, natElim head. -/
def unionAnchor_inversion_natElimHead := @HasTypeNativeUnion.invertAtNatElimHead
/-- Inversion, natSucc head. -/
def unionAnchor_inversion_natSuccHead := @HasTypeNativeUnion.invertAtNatSuccHead
/-- Inversion, boolElim head (the Match-inversion shard). -/
def unionAnchor_inversion_boolElimHead := @HasTypeNativeUnion.invertAtBoolElimHead
/-- Inversion, idJ head (the PathProj-inversion shard). -/
def unionAnchor_inversion_idJHead := @HasTypeNativeUnion.invertAtIdJHead
/-- Inversion, natRec head (the Recursive-inversion shard). -/
def unionAnchor_inversion_natRecHead := @HasTypeNativeUnion.invertAtNatRecHead
/-- Inversion, the generic root refutation the per-head inversions discharge their host disjunct
through (`cellHasNoTypingWhenRootGenericallyExcluded`, via the `ofGrown` embedding). -/
def unionAnchor_inversion_genericRefutation :=
  @HasTypeDescPi.cellHasNoTypingWhenRootGenericallyExcluded
/-- Substitution: union typing is preserved along any host-typed substitution (unconditional). -/
def unionAnchor_substitution := @HasTypeNativeUnion.substRespectingContext
/-- Root subject reduction: the total root-redex dispatcher (Conv-modulo + deferred shapes — bridged). -/
def unionAnchor_rootSubjectReduction := @unionRootStepSubjectReduction
/-- Reverse adequacy: the per-family coverage witness (union restricted to bridge heads → bespoke). -/
def unionAnchor_reverseAdequacy := @nativeUnionReverseAdequacyCoverageWitness
/-- Honesty classifier: the table-driven static-typing classifier. -/
def unionAnchor_honestyClassifier_table := @hasTableTypingRule
/-- Honesty classifier: the exact equivalence with the engine-disjunction static classifier. -/
def unionAnchor_honestyClassifier_equivalence := @hasSomeTypingRule_eq_hasTableTypingRule
/-- Affine rejection: the union refutes `pathLam(pair(var 0, var 0))` across every arm. -/
def unionAnchor_affineRejection := @HasTypeNativeUnion.unionRejectsAffineDoubleUse
/-- Weakening: union typing is preserved along any context-respecting renaming (de-Bruijn insertion),
all 25 arms (unconditional). -/
def unionAnchor_weakening := @HasTypeNativeUnion.renameRespectingContext

/-! ## Ledger facts (parity) -/

/-- Typing / adequacy is at PARITY (proven): the Bridge engine maps fully into the union. -/
theorem typingAdequacy_atParity :
    UnionCapability.typingAdequacy.parityStatus = .proven := rfl

/-- Inversion is at PARITY (proven): the per-head `invertAt*Head` family covers every head. -/
theorem inversion_atParity :
    UnionCapability.inversion.parityStatus = .proven := rfl

/-- Substitution is at PARITY (proven): unconditional union substitution. -/
theorem substitution_atParity :
    UnionCapability.substitution.parityStatus = .proven := rfl

/-- Root subject reduction is BRIDGED: the dispatcher pins the reduct up to a Conv-equal classifier
and surfaces β / the deferred ι as shapes, rather than typing every reduct at the SAME classifier
unconditionally.  Recorded honestly as `bridged`, not `proven`. -/
theorem rootSubjectReduction_isBridged :
    UnionCapability.rootSubjectReduction.parityStatus = .bridged := rfl

/-- Reverse adequacy is at PARITY (proven): the coverage witness inhabits the per-family relativized
adequacy back to the bespoke engines. -/
theorem reverseAdequacy_atParity :
    UnionCapability.reverseAdequacy.parityStatus = .proven := rfl

/-- The honesty classifier is at PARITY (proven): the table classifier equals the engine-disjunction. -/
theorem honestyClassifier_atParity :
    UnionCapability.honestyClassifier.parityStatus = .proven := rfl

/-- Affine rejection is at PARITY (proven) — and is also a SURPASS row (no bespoke engine had it). -/
theorem affineRejection_atParity :
    UnionCapability.affineRejection.parityStatus = .proven := rfl

/-- Weakening is at PARITY (proven): union typing is preserved along any context-respecting renaming,
anchored to `HasTypeNativeUnion.renameRespectingContext` (all 25 arms, unconditional, zero-axiom). -/
theorem weakening_atParity :
    UnionCapability.weakening.parityStatus = .proven := rfl

/-- Uniqueness is OPEN: the union carries no classifier-uniqueness theorem yet (union-uniqueness
task).  Classifier uniqueness lives on the bespoke / grown engines and is not restated union-wide. -/
theorem uniqueness_isOpen :
    UnionCapability.uniqueness.parityStatus = .open := rfl

/-- Reducibility / strong normalization is OPEN at the union level: SN is proven on the grown engine
(`HasTypeDescPi.stronglyNormalizingOfWfContextDesc`) but NOT restated for `HasTypeNativeUnion`
(union-reducibility task). -/
theorem reducibilityStrongNormalization_isOpen :
    UnionCapability.reducibilityStrongNormalization.parityStatus = .open := rfl

/-- Canonicity is OPEN at the union level: closed-form canonicity is proven per bespoke engine but not
restated for `HasTypeNativeUnion` (union-canonicity task). -/
theorem canonicity_isOpen :
    UnionCapability.canonicity.parityStatus = .open := rfl

/-- Context conversion is OPEN at the union level: the grown engine has the conditional
context-conversion bundle, but the union has no context-conversion theorem (union-context-conversion
task). -/
theorem contextConversion_isOpen :
    UnionCapability.contextConversion.parityStatus = .open := rfl

/-! ## The parity criterion (computed coverage) -/

/-- A capability is "covered" when its status is `proven` or `bridged` (a positive cell). -/
def ParityStatus.isCovered : ParityStatus → Bool
  | .proven => true
  | .bridged => true
  | .open => false

/-- A capability is "strictly proven" (full strength, no Conv-modulo qualifier). -/
def ParityStatus.isStrictlyProven : ParityStatus → Bool
  | .proven => true
  | .bridged => false
  | .open => false

/-- Every capability row, enumerated. -/
def allCapabilities : List UnionCapability :=
  [ .typingAdequacy, .inversion, .substitution, .rootSubjectReduction, .reverseAdequacy,
    .honestyClassifier, .affineRejection, .weakening, .uniqueness,
    .reducibilityStrongNormalization, .canonicity, .contextConversion ]

/-- How many capability rows are positive (proven or bridged) RIGHT NOW. -/
def coveredCapabilityCount : Nat :=
  (allCapabilities.filter (fun capability => capability.parityStatus.isCovered)).length

/-- How many capability rows are strictly proven (full strength) RIGHT NOW. -/
def strictlyProvenCapabilityCount : Nat :=
  (allCapabilities.filter (fun capability => capability.parityStatus.isStrictlyProven)).length

/-- How many capability rows are honestly OPEN RIGHT NOW. -/
def openCapabilityCount : Nat :=
  (allCapabilities.filter (fun capability => not capability.parityStatus.isCovered)).length

/-- ★ The honest present count: EIGHT of twelve capability rows are positive (seven strictly proven
plus the bridged root-SR row).  Computed by `rfl`. -/
theorem coveredCapabilityCount_isEight : coveredCapabilityCount = 8 := rfl

/-- SEVEN of twelve rows are strictly proven (typing, inversion, substitution, reverse adequacy,
honesty, affine rejection, weakening); root-SR is bridged, not counted here. -/
theorem strictlyProvenCapabilityCount_isSeven : strictlyProvenCapabilityCount = 7 := rfl

/-- FOUR of twelve rows are honestly OPEN (uniqueness, reducibility/SN, canonicity, context
conversion).  The ledger marks none of these `proven`. -/
theorem openCapabilityCount_isFour : openCapabilityCount = 4 := rfl

/-- The full-parity criterion asks for all twelve capability rows strictly proven. -/
@[reducible] def unionAchievesFullParity : Prop := strictlyProvenCapabilityCount = 12

/-- ★ Honest: full parity is NOT yet achieved (five rows open, one bridged).  This is the honest
parity CRITERION, not a closure claim. -/
theorem unionFullParity_not_yet_achieved : ¬ unionAchievesFullParity := by decide

/-! ## The SURPASS rows — capabilities NO bespoke engine had -/

/-- A capability the unified judgment carries that NO single bespoke `HasTypeDesc*` engine ever had. -/
inductive SurpassCapability where
  | unionWideAffineRejection
  | twoPathStrictSubsumption
  | conversionArmClosure
  | tableDrivenStaticClassifier
  | crossFamilyRootSubjectReduction
  deriving DecidableEq

/-- Whether the union's witness for a surpass capability is SHIPPED (cited below).  All five are. -/
def SurpassCapability.isShipped : SurpassCapability → Bool
  | .unionWideAffineRejection => true
  | .twoPathStrictSubsumption => true
  | .conversionArmClosure => true
  | .tableDrivenStaticClassifier => true
  | .crossFamilyRootSubjectReduction => true

/-! ### Surpass anchors -/

/-- Surpass 1 — union-wide affine rejection. -/
def surpassAnchor_affineRejection := @HasTypeNativeUnion.unionRejectsAffineDoubleUse
/-- Surpass 2 — two-path strict subsumption: the recursive row strictly subsumes the intro embedding. -/
def surpassAnchor_twoPathSubsumption :=
  @HasTypeNativeUnion.natSuccRowStrictlyMoreGeneralThanEmbedding
/-- Surpass 4 — table-driven static-typing classifier. -/
def surpassAnchor_tableClassifier := @hasTableTypingRule
/-- Surpass 4 — its exact cross-table equivalence with the engine-disjunction. -/
def surpassAnchor_tableEquivalence := @hasSomeTypingRule_eq_hasTableTypingRule
/-- Surpass 5 — cross-family single-judgment root-SR dispatcher over core `Step`. -/
def surpassAnchor_crossFamilyRootSR := @unionRootStepSubjectReduction

/-- ★ Surpass 3 — the conversion arm: a non-vacuous witness that `HasTypeNativeUnion.conv` actually
admits a derivation (a union-typed subject reclassifies along a raw `Conv`, with the target classifier
itself union-typed at a universe code).  No bespoke DATA engine carried a conv rule.  This inhabits the
conv-arm shape directly from a union typing + a `Conv` + a universe-code typing of the target. -/
def conversionArmAdmitsReclassification {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subject classifier reclassifier : RawTerm scope}
    (levelExpr : LevelExpr) (flag : UniverseFlag)
    (typed : HasTypeNativeUnion profile context subject classifier)
    (converts : Conv classifier reclassifier)
    (reclassifierTyped :
      HasTypeNativeUnion profile context reclassifier (universeCodeCell levelExpr flag)) :
    HasTypeNativeUnion profile context subject reclassifier :=
  HasTypeNativeUnion.conv levelExpr flag typed converts reclassifierTyped

/-! ## The surpass criterion (computed) -/

def allSurpassCapabilities : List SurpassCapability :=
  [ .unionWideAffineRejection, .twoPathStrictSubsumption, .conversionArmClosure,
    .tableDrivenStaticClassifier, .crossFamilyRootSubjectReduction ]

/-- How many surpass capabilities are SHIPPED (cited) RIGHT NOW. -/
def shippedSurpassCount : Nat :=
  (allSurpassCapabilities.filter SurpassCapability.isShipped).length

/-- ★ All five surpass capabilities are shipped and cited.  Computed by `rfl`. -/
theorem allSurpassCapabilitiesShipped : shippedSurpassCount = 5 := rfl

/-- The surpass criterion asks for all five surpass capabilities shipped — and it is MET. -/
@[reducible] def unionSurpasses : Prop := shippedSurpassCount = 5

/-- ★ The union SURPASSES the bespoke engines: all five capabilities no bespoke engine had are
shipped and cited. -/
theorem unionSurpasses_isMet : unionSurpasses := rfl

/-! ## Non-vacuity: the ledger genuinely discriminates -/

/-- The ledger is not constant: typing-adequacy (proven) differs from uniqueness (open). -/
theorem parity_discriminates_proven_vs_open :
    UnionCapability.typingAdequacy.parityStatus ≠ UnionCapability.uniqueness.parityStatus := by
  intro statusEq
  rw [typingAdequacy_atParity, uniqueness_isOpen] at statusEq
  exact ParityStatus.noConfusion statusEq

/-- The ledger keeps `bridged` distinct from `proven`: the root-SR row's honest Conv-modulo status is
NOT conflated with a full-strength proven row. -/
theorem parity_discriminates_bridged_vs_proven :
    UnionCapability.rootSubjectReduction.parityStatus ≠
      UnionCapability.substitution.parityStatus := by
  intro statusEq
  rw [rootSubjectReduction_isBridged, substitution_atParity] at statusEq
  exact ParityStatus.noConfusion statusEq

/-- The ledger keeps `bridged` distinct from `open`: a Conv-modulo positive row is not an open row. -/
theorem parity_discriminates_bridged_vs_open :
    UnionCapability.rootSubjectReduction.parityStatus ≠
      UnionCapability.uniqueness.parityStatus := by
  intro statusEq
  rw [rootSubjectReduction_isBridged, uniqueness_isOpen] at statusEq
  exact ParityStatus.noConfusion statusEq

end FX1Poly.Typed
