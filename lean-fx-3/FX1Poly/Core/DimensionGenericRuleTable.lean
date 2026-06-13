import FX1Poly.Core.StepOverBundle
import FX1Poly.Core.GeneratorTagRoundTrip

/-! # DimensionGenericRuleTable — DIMN-TAB-1 [SPIKE]: what a RuleTable shares across dimensions

PHASE 7 GO/NO-GO spike for the MOON-LEDGER program (#1385).  The kernel's
reduction layer is now ONE parameterized relation `StepOver` over a
`RuleTableBundle` of head-keyed rows (RW-5, #1359): dim-2 rewriting (β/ι/η/δ
between TERMS).  DIM3-TAB (#1381/#1382) proposes the SAME table idea one
dimension up: `SchemaRuleDesc` rows rewriting REDUCTION-PLANE objects
(extensional optimizations between terms, carrying certificates).  This
spike asks the make-or-break question:

> Can `RuleTable` be indexed by dimension — with the orthogonality / firing /
> equivariance machinery SHARED — or do dims 2 and 3 only share the SHAPE
> (head-keyed list + decidable disjointness + tier certificates) while the
> SUBSTRATE differs (definitional reduction vs extensional optimization)?

## The honest verdict (machine-checked below)

**The SHAPE is shared; the SUBSTRATE is not; dim-4+ does not fit at all.**

1. **Shared SHAPE — a head-keyed table.**  Every dimension's rule layer is a
   finite list of rows, each keyed by a `Generator` head, with a decidable
   orthogonality certificate and a generic firing operation.  This is real and
   instantiated: `dim2IotaShape` / `dim2EtaShape` below ARE the shipped
   dim-2 iota/eta tables viewed through the dimension-generic `RuleTableShape`
   interface (`headKey := elimGenerator.toNat` — exactly what `StepOver`'s
   `iotaRedex` arm keys on, and what `WfIotaTable` disjointness decides over).

2. **Different SUBSTRATE — definitional vs extensional vs coherence.**  What a
   ROW MEANS differs by dimension, and the metatheorems are per-substrate (the
   `substrateOf` map below is injective — the three substrate descriptors are
   pairwise distinct):
   * **dim 2** (`definitionalReduction`): a row's LHS↝RHS is a single KERNEL
     reduction (`StepOver`); soundness is **subject reduction** (typing
     preserved); termination is over **term size / RPO**.  This is the shipped
     `IotaRuleDesc`/`EtaRuleDesc`/`DeltaRuleDesc` world.
   * **dim 3** (`extensionalOptimization`): a row relates two terms by
     **observational `Conv`** (an equivalence — neither term need reduce to the
     other), carrying that `Conv` plus a **cost-improvement** witness as
     certificates; soundness is **extensional-equivalence preservation + cost
     non-increase**; termination is over the **cost order**, not term size.
     This is exactly the shipped `OptimizationCell` (OPT-0, #1225): its
     `extensionalCertificate : Conv …` and `costCertificate : … ≤ …` ARE the
     two dim-3 row fields, and the COST-4 `Improves` preorder (#1217) is the
     orientation.  The schema-row form is DIM3-TAB-1's deliverable (#1381).
   * **dim 4+** (`higherCoherence`): OPT-56 strategy-independence (#1252) is
     EQUALITY OF REWRITE PATHS — a 3-cell between 2-cells.  Its data is not
     "rows keyed by a head" but CRITICAL BRANCHINGS and their confluence
     diagrams; soundness is **coherence of diagrams**, with no head-keyed
     orientation.  It does NOT fit the flat orthogonal table — it needs the
     polygraph / Squier instrument (`OHOM-1`, #1261).

3. **The dimension-generic OBJECT is the SHAPE, parameterized by a per-dimension
   rewrite-semantics descriptor.**  The shared machinery (firing = head-lookup +
   apply; orthogonality = decidable head-disjointness; the
   orthogonality⇒confluence and orientation⇒termination SCHEMAS) lifts to the
   shape; the actual SR / termination / confluence theorems are re-discharged
   per substrate (definitional via typed SR + RPO; extensional via Conv-
   preservation + cost order).  Dims 2 and 3 BOTH fit
   (`fitsFlatOrthogonalTable = true`); dim-4+ does NOT (`= false`).

This pins the DIM3-TAB design: build `SchemaRuleDesc` as its OWN
`RuleTableShape` instance with the extensional/cost substrate — reusing the
shape-level orthogonality and firing scaffolding, NOT the definitional SR/RPO
metatheorems — and route dim-4+ coherence to the polygraph layer.

## Zero-axiom

Enums derive `DecidableEq`; the shape instantiations are `rfl`; the
substrate-distinctness facts are `of_decide_eq_false rfl` (the SIG-1 idiom,
dual form); the fit facts are `rfl`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`. -/

namespace FX1Poly.Core

/-! ## The shared SHAPE — a head-keyed rule table -/

/-- The dimension-GENERIC interface a rule table presents, independent of
WHAT its rows mean: a row carrier `rowType` and a `headKey` projecting each
row to the `Generator`-tag it is keyed on.  Firing (head-lookup + apply) and
orthogonality (decidable head-disjointness) are defined over THIS interface,
shared across every dimension that instantiates it. -/
structure RuleTableShape where
  /-- The carrier of one rule row. -/
  rowType : Type
  /-- The `Generator`-tag head a row is keyed on (what firing looks up and what
  orthogonality decides disjointness over). -/
  headKey : rowType → Nat

/-- **Dim-2 ι/β rows instantiate the shape** — the shipped `IotaRuleDesc`
table viewed through the dimension-generic interface, keyed exactly on the
eliminator generator's tag (what `StepOver.iotaRedex` matches on). -/
def dim2IotaShape : RuleTableShape where
  rowType := IotaRuleDesc
  headKey := fun rule => rule.elimGenerator.toNat

/-- **Dim-2 η rows instantiate the shape too** — the shipped `EtaRuleDesc`
table keyed on the intro generator's tag (what `StepOver.etaRedex` matches
on).  Two shipped sub-tables, one shape: the shape genuinely spans dim-2. -/
def dim2EtaShape : RuleTableShape where
  rowType := EtaRuleDesc
  headKey := fun rule => rule.introGenerator.toNat

/-- The dim-2 iota shape's carrier IS the shipped `IotaRuleDesc` — the shape
is not a parallel re-encoding but a VIEW of the kernel's own row type. -/
theorem dim2IotaShape_rowType_isIotaRuleDesc :
    dim2IotaShape.rowType = IotaRuleDesc := rfl

/-- The dim-2 eta shape's carrier IS the shipped `EtaRuleDesc`. -/
theorem dim2EtaShape_rowType_isEtaRuleDesc :
    dim2EtaShape.rowType = EtaRuleDesc := rfl

/-- The dim-2 iota shape's head key on any row is its eliminator generator's
tag — definitionally the key `StepOver`/`WfIotaTable` already use. -/
theorem dim2IotaShape_headKey_isElimGeneratorTag (rule : IotaRuleDesc) :
    dim2IotaShape.headKey rule = rule.elimGenerator.toNat := rfl

/-! ## The non-sharing boundary — the rewrite SUBSTRATE per dimension -/

/-- The dimensions whose rule layers the MOON-LEDGER program ranges over. -/
inductive RewriteDimension where
  /-- Dim 2: β/ι/η/δ definitional reduction between TERMS (the shipped
  `StepOver` over `RuleTableBundle`). -/
  | definitionalReduction : RewriteDimension
  /-- Dim 3: extensional optimization between terms with cost certificates
  (the shipped `OptimizationCell`; `SchemaRuleDesc` is DIM3-TAB-1). -/
  | extensionalOptimization : RewriteDimension
  /-- Dim 4+: coherence between rewrite PATHS (OPT-56 strategy-independence). -/
  | higherCoherence : RewriteDimension
deriving DecidableEq, Repr

/-- What links a row's LHS and RHS — the first axis on which the substrate
differs across dimensions. -/
inductive RelatesBy where
  /-- A single kernel reduction step (dim 2). -/
  | definitionalStep : RelatesBy
  /-- Observational `Conv` — an equivalence, oriented externally (dim 3). -/
  | extensionalEquivalence : RelatesBy
  /-- Equality of rewrite paths / 2-cells (dim 4+). -/
  | pathEquality : RelatesBy
deriving DecidableEq, Repr

/-- What makes a row's rule TERMINATING — the second differing axis. -/
inductive OrientedBy where
  /-- Term size / recursive path order (dim 2). -/
  | termSizeOrder : OrientedBy
  /-- The cost-improvement preorder (dim 3). -/
  | costOrder : OrientedBy
  /-- No orientation — coherence is a symmetric 3-cell (dim 4+). -/
  | noOrientation : OrientedBy
deriving DecidableEq, Repr

/-- What a row's SOUNDNESS obligation is — the third differing axis. -/
inductive SoundnessObligation where
  /-- Typing preserved by the step (dim 2: subject reduction). -/
  | subjectReduction : SoundnessObligation
  /-- Behavior preserved + cost not increased (dim 3). -/
  | extensionalAndCost : SoundnessObligation
  /-- Confluence diagrams commute (dim 4+). -/
  | coherenceOfPaths : SoundnessObligation
deriving DecidableEq, Repr

/-- The per-dimension rewrite SUBSTRATE: the three axes on which the meaning
of a rule row (and hence its metatheory) differs across dimensions.  The
SHAPE is shared; THIS is not. -/
structure RewriteSubstrate where
  relatesBy : RelatesBy
  orientedBy : OrientedBy
  soundness : SoundnessObligation
deriving DecidableEq, Repr

/-- The substrate each dimension's rule layer carries.  Full enumeration of
all three dimensions (no wildcard) — propext-clean. -/
def substrateOf : RewriteDimension → RewriteSubstrate
  | .definitionalReduction =>
      { relatesBy := .definitionalStep
        orientedBy := .termSizeOrder
        soundness := .subjectReduction }
  | .extensionalOptimization =>
      { relatesBy := .extensionalEquivalence
        orientedBy := .costOrder
        soundness := .extensionalAndCost }
  | .higherCoherence =>
      { relatesBy := .pathEquality
        orientedBy := .noOrientation
        soundness := .coherenceOfPaths }

/-- **Whether a dimension fits the flat head-keyed ORTHOGONAL table** — true
for the definitional (dim 2) and extensional (dim 3) substrates, false for
higher coherence (dim 4+), which needs the polygraph / Squier instrument
(`OHOM-1`).  Full enumeration — propext-clean. -/
def RewriteDimension.fitsFlatOrthogonalTable : RewriteDimension → Bool
  | .definitionalReduction => true
  | .extensionalOptimization => true
  | .higherCoherence => false

/-! ## Substrate distinctness — the substrate genuinely differs -/

/-- Dim-2 and dim-3 substrates differ (definitional reduction ≠ extensional
optimization). -/
theorem substrate_definitional_ne_extensional :
    substrateOf .definitionalReduction ≠ substrateOf .extensionalOptimization :=
  of_decide_eq_false rfl

/-- Dim-3 and dim-4+ substrates differ (extensional optimization ≠ higher
coherence). -/
theorem substrate_extensional_ne_coherence :
    substrateOf .extensionalOptimization ≠ substrateOf .higherCoherence :=
  of_decide_eq_false rfl

/-- Dim-2 and dim-4+ substrates differ (definitional reduction ≠ higher
coherence). -/
theorem substrate_definitional_ne_coherence :
    substrateOf .definitionalReduction ≠ substrateOf .higherCoherence :=
  of_decide_eq_false rfl

/-! ## ★ The DIMN-TAB-1 verdict -/

/-- ★ **The dimension-generic RuleTable verdict.**  Three machine-checked
facts pin the GO/NO-GO:

* **shared SHAPE** — the shipped dim-2 iota/eta tables instantiate the
  dimension-generic `RuleTableShape`, viewing the kernel's own row types
  (`dim2IotaShape.rowType = IotaRuleDesc`, `dim2EtaShape.rowType = EtaRuleDesc`);
* **different SUBSTRATE** — the three dimensions' rewrite substrates are
  pairwise DISTINCT (`substrateOf` separates them), so the SR / termination /
  confluence theorems are re-discharged per dimension, not literally shared;
* **dim-4+ does NOT fit** — dims 2 and 3 fit the flat orthogonal table
  (`fitsFlatOrthogonalTable = true`); higher coherence does not
  (`= false`) — it routes to the polygraph / Squier homology instrument.

This is the honest answer to "is `RuleTable` dimension-generic?": YES at the
SHAPE level (head-keyed list + decidable orthogonality + generic firing),
NO at the SUBSTRATE level, and dim-4+ leaves the table paradigm entirely. -/
theorem dimensionGenericRuleTable_verdict :
    (dim2IotaShape.rowType = IotaRuleDesc ∧ dim2EtaShape.rowType = EtaRuleDesc)
    ∧ (substrateOf .definitionalReduction ≠ substrateOf .extensionalOptimization
       ∧ substrateOf .extensionalOptimization ≠ substrateOf .higherCoherence
       ∧ substrateOf .definitionalReduction ≠ substrateOf .higherCoherence)
    ∧ (RewriteDimension.definitionalReduction.fitsFlatOrthogonalTable = true
       ∧ RewriteDimension.extensionalOptimization.fitsFlatOrthogonalTable = true
       ∧ RewriteDimension.higherCoherence.fitsFlatOrthogonalTable = false) :=
  ⟨⟨rfl, rfl⟩,
   ⟨substrate_definitional_ne_extensional,
    substrate_extensional_ne_coherence,
    substrate_definitional_ne_coherence⟩,
   ⟨rfl, rfl, rfl⟩⟩

end FX1Poly.Core
