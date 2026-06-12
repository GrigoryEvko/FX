import FX1Poly.Core.StepTable
import FX1Poly.Core.Newman

/-! # FX1Poly/Core/TableParallelReduction — IOTA-T6: the table-driven parallel reduction

The TABLE twin of `ParallelReduction.lean`: a Tait/Martin-Löf/Takahashi
parallel reduction whose root-contraction arm is ONE generic rule —
"some table row fires" — instead of eighteen bespoke constructors.
Adding an ι-rule to the kernel adds a table ROW; this relation, its
sandwich bounds, and (downstream) its Takahashi triangle and confluence
are inherited with zero new constructors.

## The redex arm's shape

`tableRedex` requires THREE things:

  * `spinePar` — the eliminator spine reduces POINTWISE to a reduced
    spine (every child contracts its own redexes simultaneously);
  * `sourceFires` — the row's left-linear pattern matches the SOURCE
    spine.  Without this the relation would let a child first develop
    INTO the constructor shape and then fire the root in the same
    parallel step — two nested developments at once, which breaks the
    Takahashi triangle (the complete development of the source does not
    fire a root whose pattern is absent in the source);
  * `fires` — the row fires on the REDUCED spine, producing the reduct.
    Interpreting the template over the reduced spine is exactly the
    Takahashi contractum-from-developed-components shape (β's
    `subst0 body' arg'`, generalized to every row).

## What ships here

  * `ParStepOverTable` / `ParStepOverTableChildren` — the mutual
    relation, parameterized by the table; `ParStepTable` is the
    canonical 18-row instance.
  * Reflexivity (mutual structural recursion, the `ParStep.refl` idiom).
  * `Step ⊆ Par`: `StepOverTable.toParStepOverTable` — a single table
    step is a parallel step contracting only that redex.
  * `Par ⊆ Step*`: `ParStepOverTable.toStepClosure` — a parallel step is
    a finite chain of single table steps (reduce the spine by pointwise
    child chains under congruence, then fire the root on the reduced
    spine).  Stated against the abstract `ReflTransClosure`, the form
    the diamond plumbing (`confluentOfDiamondSimulation`) consumes.

## Zero-axiom verification

Mutual `Prop` inductives, mutual structural recursion on terms and
derivations (the `Step.toParStep` idiom), and a generic
`ReflTransClosure.map` relation-homomorphism lemma.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Gated per declaration in
`FX1PolyAudit/AuditTableParallelReduction.lean`. -/

namespace FX1Poly.Core

/-! ## The relation -/

mutual

/-- **Table-driven parallel reduction** — contract any set of redexes
simultaneously, where a root redex is a firing of some row of `table`.
The Takahashi parallel reduction over the ι-rule table: the redex arm
demands the pattern on the SOURCE spine (`sourceFires`) and interprets
the reduct over the pointwise-REDUCED spine (`fires`). -/
inductive ParStepOverTable (table : List IotaRuleDesc) :
    {scope : Nat} → RawTerm scope → RawTerm scope → Prop where
  /-- **A table row fires at the root of a pointwise-reducing cell.**
      The pattern must match the source spine; the reduct is the row's
      template interpreted over the reduced spine. -/
  | tableRedex {scope : Nat} {rule : IotaRuleDesc} (isRow : rule ∈ table)
      (elimPayload : rule.elimGenerator.payload scope)
      {spine reducedSpine :
        RawTermChildren rule.elimGenerator.binderShifts scope}
      {reduct : RawTerm scope}
      (spinePar : ParStepOverTableChildren table spine reducedSpine)
      (sourceFires : rule.scrutineesFire spine rule.scrutinees = true)
      (fires : rule.firesOn? elimPayload reducedSpine = some reduct) :
      ParStepOverTable table (.mkGen rule.elimGenerator elimPayload spine)
        reduct
  /-- **Uniform congruence under any generator** — every child reduces
      in parallel; the cell rebuilds.  Also the source of reflexivity. -/
  | cong {scope : Nat} (gen : Generator) (payload : gen.payload scope)
      {children children' : RawTermChildren gen.binderShifts scope}
      (childrenPar : ParStepOverTableChildren table children children') :
      ParStepOverTable table (.mkGen gen payload children)
        (.mkGen gen payload children')

/-- **Pointwise parallel reduction of a children spine** — every child
reduces simultaneously (mirroring `ParStepChildren`, NOT the
single-child `StepOverTableChildren`). -/
inductive ParStepOverTableChildren (table : List IotaRuleDesc) :
    {binderShifts : List Nat} → {scope : Nat} →
    RawTermChildren binderShifts scope →
    RawTermChildren binderShifts scope → Prop where
  | nil {scope : Nat} :
      ParStepOverTableChildren table (scope := scope) .childNil .childNil
  | cons {scope : Nat} {headShift : Nat} {restShifts : List Nat}
      {childHead childHead' : RawTerm (scope + headShift)}
      {childTail childTail' : RawTermChildren restShifts scope}
      (headPar : ParStepOverTable table childHead childHead')
      (tailPar : ParStepOverTableChildren table childTail childTail') :
      ParStepOverTableChildren table
        (.childCons childHead childTail) (.childCons childHead' childTail')

end

/-- THE canonical table parallel reduction: `ParStepOverTable` at the
full 18-row `iotaRuleTable`. -/
abbrev ParStepTable {scope : Nat} (source target : RawTerm scope) : Prop :=
  ParStepOverTable iotaRuleTable source target

/-! ## Reflexivity -/

mutual

/-- Every term parallel-reduces to itself over any table — congruence
over the reflexively-reduced children spine. -/
theorem ParStepOverTable.refl {table : List IotaRuleDesc} {scope : Nat} :
    (term : RawTerm scope) → ParStepOverTable table term term
  | .mkGen gen payload children =>
      ParStepOverTable.cong gen payload
        (ParStepOverTableChildren.refl children)

/-- Every children spine parallel-reduces to itself over any table. -/
theorem ParStepOverTableChildren.refl {table : List IotaRuleDesc}
    {binderShifts : List Nat} {scope : Nat} :
    (children : RawTermChildren binderShifts scope) →
    ParStepOverTableChildren table children children
  | .childNil => ParStepOverTableChildren.nil
  | .childCons childHead childTail =>
      ParStepOverTableChildren.cons (ParStepOverTable.refl childHead)
        (ParStepOverTableChildren.refl childTail)

end

/-! ## The lower sandwich bound: `Step ⊆ Par` -/

mutual

/-- **A single table step is a parallel table step** firing only that
redex: the redex arm keeps the spine reflexive (its own firing supplies
both the source pattern and the reduced-spine firing), and a congruence
maps its single stepping child into the pointwise spine. -/
theorem StepOverTable.toParStepOverTable {table : List IotaRuleDesc}
    {scope : Nat} {source target : RawTerm scope} :
    StepOverTable table source target → ParStepOverTable table source target
  | .tableRedex isRow elimPayload fires =>
      .tableRedex isRow elimPayload (ParStepOverTableChildren.refl _)
        (IotaRuleDesc.firesOn?_some_scrutineesFire fires) fires
  | .cong gen payload childStep =>
      .cong gen payload
        (StepOverTableChildren.toParStepOverTableChildren childStep)

/-- Spine companion: a single-child step lifts to the pointwise spine
reduction — the stepping child via the recursive call, the rest
reflexive. -/
theorem StepOverTableChildren.toParStepOverTableChildren
    {table : List IotaRuleDesc} {parentScope : Nat}
    {binderShifts : List Nat}
    {children children' : RawTermChildren binderShifts parentScope} :
    StepOverTableChildren table children children' →
    ParStepOverTableChildren table children children'
  | .here rest childStep =>
      .cons (StepOverTable.toParStepOverTable childStep)
        (ParStepOverTableChildren.refl rest)
  | .there head restStep =>
      .cons (ParStepOverTable.refl head)
        (StepOverTableChildren.toParStepOverTableChildren restStep)

end

/-! ## The upper sandwich bound: `Par ⊆ Step*` -/

/-- **Relation-homomorphism mapping of a reflexive-transitive chain**: a
function carrying single steps carries whole chains.  The generic brick
the spine-congruence lifters instantiate (at `childCons` slot embeddings
and at the `mkGen` cell embedding). -/
theorem ReflTransClosure.map {CarrierA : Type _} {CarrierB : Type _}
    {relA : CarrierA → CarrierA → Prop} {relB : CarrierB → CarrierB → Prop}
    (embed : CarrierA → CarrierB)
    (mapsStep : ∀ {first second : CarrierA},
      relA first second → relB (embed first) (embed second))
    {source target : CarrierA}
    (chain : ReflTransClosure relA source target) :
    ReflTransClosure relB (embed source) (embed target) := by
  induction chain with
  | refl point => exact ReflTransClosure.refl (embed point)
  | head first _rest inductionHypothesis =>
      exact ReflTransClosure.head (mapsStep first) inductionHypothesis

mutual

/-- **A parallel table step is a finite chain of single table steps.**
The redex arm reduces the spine to the reduced spine (pointwise chains
under congruence, via the spine companion), then fires the root in one
step — the firing hypothesis is stated on the reduced spine, so it
applies directly.  A congruence collapses to the spine companion's
chain mapped under the cell embedding. -/
theorem ParStepOverTable.toStepClosure {table : List IotaRuleDesc}
    {scope : Nat} {source target : RawTerm scope} :
    ParStepOverTable table source target →
    ReflTransClosure (StepOverTable table) source target
  | .tableRedex isRow elimPayload spinePar _sourceFires fires =>
      ReflTransClosure.trans
        (ReflTransClosure.map
          (fun spine => RawTerm.mkGen _ elimPayload spine)
          (fun spineStep => StepOverTable.cong _ elimPayload spineStep)
          (ParStepOverTableChildren.toChildrenStepClosure spinePar))
        (ReflTransClosure.single
          (StepOverTable.tableRedex isRow elimPayload fires))
  | .cong gen payload childrenPar =>
      ReflTransClosure.map
        (fun children => RawTerm.mkGen gen payload children)
        (fun spineStep => StepOverTable.cong gen payload spineStep)
        (ParStepOverTableChildren.toChildrenStepClosure childrenPar)

/-- Spine companion: a pointwise parallel spine reduction is a finite
chain of single-child spine steps — first the head's chain (each step
embedded at the head slot with the ORIGINAL tail), then the tail's
chain (each step under the already-reduced head). -/
theorem ParStepOverTableChildren.toChildrenStepClosure
    {table : List IotaRuleDesc} {binderShifts : List Nat} {scope : Nat}
    {children children' : RawTermChildren binderShifts scope} :
    ParStepOverTableChildren table children children' →
    ReflTransClosure (StepOverTableChildren table) children children'
  | .nil => ReflTransClosure.refl _
  | .cons (childHead := childHead) (childHead' := childHead')
      (childTail := childTail) (childTail' := childTail')
      headPar tailPar =>
      ReflTransClosure.trans
        (ReflTransClosure.map
          (fun head => RawTermChildren.childCons head childTail)
          (fun headStep => StepOverTableChildren.here childTail headStep)
          (ParStepOverTable.toStepClosure headPar))
        (ReflTransClosure.map
          (fun tail => RawTermChildren.childCons childHead' tail)
          (fun tailStep => StepOverTableChildren.there childHead' tailStep)
          (ParStepOverTableChildren.toChildrenStepClosure tailPar))

end

end FX1Poly.Core
