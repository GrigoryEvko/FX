import FX1Poly.Core.Rewriting.Confluence.StepStarConfluence
import FX1Poly.Core.Rewriting.RuleTables.StepOver.StepOverTable

/-! # FX1Poly/Core/GelRelationRetract
    — TRANSP-1: the COMPUTING leg of the Gel ≃ relation judgmental retract

The Bernardy-Coquand-Moulin / Cavallo-Harper relational universe `Gel A B R` and "the
relation `R`" are meant to be DEFINITIONALLY inter-derivable — a retract whose two legs are the
gel-β and gel-η computation rules:

  * **gel-β (the retraction `ungel ∘ gel = id_R`)**: `ungel (gel a b r) ↝ r` — projecting the
    relation witness out of a gel cell recovers it.  This is the shipped `gelBetaIotaRow` (the
    canonical iota table's relation-witness projection, `.scrutineeChildAt 0 2`), a RAW reduction
    rule, hence a raw `Step` — hence raw `Conv`.  This file ships exactly that leg as a `Conv`
    theorem: the COMPUTING half of the retract, machine-checked.

  * **gel-η (the section `gel ∘ ungel = id` on `Gel`)**: a bridge-typed `q : Gel A B R @ i` equals
    its gel-expansion `gel i (q[0/i]) (q[1/i]) (ungel (λj. q))`.  This leg is PROVABLY not a raw
    rewrite (its LHS references the subject under the interval-endpoint substitutions `q[0/i]`,
    `q[1/i]` — meta-substitutions, not first-order patterns), so it ships as the typed-only
    `gelEtaRow` in `etaRuleTable` and its `Conv`-content lives in the typed-conversion / NbE arc
    (ETA-T7 / Path-A), NOT here.  See `gelEtaRow` for the honest typed-only encoding.

Together the two legs are the judgmental `Gel A B R ≃ R` equivalence.  This module nails the leg
that COMPUTES; the docstring of `gelRelationRetract_witnessProjectionLeg` records the boundary to
the η leg.

## Zero-axiom verification

The gel-β `Step` is `Step.tableRedex gelBetaIotaRow_memTable () rfl` (the `firesOn?` head test
computes by `rfl` on the concrete `ungel(gel …)` cell, exactly as `Step.iotaFstPair`); the `Conv`
is `Conv.fromStep` of it.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditCoreSubstrate.lean`.
-/

namespace FX1Poly.Core

/-- The `gel` intro cell of its three components: the left endpoint `a : A`, the right endpoint
`b : B`, and the relation witness `r : R a b` (the interval the cell sits over is ambient, supplied
by the enclosing bridge binder — it is NOT a child). -/
abbrev gelCellOf {scope : Nat} (leftEndpoint rightEndpoint relationWitness : RawTerm scope) :
    RawTerm scope :=
  .mkGen .gen_gel ()
    (.childCons leftEndpoint (.childCons rightEndpoint (.childCons relationWitness .childNil)))

/-- The `ungel` elimination cell — the relation-witness projection applied to a bridge proof. -/
abbrev ungelProjection {scope : Nat} (bridgeProof : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_ungel () (.childCons bridgeProof .childNil)

/-- **gel-β as a single raw `Step`**: `ungel (gel a b r) ↝ r` — the canonical-iota-table
relation-witness projection firing on a concrete gel cell (the `firesOn?` head test computes by
`rfl`, mirroring `Step.iotaFstPair`). -/
theorem ungelGelStep {scope : Nat}
    (leftEndpoint rightEndpoint relationWitness : RawTerm scope) :
    Step (ungelProjection (gelCellOf leftEndpoint rightEndpoint relationWitness)) relationWitness :=
  .tableRedex gelBetaIotaRow_memTable () rfl

/-- **★ The computing retract leg: `ungel` is a definitional retraction of `gel`.**  Projecting the
relation witness out of a gel cell is judgmentally the witness — `ungel (gel a b r)` is `Conv` to
`r`.  This is the `ungel ∘ gel = id_R` half of the `Gel A B R ≃ R` judgmental equivalence, and it
COMPUTES (raw gel-β reduction).  The companion section leg `gel ∘ ungel = id` on `Gel` is the
type-directed gel-η rule (the typed-only `gelEtaRow`), whose `Conv`-content is the deferred
typed-conversion / NbE arc — it cannot be a raw reduction (its LHS needs interval-endpoint
substitutions of the subject). -/
theorem gelRelationRetract_witnessProjectionLeg {scope : Nat}
    (leftEndpoint rightEndpoint relationWitness : RawTerm scope) :
    Conv (ungelProjection (gelCellOf leftEndpoint rightEndpoint relationWitness)) relationWitness :=
  Conv.fromStep (ungelGelStep leftEndpoint rightEndpoint relationWitness)

end FX1Poly.Core
