import FX1Poly.Core.Normalize
import FX1Poly.Core.StepStarLength
import FX1Poly.Core.NormalFormUnique

/-! # FX1Poly/Core/NormalizeCost
    — the cost-instrumented kernel normalizer: EXACT evaluation cost on the SN fragment (COST-3 brick 1)

The COST-1 instrumentation recipe ported to the 198-generator kernel.
`RawTerm.normalizeWithCost` threads a step counter through the shipped
`Acc.rec` normalizer (`RawTerm.normalize`, Normalize.lean): at each
`reduceOnce` firing the counter increments, at the halt it reads zero.
The counted-chain vocabulary is the SHIPPED `StepStarN` (#368) — the
kernel's step-counted reduction needed no new relation.

  * `RawTerm.normalizeWithCost` / `normalizeCost` — the instrumented
    normalizer (constant pair motive over `Acc.rec`) and its cost
    projection.
  * ★ `normalizeWithCost_isExactChain` — **exactness**: a GENUINE
    counted chain (`StepStarN`) of exactly the reported cost from the
    term to the reported output.
  * `normalizeWithCost_fst_eq_normalize` — the instrumented output IS
    the normalizer's output.  Proved by NF-UNIQUENESS on the SN
    fragment (`normalForm_unique`), NOT by aligning the two `Acc.rec`
    matches — fst's reachability comes free from the exactness chain
    (`StepStarN.toStepStar`) and fst's normality by the mirror
    induction, so uniqueness identifies the outputs.
  * ★ `normalizeCost_isExact` — the packaged headline: every
    strongly-normalizing kernel term carries an EXACT computable
    evaluation cost — a counted chain of exactly `normalizeCost` steps
    reaching THE normal form.
  * `normalizeCost_unit_isZero` — non-vacuity: the cost computes (the
    normal form `unit` costs zero, by kernel evaluation through the
    `Acc.intro` witness).

The typed packaging (`HasTypeDescPi` ⟹ calculable cost via the shipped
typed-SN theorems — the FX-language headline "every well-typed program
has calculable cost") is the later COST-3 brick; `IsStronglyNormalizing`
is definitionally `Acc StepStar.StepSuccessor`, so typed SN witnesses
feed this module directly.

Zero-axiom; gated in `FX1PolyAudit/AuditTypedSubstVecCwR.lean`. -/

namespace FX1Poly.Core

open Foundation

/-- **The cost-instrumented normalizer**: iterate `reduceOnce` along the
accessibility witness, counting the fired steps.  The constant pair
motive over `Acc.rec` is the COST-1 recipe at the kernel. -/
def RawTerm.normalizeWithCost {scope : Nat} (term : RawTerm scope)
    (accessible : Acc (@StepStar.StepSuccessor scope) term) : RawTerm scope × Nat :=
  Acc.rec
    (motive := fun _currentTerm _acc => RawTerm scope × Nat)
    (fun currentTerm _accStep normalizeRec =>
      match hReduce : RawTerm.reduceOnce currentTerm with
      | none => (currentTerm, 0)
      | some reduct =>
          let restPair := normalizeRec reduct (RawTerm.reduceOnce_sound hReduce)
          (restPair.fst, restPair.snd + 1))
    accessible

/-- One-step unfolding of `normalizeWithCost` at an `Acc.intro` witness
(holds by `rfl`; the proof handle for the correctness theorems). -/
theorem RawTerm.normalizeWithCost_unfold {scope : Nat} (term : RawTerm scope)
    (accStep : ∀ later, StepStar.StepSuccessor later term → Acc StepStar.StepSuccessor later) :
    RawTerm.normalizeWithCost term (.intro term accStep) =
      (match hReduce : RawTerm.reduceOnce term with
        | none => (term, 0)
        | some reduct =>
            let restPair := RawTerm.normalizeWithCost reduct
              (accStep reduct (RawTerm.reduceOnce_sound hReduce))
            (restPair.fst, restPair.snd + 1)) := rfl

/-- The exact evaluation cost of a strongly-normalizing kernel term. -/
def RawTerm.normalizeCost {scope : Nat} (term : RawTerm scope)
    (accessible : Acc (@StepStar.StepSuccessor scope) term) : Nat :=
  (RawTerm.normalizeWithCost term accessible).snd

/-- ★ **Exactness**: the instrumented normalizer's reported cost is
attained by a GENUINE counted chain (`StepStarN`) from the term to the
reported output — the cost is not an estimate.  By `Acc`-induction: the
halt is the length-0 chain; a fired step prepends `reduceOnce_sound` to
the inductive chain, incrementing the count in lockstep. -/
theorem RawTerm.normalizeWithCost_isExactChain {scope : Nat} (term : RawTerm scope)
    (accessible : Acc (@StepStar.StepSuccessor scope) term) :
    StepStarN (RawTerm.normalizeWithCost term accessible).snd term
      (RawTerm.normalizeWithCost term accessible).fst := by
  induction accessible with
  | intro currentTerm accStep ih =>
      rw [RawTerm.normalizeWithCost_unfold currentTerm accStep]
      split
      · exact StepStarN.reflN currentTerm
      · next reduct hReduce =>
          exact StepStarN.transN (RawTerm.reduceOnce_sound hReduce)
            (ih reduct (RawTerm.reduceOnce_sound hReduce))

/-- The instrumented output is reached by a reduction chain (free from
the exactness chain by forgetting the count). -/
theorem RawTerm.normalizeWithCost_reducesToFst {scope : Nat} (term : RawTerm scope)
    (accessible : Acc (@StepStar.StepSuccessor scope) term) :
    StepStar term (RawTerm.normalizeWithCost term accessible).fst :=
  (RawTerm.normalizeWithCost_isExactChain term accessible).toStepStar

/-- The instrumented output is structurally normal (the mirror of
`normalize_isStepNormalForm` over the instrumented recursion). -/
theorem RawTerm.normalizeWithCost_fst_isStepNormalForm {scope : Nat} (term : RawTerm scope)
    (accessible : Acc (@StepStar.StepSuccessor scope) term) :
    RawTerm.isStepNormalForm (RawTerm.normalizeWithCost term accessible).fst := by
  induction accessible with
  | intro currentTerm accStep ih =>
      rw [RawTerm.normalizeWithCost_unfold currentTerm accStep]
      split
      · next hReduce => exact RawTerm.reduceOnce_complete hReduce
      · next reduct hReduce => exact ih reduct (RawTerm.reduceOnce_sound hReduce)

/-- **The instrumented output IS the normalizer's output** — by
NF-uniqueness on the SN fragment, NOT by aligning the two `Acc.rec`
recursions: both outputs are normal forms reached from the same term,
and an SN term has one normal form. -/
theorem RawTerm.normalizeWithCost_fst_eq_normalize {scope : Nat} (term : RawTerm scope)
    (accessible : Acc (@StepStar.StepSuccessor scope) term) :
    (RawTerm.normalizeWithCost term accessible).fst = RawTerm.normalize term accessible :=
  normalForm_unique accessible
    (RawTerm.normalizeWithCost_reducesToFst term accessible)
    (RawTerm.normalizeWithCost_fst_isStepNormalForm term accessible)
    (RawTerm.normalize_reducesTo term accessible)
    (RawTerm.normalize_isStepNormalForm term accessible)

/-- ★ **The exact-cost theorem**: every strongly-normalizing kernel term
has an EXACT computable evaluation cost — a counted chain of exactly
`normalizeCost` steps from the term to THE normal form computed by
`RawTerm.normalize`. -/
theorem RawTerm.normalizeCost_isExact {scope : Nat} (term : RawTerm scope)
    (accessible : Acc (@StepStar.StepSuccessor scope) term) :
    StepStarN (RawTerm.normalizeCost term accessible) term
      (RawTerm.normalize term accessible) := by
  have exactChain := RawTerm.normalizeWithCost_isExactChain term accessible
  rw [RawTerm.normalizeWithCost_fst_eq_normalize term accessible] at exactChain
  exact exactChain

/-! ## Non-vacuity — the cost computes -/

/-- The closed `unit` value (a normal form). -/
def unitNormalFormFixture : RawTerm 0 := .mkGen .gen_unit () .childNil

/-- `unit` is a `reduceOnce` halt (kernel evaluation over the generator
table). -/
theorem unitNormalFormFixture_reduceOnce_halts :
    RawTerm.reduceOnce unitNormalFormFixture = none := rfl

/-- The accessibility witness for the normal form `unit`: it has no
successors (`reduceOnce` completeness blocks every step). -/
def unitNormalFormFixture_accessible :
    Acc (@StepStar.StepSuccessor 0) unitNormalFormFixture :=
  Acc.intro unitNormalFormFixture
    (fun _later laterStep =>
      absurd laterStep
        (RawTerm.isStepNormalForm_blocks_step
          (RawTerm.reduceOnce_complete unitNormalFormFixture_reduceOnce_halts) _later))

/-- **The cost computes**: normalizing the normal form `unit` costs
exactly zero — the instrumented normalizer evaluates through the
concrete `Acc.intro` witness by kernel computation. -/
theorem RawTerm.normalizeCost_unit_isZero :
    RawTerm.normalizeCost unitNormalFormFixture unitNormalFormFixture_accessible = 0 := rfl

end FX1Poly.Core
