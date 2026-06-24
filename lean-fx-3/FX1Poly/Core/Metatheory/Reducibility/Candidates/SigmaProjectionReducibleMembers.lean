import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationIotaRedexes
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationConstructors
import FX1Poly.Core.Rewriting.Reduction.Head.IotaHeadStep
import FX1Poly.Core.Metatheory.Reducibility.Candidates.ReducibilityCandidate
import FX1Poly.Core.Metatheory.Reducibility.Candidates.CandidateInterpretationDeterminism
import FX1Poly.Core.Metatheory.Canonicity.SigmaProjectionCanonicalComputation

/-! # FX1Poly/Core/SigmaProjectionReducibleMembers
    — the PROJECTION-based Σ reducibility clause (the carrier-aware product candidate's residue resolver)

The carrier-aware product candidate `carrierAwarePairCandidate firstCandidate secondCandidate` records
component membership only at the term's NORMAL forms (`pairValueWithMembers` requires the components to be
normal).  That suffices for canonicity and the type's strong normalization, but it WALLS the projection
eliminator (`fst`/`snd`) fundamental-theorem arm: the FT's projection valueHandler fires its component residue
`firstMemberIfReachesPair : ∀ a b, scrutinee ↝* pairCell a b → firstCandidate a` at a WEAK-HEAD pair focus
whose components `a`, `b` are reducible-but-NOT-normal.  Reading `firstCandidate a` off the normal-form record
would need to lift `firstCandidate aNormalForm` BACKWARD along `a ↝* aNormalForm` — backward closure along
arbitrary internal reduction, which a general reducibility candidate does NOT have.

This file ships the clause that resolves that obstruction WITHOUT backward closure: the **projection-based**
Σ-membership clause, the standard Girard formulation of the product candidate via its projections.

  * `sigmaProjectionMembers firstCandidate secondCandidate term` — `firstCandidate (fstCell term) ∧
    secondCandidate (sndCell term)`: the projections of `term` lie in the carrier candidates.

The decisive property is `*_firstComponentOfReachesPair` / `*_secondComponentOfReachesPair`: when a member
reaches `pairCell a b`, the component `a` is a `firstCandidate` member — derived by FORWARD closure, NOT
backward.  `term ↝* pairCell a b` lifts under `fst` (`StepStar.fstScrutinee`) and ι-projects
(`IotaHeadStep.iotaFstPair`) to `fstCell term ↝* a`; the clause's first conjunct `firstCandidate (fstCell term)`
then carries forward along that reduction by `IsReducibilityCandidate.closedUnderStepStar` (CR2 iterated).  This
is the exact discharge the native fundamental theorem's `fst`/`snd`/`eitherMatch` elim rows need to become
residue-FREE — the unblock for the `elimFundamental` premise of the native closed-term SN / consistency leg.

The clause is closed under the moves the conjoined candidate inherits, each WITHOUT backward closure:

  * `*_closedUnderStep` (CR2) — a `Step` of `term` lifts under each projection; the projected member carries
    forward by `closedUnderStepStar`;
  * `*_memberWeakHeadExpansion` (WHE) — a weak-head step of `source` lifts under each projection to a weak-head
    step (`WeakHeadStep.scrutineeFst` / `…Snd`), discharged by the carrier candidate's own weak-head expansion
    (the `firstHeadExpand` / `secondHeadExpand` interface the projection FT engines already take), with the
    projected source strongly normalizing by `fst`/`snd_isStronglyNormalizing_of_argument`;
  * `*_ofReducibleComponents` (intro) — `fstCell (pairCell first second)` ι-reduces to `first`, so a pair of
    reducible components has reducible projections by one weak-head expansion at each projection;
  * `*_congr` — pointwise-equivalent carriers yield pointwise-equivalent clauses (the determinism finisher).

## Zero-axiom verification

Projection congruence (`StepStar.fstScrutinee` / `…sndScrutinee`) + the ι head steps
(`IotaHeadStep.iotaFstPair` / `…iotaSndPair`) + `IsReducibilityCandidate.closedUnderStepStar` + the projection
SN lemmas + the weak-head-expansion interface.  No backward closure, no `funext`.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Core

open StepStar

/-- The unary `fst` projection cell over its sole child (the pair scrutinee).  A file-local reducible copy of
the (file-private) projection-cell abbreviation, so the projection primitives apply by defeq. -/
private abbrev fstCell {scope : Nat} (scrutinee : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_fst () (.childCons scrutinee .childNil)

/-- The unary `snd` projection cell over its sole child (the pair scrutinee).  The `snd` twin of `fstCell`. -/
private abbrev sndCell {scope : Nat} (scrutinee : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_snd () (.childCons scrutinee .childNil)

/-- **The projection-based Σ-membership clause.**  A term's two projections lie in the carrier candidates:
`firstCandidate (fstCell term) ∧ secondCandidate (sndCell term)`.  The standard Girard product candidate read
through `fst`/`snd` — closed under reduction and weak-head expansion by FORWARD closure of the carriers (no
backward closure), and supplying reached-pair component membership directly by projection. -/
def sigmaProjectionMembers {scope : Nat} (firstCandidate secondCandidate : RawTerm scope → Prop)
    (term : RawTerm scope) : Prop :=
  firstCandidate (fstCell term) ∧ secondCandidate (sndCell term)

/-- **The projection clause is forward-closed under one `Step`** (CR2).  Each projection of `reduct` is a
multi-step reduct of the corresponding projection of `term` (`StepStar.fstScrutinee` of the single step), along
which the carrier candidate carries membership forward by `closedUnderStepStar`. -/
theorem sigmaProjectionMembers_closedUnderStep {scope : Nat}
    {firstCandidate secondCandidate : RawTerm scope → Prop}
    (firstIsCandidate : IsReducibilityCandidate firstCandidate)
    (secondIsCandidate : IsReducibilityCandidate secondCandidate)
    {term reduct : RawTerm scope}
    (members : sigmaProjectionMembers firstCandidate secondCandidate term) (step : Step term reduct) :
    sigmaProjectionMembers firstCandidate secondCandidate reduct :=
  ⟨firstIsCandidate.closedUnderStepStar (StepStar.fstScrutinee (StepStar.single step)) members.1,
   secondIsCandidate.closedUnderStepStar (StepStar.sndScrutinee (StepStar.single step)) members.2⟩

/-- **The projection clause is closed under member weak-head expansion** (WHE).  A weak-head step of `source`
lifts under each projection to a weak-head step (`WeakHeadStep.scrutineeFst` / `…Snd`); the carrier candidate's
own weak-head expansion (`firstHeadExpand` / `secondHeadExpand`, the interface the projection FT engines take)
carries membership back, with `fstCell source` / `sndCell source` strongly normalizing from `source` by the
projection SN lemmas. -/
theorem sigmaProjectionMembers_memberWeakHeadExpansion {scope : Nat}
    {firstCandidate secondCandidate : RawTerm scope → Prop}
    (firstHeadExpand : ∀ {redex contractum : RawTerm scope},
        WeakHeadStep redex contractum → firstCandidate contractum →
        IsStronglyNormalizing redex → firstCandidate redex)
    (secondHeadExpand : ∀ {redex contractum : RawTerm scope},
        WeakHeadStep redex contractum → secondCandidate contractum →
        IsStronglyNormalizing redex → secondCandidate redex)
    {source reduct : RawTerm scope}
    (weakHeadStep : WeakHeadStep source reduct)
    (sourceStronglyNormalizing : IsStronglyNormalizing source)
    (reductMembers : sigmaProjectionMembers firstCandidate secondCandidate reduct) :
    sigmaProjectionMembers firstCandidate secondCandidate source :=
  ⟨firstHeadExpand (WeakHeadStep.scrutineeFst weakHeadStep) reductMembers.1
     (fst_isStronglyNormalizing_of_argument sourceStronglyNormalizing),
   secondHeadExpand (WeakHeadStep.scrutineeSnd weakHeadStep) reductMembers.2
     (snd_isStronglyNormalizing_of_argument sourceStronglyNormalizing)⟩

/-- **★ Reached-pair FIRST component membership — the residue resolver, by FORWARD closure.**  When a projection
member reaches `pairCell first second`, the first component is a `firstCandidate` member: `fstCell term`
multi-steps to `first` (`StepStar.fstScrutinee` of the reach, then the `iotaFstPair` ι), and the clause's first
conjunct carries forward along that reduction by `closedUnderStepStar`.  This is the discharge the bounded `fst`
fundamental-theorem arm's component residue `firstMemberIfReachesPair` consumes — with NO backward closure and NO
assumption that `first` is normal. -/
theorem sigmaProjectionMembers_firstComponentOfReachesPair {scope : Nat}
    {firstCandidate secondCandidate : RawTerm scope → Prop}
    (firstIsCandidate : IsReducibilityCandidate firstCandidate)
    {term first second : RawTerm scope}
    (members : sigmaProjectionMembers firstCandidate secondCandidate term)
    (reachesPair : StepStar term (pairCell first second)) :
    firstCandidate first :=
  firstIsCandidate.closedUnderStepStar
    (StepStar.transLast (StepStar.fstScrutinee reachesPair) IotaHeadStep.iotaFstPair.toStep) members.1

/-- **★ Reached-pair SECOND component membership — the residue resolver, by FORWARD closure.**  Symmetric to
`sigmaProjectionMembers_firstComponentOfReachesPair`, projecting the second component via `StepStar.sndScrutinee`
and the `iotaSndPair` ι.  The discharge the bounded `snd` FT arm's `secondMemberIfReachesPair` consumes. -/
theorem sigmaProjectionMembers_secondComponentOfReachesPair {scope : Nat}
    {firstCandidate secondCandidate : RawTerm scope → Prop}
    (secondIsCandidate : IsReducibilityCandidate secondCandidate)
    {term first second : RawTerm scope}
    (members : sigmaProjectionMembers firstCandidate secondCandidate term)
    (reachesPair : StepStar term (pairCell first second)) :
    secondCandidate second :=
  secondIsCandidate.closedUnderStepStar
    (StepStar.transLast (StepStar.sndScrutinee reachesPair) IotaHeadStep.iotaSndPair.toStep) members.2

/-- **The projection clause's introduction: reducible components give reducible projections.**  A pair of
reducible carrier components has reducible projections — `fstCell (pairCell first second)` ι-reduces (one
weak-head step, `iotaFstPair`) to `first`, so the carrier candidate's weak-head expansion carries `firstCandidate
first` back to `firstCandidate (fstCell (pairCell first second))`, with the projection strongly normalizing from
the components' SN.  The data-intro the bounded `pair` FT row produces for the projection clause. -/
theorem sigmaProjectionMembers_ofReducibleComponents {scope : Nat}
    {firstCandidate secondCandidate : RawTerm scope → Prop}
    (firstHeadExpand : ∀ {redex contractum : RawTerm scope},
        WeakHeadStep redex contractum → firstCandidate contractum →
        IsStronglyNormalizing redex → firstCandidate redex)
    (secondHeadExpand : ∀ {redex contractum : RawTerm scope},
        WeakHeadStep redex contractum → secondCandidate contractum →
        IsStronglyNormalizing redex → secondCandidate redex)
    {first second : RawTerm scope}
    (firstStronglyNormalizing : IsStronglyNormalizing first)
    (secondStronglyNormalizing : IsStronglyNormalizing second)
    (firstMember : firstCandidate first) (secondMember : secondCandidate second) :
    sigmaProjectionMembers firstCandidate secondCandidate (pairCell first second) :=
  ⟨firstHeadExpand IotaHeadStep.iotaFstPair.toWeakHeadStep firstMember
     (fst_isStronglyNormalizing_of_argument
       (pair_isStronglyNormalizing_of_components firstStronglyNormalizing secondStronglyNormalizing)),
   secondHeadExpand IotaHeadStep.iotaSndPair.toWeakHeadStep secondMember
     (snd_isStronglyNormalizing_of_argument
       (pair_isStronglyNormalizing_of_components firstStronglyNormalizing secondStronglyNormalizing))⟩

/-- **The projection clause is congruent in its carriers.**  Pointwise-equivalent carriers yield
pointwise-equivalent projection clauses — each conjunct swaps under the respective carrier iff at the
projection.  The determinism finisher the conjoined candidate's `assemble_congr` consumes. -/
theorem sigmaProjectionMembers_congr {scope : Nat}
    {firstCandidate1 firstCandidate2 secondCandidate1 secondCandidate2 : RawTerm scope → Prop}
    (firstIff : PointwiseIff firstCandidate1 firstCandidate2)
    (secondIff : PointwiseIff secondCandidate1 secondCandidate2) :
    PointwiseIff (sigmaProjectionMembers firstCandidate1 secondCandidate1)
      (sigmaProjectionMembers firstCandidate2 secondCandidate2) := by
  intro term
  constructor
  · rintro ⟨firstMember, secondMember⟩
    exact ⟨(firstIff _).mp firstMember, (secondIff _).mp secondMember⟩
  · rintro ⟨firstMember, secondMember⟩
    exact ⟨(firstIff _).mpr firstMember, (secondIff _).mpr secondMember⟩

end FX1Poly.Core
