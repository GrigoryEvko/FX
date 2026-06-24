import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationIotaRedexes
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationConstructors
import FX1Poly.Core.Rewriting.Reduction.Head.IotaHeadStep
import FX1Poly.Core.Rewriting.Reduction.Step.StepInversion
import FX1Poly.Core.Metatheory.Reducibility.Candidates.ReducibilityCandidate
import FX1Poly.Core.Metatheory.Reducibility.Candidates.CandidateInterpretationDeterminism
import FX1Poly.Core.Metatheory.Reducibility.Core.HeadExpansionClosure
import FX1Poly.Core.Metatheory.Reducibility.Stratified.StratifiedReducibleTypeHeadExpansion
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

/-- **Strong normalization REFLECTS through `fstCell`.**  A self-contained copy of the one-child SN reflection:
the generic engine `isStronglyNormalizing_child_of_oneChildCong` lives in the `Eliminators` layer, which the
`Candidates` layer may not import, so the `Acc`-descent argument is replayed here at the `fst` wrapper.  Any
`Step scrutinee scrutineeAfter` lifts under `fst` (`Step.cong` at the head child) to `Step (fstCell scrutinee)
(fstCell scrutineeAfter)`, so an infinite reduction of `scrutinee` would lift to one of `fstCell scrutinee`,
contradicting its accessibility.  Proved by `Acc` induction on the cell generalized over the wrapper equation.
This is what routes the projection clause's CR1 back to the scrutinee. -/
private theorem scrutinee_isStronglyNormalizing_of_fstCell {scope : Nat} {scrutinee : RawTerm scope}
    (cellTerminates : IsStronglyNormalizing (fstCell scrutinee)) : IsStronglyNormalizing scrutinee := by
  suffices general :
      ∀ {cellTerm : RawTerm scope}, Acc StepSuccessor cellTerm →
        ∀ {currentScrutinee : RawTerm scope}, cellTerm = fstCell currentScrutinee →
          Acc StepSuccessor currentScrutinee from
    general cellTerminates rfl
  intro cellTerm cellAccessible
  induction cellAccessible with
  | intro _cellWitness _cellPredecessors cellInductiveHypothesis =>
      intro currentScrutinee witnessEq
      subst witnessEq
      apply Acc.intro
      intro scrutineeAfter scrutineeStep
      exact cellInductiveHypothesis (fstCell scrutineeAfter)
        (Step.cong .gen_fst () (StepChildren.here (.childNil : RawTermChildren [] scope) scrutineeStep)) rfl

/-- **A neutral term's head is never the `pair` constructor.**  The Σ-data ι-vacuity discriminator (the `pair`
twin of `IsNeutral.rootGenerator_ne_optionNone` etc.): `IsNeutral` has no `gen_pair` arm, so every arm's concrete
head is refuted by `Generator.noConfusion`.  Used to kill the ι case of the `fst`/`snd` step inversion when the
scrutinee is neutral — a neutral scrutinee is never a pair, so the projection ι cannot fire. -/
private theorem isNeutralRootGeneratorNePair {scope : Nat} {term : RawTerm scope}
    (neutral : IsNeutral term) : term.rootGenerator ≠ Generator.gen_pair := by
  cases neutral <;> exact fun shapeEquation => Generator.noConfusion shapeEquation

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

/-- **★ The projection clause is β-spine head-expansion-closed** (the Π-codomain-ready property).  A spined
β-redex `applySpineApp (app (lam ann body) arg) spine` whose β-contractum has reducible projections has reducible
projections itself.  This is the Core piece the CONJOINED carrier-aware product candidate's `headExpansionClosed`
needs from the projection conjunct: the β-spine redex WEAK-HEAD-steps to its contractum (`WeakHeadStep.betaSpine`),
so this is exactly `sigmaProjectionMembers_memberWeakHeadExpansion` instantiated at that weak-head step — no new
proof, just the recognition that β-spine head-expansion is the weak-head expansion at `betaSpine`.  Takes the
carriers' GENERAL weak-head expansion (`firstHeadExpand`/`secondHeadExpand`), which at the Typed denote level is
supplied STANDALONE by `ReducibleTypeAtBounded.memberWeakHeadExpansion` (no IH threading) — the resolution of the
apparent "projection clause is not head-expansion-closed" obstruction: it IS, once the carriers are
saturated-style (general weak-head expansion), which `dataTaitCandidate` and every bounded-reducible candidate
are.  `firstIsCandidate` supplies the source SN: the contractum's SN reflects through `fstCell` and lifts back
over the β-spine by `betaSpineHeadExpansion`. -/
theorem sigmaProjectionMembers_headExpansionClosed {scope : Nat}
    {firstCandidate secondCandidate : RawTerm scope → Prop}
    (firstIsCandidate : IsReducibilityCandidate firstCandidate)
    (firstHeadExpand : ∀ {redex contractum : RawTerm scope},
        WeakHeadStep redex contractum → firstCandidate contractum →
        IsStronglyNormalizing redex → firstCandidate redex)
    (secondHeadExpand : ∀ {redex contractum : RawTerm scope},
        WeakHeadStep redex contractum → secondCandidate contractum →
        IsStronglyNormalizing redex → secondCandidate redex) :
    HeadExpansionClosed (sigmaProjectionMembers firstCandidate secondCandidate) := by
  intro domainAnn body argument spine domainAnnSN argumentSN contractumMember
  exact sigmaProjectionMembers_memberWeakHeadExpansion firstHeadExpand secondHeadExpand
    WeakHeadStep.betaSpine
    (betaSpineHeadExpansion domainAnnSN argumentSN
      (scrutinee_isStronglyNormalizing_of_fstCell (firstIsCandidate.stronglyNormalizing contractumMember.1)))
    contractumMember

/-- **The projection clause is closed under neutral expansion** (CR3).  A NEUTRAL term whose every one-step
reduct has reducible projections has reducible projections itself.  Each projection `fstCell term` / `sndCell
term` is neutral (`IsNeutral.fst` / `…snd`), so the carrier candidate's own CR3 (`neutralExpansion`) applies;
its per-reduct obligation inverts `Step (fstCell term) reduct` by `Step.from_fst` — the ι case is impossible
because a neutral `term` is never a pair (`isNeutralRootGeneratorNePair`), leaving the congruence case
`reduct = fstCell scrutineeAfter` with `Step term scrutineeAfter`, whose first projection is reducible by the
hypothesis at `scrutineeAfter`.  This is the conjunct CR3 the conjoined carrier-aware product candidate inherits
(its other conjunct, `dataTaitCandidate`, supplies the unconditional CR1 and canonicity). -/
theorem sigmaProjectionMembers_neutralExpansion {scope : Nat}
    {firstCandidate secondCandidate : RawTerm scope → Prop}
    (firstIsCandidate : IsReducibilityCandidate firstCandidate)
    (secondIsCandidate : IsReducibilityCandidate secondCandidate)
    {term : RawTerm scope} (neutral : IsNeutral term)
    (reductsMembers : ∀ reduct : RawTerm scope, Step term reduct →
        sigmaProjectionMembers firstCandidate secondCandidate reduct) :
    sigmaProjectionMembers firstCandidate secondCandidate term :=
  ⟨firstIsCandidate.neutralExpansion (IsNeutral.fst neutral) (fun reduct stepFst => by
      rcases Step.from_fst stepFst with
        ⟨_firstValue, _secondValue, termIsPair, _⟩ | ⟨scrutineeAfter, reductEq, scrutineeStep⟩
      · exact (isNeutralRootGeneratorNePair (termIsPair ▸ neutral) rfl).elim
      · subst reductEq; exact (reductsMembers scrutineeAfter scrutineeStep).1),
   secondIsCandidate.neutralExpansion (IsNeutral.snd neutral) (fun reduct stepSnd => by
      rcases Step.from_snd stepSnd with
        ⟨_firstValue, _secondValue, termIsPair, _⟩ | ⟨scrutineeAfter, reductEq, scrutineeStep⟩
      · exact (isNeutralRootGeneratorNePair (termIsPair ▸ neutral) rfl).elim
      · subst reductEq; exact (reductsMembers scrutineeAfter scrutineeStep).2)⟩

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

/-- **★ The projection clause is a Girard reducibility candidate.**  When both carriers are reducibility
candidates, so is `sigmaProjectionMembers firstCandidate secondCandidate` — the classical Girard product
candidate read through `fst`/`snd`:

  * **CR1** — a member's first projection is reducible, hence SN by the carrier's CR1, and SN reflects through
    `fstCell` back to the term (`scrutinee_isStronglyNormalizing_of_fstCell`);
  * **CR2** — `sigmaProjectionMembers_closedUnderStep` (each projection carries membership forward along the
    lifted reduction);
  * **CR3** — `sigmaProjectionMembers_neutralExpansion` (each projection is neutral, the carriers' CR3 apply).

The decisive feature versus the normal-form record `carrierAwarePairCandidate` is that membership is read off the
projections by FORWARD closure, so the reached-pair component residues (`*_firstComponentOfReachesPair`) discharge
WITHOUT backward closure — the exact unblock the native `fst`/`snd` elim FT rows need. -/
theorem sigmaProjectionMembers_isReducibilityCandidate {scope : Nat}
    {firstCandidate secondCandidate : RawTerm scope → Prop}
    (firstIsCandidate : IsReducibilityCandidate firstCandidate)
    (secondIsCandidate : IsReducibilityCandidate secondCandidate) :
    IsReducibilityCandidate (sigmaProjectionMembers firstCandidate secondCandidate) where
  stronglyNormalizing := fun members =>
    scrutinee_isStronglyNormalizing_of_fstCell (firstIsCandidate.stronglyNormalizing members.1)
  closedUnderStep := fun members step =>
    sigmaProjectionMembers_closedUnderStep firstIsCandidate secondIsCandidate members step
  neutralExpansion := fun neutral reductsMembers =>
    sigmaProjectionMembers_neutralExpansion firstIsCandidate secondIsCandidate neutral reductsMembers

end FX1Poly.Core
