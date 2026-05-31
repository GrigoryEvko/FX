import FX1Poly.Core.StratifiedReducibleTypeCandidate

/-! # Foundation/PolyCell/Core/StratifiedReducibleTypeNeutral
    — neutrals are weak-head-normal, discharging the universe candidate's neutral-inclusion leg

Last brick left the Tarski-universe candidate's CR-hood conditional on two type-level interface hypotheses
on the lower relation: `lowerForwardStep` (discharged via `forwardStep`) and `lowerNeutralInclusion` (a
neutral type all of whose reducts are reducible types is itself a reducible type).  This file discharges
the second leg and closes the result UNCONDITIONALLY at every level.

The key missing lemma is `IsNeutral.noWeakHeadStep`: a neutral term admits no weak-head step.  It is the
engine that lets a neutral type fire the `neutral` arm of `ReducibleTypeStep` (which demands weak-head
normality).  The proof inducts on the 12-arm `IsNeutral`:

  * `var` — the only weak-head step shape matching a variable root is `rootIota`, and no `IotaHeadStep`
    fires on a variable (`cases iotaStep` is vacuous); the `WeakHeadStep.not_from_lam` pattern.
  * `app` — `beta` would force the neutral head to be a λ (impossible: `cases headIsNeutral` has no λ arm);
    `appCongruence` contradicts the head's induction hypothesis; `rootIota` is vacuous (β is the SEPARATE
    `beta` constructor — no `IotaHeadStep` is app-rooted).
  * each eliminator (`fst`/`snd`/`boolElim`/`natElim`/`natRec`/`listElim`/`optionMatch`/`eitherMatch`/`idJ`/
    `idStrictRec`) — `rootIota` forces the scrutinee to a CONSTRUCTOR (`true`/`pair`/`zero`/`succ`/…), which
    has no `IsNeutral` arm (`cases iotaStep <;> cases scrutineeIsNeutral`); the matching `scrutineeCong`
    contradicts the scrutinee's induction hypothesis.

From it, `ReducibleTypeStep.reducibleOfNeutral` (a neutral type IS a reducible type — fire the `neutral`
arm with weak-head normality + the non-Π, non-universe root) discharges `lowerNeutralInclusion`, and the
unconditional `ReducibleTypeAt.universeCandidateIsReducibilityCandidate` follows: at every fuel level the
universe code's candidate is a genuine Girard reducibility candidate.

## Zero-axiom verification

`induction` over `IsNeutral`; each arm `cases` on `WeakHeadStep` then (for `rootIota`) on `IotaHeadStep`,
all vacuous-by-root or closed by an induction hypothesis / a non-neutral constructor.  The root
disequalities are `rootGenerator` reductions refuted by `nomatch`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Swept per declaration by `#audit_namespace
FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation
open StepStar

/-- **A neutral term admits no weak-head step.**  Stuck at the root: no β (the head/scrutinee never reaches
a λ or a constructor), no root-ι (same), no congruence into a sub-reduct (the principal child is neutral,
so its induction hypothesis forbids a weak-head step).  This is the weak-head-normality the `neutral` arm of
`ReducibleTypeStep` demands of a neutral type. -/
theorem IsNeutral.noWeakHeadStep {scope : Nat} {term : RawTerm scope}
    (neutral : IsNeutral term) :
    ∀ reduct : RawTerm scope, ¬ WeakHeadStep term reduct := by
  induction neutral with
  | var _index =>
      intro reduct weakHeadStep
      cases weakHeadStep with
      | rootIota iotaStep => cases iotaStep
  | app headIsNeutral headNoWeakHeadStep =>
      intro reduct weakHeadStep
      cases weakHeadStep with
      | beta => cases headIsNeutral
      | appCongruence functionStep => exact headNoWeakHeadStep _ functionStep
      | rootIota iotaStep => cases iotaStep
  | fst scrutineeIsNeutral scrutineeNoWeakHeadStep =>
      intro reduct weakHeadStep
      cases weakHeadStep with
      | rootIota iotaStep => cases iotaStep <;> cases scrutineeIsNeutral
      | scrutineeFst scrutineeStep => exact scrutineeNoWeakHeadStep _ scrutineeStep
  | snd scrutineeIsNeutral scrutineeNoWeakHeadStep =>
      intro reduct weakHeadStep
      cases weakHeadStep with
      | rootIota iotaStep => cases iotaStep <;> cases scrutineeIsNeutral
      | scrutineeSnd scrutineeStep => exact scrutineeNoWeakHeadStep _ scrutineeStep
  | boolElim scrutineeIsNeutral scrutineeNoWeakHeadStep =>
      intro reduct weakHeadStep
      cases weakHeadStep with
      | rootIota iotaStep => cases iotaStep <;> cases scrutineeIsNeutral
      | scrutineeBoolElim scrutineeStep => exact scrutineeNoWeakHeadStep _ scrutineeStep
  | natElim scrutineeIsNeutral scrutineeNoWeakHeadStep =>
      intro reduct weakHeadStep
      cases weakHeadStep with
      | rootIota iotaStep => cases iotaStep <;> cases scrutineeIsNeutral
      | scrutineeNatElim scrutineeStep => exact scrutineeNoWeakHeadStep _ scrutineeStep
  | natRec scrutineeIsNeutral scrutineeNoWeakHeadStep =>
      intro reduct weakHeadStep
      cases weakHeadStep with
      | rootIota iotaStep => cases iotaStep <;> cases scrutineeIsNeutral
      | scrutineeNatRec scrutineeStep => exact scrutineeNoWeakHeadStep _ scrutineeStep
  | listElim scrutineeIsNeutral scrutineeNoWeakHeadStep =>
      intro reduct weakHeadStep
      cases weakHeadStep with
      | rootIota iotaStep => cases iotaStep <;> cases scrutineeIsNeutral
      | scrutineeListElim scrutineeStep => exact scrutineeNoWeakHeadStep _ scrutineeStep
  | optionMatch scrutineeIsNeutral scrutineeNoWeakHeadStep =>
      intro reduct weakHeadStep
      cases weakHeadStep with
      | rootIota iotaStep => cases iotaStep <;> cases scrutineeIsNeutral
      | scrutineeOptionMatch scrutineeStep => exact scrutineeNoWeakHeadStep _ scrutineeStep
  | eitherMatch scrutineeIsNeutral scrutineeNoWeakHeadStep =>
      intro reduct weakHeadStep
      cases weakHeadStep with
      | rootIota iotaStep => cases iotaStep <;> cases scrutineeIsNeutral
      | scrutineeEitherMatch scrutineeStep => exact scrutineeNoWeakHeadStep _ scrutineeStep
  | idJ witnessIsNeutral witnessNoWeakHeadStep =>
      intro reduct weakHeadStep
      cases weakHeadStep with
      | rootIota iotaStep => cases iotaStep <;> cases witnessIsNeutral
      | scrutineeIdJ witnessStep => exact witnessNoWeakHeadStep _ witnessStep
  | idStrictRec witnessIsNeutral witnessNoWeakHeadStep =>
      intro reduct weakHeadStep
      cases weakHeadStep with
      | rootIota iotaStep => cases iotaStep <;> cases witnessIsNeutral
      | scrutineeIdStrictRec witnessStep => exact witnessNoWeakHeadStep _ witnessStep

/-- **A neutral type is a stratified reducible type.**  It is weak-head-normal (`IsNeutral.noWeakHeadStep`)
and its root is an eliminator/variable generator — never `gen_piTyCode`, never `gen_universeCode` — so the
`neutral` arm of `ReducibleTypeStep` fires with the strong-normalization candidate.  This DISCHARGES the
`lowerNeutralInclusion` interface leg (the reducts hypothesis is unused: neutrality alone suffices). -/
theorem ReducibleTypeStep.reducibleOfNeutral {scope : Nat}
    {lowerReducible : RawTerm scope → (RawTerm scope → Prop) → Prop}
    {typeCode : RawTerm scope} (neutral : IsNeutral typeCode) :
    ∃ candidate : RawTerm scope → Prop, ReducibleTypeStep lowerReducible typeCode candidate := by
  refine ⟨IsStronglyNormalizing, ReducibleTypeStep.neutral
    (fun reduct => neutral.noWeakHeadStep reduct) ?notPiType ?notUniverse⟩
  · cases neutral <;> exact fun rootEquation => nomatch rootEquation
  · cases neutral <;> exact fun rootEquation => nomatch rootEquation

/-- **A neutral type is reducible at every level** — `reducibleOfNeutral` through the `Nat` recursion of
`ReducibleTypeAt`.  Explicit `ReducibleTypeStep.reducibleOfNeutral` avoids a self-recursive resolution. -/
theorem ReducibleTypeAt.reducibleOfNeutral {scope : Nat} {level : Nat}
    {typeCode : RawTerm scope} (neutral : IsNeutral typeCode) :
    ∃ candidate : RawTerm scope → Prop, ReducibleTypeAt level typeCode candidate := by
  cases level with
  | zero => exact ReducibleTypeStep.reducibleOfNeutral neutral
  | succ predLevel => exact ReducibleTypeStep.reducibleOfNeutral neutral

/-- **The Tarski-universe candidate is UNCONDITIONALLY a Girard reducibility candidate at every level.**
The conditional `ReducibleTypeStep.universeCandidateIsReducibilityCandidate` with both interface legs now
discharged for `ReducibleTypeAt level`: the forward leg by `ReducibleTypeAt.forwardStep`, the neutral leg by
`ReducibleTypeAt.reducibleOfNeutral`.  So the candidate a universe code denotes at level `level + 1`
(namely `universeReducibilityPredicate (ReducibleTypeAt level)`) is a legitimate reducibility candidate —
the universe is reducibility-sound, with no remaining hypothesis. -/
theorem ReducibleTypeAt.universeCandidateIsReducibilityCandidate {scope : Nat} {level : Nat} :
    IsReducibilityCandidate
      (universeReducibilityPredicate (ReducibleTypeAt (scope := scope) level)) :=
  ReducibleTypeStep.universeCandidateIsReducibilityCandidate
    (fun reducible step => ReducibleTypeAt.forwardStep reducible step)
    (fun neutral _reductsAreReducible => ReducibleTypeAt.reducibleOfNeutral neutral)

end FX1Poly.Core
