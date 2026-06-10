import FX1Poly.Typed.GrownCanonicalForms
import FX1Poly.Typed.ConvergentCanonicityBoundary
import FX1Poly.Typed.CertifiedWordReductionTermination
import FX1Poly.Typed.HasTypeDescPiSubjectReductionUnconditional
import FX1Poly.Core.WeakNormalization
import FX1Poly.Typed.UniverseCodeShape

/-! # FX1Poly/Typed/ThirdWayBoundaries
    — the third-way (word/RPO/convergent) leg's THREE boundary bricks, machine-checked

The POWERFUL-SN reframing (#653) demands that what the third leg can and cannot supply be COMMITTED
as theorems, not prose.  This file ships the three outstanding boundary bricks:

## Brick 1 — third-way CONSISTENCY decomposes as Tait-free ⊕ Tait-imported (#1146)

`ThirdWayConsistencyBoundary` records the decomposition of consistency-at-`Empty` (which IS
canonicity-at-`Empty`, since `Empty` has no value):

  * `taitFreeNormalFormConsistency` — the Tait-FREE half: no closed NORMAL inhabitant of
    `emptyTypeCell` (`noClosedNormalTermAtEmptyType`, canonical forms only — no reducibility model).
  * `taitImportedNormalization` — the Tait-IMPORTED half: reaching a normal form from an ARBITRARY
    closed inhabitant is weak normalization (`exists_normalForm_of_isStronglyNormalizing`), whose
    only β-covering supply is typed SN (`stronglyNormalizingOfWfContextDesc` = the Tait fundamental;
    raw β admits no RPO, `betaNotOrientableByErasure`).
  * `betaNormalityGap` — the NO-GO keeping the import essential: a convergent (ι∪η) normal form can
    still β-step (`convergentNormalFormNeedNotBeCanonical`), so the Tait-free convergent fragment
    cannot supply the normalization step.

`thirdWayConsistencyAssembled` re-derives full consistency through exactly this decomposition
(normalize via the imported half, transport the typing along the chain via `subjectReductionStar`,
refute the normal form via the free half) — making the import boundary VISIBLE in the proof term.

## Brick 2 — the termination ≡ SN correspondence is CHAIN-LEVEL (#642)

The real half: `typedRootWordReductionTerminates` (word-rewrite chains induced from a well-typed
root terminate — CONSUMES SN-043).  The mirror shipped here,
`infiniteTermChainInducesInfiniteWordChain`, gives the divergence direction: any infinite term
chain induces an infinite `fxStepSystem` word chain AND refutes SN of its root — so term-SN and
induced-word-termination stand or fall together, chain by chain.  An unrestricted iff
("every word chain from `t.toCode` terminates → `t` SN") is NOT stated: extracting an infinite
chain from `¬ Acc` needs choice, off the zero-axiom menu.  The independent-CANONICITY claim for
this leg stays dropped per the refutation `convergentNormalFormNeedNotBeCanonical`.

## Brick 3 — the word→Conv reverse is BLOCKED by code collapse (#641)

Forward is shipped (`Conv.toWordJoinable`); the REVERSE (word-joinable → `Conv`) is blocked
because `RawTerm.toCode` is NOT injective: `payloadToNat` collapses every non-`Nat`/`Fin` payload
to `0`, so distinct universe codes share one word.  `RawTerm.toCode_not_injective` commits the
counterexample (`Type@0` vs `Type@1`): a common word-reduct need not decode to a common
term-reduct.  The residual (a code-injectivity-on-certified-terms lemma, or a payload-faithful
encoding) is named, not absorbed.

## Zero-axiom verification

Every field is a shipped named theorem or a two-line composition of shipped theorems; the
non-injectivity witness is `universeCodeCell_inj` + `LevelExpr.noConfusion` + a `rfl`/`decide`
code computation.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Per-declaration audit-gated in `FX1PolyAudit/CapstoneSignoff.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The third-way consistency boundary (#1146)**: consistency-at-`Empty` decomposed into its
Tait-FREE normal-form half, its Tait-IMPORTED normalization half, and the NO-GO witness that keeps
the import essential. -/
structure ThirdWayConsistencyBoundary (profile : PolyProfile) : Prop where
  /-- Tait-FREE: no closed NORMAL term inhabits `emptyTypeCell` (canonical forms only). -/
  taitFreeNormalFormConsistency : ∀ {subject : RawTerm 0},
    HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject
      (emptyTypeCell (scope := 0)) →
    RawTerm.isStepNormalForm subject → False
  /-- Tait-IMPORTED: every closed inhabitant reaches a normal form — weak normalization from typed
  SN, the step only the Tait fundamental supplies (raw β admits no RPO). -/
  taitImportedNormalization : ∀ {subject : RawTerm 0},
    HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject
      (emptyTypeCell (scope := 0)) →
    ∃ normalForm : RawTerm 0, StepStar subject normalForm ∧ RawTerm.isStepNormalForm normalForm
  /-- The NO-GO: a convergent (ι∪η) normal form can still β-step — the Tait-free convergent
  fragment cannot supply the normalization half. -/
  betaNormalityGap : ∃ closedTerm value : RawTerm 0,
    (∀ reduct, ¬ IotaEtaStep closedTerm reduct) ∧ Step closedTerm value

/-- **The boundary holds** — each field is the shipped named theorem:
`noClosedNormalTermAtEmptyType` / `exists_normalForm_of_isStronglyNormalizing` over
`stronglyNormalizingOfWfContextDesc` / `convergentNormalFormNeedNotBeCanonical`. -/
theorem thirdWayConsistencyBoundaryHolds {profile : PolyProfile} :
    ThirdWayConsistencyBoundary profile where
  taitFreeNormalFormConsistency typed normal :=
    HasTypeDescPi.noClosedNormalTermAtEmptyType typed normal
  taitImportedNormalization typed :=
    exists_normalForm_of_isStronglyNormalizing
      (HasTypeDescPi.stronglyNormalizingOfWfContextDesc WfContextDesc.emptyIsWellFormed typed)
  betaNormalityGap := convergentNormalFormNeedNotBeCanonical

/-- **Third-way consistency, assembled THROUGH the boundary** — normalize via the Tait-imported
half, transport the typing along the chain (`subjectReductionStar`), refute the normal form via
the Tait-free half.  Same conclusion as `emptyConsistencyViaCandidateBridge`, but with the
Tait-import made visible as exactly one proof step. -/
theorem thirdWayConsistencyAssembled {profile : PolyProfile} {subject : RawTerm 0}
    (typed : HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject
      (emptyTypeCell (scope := 0))) :
    False := by
  obtain ⟨normalForm, chain, normal⟩ :=
    thirdWayConsistencyBoundaryHolds.taitImportedNormalization typed
  exact thirdWayConsistencyBoundaryHolds.taitFreeNormalFormConsistency
    (HasTypeDescPi.subjectReductionStar WfContextDescPi.emptyIsWellFormed typed chain) normal

/-- **The divergence mirror of `typedRootWordReductionTerminates` (#642)**: an infinite term chain
induces an infinite `fxStepSystem` word chain AND refutes SN of its root.  Together with the
typed-root termination theorem this is the chain-level termination ≡ SN correspondence; the
unrestricted iff is not stated (extracting an infinite chain from `¬ Acc` needs choice). -/
theorem infiniteTermChainInducesInfiniteWordChain {scope : Nat}
    (reductionSequence : Nat → RawTerm scope)
    (eachStepsToNext : ∀ index, Step (reductionSequence index) (reductionSequence (index + 1))) :
    (∀ index, FxWordRewritesOneStep fxStepSystem
        (reductionSequence index).toCode (reductionSequence (index + 1)).toCode) ∧
      ¬ StepStar.IsStronglyNormalizing (reductionSequence 0) :=
  ⟨certifiedReductionInducesWordChain reductionSequence eachStepsToNext,
   notStronglyNormalizing_of_infiniteReduction reductionSequence eachStepsToNext⟩

/-- **`RawTerm.toCode` is NOT injective (#641's reverse blocker, committed)**: `payloadToNat`
collapses every non-`Nat`/`Fin` payload to `0`, so the distinct universe codes `Type@0` and
`Type@1` share one word.  Hence word-joinability cannot be reflected back to `Conv` through
decoding — the word→Conv reverse needs a payload-faithful encoding or a code-injectivity-on-
certified-terms lemma (the named residual). -/
theorem _root_.FX1Poly.Core.RawTerm.toCode_not_injective :
    ∃ leftTerm rightTerm : RawTerm 0,
      leftTerm ≠ rightTerm ∧ leftTerm.toCode = rightTerm.toCode :=
  ⟨universeCodeCell LevelExpr.lzero UniverseFlag.standard,
   universeCodeCell LevelExpr.lzero.lsucc UniverseFlag.standard,
   fun cellsEqual => LevelExpr.noConfusion (universeCodeCell_inj cellsEqual).1,
   rfl⟩

end FX1Poly.Typed
