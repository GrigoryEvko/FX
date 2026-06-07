import FX1Poly.Core.StepWordRewriteSoundness
import FX1Poly.Typed.OpenStronglyNormalizingUnconditional
import FX1Poly.Typed.UnboundedGrowthNotStronglyNormalizing

/-! # FX1Poly/Typed/CertifiedWordReductionTermination — Leg-3 word-rewrite termination on the certified fragment (SN-131)

The Leg-3 word-presentation substrate (`StepWordRewriteSoundness.lean`) encodes every FX reduction as a
one-step rewrite of the term-code word (`RawTerm.toCode : RawTerm scope → List Nat`) under the generated
system `fxStepSystem`: `Step.toWordRewrite : Step redex reduct → FxWordRewritesOneStep fxStepSystem
redex.toCode reduct.toCode`.  For the three-way SN closure (SN-150) Leg-3 needs its TERMINATION leg.

★ **The honest scoping.**  The FULL word system is NOT terminating — `FxWordRewritesOneStep` fires under
left/right word context (subword rewriting), `toCode` is non-injective, and an UNTYPED diverging term
(`growingDivergentTerm`, the unbounded-growth combinator) maps to a word with an infinite rewrite chain
(`untypedWordReductionDiverges` below).  So word-termination is FALSE as a property of the raw word system;
it holds only on the CERTIFIED fragment — words that are `toCode`-images of reductions rooted at a
WELL-TYPED term.  And there it consumes ONLY root strong normalization (SN-043 /
`stronglyNormalizingOfWfContextDesc`), NOT subject reduction: the root being typed makes EVERY reduction
sequence from it finite (`IsStronglyNormalizing` is `Acc StepSuccessor`, an all-paths property), regardless
of whether the intermediate reducts are themselves well-typed.  This is why Leg-3 termination is GCC-5-free
— it never needs the reduct to stay typed, only the root.

  * **`certifiedReductionInducesWordChain`** — the bridge: a `Step` reduction sequence's `toCode` images form
    a genuine `fxStepSystem` word-rewrite chain (`Step.toWordRewrite` pointwise).  The certified word
    reductions ARE real word rewrites.
  * **`typedRootWordReductionTerminates`** — the headline: a reduction sequence rooted at a well-typed term
    cannot be infinite.  Feeds the sequence to `notStronglyNormalizing_of_infiniteReduction` and discharges
    the resulting `IsStronglyNormalizing` obligation with `stronglyNormalizingOfWfContextDesc` (SN-043).  By
    `certifiedReductionInducesWordChain` the refuted sequence's images ARE an `fxStepSystem` chain — so the
    certified word reduction word-terminates.
  * **`untypedWordReductionDiverges`** — the necessity / non-vacuity: the full word system diverges on an
    UNTYPED word.  `growingDivergentTerm.toCode` admits an infinite `fxStepSystem` rewrite chain, and its
    source term is provably non-`IsStronglyNormalizing` — so the diverging words are exactly images of
    untypable terms (by SN-043's contrapositive), and the certified restriction in the headline is precisely
    what excludes them.  Mirrors SN-NECESSITY (#950) at the word layer.

## Zero-axiom

The bridge is `Step.toWordRewrite` applied pointwise; the headline is `apply
notStronglyNormalizing_of_infiniteReduction` + `rw [startsAtRoot]` + `stronglyNormalizingOfWfContextDesc`;
the necessity is the concrete `growingReductionSequence` images paired with `growingReductionSequence_steps`
mapped through `toWordRewrite` and the shipped `growingDivergentTerm_notStronglyNormalizing`.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- **The certified-reduction → word-chain bridge.**  Every `Step` in a reduction sequence maps to a
one-step `fxStepSystem` word rewrite of the `toCode` images (`Step.toWordRewrite`), so a term-reduction
sequence induces a genuine `fxStepSystem` word-rewrite chain.  The certified word reductions ARE real
word rewrites of the generated system. -/
theorem certifiedReductionInducesWordChain {scope : Nat}
    (reductionSequence : Nat → RawTerm scope)
    (eachStepsToNext : ∀ index, Step (reductionSequence index) (reductionSequence (index + 1))) :
    ∀ index, FxWordRewritesOneStep fxStepSystem
      (reductionSequence index).toCode (reductionSequence (index + 1)).toCode :=
  fun index => (eachStepsToNext index).toWordRewrite

/-- ★ **Word-rewrite termination on the certified fragment.**  A reduction sequence rooted at a WELL-TYPED
term (`HasTypeDescPi` under a well-formed `WfContextDesc`) cannot be infinite — so the `fxStepSystem`
word-rewrite chain it induces (via `certifiedReductionInducesWordChain`) terminates.  Consumes SN-043
(`stronglyNormalizingOfWfContextDesc`) on the ROOT only: an infinite `Step` sequence from the root would
contradict `IsStronglyNormalizing rootTerm` (which is `Acc StepSuccessor`, ruling out every infinite
descending chain), so NO subject reduction is needed — the reducts need not stay typed.  This is the
GCC-5-free Leg-3 termination leg. -/
theorem typedRootWordReductionTerminates {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {rootTerm rootType : RawTerm scope}
    (contextWellFormed : WfContextDesc context)
    (typed : HasTypeDescPi profile context rootTerm rootType)
    (reductionSequence : Nat → RawTerm scope)
    (startsAtRoot : reductionSequence 0 = rootTerm)
    (eachStepsToNext : ∀ index, Step (reductionSequence index) (reductionSequence (index + 1))) :
    False := by
  apply notStronglyNormalizing_of_infiniteReduction reductionSequence eachStepsToNext
  rw [startsAtRoot]
  exact HasTypeDescPi.stronglyNormalizingOfWfContextDesc contextWellFormed typed

/-- **The necessity of the certified restriction.**  The FULL word system does NOT terminate: the UNTYPED
unbounded-growth term `growingDivergentTerm` maps to a word `growingDivergentTerm.toCode` that admits an
infinite `fxStepSystem` rewrite chain (its strictly-growing reduction sequence mapped through
`Step.toWordRewrite`), and the source term is provably non-`IsStronglyNormalizing`.  So the words on which
`fxStepSystem` diverges are exactly `toCode`-images of NON-strongly-normalizing (hence, by SN-043's
contrapositive, untypable) terms — the certified restriction in `typedRootWordReductionTerminates` is
precisely what rules them out.  The word-layer mirror of SN-NECESSITY (#950): word-termination genuinely
requires the typing hypothesis. -/
theorem untypedWordReductionDiverges :
    ∃ wordSequence : Nat → List Nat,
      wordSequence 0 = growingDivergentTerm.toCode ∧
      (∀ index, FxWordRewritesOneStep fxStepSystem (wordSequence index) (wordSequence (index + 1))) ∧
      ¬ StepStar.IsStronglyNormalizing growingDivergentTerm :=
  ⟨fun index => (growingReductionSequence index).toCode, rfl,
   (fun index => (growingReductionSequence_steps index).toWordRewrite),
   growingDivergentTerm_notStronglyNormalizing⟩

end FX1Poly.Typed
