import FX1Poly.Core.StepOverBundleConfluence
import FX1Poly.Core.RawConfluence
import FX1Poly.Core.Normalize

/-! # FX1Poly/Core/StepOverBundleConv — RW-6 (b): no-regression decidable
conversion for the iota-only bundle.

The convertibility companion to `StepOverBundleConfluence`.  Raw `Conv`
is `StepStar.Join` — joinability via a common reduct of core `Step`.  The
bundle-level `ConvOver bundle` is the same shape over `StepOver bundle`;
at the iota-only bundle the RW-5 adequacy lifts to the
reflexive-transitive closures, so `ConvOver fxIotaBundle` IS `Conv`.

  * `reflTransClosure_fxIotaBundle_iff_stepStar` — the closure-level
    bridge: a `StepOver fxIotaBundle` chain is a `StepStar` chain
    (`mapForward` across the RW-5 single-step adequacy, composed with the
    shipped `StepStar`/`ReflTransClosure (StepOverTable iotaRuleTable)`
    maps);
  * `convOver_fxIotaBundle_iff_conv` — `ConvOver fxIotaBundle ↔ Conv`,
    the bridge applied to both joining legs;
  * `Conv.decidableOverFxIotaBundleOfNormalForms` — transport the raw
    no-SN-hypothesis decider `Conv.decidableOfNormalForms` across the
    iff.  Honest scope: decidability needs normal-form witnesses (raw
    β+ι is not globally SN), exactly as the raw layer; on the SN/typed
    fragment a normalizer supplies them.
  * `Conv.decidableOverFxIotaBundleOfStronglyNormalizing` — closes that
    loop on the SN fragment: the kernel normalizer
    (`Conv.decidableOfStronglyNormalizing`) computes the NF witnesses, so
    the bundle decider is parameter-free, keyed only on termination of
    both sides.  This is RW-6's normalizer leg for the iota-only bundle.

Together with `StepOver.fxIotaBundleConfluent` this is RW-6's
no-regression gate for the iota-only bundle: confluence AND decidable
conversion recovered from the parameterized relation with no fresh
metatheory.

## Zero-axiom verification

Closure inductions + the shipped decider; no `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration gated in `FX1PolyAudit/AuditStepOverBundleConv.lean`. -/

namespace FX1Poly.Core

/-! ## The closure-level bridge -/

/-- A reflexive-transitive `StepOver fxIotaBundle` chain IS a `StepStar`
chain — push across the RW-5 single-step adequacy, then collapse through
the shipped table/StepStar maps. -/
theorem reflTransClosure_fxIotaBundle_iff_stepStar {scope : Nat}
    {source target : RawTerm scope} :
    ReflTransClosure
      (fun first second : RawTerm scope => StepOver fxIotaBundle first second)
      source target
      ↔ StepStar source target := by
  constructor
  · intro bundleChain
    exact ReflTransClosure.toStepStar
      (bundleChain.mapForward
        (targetRel := fun first second : RawTerm scope =>
          StepOverTable iotaRuleTable first second)
        StepOver.toStepOverTable_iotaOnly)
  · intro stepStarChain
    exact stepStarChain.toTableClosure.mapForward
      (targetRel := fun first second : RawTerm scope =>
        StepOver fxIotaBundle first second)
      StepOverTable.toStepOver_iotaOnly

/-! ## Bundle conversion -/

/-- Convertibility over a bundle: joinability of the bundle relation. -/
def ConvOver (bundle : RuleTableBundle) {scope : Nat}
    (source target : RawTerm scope) : Prop :=
  Joinable (fun first second : RawTerm scope => StepOver bundle first second)
    source target

/-- ★ **The iota-only bundle conversion IS raw `Conv`.**  Both joining
legs transport across the closure-level bridge. -/
theorem convOver_fxIotaBundle_iff_conv {scope : Nat}
    {source target : RawTerm scope} :
    ConvOver fxIotaBundle source target ↔ Conv source target := by
  constructor
  · rintro ⟨commonReduct, leftChain, rightChain⟩
    exact ⟨commonReduct,
      reflTransClosure_fxIotaBundle_iff_stepStar.mp leftChain,
      reflTransClosure_fxIotaBundle_iff_stepStar.mp rightChain⟩
  · rintro ⟨commonReduct, leftChain, rightChain⟩
    exact ⟨commonReduct,
      reflTransClosure_fxIotaBundle_iff_stepStar.mpr leftChain,
      reflTransClosure_fxIotaBundle_iff_stepStar.mpr rightChain⟩

/-! ## The no-regression decider -/

/-- ★ **Decidable iota-only-bundle conversion from normal forms.**  The
raw no-SN-hypothesis decider `Conv.decidableOfNormalForms` transported
across `convOver_fxIotaBundle_iff_conv`.  Honest scope: needs normal-form
witnesses (raw β+ι is not globally SN); on the SN/typed fragment a
normalizer supplies them. -/
def Conv.decidableOverFxIotaBundleOfNormalForms {scope : Nat}
    {leftTerm rightTerm leftNormalForm rightNormalForm : RawTerm scope}
    (leftReducesToNF : StepStar leftTerm leftNormalForm)
    (leftIsNormal : RawTerm.isStepNormalForm leftNormalForm)
    (rightReducesToNF : StepStar rightTerm rightNormalForm)
    (rightIsNormal : RawTerm.isStepNormalForm rightNormalForm) :
    Decidable (ConvOver fxIotaBundle leftTerm rightTerm) :=
  letI : Decidable (Conv leftTerm rightTerm) :=
    Conv.decidableOfNormalForms leftReducesToNF leftIsNormal
      rightReducesToNF rightIsNormal
  decidable_of_iff (Conv leftTerm rightTerm)
    convOver_fxIotaBundle_iff_conv.symm

/-- ★ **Decidable iota-only-bundle conversion on the strongly-normalizing
fragment.**  Where `decidableOverFxIotaBundleOfNormalForms` needs the
normal forms supplied, this closes the loop on the SN fragment: the
kernel normalizer inside `Conv.decidableOfStronglyNormalizing` computes
the NF witnesses, then the result transports across
`convOver_fxIotaBundle_iff_conv`.  This is RW-6's normalizer leg for the
iota-only bundle — a parameter-free decider keyed only on termination of
both sides, so the SN/typed fragment needs no externally-supplied normal
forms. -/
def Conv.decidableOverFxIotaBundleOfStronglyNormalizing {scope : Nat}
    {leftTerm rightTerm : RawTerm scope}
    (leftTerminates : StepStar.IsStronglyNormalizing leftTerm)
    (rightTerminates : StepStar.IsStronglyNormalizing rightTerm) :
    Decidable (ConvOver fxIotaBundle leftTerm rightTerm) :=
  letI : Decidable (Conv leftTerm rightTerm) :=
    Conv.decidableOfStronglyNormalizing leftTerminates rightTerminates
  decidable_of_iff (Conv leftTerm rightTerm)
    convOver_fxIotaBundle_iff_conv.symm

end FX1Poly.Core
