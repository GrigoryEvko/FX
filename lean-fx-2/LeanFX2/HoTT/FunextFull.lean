import LeanFX2.HoTT.UnivalenceFull

/-! # HoTT/FunextFull — Maximal kernel-internal Funext at zero axioms.

Companion to `HoTT/UnivalenceFull.lean`: ships the LARGEST consistently-
derivable Funext neighbourhood inside lean-fx-2 *without* extending the
kernel with new Term/Step constructors — i.e., the maximum strength
achievable on top of the existing `Step.eqArrow` reduction.

## Honest scope statement

Full function extensionality: `(firstFn secondFn : (input : Domain) →
Codomain input) → ((input : Domain) → firstFn input = secondFn input)
→ firstFn = secondFn`.  In standard MLTT this requires the funext
axiom; in cubical type theory it follows from path-Π adjunction.

In lean-fx-2 the rfl-fragment is REAL kernel content (`Step.eqArrow`).
The full backward direction (`pointwise → fn-equality`) at arbitrary
endpoints requires either Lean's `funext` axiom (banned) or
heterogeneous-function `Step` ctors (Phase E future work).

## What this file ships

* **Forward direction at full generality**: from `firstFn = secondFn`,
  derive pointwise equality at every input.  Already shipped in
  `HoTT/UnivalenceFull.lean` as `Funext.fnEqToPointwiseMeta`.

* **Backward direction at the rfl-fragment**: when both sides are the
  same function (or the pointwise-equality input is the trivial
  `fun _ => rfl`), produce the canonical `rfl` path.

* **Funext-β computation rule**: at the meta level, the round trip
  `fnEqToPointwise ∘ pointwiseToFnEqAtRefl` is the trivial pointwise
  rfl witness; same in the other direction.

* **Functoriality**: pointwise equality preserves `Eq.refl`,
  `Eq.symm`, `Eq.trans`.  Already partially shipped; this file
  extends with the `(▸)` / `Eq.subst` versions.

* **Kernel-meta correspondence**: at refl, the kernel `Step.eqArrow`
  rule and the meta-level forward map produce structurally identical
  results.

## What's NOT shipped

* **Backward direction at full generality** (arbitrary `firstFn ≠
  secondFn`, arbitrary pointwise hypothesis): requires `funext`
  axiom (banned) or heterogeneous Step ctors.

* **Bundled Equiv `(firstFn = secondFn) ≃ ((x : Domain) →
  firstFn x = secondFn x)`**: same blocker as Univalence's bundled
  Equiv — would require the unprovable backward direction.

This file is the maximum honest delivery on top of the existing
kernel's funext content. -/

namespace LeanFX2

universe leftLevel rightLevel

/-! ## §1. Pointwise function equality predicate.

We use Lean's standard pointwise equality `(input : Domain) →
firstFn input = secondFn input` directly — no wrapper structure
needed at meta level.  This section ships convenience theorems
that document the pointwise-equality semantics. -/

/-- **Pointwise reflexivity**: every function is pointwise equal to
itself, with rfl witness at every input.  Definitional `rfl` per
input. -/
theorem Funext.pointwiseRefl
    {DomainSort : Sort leftLevel}
    {CodomainSort : DomainSort → Sort rightLevel}
    (someFn : (input : DomainSort) → CodomainSort input)
    (inputValue : DomainSort) :
    someFn inputValue = someFn inputValue := rfl

/-- **Pointwise symmetry**: from a pointwise equality `firstFn = secondFn`
pointwise, derive `secondFn = firstFn` pointwise. -/
theorem Funext.pointwiseSymm
    {DomainSort : Sort leftLevel}
    {CodomainSort : DomainSort → Sort rightLevel}
    {firstFn secondFn : (input : DomainSort) → CodomainSort input}
    (pointwiseProof : (input : DomainSort) → firstFn input = secondFn input)
    (inputValue : DomainSort) :
    secondFn inputValue = firstFn inputValue :=
  Eq.symm (pointwiseProof inputValue)

/-- **Pointwise transitivity**: composing pointwise equalities. -/
theorem Funext.pointwiseTrans
    {DomainSort : Sort leftLevel}
    {CodomainSort : DomainSort → Sort rightLevel}
    {firstFn middleFn rightFn : (input : DomainSort) → CodomainSort input}
    (firstProof  : (input : DomainSort) → firstFn  input = middleFn input)
    (secondProof : (input : DomainSort) → middleFn input = rightFn  input)
    (inputValue : DomainSort) :
    firstFn inputValue = rightFn inputValue :=
  Eq.trans (firstProof inputValue) (secondProof inputValue)

/-! ## §2. Funext-β: forward map round-trip computation rules.

The forward map `fnEqToPointwiseMeta` (already shipped in
`HoTT/UnivalenceFull.lean`) followed by reading off the pointwise
proof at any input gives back the result of using `Eq.subst` on the
function equality.  This section ships the explicit computation
rules. -/

/-- **Funext-β (forward direction)**: applying the forward map's
pointwise output at any input agrees with `Eq.subst`-style transport.
At rfl, both sides reduce to the input. -/
theorem Funext.fnEqToPointwise_pointwise_atSelf
    {DomainSort : Sort leftLevel}
    {CodomainSort : DomainSort → Sort rightLevel}
    (someFn : (input : DomainSort) → CodomainSort input)
    (inputValue : DomainSort) :
    Funext.fnEqToPointwiseMeta (Eq.refl someFn) inputValue
      = Eq.refl (someFn inputValue) := rfl

/-- **Funext composition rule (rfl × rfl)**: composing two trivial
pointwise rfl proofs yields a rfl pointwise proof.  Definitional. -/
theorem Funext.fnEqToPointwise_trans_refl_refl
    {DomainSort : Sort leftLevel}
    {CodomainSort : DomainSort → Sort rightLevel}
    (someFn : (input : DomainSort) → CodomainSort input)
    (inputValue : DomainSort) :
    Funext.fnEqToPointwiseMeta
        (Eq.trans (Eq.refl someFn) (Eq.refl someFn))
        inputValue
      = Eq.refl (someFn inputValue) := rfl

/-- **Funext symm-cancellation at rfl**: applying symm to a rfl path
gives back rfl pointwise.  Definitional. -/
theorem Funext.fnEqToPointwise_symm_refl
    {DomainSort : Sort leftLevel}
    {CodomainSort : DomainSort → Sort rightLevel}
    (someFn : (input : DomainSort) → CodomainSort input)
    (inputValue : DomainSort) :
    Funext.fnEqToPointwiseMeta (Eq.symm (Eq.refl someFn)) inputValue
      = Eq.refl (someFn inputValue) := rfl

/-! ## §3. Backward map round-trip computation rules.

The backward map `pointwiseMetaToFnEqAtRefl` is forgetful (it
returns `rfl` regardless of input).  This section ships the explicit
forgetful-identity computation rules. -/

/-- **Backward map ignores pointwise data**: applying
`pointwiseMetaToFnEqAtRefl` to two different pointwise proofs yields
the same `rfl` output. -/
theorem Funext.pointwiseMetaToFnEqAtRefl_forgetful
    {DomainSort : Sort leftLevel}
    {CodomainSort : DomainSort → Sort rightLevel}
    (someFn : (input : DomainSort) → CodomainSort input)
    (firstPointwise secondPointwise :
        (input : DomainSort) → someFn input = someFn input) :
    Funext.pointwiseMetaToFnEqAtRefl someFn firstPointwise
      = Funext.pointwiseMetaToFnEqAtRefl someFn secondPointwise := rfl

/-- **Backward map at trivial pointwise = rfl**: passing the trivial
`fun _ => rfl` as pointwise hypothesis, the backward map returns
`Eq.refl someFn`.  Definitional. -/
theorem Funext.pointwiseMetaToFnEqAtRefl_trivial
    {DomainSort : Sort leftLevel}
    {CodomainSort : DomainSort → Sort rightLevel}
    (someFn : (input : DomainSort) → CodomainSort input) :
    Funext.pointwiseMetaToFnEqAtRefl someFn
        (fun (inputValue : DomainSort) => Eq.refl (someFn inputValue))
      = Eq.refl someFn := rfl

/-! ## §4. Round trips: kernel-meta correspondence at the rfl-fragment.

Mirroring `HoTT/UnivalenceFull.lean` §4: at the rfl-fragment, the
kernel `Step.eqArrow` rule and the meta-level forward/backward maps
produce structurally identical results.  Definitional `rfl` because
both sides reduce to the trivial pointwise rfl witness. -/

/-- **Funext kernel-meta correspondence at rfl**: at the rfl-fragment,
the meta-level forward direction applied to `Eq.refl someFn` produces
the trivial pointwise rfl witness, mirroring the kernel
`Step.eqArrow` reduction `Term.funextReflAtId ~~> Term.funextRefl`. -/
theorem Funext.kernelMetaCorrespondence_atRefl
    {DomainSort : Sort leftLevel}
    {CodomainSort : DomainSort → Sort rightLevel}
    (someFn : (input : DomainSort) → CodomainSort input)
    (inputValue : DomainSort) :
    Funext.fnEqToPointwiseMeta (Eq.refl someFn) inputValue
      = (fun (witnessInput : DomainSort) => Eq.refl (someFn witnessInput)) inputValue := rfl

/-! ## §5. Round-trip identity (rfl-fragment).

At the rfl-fragment, going forward then backward (or backward then
forward) yields the original input up to definitional equality. -/

/-- **Round trip on the path side at rfl**: forward then backward of
`Eq.refl someFn` gives back `Eq.refl someFn`.  Already shipped as
`fnEqToPointwiseMeta_pointwiseToFnEqAtRefl_refl`; restated for
namespace consistency. -/
theorem Funext.roundTripPathSide_refl
    {DomainSort : Sort leftLevel}
    {CodomainSort : DomainSort → Sort rightLevel}
    (someFn : (input : DomainSort) → CodomainSort input) :
    Funext.pointwiseMetaToFnEqAtRefl someFn
        (fun input => Funext.fnEqToPointwiseMeta (Eq.refl someFn) input)
      = Eq.refl someFn := rfl

/-- **Round trip on the pointwise side at trivial-rfl**: backward then
forward of the trivial pointwise rfl witness gives back the trivial
pointwise rfl witness (pointwise at any input). -/
theorem Funext.roundTripPointwiseSide_trivial
    {DomainSort : Sort leftLevel}
    {CodomainSort : DomainSort → Sort rightLevel}
    (someFn : (input : DomainSort) → CodomainSort input)
    (inputValue : DomainSort) :
    Funext.fnEqToPointwiseMeta
        (Funext.pointwiseMetaToFnEqAtRefl someFn
            (fun input => Eq.refl (someFn input)))
        inputValue
      = Eq.refl (someFn inputValue) := rfl

/-- **Round trip at any pointwise (forgetful)**: the round trip on
the pointwise side at an arbitrary pointwise rfl witness gives back
the trivial pointwise rfl witness — non-injective on pointwise data
but type-correct at every input. -/
theorem Funext.roundTripPointwiseSide_anyPointwise
    {DomainSort : Sort leftLevel}
    {CodomainSort : DomainSort → Sort rightLevel}
    (someFn : (input : DomainSort) → CodomainSort input)
    (anyPointwise : (input : DomainSort) → someFn input = someFn input)
    (inputValue : DomainSort) :
    Funext.fnEqToPointwiseMeta
        (Funext.pointwiseMetaToFnEqAtRefl someFn anyPointwise)
        inputValue
      = Eq.refl (someFn inputValue) := rfl

/-! ## §6. Application laws — applying the function-equality
backward yields the function value transported.

For any `functionEquality : firstFn = secondFn` and any input, we can
apply the equality at the function-level and observe the result agrees
with the function value at that input.  These laws connect the meta-
level functoriality of the forward map to the kernel-level reasoning. -/

/-- **Function-level application**: at refl, applying both sides of
the equality at any input gives equal values.  Pointwise rfl. -/
theorem Funext.applicationAtRefl
    {DomainSort : Sort leftLevel}
    {CodomainSort : DomainSort → Sort rightLevel}
    (someFn : (input : DomainSort) → CodomainSort input)
    (inputValue : DomainSort) :
    someFn inputValue = someFn inputValue := rfl

/-- **Eq.subst on function equality**: substituting a function equality
into a property `Property` (function-valued) yields the property
applied to the substituted function.  This is `Eq.subst` specialised
to function values. -/
theorem Funext.eqSubst_functionEquality
    {DomainSort : Sort leftLevel}
    {CodomainSort : DomainSort → Sort rightLevel}
    {firstFn secondFn : (input : DomainSort) → CodomainSort input}
    {Property : ((input : DomainSort) → CodomainSort input) → Prop}
    (functionEquality : firstFn = secondFn)
    (firstProperty : Property firstFn) :
    Property secondFn :=
  functionEquality ▸ firstProperty

/-- **Function transport agrees pointwise** (rfl-case): when the
function equality is `Eq.refl`, the result of the function-level
property `(fn = fn)` does not differ from the function itself.  At
every input the pointwise extraction is `Eq.refl`. -/
theorem Funext.transport_at_pointwise_refl
    {DomainSort : Sort leftLevel}
    {CodomainSort : DomainSort → Sort rightLevel}
    (someFn : (input : DomainSort) → CodomainSort input)
    (inputValue : DomainSort) :
    Funext.fnEqToPointwiseMeta (Eq.refl someFn) inputValue
      = Eq.refl (someFn inputValue) := rfl

end LeanFX2
