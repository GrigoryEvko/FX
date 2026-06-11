import FX1Poly.Extension.ProfileExtension
import FX1Poly.Typed.GeneratorSemanticTier
/-! # FX1Poly/Extension/ProfileLens — the generator-allocation lens

Until this file, the extension subsystem's construction ledger claimed
`hasProfileLensInstance` while NO ProfileLens type existed anywhere —
the most overstated rung in the audit.  This file ships the type, the
instance that backs the ledger, the non-degenerate demonstration, and
the impossibility pin that explains why the demonstration cannot yet
ride on a `ProfileExtension`.

## Design: reserved-slot allocation, not enum extension

The kernel's `Generator` enum is CLOSED (203 constructors); a profile
extension cannot add Lean-level constructors to it.  The
architecturally honest way for an extension to "interpret new
generators" against a closed enum is ALLOCATION: map each interface
generator slot to a RESERVED kernel generator (`semanticTier =
.reserved`, the HON-3 classifier — a bare syntactic name with no
encoded semantics) of MATCHING arity.  The lens is therefore a prism:

* `liftGenerator`    — slot → allocated kernel generator (review)
* `forgetGenerator?` — kernel generator → slot, partial (preview)
* prism laws: forget∘lift = some (roundtrip), and forget hits only
  lift's image
* `liftArity_matchesInterface` — the allocated generator's child
  count is the interface's declared arity (so interface terms
  transport to well-formed `mkGen` cells)
* `liftLandsOnReserved` — allocation never collides with live
  semantics (typed or reducing generators are off-limits)

This is a GENERATOR-level lens.  The term-level transport it induces
(`mkGen`-head renaming along `liftGenerator`) is mechanical given the
arity law and is deliberately not built here — for every extension
constructible TODAY it would be the identity (see the impossibility
pin below).

## What backs the ledger

`ProfileExtension.lens` gives EVERY constructible extension a
`ProfileLens` — the degenerate instance, derived from the extension's
own `hasNoNewGenerators` evidence.  That makes the
`hasProfileLensInstance` ledger rung TRUE with a concrete witness
(previously it was claimed with none).

## The honest boundary

`profileExtension_generatorCount_zero` pins that every constructible
`ProfileExtension` has ZERO interface generators — the evidence record
is currently eta-shaped (`BilaxCompatibilityEvidence` et al. demand
`generatorCount = 0`), so a generator-ADDING extension value cannot
even be built.  The non-degenerate lens content is therefore
demonstrated at the `PolynomialInterface` level
(`reservedAllocationDemoLens`: one new generator slot, allocated to
the reserved `gen_npComplete`, all four laws discharged).  Upgrading
`ProfileExtension` to carry generator-adding interfaces (and the
term-level transport that becomes non-trivial then) is the genuine
follow-on, gated on per-generator admission evidence — not claimed
here.

Zero-axiom; gated in `FX1PolyAudit/AuditProfile.lean`. -/

namespace FX1Poly.Extension

open Core

/-- The generator-allocation lens (a prism): interprets an interface's
new generator slots as RESERVED kernel generators of matching arity.
See the file docstring for the design rationale. -/
structure ProfileLens (interface : PolynomialInterface) where
  /-- Allocate each interface slot to a kernel generator. -/
  liftGenerator : Fin interface.generatorCount → Generator
  /-- Partially recover the interface slot from a kernel generator. -/
  forgetGenerator? : Generator → Option (Fin interface.generatorCount)
  /-- The allocated generator's child count matches the interface's
  declared arity for that slot. -/
  liftArity_matchesInterface :
    ∀ (slot : Fin interface.generatorCount),
      (liftGenerator slot).binderShifts.length = interface.arities slot
  /-- Allocation lands on RESERVED generators only — no collision with
  statically-typed or operationally-reducing kernel semantics. -/
  liftLandsOnReserved :
    ∀ (slot : Fin interface.generatorCount),
      Typed.semanticTier (liftGenerator slot) = .reserved
  /-- Prism law 1: forgetting an allocated generator recovers the slot. -/
  forget_lift_roundtrip :
    ∀ (slot : Fin interface.generatorCount),
      forgetGenerator? (liftGenerator slot) = some slot
  /-- Prism law 2: forgetting succeeds only on allocated generators. -/
  lift_of_forget :
    ∀ (generator : Generator) (slot : Fin interface.generatorCount),
      forgetGenerator? generator = some slot →
      generator = liftGenerator slot

/-- Allocation is injective — distinct interface slots occupy distinct
kernel generators (a corollary of the roundtrip law). -/
theorem ProfileLens.liftGenerator_injective
    {interface : PolynomialInterface} (lens : ProfileLens interface)
    {slotA slotB : Fin interface.generatorCount}
    (liftsAgree : lens.liftGenerator slotA = lens.liftGenerator slotB) :
    slotA = slotB :=
  Option.some.inj
    (((lens.forget_lift_roundtrip slotA).symm.trans
        (congrArg lens.forgetGenerator? liftsAgree)).trans
      (lens.forget_lift_roundtrip slotB))

/-- The degenerate lens for a generator-free interface: every field is
vacuous over `Fin 0`.  This is the lens every CURRENT extension
carries (see `profileExtension_generatorCount_zero`). -/
def ProfileLens.degenerate (interface : PolynomialInterface)
    (hasNoGenerators : interface.generatorCount = 0) :
    ProfileLens interface where
  liftGenerator := fun slot =>
    (Nat.not_lt_zero slot.val (hasNoGenerators ▸ slot.isLt)).elim
  forgetGenerator? := fun _ => none
  liftArity_matchesInterface := fun slot =>
    (Nat.not_lt_zero slot.val (hasNoGenerators ▸ slot.isLt)).elim
  liftLandsOnReserved := fun slot =>
    (Nat.not_lt_zero slot.val (hasNoGenerators ▸ slot.isLt)).elim
  forget_lift_roundtrip := fun slot =>
    (Nat.not_lt_zero slot.val (hasNoGenerators ▸ slot.isLt)).elim
  lift_of_forget := fun _ _ noneIsSome => nomatch noneIsSome

/-! ## The honest boundary pin -/

/-- Every constructible `ProfileExtension` has ZERO interface
generators: the evidence record is eta-shaped (the bilax field demands
`generatorCount = 0`), so a generator-ADDING extension value cannot be
built today.  This is why the non-degenerate lens demonstration below
lives at the `PolynomialInterface` level. -/
theorem profileExtension_generatorCount_zero
    {baseProfile : PolyProfile}
    (extension : ProfileExtension baseProfile) :
    extension.interface.generatorCount = 0 :=
  extension.bilaxCompatibilityEvidence.hasNoNewGenerators

/-- ★ The ledger-backing instance: EVERY constructible extension
carries a `ProfileLens` (the degenerate one, from its own
no-new-generators evidence).  This is the concrete witness the
`hasProfileLensInstance` ledger rung previously lacked. -/
def ProfileExtension.lens {baseProfile : PolyProfile}
    (extension : ProfileExtension baseProfile) :
    ProfileLens extension.interface :=
  ProfileLens.degenerate extension.interface
    (profileExtension_generatorCount_zero extension)

/-- The eta demonstration extension's lens, by the generic route. -/
def etaReductionExtensionLens : ProfileLens etaReductionInterface :=
  etaReductionExtension.lens

/-! ## The non-degenerate demonstration

A one-generator interface whose lens allocates the RESERVED kernel
generator `gen_npComplete` (binder shifts `[0, 0]`, arity 2) — the
structure has real content, not just the vacuous instance. -/

/-- Demonstration interface: ONE new generator of arity 2, no new
reduction rules. -/
def reservedAllocationDemoInterface : PolynomialInterface where
  generatorCount := 1
  arities := fun _ => 2
  reductionCount := 0
  reductionArities := fun slot =>
    (Nat.not_lt_zero slot.val slot.isLt).elim

/-- ★ The non-degenerate lens: the demo interface's single generator
slot is allocated to the reserved kernel generator `gen_npComplete`,
with arity match, reserved landing, and both prism laws discharged. -/
def reservedAllocationDemoLens :
    ProfileLens reservedAllocationDemoInterface where
  liftGenerator := fun _ => .gen_npComplete
  forgetGenerator? := fun generator =>
    if generator = Generator.gen_npComplete then
      some ⟨0, Nat.zero_lt_one⟩
    else
      none
  liftArity_matchesInterface := fun _ => rfl
  liftLandsOnReserved := fun _ => rfl
  forget_lift_roundtrip := fun slot =>
    match slot with
    | ⟨0, _⟩ => rfl
    | ⟨_ + 1, slotBound⟩ =>
        (Nat.not_lt_zero _ (Nat.lt_of_succ_lt_succ slotBound)).elim
  lift_of_forget := fun generator slot =>
    if isAllocated : generator = Generator.gen_npComplete then
      fun _ => isAllocated
    else
      fun forgetSucceeded =>
        nomatch
          (forgetSucceeded.symm.trans (if_neg isAllocated) :
            some slot = none)

/-- Pin: the demo lens genuinely allocates (non-vacuous content). -/
theorem reservedAllocationDemoLens_allocates :
    reservedAllocationDemoLens.liftGenerator ⟨0, Nat.zero_lt_one⟩ =
      Generator.gen_npComplete := rfl

/-- Pin: the allocated generator is indeed RESERVED under the honest
HON-3 classifier — the demonstration does not squat on live semantics. -/
theorem gen_npComplete_isReserved :
    Typed.semanticTier .gen_npComplete = .reserved := rfl

end FX1Poly.Extension
