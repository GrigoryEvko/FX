import FX1Poly.Typed.SimplyTypedNormalForm
import FX1Poly.Typed.SimplyTypedConvDecision
import FX1Poly.Core.StepStarConfluence

/-! # FX1Poly/Typed/SimplyTypedConvEquivalence
    — convertibility is a decidable equivalence relation on closed simply-typed terms.

The raw `Conv` relation (`Core/StepStarConfluence.lean`) is reflexive and symmetric unconditionally, but its
transitivity is genuinely conditional: it needs Church-Rosser for the chains leaving the shared middle term,
which at the raw layer requires that middle term to be strongly normalizing (raw `Step` is not globally SN —
see `Core/StronglyNormalizingSubst.lean` and the WN-grind notes).  On the *simply-typed* fragment that
obstruction vanishes: every closed simply-typed term is strongly normalizing (the fundamental theorem), so
the middle term always terminates and transitivity holds.

This file packages that observation.

* `SimplyTypedTermLF.conv_trans` — **Conv.trans for the simply-typed fragment**: conversion composes through
  any simply-typed middle term, whose typing supplies the strong-normalization hypothesis of
  `Conv.trans_of_middle_accessible`.
* `SimplyTypedClosedTerm` — the carrier: a closed `RawTerm 0` bundled with a type and a typing derivation.
* `SimplyTypedClosedTerm.convertsTo` — convertibility of closed simply-typed terms (underlying raw `Conv`).
* `SimplyTypedClosedTerm.convertsTo_equivalence` — **convertibility is an equivalence relation** (refl/sym
  unconditional, trans through the middle's strong normalization).
* `SimplyTypedClosedTerm.decidableConvertsTo` — **and it is decidable** (the normalize-and-compare decider
  fed by the fundamental theorem's strong normalization).  Together: a *decidable equivalence relation*.

This addresses the long-standing `Conv.trans` roadmap obligation for the part of the kernel that is actually
strongly normalizing.  The unconditional raw `Conv.trans` remains genuinely unavailable (raw `Step` is not
globally confluent), and that is the honest state — the simply-typed fragment is exactly the locus where the
equivalence-relation structure becomes provable.

## Zero-axiom verification

`conv_trans` is `Conv.trans_of_middle_accessible` applied to `stronglyNormalizingBare`; the equivalence
bundles `Conv.refl`/`Conv.sym`/`conv_trans`; decidability is `Conv.decidableOfSimplyTypedBareClosed`.  Every
ingredient is already zero-axiom, so the package is too: no `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`.  Gated per declaration in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Transitivity of conversion through a simply-typed middle term.**  Composing `Conv firstTerm
middleTerm` with `Conv middleTerm lastTerm` needs Church-Rosser only for the two chains leaving
`middleTerm`; the middle term's typing makes it strongly normalizing (fundamental theorem), which is exactly
the hypothesis of `Conv.trans_of_middle_accessible`.  This is `Conv.trans` for the simply-typed fragment. -/
theorem SimplyTypedTermLF.conv_trans {profile : PolyProfile}
    {firstTerm middleTerm lastTerm middleType : RawTerm 0}
    (middleTyped : SimplyTypedTermLF (TypingContext.empty : TypingContext profile 0) middleTerm middleType)
    (firstMiddle : Conv firstTerm middleTerm) (middleLast : Conv middleTerm lastTerm) :
    Conv firstTerm lastTerm :=
  Conv.trans_of_middle_accessible middleTyped.stronglyNormalizingBare firstMiddle middleLast

/-- A closed simply-typed term: a `RawTerm 0` together with a type and a typing derivation at the empty
context.  This is the carrier on which convertibility forms an equivalence relation. -/
structure SimplyTypedClosedTerm (profile : PolyProfile) where
  term : RawTerm 0
  type : RawTerm 0
  typed : SimplyTypedTermLF (TypingContext.empty : TypingContext profile 0) term type

/-- Convertibility of closed simply-typed terms — the underlying raw `Conv` on the bare terms. -/
def SimplyTypedClosedTerm.convertsTo {profile : PolyProfile}
    (firstTerm secondTerm : SimplyTypedClosedTerm profile) : Prop :=
  Conv firstTerm.term secondTerm.term

/-- **Convertibility is an equivalence relation on closed simply-typed terms.**  Reflexivity and symmetry are
unconditional (`Conv.refl` / `Conv.sym`); transitivity holds because every closed simply-typed term — in
particular the shared middle one — is strongly normalizing, supplying the hypothesis of
`Conv.trans_of_middle_accessible` (via `conv_trans`). -/
theorem SimplyTypedClosedTerm.convertsTo_equivalence {profile : PolyProfile} :
    Equivalence (SimplyTypedClosedTerm.convertsTo (profile := profile)) where
  refl firstTerm := Conv.refl firstTerm.term
  symm convertibility := Conv.sym convertibility
  trans {_firstTerm middleTerm _lastTerm} firstSecond secondThird :=
    SimplyTypedTermLF.conv_trans middleTerm.typed firstSecond secondThird

/-- **Convertibility of closed simply-typed terms is decidable.**  Each term's typing supplies strong
normalization (the fundamental theorem), so the normalize-and-compare decider applies — typing alone decides
convertibility.  Together with `convertsTo_equivalence`, convertibility is a *decidable equivalence relation*
on closed simply-typed terms. -/
instance SimplyTypedClosedTerm.decidableConvertsTo {profile : PolyProfile} :
    DecidableRel (SimplyTypedClosedTerm.convertsTo (profile := profile)) :=
  fun firstTerm secondTerm =>
    Conv.decidableOfSimplyTypedBareClosed firstTerm.typed secondTerm.typed

end FX1Poly.Typed
