import FX1Poly.Axis.Context.Instances.Subst.FxBaseSubstCategory

/-! # FX1Poly/Axis/FxBaseSubstColimits
    — the RIGHT / colimits leg of the context category: initial object + binary coproduct

`context-0` shipped the context-axis root (the renaming RMC + the substitution category +
global sections); `context-1` the LEFT/Σ comprehension leg; `context-2` the slice-category
substrate.  This file lands the RIGHT leg the context ω-category still owes: the FINITE
COPRODUCTS of `fxBaseSubstCategory` (`FxBaseSubstCategory.lean`) — the INITIAL object and the
binary COPRODUCT — each as a genuine, proved categorical universal property.

Recall `fxBaseSubstCategory.Morphism sourceScope targetScope := SubstVec targetScope sourceScope`
(a morphism `A ⟶ B` is a length-`A` vector of `RawTerm`-over-`B`, i.e. a substitution that maps
each of `A`'s variables to a `B`-scoped term).  Reading the universal properties straight off the
hom-sets:

  * **Initial object = scope `0`.**  `Morphism 0 B = SubstVec B 0 = PUnit` definitionally, so there
    is EXACTLY one substitution out of the empty context, and its uniqueness is `PUnit` eta (`rfl`).
    (Scope 0 is initial — NOT terminal — because this base is the opposite of the CwF
    category-of-contexts: the empty context is terminal there, initial here.)
  * **Binary coproduct = scope addition.**  `Morphism (A + B) C = SubstVec C (A + B)`, and a
    length-`(A+B)` vector splits canonically into a length-`A` part and a length-`B` part:
    `SubstVec C (A + B) ≅ SubstVec C A × SubstVec C B`.  That bijection IS the coproduct's defining
    `Hom(A + B, C) ≅ Hom(A, C) × Hom(B, C)`, witnessed concretely by `append` / `split`, with
    variable-injection morphisms `inl`, `inr` and copairing `[f, g] = append f g`.

## What lands here (all zero-axiom)

  * Generic `IsInitialObject` / `IsBinaryCoproduct` — the universal properties over an arbitrary
    `RawCategory` (injections, copairing, the two β-laws, and η/uniqueness as honest fields).
  * `fxBaseSubstInitial : IsInitialObject fxBaseSubstCategory 0` — the empty-context initial object.
  * `SubstVec.append` + the index injections `finIntoCoproductLeft` / `finIntoCoproductRight` + the
    two append-lookup laws (`lookup_append_left` / `lookup_append_right`).
  * `SubstVec.coproductInjectLeft` / `coproductInjectRight` (the variable-injection substitutions)
    and `coproductSplitLeft` / `coproductSplitRight` (the two projections), with `append_split` —
    the η-law that every vector is the append of its two projections.
  * `fxBaseSubstBinaryCoproduct (A B) : IsBinaryCoproduct fxBaseSubstCategory A B (A + B)` — the
    full universal property: both β-laws via the append-lookup laws, uniqueness via `append_split`.

## Why the index injections recurse on the RIGHT length

A `Fin A` injects into `Fin (A + B)` at numeric position `B + i`, and `B + i < A + B` is
`Nat.add_comm`-shaped — and `Nat.add_comm` is NOT among the zero-axiom Nat lemmas.  The fix:
`finIntoCoproductLeft` recurses on `B`, wrapping one `Nat.succ` (`Nat.succ_lt_succ`, axiom-free) per
step, so the bound proof is BUILT structurally and `Nat.add_comm` never appears.  The right
injection is value-preserving and needs only the axiom-free `Nat.le_add_left`.  All Fin-index
juggling rides on definitional proof-irrelevance (two `Fin`s with equal `.val` are defeq).

## Honest scope boundary

This is the FINITE-coproduct (initial + binary) leg.  The dimensional adjoint QUADRUPLE
(transpension proper — the fresh-weakening / boundary modalities and their
Frobenius / Beck-Chevalley coherences) is the cross-axis mode-side deliverable and stays deferred
to `fib-4`, per the `context-3` split annotation.  What lands here is exactly the context-side
colimits the substitution category owns outright.

## Zero-axiom verification

`append` is product recursion on the right length; the injections are structural; the lookup laws
and `append_split` are structural inductions composing the shipped `SubstVec` algebra
(`lookup_zero` / `lookup_succ` / `lookup_tabulate` / `tabulate_lookup` / `ext`) with `Fin`
proof-irrelevance.  No `funext`, no `Nat.add_comm`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit`.
-/

namespace FX1Poly.Axis
open FX1Poly.Polygraph

open FX1Poly.Core

universe u v

/-! ## Generic universal properties over a `RawCategory` -/

/-- An object is INITIAL when it has exactly one morphism to every object. -/
structure IsInitialObject (category : RawCategory.{u, v}) (initialObject : category.Object) where
  /-- The unique morphism from the initial object to any target. -/
  fromInitial : (target : category.Object) → category.Morphism initialObject target
  /-- Every morphism out of the initial object IS that unique one. -/
  fromInitialUnique : ∀ {target : category.Object}
    (morphism : category.Morphism initialObject target), morphism = fromInitial target

/-- A BINARY COPRODUCT of `leftSummand` and `rightSummand`: an object with two injections such that
every pair of legs out of the summands factors through it uniquely.  The four laws (`copair` after
each injection recovers that leg, and any mediator agreeing on both injections IS the copair) are
the full universal property. -/
structure IsBinaryCoproduct (category : RawCategory.{u, v})
    (leftSummand rightSummand coproductObject : category.Object) where
  /-- The left injection into the coproduct. -/
  injectLeft : category.Morphism leftSummand coproductObject
  /-- The right injection into the coproduct. -/
  injectRight : category.Morphism rightSummand coproductObject
  /-- The mediating morphism out of the coproduct, given a leg from each summand. -/
  copair : ∀ {target : category.Object},
    category.Morphism leftSummand target → category.Morphism rightSummand target →
    category.Morphism coproductObject target
  /-- β-LEFT: `copair` after the left injection is the left leg. -/
  copairInjectLeft : ∀ {target : category.Object}
    (leftLeg : category.Morphism leftSummand target)
    (rightLeg : category.Morphism rightSummand target),
    category.compose injectLeft (copair leftLeg rightLeg) = leftLeg
  /-- β-RIGHT: `copair` after the right injection is the right leg. -/
  copairInjectRight : ∀ {target : category.Object}
    (leftLeg : category.Morphism leftSummand target)
    (rightLeg : category.Morphism rightSummand target),
    category.compose injectRight (copair leftLeg rightLeg) = rightLeg
  /-- η / UNIQUENESS: any mediator agreeing with both legs after the injections is the copair. -/
  copairUnique : ∀ {target : category.Object}
    (mediator : category.Morphism coproductObject target)
    (leftLeg : category.Morphism leftSummand target)
    (rightLeg : category.Morphism rightSummand target),
    category.compose injectLeft mediator = leftLeg →
    category.compose injectRight mediator = rightLeg →
    mediator = copair leftLeg rightLeg

/-! ## The initial object: scope `0` (the empty context) -/

/-- **Scope `0` is INITIAL in the substitution category.**  The only substitution out of the empty
context is the empty one (`Morphism 0 target = SubstVec target 0 = PUnit`), and its uniqueness is
`PUnit` definitional eta. -/
def fxBaseSubstInitial : IsInitialObject fxBaseSubstCategory (0 : Nat) where
  fromInitial := fun _target => PUnit.unit
  fromInitialUnique := fun _morphism => rfl

/-! ## Substitution-vector append and the coproduct index injections -/

/-- Concatenate a `leftLen`-vector and a `rightLen`-vector into a `(leftLen + rightLen)`-vector.
Recurses on the SECOND length: `Nat.add` recurses on its right argument, so the result type
`SubstVec target (leftLen + rightLen)` stays definitionally aligned at every step.  The `rightLen`
images occupy the LOW indices `[0, rightLen)`; the `leftLen` images the HIGH block. -/
def SubstVec.append {target leftLen : Nat} :
    {rightLen : Nat} → SubstVec target leftLen → SubstVec target rightLen →
      SubstVec target (leftLen + rightLen)
  | 0, leftVec, _rightVec => leftVec
  | _rightLen + 1, leftVec, rightVec => (rightVec.1, SubstVec.append leftVec rightVec.2)

/-- The RIGHT coproduct injection on indices: a `Fin rightLen` lands at the SAME numeric position in
`Fin (leftLen + rightLen)` (the low block).  Needs only the axiom-free `Nat.le_add_left`. -/
def finIntoCoproductRight (leftLen : Nat) {rightLen : Nat} (index : Fin rightLen) :
    Fin (leftLen + rightLen) :=
  ⟨index.val, Nat.lt_of_lt_of_le index.isLt (Nat.le_add_left rightLen leftLen)⟩

/-- The LEFT coproduct injection on indices: a `Fin leftLen` lands `rightLen` positions UP in
`Fin (leftLen + rightLen)` (the high block).  Defined by recursion on `rightLen` so the bound proof
is built structurally (one `Nat.succ_lt_succ` per step) — `Nat.add_comm` never appears. -/
def finIntoCoproductLeft {leftLen : Nat} :
    (rightLen : Nat) → Fin leftLen → Fin (leftLen + rightLen)
  | 0, index => index
  | rightLen + 1, index =>
      ⟨(finIntoCoproductLeft rightLen index).val + 1,
        Nat.succ_lt_succ (finIntoCoproductLeft rightLen index).isLt⟩

/-- Looking up a RIGHT-injected index in an append recovers the right vector — structural induction
on `rightLen`, riding `Fin` proof-irrelevance. -/
theorem SubstVec.lookup_append_right {target leftLen : Nat} (leftVec : SubstVec target leftLen) :
    {rightLen : Nat} → (rightVec : SubstVec target rightLen) → (index : Fin rightLen) →
      (leftVec.append rightVec).lookup (finIntoCoproductRight leftLen index) = rightVec.lookup index
  | 0, _rightVec, index => index.elim0
  | _rightLen + 1, _rightVec, ⟨0, _⟩ => rfl
  | _rightLen + 1, rightVec, ⟨position + 1, isLt⟩ =>
      SubstVec.lookup_append_right leftVec rightVec.2 ⟨position, Nat.lt_of_succ_lt_succ isLt⟩

/-- Looking up a LEFT-injected index in an append recovers the left vector — structural induction on
`rightLen`, riding `Fin` proof-irrelevance. -/
theorem SubstVec.lookup_append_left {target leftLen : Nat} (leftVec : SubstVec target leftLen) :
    {rightLen : Nat} → (rightVec : SubstVec target rightLen) → (index : Fin leftLen) →
      (leftVec.append rightVec).lookup (finIntoCoproductLeft rightLen index) = leftVec.lookup index
  | 0, _rightVec, _index => rfl
  | _rightLen + 1, rightVec, index =>
      SubstVec.lookup_append_left leftVec rightVec.2 index

/-! ## The coproduct injections, projections, and the append/split η-law -/

/-- Pointwise congruence for `tabulate`: equal-on-every-index functions tabulate to equal vectors
(via `ext`; the function-equality form would need `funext`). -/
theorem SubstVec.tabulate_congr {target source : Nat}
    (imageOfA imageOfB : Fin source → RawTerm target)
    (pointwise : ∀ index, imageOfA index = imageOfB index) :
    SubstVec.tabulate imageOfA = SubstVec.tabulate imageOfB :=
  SubstVec.ext _ _ (fun index =>
    (SubstVec.lookup_tabulate imageOfA index).trans
      ((pointwise index).trans (SubstVec.lookup_tabulate imageOfB index).symm))

/-- The LEFT coproduct injection substitution `A ⟶ A + B`: variable `i` maps to variable
`finIntoCoproductLeft B i` of `A + B`. -/
def SubstVec.coproductInjectLeft (leftLen rightLen : Nat) : SubstVec (leftLen + rightLen) leftLen :=
  SubstVec.tabulate
    (fun index => RawTerm.mkGen .gen_var (finIntoCoproductLeft rightLen index) .childNil)

/-- The RIGHT coproduct injection substitution `B ⟶ A + B`: variable `j` maps to variable
`finIntoCoproductRight A j` of `A + B`. -/
def SubstVec.coproductInjectRight (leftLen rightLen : Nat) : SubstVec (leftLen + rightLen) rightLen :=
  SubstVec.tabulate
    (fun index => RawTerm.mkGen .gen_var (finIntoCoproductRight leftLen index) .childNil)

/-- The left injection's lookup is the injected variable term. -/
theorem SubstVec.coproductInjectLeft_lookup (leftLen rightLen : Nat) (index : Fin leftLen) :
    (SubstVec.coproductInjectLeft leftLen rightLen).lookup index
      = RawTerm.mkGen .gen_var (finIntoCoproductLeft rightLen index) .childNil :=
  SubstVec.lookup_tabulate _ index

/-- The right injection's lookup is the injected variable term. -/
theorem SubstVec.coproductInjectRight_lookup (leftLen rightLen : Nat) (index : Fin rightLen) :
    (SubstVec.coproductInjectRight leftLen rightLen).lookup index
      = RawTerm.mkGen .gen_var (finIntoCoproductRight leftLen index) .childNil :=
  SubstVec.lookup_tabulate _ index

/-- The LEFT projection of a `(leftLen + rightLen)`-vector: tabulate its lookups at the
left-injected indices. -/
def SubstVec.coproductSplitLeft {target leftLen rightLen : Nat}
    (vec : SubstVec target (leftLen + rightLen)) : SubstVec target leftLen :=
  SubstVec.tabulate (fun index => vec.lookup (finIntoCoproductLeft rightLen index))

/-- The RIGHT projection of a `(leftLen + rightLen)`-vector: tabulate its lookups at the
right-injected indices. -/
def SubstVec.coproductSplitRight {target leftLen rightLen : Nat}
    (vec : SubstVec target (leftLen + rightLen)) : SubstVec target rightLen :=
  SubstVec.tabulate (fun index => vec.lookup (finIntoCoproductRight leftLen index))

/-- **The append/split η-law.**  Every `(leftLen + rightLen)`-vector is the append of its two
coproduct projections — structural induction on `rightLen`, using `Fin` proof-irrelevance and
product eta (the base collapses to `tabulate_lookup`). -/
theorem SubstVec.append_split {target leftLen : Nat} :
    {rightLen : Nat} → (vec : SubstVec target (leftLen + rightLen)) →
      vec.coproductSplitLeft.append vec.coproductSplitRight = vec
  | 0, vec => SubstVec.tabulate_lookup vec
  | _rightLen + 1, vec => by
      show (vec.1, vec.2.coproductSplitLeft.append vec.2.coproductSplitRight) = vec
      exact Prod.ext rfl (SubstVec.append_split vec.2)

/-- The left projection equals precomposition with the left injection (so the projection of a
mediator is determined by its left leg). -/
theorem SubstVec.coproductSplitLeft_eq_compose {target leftLen rightLen : Nat}
    (vec : SubstVec target (leftLen + rightLen)) :
    vec.coproductSplitLeft
      = fxBaseSubstCategory.compose (SubstVec.coproductInjectLeft leftLen rightLen) vec :=
  SubstVec.ext _ _ (fun index => by
    show vec.coproductSplitLeft.lookup index
        = ((SubstVec.coproductInjectLeft leftLen rightLen).compose vec).lookup index
    rw [SubstVec.lookup_compose, SubstVec.coproductInjectLeft_lookup]
    exact SubstVec.lookup_tabulate _ index)

/-- The right projection equals precomposition with the right injection. -/
theorem SubstVec.coproductSplitRight_eq_compose {target leftLen rightLen : Nat}
    (vec : SubstVec target (leftLen + rightLen)) :
    vec.coproductSplitRight
      = fxBaseSubstCategory.compose (SubstVec.coproductInjectRight leftLen rightLen) vec :=
  SubstVec.ext _ _ (fun index => by
    show vec.coproductSplitRight.lookup index
        = ((SubstVec.coproductInjectRight leftLen rightLen).compose vec).lookup index
    rw [SubstVec.lookup_compose, SubstVec.coproductInjectRight_lookup]
    exact SubstVec.lookup_tabulate _ index)

/-! ## The binary coproduct instance -/

/-- **Scope addition is the BINARY COPRODUCT in the substitution category.**  Injections are the
variable injections; copairing is `append`; both β-laws fall out of the append-lookup laws (a
substitution into a variable is a lookup); uniqueness is the append/split η-law (a mediator's two
projections are exactly its two legs). -/
def fxBaseSubstBinaryCoproduct (leftLen rightLen : Nat) :
    IsBinaryCoproduct fxBaseSubstCategory leftLen rightLen (leftLen + rightLen) where
  injectLeft := SubstVec.coproductInjectLeft leftLen rightLen
  injectRight := SubstVec.coproductInjectRight leftLen rightLen
  copair := fun leftLeg rightLeg => leftLeg.append rightLeg
  copairInjectLeft := fun leftLeg rightLeg =>
    SubstVec.ext _ _ (fun index => by
      show ((SubstVec.coproductInjectLeft leftLen rightLen).compose (leftLeg.append rightLeg)).lookup index
            = leftLeg.lookup index
      rw [SubstVec.lookup_compose, SubstVec.coproductInjectLeft_lookup]
      exact SubstVec.lookup_append_left leftLeg rightLeg index)
  copairInjectRight := fun leftLeg rightLeg =>
    SubstVec.ext _ _ (fun index => by
      show ((SubstVec.coproductInjectRight leftLen rightLen).compose (leftLeg.append rightLeg)).lookup index
            = rightLeg.lookup index
      rw [SubstVec.lookup_compose, SubstVec.coproductInjectRight_lookup]
      exact SubstVec.lookup_append_right leftLeg rightLeg index)
  copairUnique := fun mediator leftLeg rightLeg hLeft hRight => by
    have eta := SubstVec.append_split mediator
    rw [SubstVec.coproductSplitLeft_eq_compose, hLeft,
        SubstVec.coproductSplitRight_eq_compose, hRight] at eta
    exact eta.symm

/-! ## The categorical calculus of finite coproducts (generic) + the substitution bifunctor

The universal properties above already PROVE the finite-coproduct structure exists; this section
earns the calculus that structure carries — generic consequences of `IsInitialObject` /
`IsBinaryCoproduct` (so they hold in any category and specialize to `fxBaseSubstCategory` for free),
then the concrete coproduct BIFUNCTOR `+` on the substitution category with its two functor laws. -/

/-- Any two morphisms out of an INITIAL object are equal (initial objects are "thin from the left"). -/
theorem IsInitialObject.homExt {category : RawCategory.{u, v}} {initialObject : category.Object}
    (initial : IsInitialObject category initialObject) {target : category.Object}
    (firstMorphism secondMorphism : category.Morphism initialObject target) :
    firstMorphism = secondMorphism :=
  (initial.fromInitialUnique firstMorphism).trans (initial.fromInitialUnique secondMorphism).symm

/-- The η-rule: copairing a coproduct's OWN two injections is the identity. -/
theorem IsBinaryCoproduct.copairInjections {category : RawCategory.{u, v}}
    {leftSummand rightSummand coproductObject : category.Object}
    (coproduct : IsBinaryCoproduct category leftSummand rightSummand coproductObject) :
    coproduct.copair coproduct.injectLeft coproduct.injectRight
      = category.identity coproductObject :=
  (coproduct.copairUnique (category.identity coproductObject)
    coproduct.injectLeft coproduct.injectRight
    (category.identityRight coproduct.injectLeft)
    (category.identityRight coproduct.injectRight)).symm

/-- POST-COMPOSITION FUSION: copairing then a map equals copairing the post-composed legs. -/
theorem IsBinaryCoproduct.copairPostCompose {category : RawCategory.{u, v}}
    {leftSummand rightSummand coproductObject : category.Object}
    (coproduct : IsBinaryCoproduct category leftSummand rightSummand coproductObject)
    {target nextTarget : category.Object}
    (leftLeg : category.Morphism leftSummand target)
    (rightLeg : category.Morphism rightSummand target)
    (after : category.Morphism target nextTarget) :
    category.compose (coproduct.copair leftLeg rightLeg) after
      = coproduct.copair (category.compose leftLeg after) (category.compose rightLeg after) :=
  coproduct.copairUnique (category.compose (coproduct.copair leftLeg rightLeg) after)
    (category.compose leftLeg after) (category.compose rightLeg after)
    (by rw [← category.composeAssoc, coproduct.copairInjectLeft])
    (by rw [← category.composeAssoc, coproduct.copairInjectRight])

/-- JOINTLY EPIC injections: two maps out of a coproduct agreeing after both injections are equal. -/
theorem IsBinaryCoproduct.homExt {category : RawCategory.{u, v}}
    {leftSummand rightSummand coproductObject : category.Object}
    (coproduct : IsBinaryCoproduct category leftSummand rightSummand coproductObject)
    {target : category.Object}
    (firstMorphism secondMorphism : category.Morphism coproductObject target)
    (afterLeft : category.compose coproduct.injectLeft firstMorphism
      = category.compose coproduct.injectLeft secondMorphism)
    (afterRight : category.compose coproduct.injectRight firstMorphism
      = category.compose coproduct.injectRight secondMorphism) :
    firstMorphism = secondMorphism :=
  (coproduct.copairUnique firstMorphism _ _ rfl rfl).trans
    (coproduct.copairUnique secondMorphism _ _ afterLeft.symm afterRight.symm).symm

/-- The substitution category's joint-epi extensionality, in `SubstVec.compose` form. -/
theorem SubstVec.homExt {targetScope leftLen rightLen : Nat}
    (firstVec secondVec : SubstVec targetScope (leftLen + rightLen))
    (afterLeft : (SubstVec.coproductInjectLeft leftLen rightLen).compose firstVec
      = (SubstVec.coproductInjectLeft leftLen rightLen).compose secondVec)
    (afterRight : (SubstVec.coproductInjectRight leftLen rightLen).compose firstVec
      = (SubstVec.coproductInjectRight leftLen rightLen).compose secondVec) :
    firstVec = secondVec :=
  (fxBaseSubstBinaryCoproduct leftLen rightLen).homExt firstVec secondVec afterLeft afterRight

/-- Append commutes with post-composition (the `SubstVec`-level copair fusion). -/
theorem SubstVec.append_compose {targetScope nextScope leftLen rightLen : Nat}
    (leftVec : SubstVec targetScope leftLen) (rightVec : SubstVec targetScope rightLen)
    (afterVec : SubstVec nextScope targetScope) :
    (leftVec.append rightVec).compose afterVec
      = (leftVec.compose afterVec).append (rightVec.compose afterVec) :=
  (fxBaseSubstBinaryCoproduct leftLen rightLen).copairPostCompose leftVec rightVec afterVec

/-- **The coproduct BIFUNCTOR `+ : C × C → C`.**  `coproductMap leftMap rightMap` sends
`A + B → A' + B'` by acting with `leftMap` on the left block and `rightMap` on the right (the copair
of the two injected maps). -/
def SubstVec.coproductMap {leftLen leftTarget rightLen rightTarget : Nat}
    (leftMap : SubstVec leftTarget leftLen) (rightMap : SubstVec rightTarget rightLen) :
    SubstVec (leftTarget + rightTarget) (leftLen + rightLen) :=
  (leftMap.compose (SubstVec.coproductInjectLeft leftTarget rightTarget)).append
    (rightMap.compose (SubstVec.coproductInjectRight leftTarget rightTarget))

/-- Naturality of the bifunctor against the LEFT injection. -/
theorem SubstVec.injectLeft_coproductMap {leftLen leftTarget rightLen rightTarget : Nat}
    (leftMap : SubstVec leftTarget leftLen) (rightMap : SubstVec rightTarget rightLen) :
    (SubstVec.coproductInjectLeft leftLen rightLen).compose
        (SubstVec.coproductMap leftMap rightMap)
      = leftMap.compose (SubstVec.coproductInjectLeft leftTarget rightTarget) :=
  (fxBaseSubstBinaryCoproduct leftLen rightLen).copairInjectLeft
    (leftMap.compose (SubstVec.coproductInjectLeft leftTarget rightTarget))
    (rightMap.compose (SubstVec.coproductInjectRight leftTarget rightTarget))

/-- Naturality of the bifunctor against the RIGHT injection. -/
theorem SubstVec.injectRight_coproductMap {leftLen leftTarget rightLen rightTarget : Nat}
    (leftMap : SubstVec leftTarget leftLen) (rightMap : SubstVec rightTarget rightLen) :
    (SubstVec.coproductInjectRight leftLen rightLen).compose
        (SubstVec.coproductMap leftMap rightMap)
      = rightMap.compose (SubstVec.coproductInjectRight leftTarget rightTarget) :=
  (fxBaseSubstBinaryCoproduct leftLen rightLen).copairInjectRight
    (leftMap.compose (SubstVec.coproductInjectLeft leftTarget rightTarget))
    (rightMap.compose (SubstVec.coproductInjectRight leftTarget rightTarget))

/-- FUNCTOR LAW (identities): `+` preserves identity morphisms. -/
theorem SubstVec.coproductMap_identity (leftLen rightLen : Nat) :
    SubstVec.coproductMap (SubstVec.identity leftLen) (SubstVec.identity rightLen)
      = SubstVec.identity (leftLen + rightLen) := by
  show ((SubstVec.identity leftLen).compose (SubstVec.coproductInjectLeft leftLen rightLen)).append
        ((SubstVec.identity rightLen).compose (SubstVec.coproductInjectRight leftLen rightLen))
      = SubstVec.identity (leftLen + rightLen)
  rw [SubstVec.identity_compose, SubstVec.identity_compose]
  exact (fxBaseSubstBinaryCoproduct leftLen rightLen).copairInjections

/-- FUNCTOR LAW (composition): `+` preserves composition (the bifunctor is functorial). -/
theorem SubstVec.coproductMap_compose
    {leftA leftB leftC rightA rightB rightC : Nat}
    (leftFirst : SubstVec leftB leftA) (leftSecond : SubstVec leftC leftB)
    (rightFirst : SubstVec rightB rightA) (rightSecond : SubstVec rightC rightB) :
    SubstVec.coproductMap (leftFirst.compose leftSecond) (rightFirst.compose rightSecond)
      = (SubstVec.coproductMap leftFirst rightFirst).compose
          (SubstVec.coproductMap leftSecond rightSecond) := by
  apply SubstVec.homExt
  · calc (SubstVec.coproductInjectLeft leftA rightA).compose
            (SubstVec.coproductMap (leftFirst.compose leftSecond) (rightFirst.compose rightSecond))
        = (leftFirst.compose leftSecond).compose (SubstVec.coproductInjectLeft leftC rightC) :=
          SubstVec.injectLeft_coproductMap _ _
      _ = leftFirst.compose (leftSecond.compose (SubstVec.coproductInjectLeft leftC rightC)) :=
          SubstVec.compose_assoc _ _ _
      _ = leftFirst.compose ((SubstVec.coproductInjectLeft leftB rightB).compose
            (SubstVec.coproductMap leftSecond rightSecond)) := by
          rw [SubstVec.injectLeft_coproductMap]
      _ = (leftFirst.compose (SubstVec.coproductInjectLeft leftB rightB)).compose
            (SubstVec.coproductMap leftSecond rightSecond) := (SubstVec.compose_assoc _ _ _).symm
      _ = ((SubstVec.coproductInjectLeft leftA rightA).compose
            (SubstVec.coproductMap leftFirst rightFirst)).compose
            (SubstVec.coproductMap leftSecond rightSecond) := by
          rw [SubstVec.injectLeft_coproductMap]
      _ = (SubstVec.coproductInjectLeft leftA rightA).compose
            ((SubstVec.coproductMap leftFirst rightFirst).compose
              (SubstVec.coproductMap leftSecond rightSecond)) :=
          SubstVec.compose_assoc _ _ _
  · calc (SubstVec.coproductInjectRight leftA rightA).compose
            (SubstVec.coproductMap (leftFirst.compose leftSecond) (rightFirst.compose rightSecond))
        = (rightFirst.compose rightSecond).compose (SubstVec.coproductInjectRight leftC rightC) :=
          SubstVec.injectRight_coproductMap _ _
      _ = rightFirst.compose (rightSecond.compose (SubstVec.coproductInjectRight leftC rightC)) :=
          SubstVec.compose_assoc _ _ _
      _ = rightFirst.compose ((SubstVec.coproductInjectRight leftB rightB).compose
            (SubstVec.coproductMap leftSecond rightSecond)) := by
          rw [SubstVec.injectRight_coproductMap]
      _ = (rightFirst.compose (SubstVec.coproductInjectRight leftB rightB)).compose
            (SubstVec.coproductMap leftSecond rightSecond) := (SubstVec.compose_assoc _ _ _).symm
      _ = ((SubstVec.coproductInjectRight leftA rightA).compose
            (SubstVec.coproductMap leftFirst rightFirst)).compose
            (SubstVec.coproductMap leftSecond rightSecond) := by
          rw [SubstVec.injectRight_coproductMap]
      _ = (SubstVec.coproductInjectRight leftA rightA).compose
            ((SubstVec.coproductMap leftFirst rightFirst).compose
              (SubstVec.coproductMap leftSecond rightSecond)) :=
          SubstVec.compose_assoc _ _ _

/-! ## Symmetry: the coproduct is symmetric (`L + R ≅ R + L`)

The braiding is an ISO between the coproduct of `(L, R)` and that of `(R, L)` — note this is an
isomorphism between (generally distinct) objects, NOT an object equality, so it needs NO
`Nat.add_comm`: it is constructed purely from the universal property via the calculus above. -/

/-- The braiding morphism `L + R → R + L` between two coproducts of swapped summands. -/
def IsBinaryCoproduct.braid {category : RawCategory.{u, v}}
    {leftSummand rightSummand coproductLeftRight coproductRightLeft : category.Object}
    (coprodLeftRight : IsBinaryCoproduct category leftSummand rightSummand coproductLeftRight)
    (coprodRightLeft : IsBinaryCoproduct category rightSummand leftSummand coproductRightLeft) :
    category.Morphism coproductLeftRight coproductRightLeft :=
  coprodLeftRight.copair coprodRightLeft.injectRight coprodRightLeft.injectLeft

/-- Braiding then braiding-back is the identity (the coproduct is symmetric). -/
theorem IsBinaryCoproduct.braid_braid {category : RawCategory.{u, v}}
    {leftSummand rightSummand coproductLeftRight coproductRightLeft : category.Object}
    (coprodLeftRight : IsBinaryCoproduct category leftSummand rightSummand coproductLeftRight)
    (coprodRightLeft : IsBinaryCoproduct category rightSummand leftSummand coproductRightLeft) :
    category.compose (coprodLeftRight.braid coprodRightLeft)
        (coprodRightLeft.braid coprodLeftRight)
      = category.identity coproductLeftRight := by
  apply coprodLeftRight.homExt
  · dsimp only [IsBinaryCoproduct.braid]
    rw [← category.composeAssoc, coprodLeftRight.copairInjectLeft,
        coprodRightLeft.copairInjectRight, category.identityRight]
  · dsimp only [IsBinaryCoproduct.braid]
    rw [← category.composeAssoc, coprodLeftRight.copairInjectRight,
        coprodRightLeft.copairInjectLeft, category.identityRight]

/-- The braiding is an ISOMORPHISM: the coproduct of `L, R` is canonically iso to that of `R, L`. -/
def IsBinaryCoproduct.braidIsIso {category : RawCategory.{u, v}}
    {leftSummand rightSummand coproductLeftRight coproductRightLeft : category.Object}
    (coprodLeftRight : IsBinaryCoproduct category leftSummand rightSummand coproductLeftRight)
    (coprodRightLeft : IsBinaryCoproduct category rightSummand leftSummand coproductRightLeft) :
    IsIsomorphism category (coprodLeftRight.braid coprodRightLeft) where
  inverse := coprodRightLeft.braid coprodLeftRight
  leftInverse := coprodRightLeft.braid_braid coprodLeftRight
  rightInverse := coprodLeftRight.braid_braid coprodRightLeft

/-- **The substitution category's coproduct is SYMMETRIC: `A + B ≅ B + A`.**  An honest object
isomorphism in `fxBaseSubstCategory` with no appeal to `Nat.add_comm`. -/
def fxBaseSubstCoproductSymmetry (leftLen rightLen : Nat) :
    IsIsomorphism fxBaseSubstCategory
      ((fxBaseSubstBinaryCoproduct leftLen rightLen).braid
        (fxBaseSubstBinaryCoproduct rightLen leftLen)) :=
  (fxBaseSubstBinaryCoproduct leftLen rightLen).braidIsIso
    (fxBaseSubstBinaryCoproduct rightLen leftLen)

end FX1Poly.Axis
