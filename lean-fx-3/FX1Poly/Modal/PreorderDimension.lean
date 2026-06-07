import FX1Poly.Modal.EffectLatticeClassification

/-! # FX1Poly/Modal/PreorderDimension
    — the PREORDER structural class (§6.3 Dim 7 / Dim 10), and the LIFETIME dimension as the first
      NON-antisymmetric dimension order

FX's graded dimensions have, so far, taken two structural shapes: ordered SEMIRINGS (usage / security /
complexity / space — the `HasGradeOver` engine) and bounded JOIN-SEMILATTICES (effect / trust / overflow /
clock / mutation — the `EffectLatticeClassification` engine).  Both give a PARTIAL ORDER: their induced `le`
is reflexive, transitive, AND antisymmetric.  But §6.3 classifies two dimensions — Lifetime (Dim 7) and
Representation (Dim 10) — as bare PREORDERS: "`'a <= 'b` when `'a` outlives `'b`", "`repr(Native) <=
repr(C)`".  A preorder is order-only — reflexive and transitive but NOT necessarily antisymmetric — so it is
a genuinely THIRD structural class, the last one in FX's dimension taxonomy that this file mechanizes.

## The preorder class and its kernel

A `PreorderDimension` carries only `le`, `le_refl`, `le_trans` — no algebraic operation, no bottom.  Its
distinguishing structure is the induced EQUIVALENCE (the preorder KERNEL): `equiv a b := le a b ∧ le b a`.
On a partial order this kernel is just equality, but on a proper preorder it has non-trivial classes — and
it is always a genuine equivalence relation (`equiv_refl` / `equiv_symm` / `equiv_trans`), proved generically
over any preorder.

## The lattice bridge and the antisymmetry distinction

Every bounded join-semilattice FORGETS to a preorder (`boundedJoinSemilatticeToPreorder`, its induced `le`),
and that preorder is ANTISYMMETRIC (`latticePreorderIsAntisymmetric`, via the shipped `le_antisymm`) — i.e. a
partial order.  So every lattice/semiring dimension lands in the preorder class as a PARTIAL order.  The
LIFETIME dimension does NOT: `lifetimeIsNotAntisymmetric` shows two distinct regions of equal extent are
mutually-outliving (equivalent) yet distinct, so its order is a PROPER preorder — the first dimension whose
order is genuinely not a partial order.  This is the crisp structural payoff: the preorder class strictly
contains the partial-order (lattice/semiring) dimensions, and lifetime is a witness of the strict containment.

## What lands here (all zero-axiom)

  * `PreorderDimension` (structure: `Carrier` / `le` / `le_refl` / `le_trans`) + `equiv` (the kernel) +
    `equiv_refl` / `equiv_symm` / `equiv_trans` (the kernel is an equivalence relation) + `IsAntisymmetric`
    (the partial-order predicate) + `product` (preorders compose).
  * `boundedJoinSemilatticeToPreorder` + `latticePreorderIsAntisymmetric` — every lattice forgets to a
    partial order; `effectInducedPreorder` / `effectInducedPreorderIsAntisymmetric` instantiate it concretely.
  * `LifetimeGrade` (§6.3 Dim 7: `region (identity extent : Nat)` + `staticRegion`) + `outlives` (the
    spec's "`'a` usable where `'b` expected": static outlives all; a finite region outlives another iff it
    lives at least as long) + `lifetimeOutlivesRefl` / `lifetimeOutlivesTrans` + `lifetimePreorder` +
    `lifetimeStaticOutlivesAll`.
  * **`lifetimeRegionsEquivalentButDistinct`** — the genuinely NEW content: two distinct regions of equal
    extent are EQUIVALENT (mutually outlive) yet DISTINCT — a non-trivial kernel class.
  * **`lifetimeIsNotAntisymmetric`** — lifetime's order is a PROPER preorder, NOT a partial order: the first
    dimension whose induced order is genuinely not antisymmetric, the structural opposite of every
    lattice/semiring dimension.
  * `lifetimeProductPreorder` — lifetime composes with itself in the preorder class.

## Honest scope boundary

This mechanizes the preorder structural class and the lifetime instance, proving the kernel is an equivalence
relation, the lattice→preorder forgetful bridge lands in partial orders, and lifetime is a proper (non-
antisymmetric) preorder.  It does NOT model the full §6.3 lifetime semantics (region-scoped allocation,
`with_arena`, the `<r: region>` binder, inference in local scope) — only the COMBINE/order algebra.  The
Representation dimension (§6.3 Dim 10, the other preorder) is not modeled here; the preorder CLASS it would
instantiate is.  Lifetime is NOT folded into the closed `GradedDimensionName` enum (that enum classifies the
lattice family; the preorder class is a separate structural shape).

## Zero-axiom verification

`PreorderDimension` is a plain structure; the kernel equivalence lemmas are anonymous-constructor term proofs
over `le_refl` / `le_trans`; the lattice bridge reuses the shipped `le_refl` / `le_trans` / `le_antisymm`;
`LifetimeGrade` has derived `DecidableEq`; `outlives` reflexivity/transitivity go through `Nat.le_refl` /
`Nat.le_trans` (propext-clean) with the `staticRegion` cases discharged by `trivial` / `False.elim`; the
non-antisymmetry is `injection` + `Nat.noConfusion`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditModal.lean`.
-/

namespace FX1Poly.Modal

/-- The PREORDER structural class: a carrier with a reflexive, transitive `le` — order-only, with no
algebraic operation and NOT necessarily antisymmetric.  The third shape FX dimensions take, after the ordered
semirings (`HasGradeOver`) and the bounded join-semilattices (`BoundedJoinSemilattice`). -/
structure PreorderDimension where
  Carrier : Type
  le : Carrier → Carrier → Prop
  le_refl : (element : Carrier) → le element element
  le_trans : {lower middle upper : Carrier} → le lower middle → le middle upper → le lower upper

/-- The induced equivalence — the preorder KERNEL: two elements are equivalent when each is below the other.
On a partial order this is just equality; on a proper preorder it has non-trivial classes. -/
def PreorderDimension.equiv (preorder : PreorderDimension) (first second : preorder.Carrier) : Prop :=
  preorder.le first second ∧ preorder.le second first

/-- The kernel is reflexive. -/
theorem PreorderDimension.equiv_refl (preorder : PreorderDimension) (element : preorder.Carrier) :
    preorder.equiv element element :=
  ⟨preorder.le_refl element, preorder.le_refl element⟩

/-- The kernel is symmetric. -/
theorem PreorderDimension.equiv_symm {preorder : PreorderDimension} {first second : preorder.Carrier}
    (related : preorder.equiv first second) : preorder.equiv second first :=
  ⟨related.2, related.1⟩

/-- The kernel is transitive — so it is a genuine equivalence relation on any preorder. -/
theorem PreorderDimension.equiv_trans {preorder : PreorderDimension} {first second third : preorder.Carrier}
    (firstRelated : preorder.equiv first second) (secondRelated : preorder.equiv second third) :
    preorder.equiv first third :=
  ⟨preorder.le_trans firstRelated.1 secondRelated.1, preorder.le_trans secondRelated.2 firstRelated.2⟩

/-- A preorder is a PARTIAL ORDER exactly when it is antisymmetric: mutually-below elements are equal (the
kernel collapses to equality). -/
def PreorderDimension.IsAntisymmetric (preorder : PreorderDimension) : Prop :=
  ∀ (first second : preorder.Carrier), preorder.le first second → preorder.le second first → first = second

/-- The product of two preorders is a preorder — the componentwise order (preorders compose). -/
def PreorderDimension.product (firstPreorder secondPreorder : PreorderDimension) : PreorderDimension where
  Carrier := firstPreorder.Carrier × secondPreorder.Carrier
  le := fun lowerPair upperPair =>
    firstPreorder.le lowerPair.1 upperPair.1 ∧ secondPreorder.le lowerPair.2 upperPair.2
  le_refl := fun element => ⟨firstPreorder.le_refl element.1, secondPreorder.le_refl element.2⟩
  le_trans := fun lowerToMiddle middleToUpper =>
    ⟨firstPreorder.le_trans lowerToMiddle.1 middleToUpper.1,
     secondPreorder.le_trans lowerToMiddle.2 middleToUpper.2⟩

/-! ## The lattice bridge — every lattice forgets to a PARTIAL order -/

/-- Every bounded join-semilattice forgets to a preorder: its induced `le` is reflexive and transitive. -/
def boundedJoinSemilatticeToPreorder (lattice : BoundedJoinSemilattice)
    (lawful : IsLawfulBoundedJoinSemilattice lattice) : PreorderDimension where
  Carrier := lattice.Carrier
  le := lattice.le
  le_refl := fun element => BoundedJoinSemilattice.le_refl lawful element
  le_trans := fun lowerToMiddle middleToUpper =>
    BoundedJoinSemilattice.le_trans lawful lowerToMiddle middleToUpper

/-- **A lattice's induced preorder is ANTISYMMETRIC** — i.e. a partial order (via the shipped `le_antisymm`).
So every lattice/semiring dimension lands in the preorder class as a PARTIAL order; the distinction from
lifetime is exactly this property. -/
theorem latticePreorderIsAntisymmetric (lattice : BoundedJoinSemilattice)
    (lawful : IsLawfulBoundedJoinSemilattice lattice) :
    (boundedJoinSemilatticeToPreorder lattice lawful).IsAntisymmetric :=
  fun _ _ firstLeSecond secondLeFirst => BoundedJoinSemilattice.le_antisymm lawful firstLeSecond secondLeFirst

/-- Concrete: the effect dimension's induced preorder. -/
def effectInducedPreorder : PreorderDimension :=
  boundedJoinSemilatticeToPreorder effectLattice effectIsLawfulBoundedJoinSemilattice

/-- The effect-induced preorder is antisymmetric (a partial order). -/
theorem effectInducedPreorderIsAntisymmetric : effectInducedPreorder.IsAntisymmetric :=
  latticePreorderIsAntisymmetric effectLattice effectIsLawfulBoundedJoinSemilattice

/-! ## The lifetime dimension (§6.3 Dim 7) — the first NON-antisymmetric dimension -/

/-- The lifetime grade (§6.3 Dim 7): a finite `region` with an identity and an extent (how long it lives), or
`staticRegion` (outlives every other lifetime). -/
inductive LifetimeGrade where
  | region (identity extent : Nat)
  | staticRegion
  deriving DecidableEq

/-- `'a outlives 'b` — the spec's "`'a` usable where `'b` expected".  `staticRegion` outlives all; a finite
region outlives another iff it lives at least as long (`extentB <= extentA`). -/
def LifetimeGrade.outlives : LifetimeGrade → LifetimeGrade → Prop
  | .staticRegion, _ => True
  | .region _ _, .staticRegion => False
  | .region _ extentA, .region _ extentB => extentB ≤ extentA

/-- Outlives is reflexive (a lifetime outlives itself). -/
theorem lifetimeOutlivesRefl (grade : LifetimeGrade) : grade.outlives grade := by
  cases grade with
  | region identity extent => exact Nat.le_refl extent
  | staticRegion => trivial

/-- Outlives is transitive.  The `staticRegion` cases are discharged by `trivial` (static outlives all) and
`False.elim` (a finite region does not outlive static); the all-region case is `Nat.le_trans` on extents. -/
theorem lifetimeOutlivesTrans {lower middle upper : LifetimeGrade}
    (lowerOutlivesMiddle : lower.outlives middle) (middleOutlivesUpper : middle.outlives upper) :
    lower.outlives upper := by
  cases lower with
  | staticRegion => trivial
  | region lowerIdentity lowerExtent =>
      cases middle with
      | staticRegion => exact lowerOutlivesMiddle.elim
      | region middleIdentity middleExtent =>
          cases upper with
          | staticRegion => exact middleOutlivesUpper.elim
          | region upperIdentity upperExtent =>
              exact Nat.le_trans middleOutlivesUpper lowerOutlivesMiddle

/-- The lifetime preorder (§6.3 Dim 7): carrier `LifetimeGrade`, ordered by `outlives`. -/
def lifetimePreorder : PreorderDimension where
  Carrier := LifetimeGrade
  le := LifetimeGrade.outlives
  le_refl := lifetimeOutlivesRefl
  le_trans := lifetimeOutlivesTrans

/-- `staticRegion` outlives every lifetime (the §6.3 "static outlives all other lifetimes"). -/
theorem lifetimeStaticOutlivesAll (grade : LifetimeGrade) :
    lifetimePreorder.le LifetimeGrade.staticRegion grade := trivial

/-- **The kernel has a non-trivial class.**  Two distinct regions of equal extent are EQUIVALENT (each
outlives the other) yet DISTINCT — exactly the structure a partial order cannot have. -/
theorem lifetimeRegionsEquivalentButDistinct :
    lifetimePreorder.equiv (LifetimeGrade.region 0 5) (LifetimeGrade.region 1 5) ∧
    LifetimeGrade.region 0 5 ≠ LifetimeGrade.region 1 5 :=
  ⟨⟨Nat.le_refl 5, Nat.le_refl 5⟩,
   fun areEqual => by injection areEqual with identityEq _; exact Nat.noConfusion identityEq⟩

/-- **Lifetime is NOT antisymmetric** — its order is a PROPER preorder, not a partial order.  This is the
first dimension whose induced order is genuinely not a partial order: the structural opposite of every
lattice/semiring dimension (all of which are antisymmetric). -/
theorem lifetimeIsNotAntisymmetric : ¬ lifetimePreorder.IsAntisymmetric := by
  intro antisymmetric
  have areEqual : LifetimeGrade.region 0 5 = LifetimeGrade.region 1 5 :=
    antisymmetric (LifetimeGrade.region 0 5) (LifetimeGrade.region 1 5) (Nat.le_refl 5) (Nat.le_refl 5)
  injection areEqual with identityEq _
  exact Nat.noConfusion identityEq

/-- Lifetime composes with itself in the preorder class. -/
def lifetimeProductPreorder : PreorderDimension := lifetimePreorder.product lifetimePreorder

end FX1Poly.Modal
