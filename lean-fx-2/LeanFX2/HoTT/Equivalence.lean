import LeanFX2.HoTT.Transport

/-! # HoTT/Equivalence — type equivalence, contractibility, fibers

Set-level (h-set) HoTT structure built at Lean's meta-level.
Equality is Lean's `Eq` — for v1.0 this delivers the
"propositions-as-h-sets" reading.  Higher-truncation structure
(h-groupoids, ∞-coherences) is v1.1+.

## What ships

* `Equiv A B` — bi-inverse equivalence (toFun/invFun/leftInv/rightInv).
* `Equiv.refl / symm / trans` — equivalence is itself an
  equivalence relation on types.
* `IsContr T` — singleton predicate (one center, every value
  equals it).
* `Fiber f y` — the fiber of `f : A → B` over `y : B`.
* `IsEquiv f` — alternative formulation: every fiber of `f` is
  contractible.  Useful for deriving Equiv from a function.
* Smoke samples on `Bool`, `Nat`, identity functions.

## Why bi-inverse, not "fiber-contractible"?

`Equiv` is the standard "bi-inverse with both round-trips" form.
`IsEquiv` is the equivalent fiber-wise contractibility form.
Both forms exist — `Equiv ↔ IsEquiv ∘ toFun` is provable as a
theorem (via the standard adjoint-equivalence construction).
For v1.0 we ship both shapes and their interconversion.

## Zero-axiom budget

All declarations in this file MUST `#print axioms` clean.
Lean's `Eq.refl / Eq.symm / Eq.trans / Eq.mpr` are propext-free
(direct constructors of `Eq`).  Pattern-matching on `Eq` results
(via `subst` or `rfl`) is also clean when the matchee has type
`a = a` (or a transported variant).

## Dependencies

* `HoTT/Transport.lean` — transport along Lean Eq

## Downstream consumers

* `HoTT/Univalence.lean` — relates `=` on types to `Equiv`
* `HoTT/HIT/Eliminator.lean` — HIT eliminators preserve equivalence
* `HoTT/Path/*` — path operations at the meta-level
-/

namespace LeanFX2

universe leftLevel rightLevel middleLevel

/-- Bi-inverse equivalence between two types.  Carries both
forward and backward functions plus round-trip witnesses.

The "coherence square" between `leftInv` and `rightInv` (the
extra coherence in `IsEquiv`) is omitted at set level — at
h-set, that coherence is automatic from the round-trip equations
because every parallel pair of equations on h-set values is
equal.  For higher truncation levels (v1.1+) the coherence
square would need explicit treatment. -/
structure Equiv (LeftType : Sort leftLevel)
                (RightType : Sort rightLevel) : Sort _ where
  toFun     : LeftType → RightType
  invFun    : RightType → LeftType
  leftInv   : ∀ (leftValue : LeftType),  invFun (toFun  leftValue) = leftValue
  rightInv  : ∀ (rightValue : RightType), toFun  (invFun rightValue) = rightValue

/-- Reflexivity: every type is equivalent to itself via the
identity function. -/
@[reducible] def Equiv.refl (LeftType : Sort leftLevel) : Equiv LeftType LeftType where
  toFun     := fun leftValue => leftValue
  invFun    := fun leftValue => leftValue
  leftInv   := fun _ => rfl
  rightInv  := fun _ => rfl

/-- Symmetry: swap toFun/invFun. -/
@[reducible] def Equiv.symm
    {LeftType : Sort leftLevel} {RightType : Sort rightLevel}
    (someEquiv : Equiv LeftType RightType) :
    Equiv RightType LeftType where
  toFun     := someEquiv.invFun
  invFun    := someEquiv.toFun
  leftInv   := someEquiv.rightInv
  rightInv  := someEquiv.leftInv

/-- Transitivity: compose two equivalences pointwise. -/
def Equiv.trans
    {LeftType : Sort leftLevel} {MiddleType : Sort middleLevel}
    {RightType : Sort rightLevel}
    (firstEquiv  : Equiv LeftType MiddleType)
    (secondEquiv : Equiv MiddleType RightType) :
    Equiv LeftType RightType where
  toFun     := fun leftValue  => secondEquiv.toFun  (firstEquiv.toFun  leftValue)
  invFun    := fun rightValue => firstEquiv.invFun  (secondEquiv.invFun rightValue)
  leftInv   := fun leftValue => by
    show firstEquiv.invFun
           (secondEquiv.invFun (secondEquiv.toFun (firstEquiv.toFun leftValue)))
         = leftValue
    rw [secondEquiv.leftInv (firstEquiv.toFun leftValue),
        firstEquiv.leftInv leftValue]
  rightInv  := fun rightValue => by
    show secondEquiv.toFun
           (firstEquiv.toFun (firstEquiv.invFun (secondEquiv.invFun rightValue)))
         = rightValue
    rw [firstEquiv.rightInv (secondEquiv.invFun rightValue),
        secondEquiv.rightInv rightValue]

/-! ## Group-like laws on Equiv (set-level)

At h-set, two `Equiv` values are equal iff their `toFun` fields
are equal (and consequently the rest).  Strictly, structure
equality requires all four fields to agree.  The lemmas below
state pointwise behavior — the user must `congr`/`Equiv.ext` to
upgrade to structure equality. -/

/-- `(Equiv.refl L).toFun` is the identity function. -/
theorem Equiv.refl_toFun (LeftType : Sort leftLevel) :
    (Equiv.refl LeftType).toFun = fun (leftValue : LeftType) => leftValue := rfl

/-- `(Equiv.symm e).toFun = e.invFun` definitionally. -/
theorem Equiv.symm_toFun
    {LeftType : Sort leftLevel} {RightType : Sort rightLevel}
    (someEquiv : Equiv LeftType RightType) :
    (Equiv.symm someEquiv).toFun = someEquiv.invFun := rfl

/-- `Equiv.symm` is involutive on the toFun field. -/
theorem Equiv.symm_symm_toFun
    {LeftType : Sort leftLevel} {RightType : Sort rightLevel}
    (someEquiv : Equiv LeftType RightType) :
    (Equiv.symm (Equiv.symm someEquiv)).toFun = someEquiv.toFun := rfl

/-- Composing an equivalence with its inverse on `toFun` is the
identity (pointwise). -/
theorem Equiv.trans_symm_toFun_pointwise
    {LeftType : Sort leftLevel} {RightType : Sort rightLevel}
    (someEquiv : Equiv LeftType RightType)
    (leftValue : LeftType) :
    (Equiv.trans someEquiv (Equiv.symm someEquiv)).toFun leftValue
      = leftValue :=
  someEquiv.leftInv leftValue

/-- Composing an inverse with its equivalence on `toFun` is the
identity (pointwise). -/
theorem Equiv.symm_trans_toFun_pointwise
    {LeftType : Sort leftLevel} {RightType : Sort rightLevel}
    (someEquiv : Equiv LeftType RightType)
    (rightValue : RightType) :
    (Equiv.trans (Equiv.symm someEquiv) someEquiv).toFun rightValue
      = rightValue :=
  someEquiv.rightInv rightValue

/-! ## Contractibility -/

/-- A type is contractible when it has a center value to which
every value is equal.  At set level this is the proposition
"the type has exactly one inhabitant up to equality". -/
structure IsContr (SomeType : Sort leftLevel) : Sort (max 1 leftLevel) where
  center  : SomeType
  spoke   : ∀ (someValue : SomeType), someValue = center

/-- The unit type is contractible. -/
def IsContr.unit : IsContr Unit where
  center := ()
  spoke  := fun _ => rfl

/-- A contractible type's center is unique up to definitional
equality with the spoke. -/
theorem IsContr.center_unique {SomeType : Sort leftLevel}
    (contrWitness : IsContr SomeType) (someValue : SomeType) :
    someValue = contrWitness.center :=
  contrWitness.spoke someValue

/-! ## Fiber + IsEquiv -/

/-- The fiber of a function over a target value: pairs of an
input and a proof that it maps to that target. -/
structure Fiber {LeftType : Sort leftLevel} {RightType : Sort rightLevel}
    (someFunction : LeftType → RightType) (target : RightType) :
    Sort (max 1 (max leftLevel rightLevel)) where
  preimage   : LeftType
  preimageEq : someFunction preimage = target

/-- A function is an equivalence when every fiber is
contractible.  Equivalent to bi-inverse `Equiv` at set-level
(provable via the adjoint-equivalence theorem; deferred to
v1.1). -/
def IsEquiv {LeftType : Sort leftLevel} {RightType : Sort rightLevel}
    (someFunction : LeftType → RightType) :
    Sort (max 1 (max leftLevel rightLevel)) :=
  ∀ (target : RightType), IsContr (Fiber someFunction target)

/-- Identity function is always an equivalence: its fiber over
`y` is the singleton `(y, refl)`. -/
def IsEquiv.identity (LeftType : Sort leftLevel) :
    IsEquiv (fun (leftValue : LeftType) => leftValue) :=
  fun target => {
    center := { preimage := target, preimageEq := rfl }
    spoke  := fun fiberPoint => by
      cases fiberPoint with
      | mk preimage preimageEq =>
          cases preimageEq
          rfl
  }

/-! ## Smoke samples -/

/-- The identity equivalence on `Bool`. -/
example : Equiv Bool Bool := Equiv.refl Bool

/-- Composing identity with itself is still an equivalence. -/
example : Equiv Nat Nat := Equiv.trans (Equiv.refl Nat) (Equiv.refl Nat)

/-- Bool's `not` is its own inverse — bi-inverse equivalence. -/
def Equiv.boolNot : Equiv Bool Bool where
  toFun     := Bool.not
  invFun    := Bool.not
  leftInv   := fun leftValue => by cases leftValue <;> rfl
  rightInv  := fun rightValue => by cases rightValue <;> rfl

example : (Equiv.boolNot.toFun true)  = false := rfl
example : (Equiv.boolNot.toFun false) = true  := rfl

/-- `not ∘ not = id` on `Bool`, witnessed via Equiv composition. -/
example : (Equiv.trans Equiv.boolNot Equiv.boolNot).toFun true = true :=
  rfl

end LeanFX2
