/-!
# Polynomial Functors (Aberlé-Spivak 2024)

A polynomial p = (A, B) where A : Type (positions/operations) and
B : A → Type (directions/arities per position) represents the
endofunctor P_p(Y) = Σ (a : A), B a → Y on Type.

The category Poly has polynomials as objects and lenses as morphisms.
Cartesian lenses (where backward maps are equivalences) form the
subcategory Poly^Cart whose subterminality is the polynomial-univalence
notion used by the current Axis 2 slice.

For the planned faithful FX generator model, each Generator g should
correspond to a polynomial with one position and g.arity-many directions,
and the generator interface should be their coproduct.  The current
`fxProfile` intentionally records only the smaller monomial scaffold.

Reference: arXiv:2409.19176 §3.
Zero external dependencies.
-/

namespace LeanFX2.Foundation.PolyCell.Algebra

universe u v w

/-- A polynomial functor: positions A + per-position directions B.
Represents the endofunctor P_p(Y) = Σ (a : A), (B a → Y). -/
structure Poly where
  Position : Type u
  Direction : Position → Type v

/-- The endofunctor action of a polynomial on a type Y.
P_p(Y) = Σ (a : Position), (Direction a → Y) -/
def Poly.eval (poly : Poly.{u, v}) (targetType : Type w) : Type (max u v w) :=
  (position : poly.Position) × (poly.Direction position → targetType)

/-- The identity polynomial y: one position, one direction.
Represents the identity functor P_y(Y) = Y. -/
def Poly.identity : Poly.{0, 0} where
  Position := Unit
  Direction := fun () => Unit

/-- A constant polynomial: one position, no directions.
Represents the constant functor P_c(Y) = Unit (ignores Y). -/
def Poly.constant : Poly.{0, 0} where
  Position := Unit
  Direction := fun () => Empty

/-- A linear polynomial with n positions and one direction each.
Represents P(Y) = Fin n × Y (n-fold coproduct of Y). -/
def Poly.linear (arity : Nat) : Poly.{0, 0} where
  Position := Fin arity
  Direction := fun _ => Unit

/-- A monomial polynomial: one position, A-many directions.
Represents P(Y) = A → Y (reader functor). -/
def Poly.monomial (directionCount : Type v) : Poly.{0, v} where
  Position := Unit
  Direction := fun () => directionCount

/-- A representable polynomial: A positions, each with one direction.
Represents P(Y) = A × Y. -/
def Poly.representable (positionType : Type u) : Poly.{u, 0} where
  Position := positionType
  Direction := fun _ => Unit

/-- The coproduct of two polynomials.
P_{p+q}(Y) = P_p(Y) + P_q(Y). -/
def Poly.coproduct (polyLeft polyRight : Poly.{u, v}) : Poly.{u, v} where
  Position := polyLeft.Position ⊕ polyRight.Position
  Direction := fun pos =>
    match pos with
    | .inl posLeft => polyLeft.Direction posLeft
    | .inr posRight => polyRight.Direction posRight

/-- The product of two polynomials.
P_{p×q}(Y) = P_p(Y) × P_q(Y). -/
def Poly.product (polyLeft polyRight : Poly.{u, v}) : Poly.{u, v} where
  Position := polyLeft.Position × polyRight.Position
  Direction := fun ⟨posLeft, posRight⟩ =>
    polyLeft.Direction posLeft ⊕ polyRight.Direction posRight

/-- Composition of polynomials (substitution).
P_{p∘q}(Y) = P_p(P_q(Y)). -/
def Poly.compose (polyOuter polyInner : Poly.{u, v}) : Poly.{max u v, v} where
  Position := (posOuter : polyOuter.Position) × (polyOuter.Direction posOuter → polyInner.Position)
  Direction := fun ⟨posOuter, innerPositionChoice⟩ =>
    (dirOuter : polyOuter.Direction posOuter) × polyInner.Direction (innerPositionChoice dirOuter)

/-- A lens between polynomials: forward on positions, backward on directions. -/
structure Lens (source target : Poly.{u, v}) where
  forward : source.Position → target.Position
  backward : (pos : source.Position) → target.Direction (forward pos) → source.Direction pos

/-- Identity lens. -/
def Lens.identity (poly : Poly.{u, v}) : Lens poly poly where
  forward := id
  backward := fun _ => id

/-- Compose two lenses. -/
def Lens.compose {polyA polyB polyC : Poly.{u, v}}
    (lensF : Lens polyA polyB) (lensG : Lens polyB polyC) :
    Lens polyA polyC where
  forward := lensG.forward ∘ lensF.forward
  backward := fun pos dirC =>
    lensF.backward pos (lensG.backward (lensF.forward pos) dirC)

/-- A lens is Cartesian when each backward map is a bijection (equivalence).
Encoded as: backward has a two-sided inverse at each position. -/
structure IsCartesianLens {source target : Poly.{u, v}} (lens : Lens source target) where
  backwardInverse : (pos : source.Position) →
    source.Direction pos → target.Direction (lens.forward pos)
  leftInv : ∀ (pos : source.Position) (dir : source.Direction pos),
    lens.backward pos (backwardInverse pos dir) = dir
  rightInv : ∀ (pos : source.Position) (dir : target.Direction (lens.forward pos)),
    backwardInverse pos (lens.backward pos dir) = dir

/-- A Cartesian lens (lens + proof of Cartesianness bundled). -/
structure CartesianLens (source target : Poly.{u, v}) extends Lens source target where
  isCartesian : IsCartesianLens toLens

/-- Identity is Cartesian. -/
def CartesianLens.identity (poly : Poly.{u, v}) : CartesianLens poly poly where
  toLens := Lens.identity poly
  isCartesian := {
    backwardInverse := fun _ => id
    leftInv := fun _ _ => rfl
    rightInv := fun _ _ => rfl
  }

/-- Compose Cartesian lenses (Cartesianness preserved under composition). -/
def CartesianLens.compose {polyA polyB polyC : Poly.{u, v}}
    (lensF : CartesianLens polyA polyB)
    (lensG : CartesianLens polyB polyC) :
    CartesianLens polyA polyC where
  toLens := Lens.compose lensF.toLens lensG.toLens
  isCartesian := {
    backwardInverse := fun pos dirA =>
      lensG.isCartesian.backwardInverse (lensF.toLens.forward pos)
        (lensF.isCartesian.backwardInverse pos dirA)
    leftInv := fun pos dirA => by
      show lensF.toLens.backward pos
        (lensG.toLens.backward (lensF.toLens.forward pos)
          (lensG.isCartesian.backwardInverse (lensF.toLens.forward pos)
            (lensF.isCartesian.backwardInverse pos dirA))) = dirA
      rw [lensG.isCartesian.leftInv]
      rw [lensF.isCartesian.leftInv]
    rightInv := fun pos dirC => by
      show lensG.isCartesian.backwardInverse (lensF.toLens.forward pos)
        (lensF.isCartesian.backwardInverse pos
          (lensF.toLens.backward pos
            (lensG.toLens.backward (lensF.toLens.forward pos) dirC))) = dirC
      rw [lensF.isCartesian.rightInv]
      rw [lensG.isCartesian.rightInv]
  }

theorem Poly.identity_eval_equiv (targetType : Type w) :
    Poly.identity.eval targetType = ((_ : Unit) × (Unit → targetType)) := rfl

theorem Poly.constant_eval_equiv (targetType : Type w) :
    Poly.constant.eval targetType = ((_ : Unit) × (Empty → targetType)) := rfl

end LeanFX2.Foundation.PolyCell.Algebra
