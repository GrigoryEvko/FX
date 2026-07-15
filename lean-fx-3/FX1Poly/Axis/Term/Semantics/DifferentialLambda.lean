/-! # Axis/Term — the differential λ-calculus: derivations + linear substitution (term-25)

The fifth (and final) term-axis SEMANTICS rung.  The differential λ-calculus (Ehrhard-Regnier 2003) adds a
DERIVATIVE to the λ-calculus: a term can be differentiated against a variable, substituting a copy of the
argument for EXACTLY ONE occurrence — the LINEAR (resource) substitution — and the result is a formal SUM
over all the occurrences.  Its two structural laws are LINEARITY (the derivative is additive, zero on
constants) and the LEIBNIZ product rule (the derivative of an application differentiates the function and the
argument and adds the two).  This file ships both levels (each piece zero-axiom, Init-only):

  * **`DifferentialAlgebra`** — the ABSTRACT derivation: a carrier with `zero` / `add` / `mul` / `deriv` and
    the laws `deriv_zero`, `deriv_add` (LINEARITY) and `deriv_mul` (the LEIBNIZ product rule
    `d(xy) = (dx)y + x(dy)`).  `DifferentialAlgebra.deriv_square` derives the power rule `d(x²) = (dx)x +
    x(dx)`; `onePointDifferentialAlgebra` is a concrete model (so the law set is consistent).
  * **`ResourceTerm`** + **`linearSubst`** — the CONCRETE differential/linear substitution: `linearSubst v t`
    replaces exactly one occurrence of variable `v` by `t`, returning the formal sum (a `List`) of all such
    single-replacements.  `linearSubst_app` (★) is the LEIBNIZ product rule on the nose;
    `linearSubst_length_eq_occurrences` (★) is LINEARITY — the number of summands equals the number of
    occurrences (the derivative has degree = occurrence count); `linearSubst_eq_nil_of_absent` is the
    constant rule (a variable that does not occur has zero derivative).
  * **`exampleSquare`** — the witness `x x` (`x²`) with `linearSubst v t (x x) = [x t, t x]` and occurrence
    count `2`: the derivative of `x²` is the two-summand sum `2x`, the classic Ehrhard-Regnier example.

## Honest scope

Shipped: the abstract differential-algebra laws (linearity + Leibniz) with a concrete model + the derived
power rule, and the concrete differential/linear substitution on the variable/application fragment with the
Leibniz product rule, linearity (occurrence count), the constant rule, and the `x²` witness.  DEFERRED:
λ-ABSTRACTION in the linear substitution (capture-avoiding shift under a binder), the formal-sum MODULE
structure proper (ℕ-coefficient linear combinations up to permutation — needs a quotient or a permutation
setoid), the RESOURCE CALCULUS reduction + its confluence/normalization, and — the title's deep construction
— the TAYLOR EXPANSION (a λ-term as the infinite formal sum of its iterated derivatives on the diagonal) and
its commutation with normalization (Ehrhard-Regnier).  This is the `term-25` slice of the omnibus
`fxTerm_hasDenotationalAdequacy = false`.

## Zero-axiom verification

`DifferentialAlgebra` is a record; `onePointDifferentialAlgebra` is all `rfl` (the carrier is `Unit`);
`linearSubst` / `occurrences` are structural recursion on `ResourceTerm` with a full Bool match on the
variable test; `linearSubst_app` is `rfl`; the length law uses hand-proved `listLengthAppendReversed` /
`listLengthMap` (definitional `List` inductions, no `propext`-tainted stdlib lemmas) and `natAddEqZero`; the
variable cases split on `Nat.beq` and close by `rfl` (full Bool enumeration).  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditAxisTermDifferentialLambda.lean`.
-/

namespace FX1Poly.Core

/-! ## The abstract derivation — linearity + the Leibniz law -/

/-- A **differential algebra**: a carrier with addition, multiplication, a `zero`, and a `deriv` operator
obeying LINEARITY (`deriv_zero`, `deriv_add`) and the LEIBNIZ product rule (`deriv_mul`). -/
structure DifferentialAlgebra where
  /-- The carrier. -/
  Carrier : Type
  /-- The additive unit. -/
  zero : Carrier
  /-- Addition (the formal sum). -/
  add : Carrier → Carrier → Carrier
  /-- Multiplication (the product whose derivative obeys Leibniz). -/
  mul : Carrier → Carrier → Carrier
  /-- The derivative operator. -/
  deriv : Carrier → Carrier
  /-- LINEARITY (zero): the derivative of zero is zero. -/
  deriv_zero : deriv zero = zero
  /-- LINEARITY (additivity): the derivative distributes over a sum. -/
  deriv_add : ∀ left right : Carrier, deriv (add left right) = add (deriv left) (deriv right)
  /-- The LEIBNIZ product rule: `d(xy) = (dx)y + x(dy)`. -/
  deriv_mul : ∀ left right : Carrier,
    deriv (mul left right) = add (mul (deriv left) right) (mul left (deriv right))

/-- ★ The **power rule** `d(x²) = (dx)x + x(dx)`, a direct consequence of the Leibniz product rule. -/
theorem DifferentialAlgebra.deriv_square (algebra : DifferentialAlgebra) (value : algebra.Carrier) :
    algebra.deriv (algebra.mul value value)
      = algebra.add (algebra.mul (algebra.deriv value) value) (algebra.mul value (algebra.deriv value)) :=
  algebra.deriv_mul value value

/-- The **one-point differential algebra**: a concrete model (carrier `Unit`), so the law set is
consistent / inhabited. -/
def onePointDifferentialAlgebra : DifferentialAlgebra where
  Carrier := Unit
  zero := ()
  add := fun _ _ => ()
  mul := fun _ _ => ()
  deriv := fun _ => ()
  deriv_zero := rfl
  deriv_add := fun _ _ => rfl
  deriv_mul := fun _ _ => rfl

/-- ★ **Differential algebras are closed under PRODUCTS.**  The componentwise product of two differential
algebras is again one — addition / multiplication / derivative act componentwise and each law holds in each
factor.  (The category of differential algebras has products; `onePointDifferentialAlgebra` is the terminal
object, this the binary product.) -/
def productDifferentialAlgebra (left right : DifferentialAlgebra) : DifferentialAlgebra where
  Carrier := left.Carrier × right.Carrier
  zero := (left.zero, right.zero)
  add := fun firstPair secondPair =>
    (left.add firstPair.1 secondPair.1, right.add firstPair.2 secondPair.2)
  mul := fun firstPair secondPair =>
    (left.mul firstPair.1 secondPair.1, right.mul firstPair.2 secondPair.2)
  deriv := fun pair => (left.deriv pair.1, right.deriv pair.2)
  deriv_zero := by
    show (left.deriv left.zero, right.deriv right.zero) = (left.zero, right.zero)
    rw [left.deriv_zero, right.deriv_zero]
  deriv_add := by
    intro firstPair secondPair
    show (left.deriv (left.add firstPair.1 secondPair.1),
          right.deriv (right.add firstPair.2 secondPair.2))
        = (left.add (left.deriv firstPair.1) (left.deriv secondPair.1),
           right.add (right.deriv firstPair.2) (right.deriv secondPair.2))
    rw [left.deriv_add, right.deriv_add]
  deriv_mul := by
    intro firstPair secondPair
    show (left.deriv (left.mul firstPair.1 secondPair.1),
          right.deriv (right.mul firstPair.2 secondPair.2))
        = (left.add (left.mul (left.deriv firstPair.1) secondPair.1)
              (left.mul firstPair.1 (left.deriv secondPair.1)),
           right.add (right.mul (right.deriv firstPair.2) secondPair.2)
              (right.mul firstPair.2 (right.deriv secondPair.2)))
    rw [left.deriv_mul, right.deriv_mul]

/-! ## The concrete differential / linear substitution -/

/-- A **resource term** (the variable/application fragment): a variable or an application. -/
inductive ResourceTerm where
  /-- A variable, named by a de Bruijn-style index. -/
  | var (name : Nat)
  /-- An application of a function term to an argument term. -/
  | app (function argument : ResourceTerm)

/-- The number of free occurrences of `targetVariable` in a term. -/
def occurrences (targetVariable : Nat) : ResourceTerm → Nat
  | ResourceTerm.var nodeVariable =>
      match Nat.beq nodeVariable targetVariable with
      | true => 1
      | false => 0
  | ResourceTerm.app functionPart argumentPart =>
      occurrences targetVariable functionPart + occurrences targetVariable argumentPart

/-- **Linear (differential) substitution**: replace EXACTLY ONE occurrence of `targetVariable` by
`replacement`, summed over every occurrence — the formal sum is returned as a `List`.  On an application this
is the LEIBNIZ product rule: differentiate the argument (keep the function) PLUS differentiate the function
(keep the argument). -/
def linearSubst (targetVariable : Nat) (replacement : ResourceTerm) : ResourceTerm → List ResourceTerm
  | ResourceTerm.var nodeVariable =>
      match Nat.beq nodeVariable targetVariable with
      | true => [replacement]
      | false => []
  | ResourceTerm.app functionPart argumentPart =>
      (linearSubst targetVariable replacement argumentPart).map
          (fun derivedArgument => ResourceTerm.app functionPart derivedArgument)
        ++ (linearSubst targetVariable replacement functionPart).map
          (fun derivedFunction => ResourceTerm.app derivedFunction argumentPart)

/-- ★ **The Leibniz product rule** (definitional): differentiating an application differentiates the argument
(keeping the function) and the function (keeping the argument), and sums the two. -/
theorem linearSubst_app (targetVariable : Nat) (replacement function argument : ResourceTerm) :
    linearSubst targetVariable replacement (ResourceTerm.app function argument)
      = (linearSubst targetVariable replacement argument).map
          (fun derivedArgument => ResourceTerm.app function derivedArgument)
        ++ (linearSubst targetVariable replacement function).map
          (fun derivedFunction => ResourceTerm.app derivedFunction argument) := rfl

/-! ## Small hand-proved helpers (zero-axiom `List`/`Nat` facts) -/

/-- `List.map` preserves length (hand-proved, definitional). -/
theorem listLengthMap {Source Target : Type} (elements : List Source) (transform : Source → Target) :
    (elements.map transform).length = elements.length := by
  induction elements with
  | nil => rfl
  | cons _ rest inductionHypothesis =>
      show (rest.map transform).length + 1 = rest.length + 1
      rw [inductionHypothesis]

/-- Append-length, with the summands in reversed order (so the `cons` case is fully definitional, avoiding
`Nat.zero_add` / `Nat.add_right_comm`). -/
theorem listLengthAppendReversed {Element : Type} (front back : List Element) :
    (front ++ back).length = back.length + front.length := by
  induction front with
  | nil => rfl
  | cons _ rest inductionHypothesis =>
      show (rest ++ back).length + 1 = back.length + rest.length + 1
      rw [inductionHypothesis]

/-! ## Linearity and the constant rule -/

/-- ★ **Linearity (degree = occurrence count)**: the differential substitution produces exactly one summand
per occurrence of the variable — the number of terms in the formal sum equals `occurrences`. -/
theorem linearSubst_length_eq_occurrences (targetVariable : Nat) (replacement : ResourceTerm) :
    ∀ subject : ResourceTerm,
      (linearSubst targetVariable replacement subject).length = occurrences targetVariable subject := by
  intro subject
  induction subject with
  | var nodeVariable =>
      show (match Nat.beq nodeVariable targetVariable with
            | true => [replacement]
            | false => ([] : List ResourceTerm)).length
            = match Nat.beq nodeVariable targetVariable with
              | true => 1
              | false => 0
      cases Nat.beq nodeVariable targetVariable with
      | true => rfl
      | false => rfl
  | app functionPart argumentPart functionHypothesis argumentHypothesis =>
      show ((linearSubst targetVariable replacement argumentPart).map
              (fun derivedArgument => ResourceTerm.app functionPart derivedArgument)
            ++ (linearSubst targetVariable replacement functionPart).map
              (fun derivedFunction => ResourceTerm.app derivedFunction argumentPart)).length
            = occurrences targetVariable functionPart + occurrences targetVariable argumentPart
      rw [listLengthAppendReversed, listLengthMap, listLengthMap, functionHypothesis, argumentHypothesis]

/-- **The constant rule**: a variable that does not occur has zero derivative (the empty formal sum).  A
direct corollary of linearity — zero occurrences means zero summands, and a length-`0` list is `nil`. -/
theorem linearSubst_eq_nil_of_absent (targetVariable : Nat) (replacement : ResourceTerm)
    (subject : ResourceTerm) (absent : occurrences targetVariable subject = 0) :
    linearSubst targetVariable replacement subject = [] := by
  have lengthZero : (linearSubst targetVariable replacement subject).length = 0 := by
    rw [linearSubst_length_eq_occurrences, absent]
  cases hsum : linearSubst targetVariable replacement subject with
  | nil => rfl
  | cons _ _ =>
      rw [hsum] at lengthZero
      nomatch lengthZero

/-- ★ **The converse — a present variable has a NON-zero derivative.**  If `targetVariable` occurs, the
differential substitution is a non-empty formal sum (at least one summand).  Dual to the constant rule, again
a corollary of linearity (`length = occurrences`). -/
theorem linearSubst_ne_nil_of_present (targetVariable : Nat) (replacement : ResourceTerm)
    (subject : ResourceTerm) (present : occurrences targetVariable subject ≠ 0) :
    linearSubst targetVariable replacement subject ≠ [] := by
  intro isNil
  have lengthEq : occurrences targetVariable subject = ([] : List ResourceTerm).length := by
    rw [← linearSubst_length_eq_occurrences targetVariable replacement subject, isNil]
  exact present lengthEq

/-! ## The witness — the derivative of `x²` -/

/-- The resource term `x x` (the self-application `x²`), with `x` the variable index `0`. -/
def exampleSquare : ResourceTerm := ResourceTerm.app (ResourceTerm.var 0) (ResourceTerm.var 0)

/-- `x²` has two occurrences of `x`. -/
theorem exampleSquare_occurrences : occurrences 0 exampleSquare = 2 := rfl

/-- ★ The derivative of `x²` is the TWO-summand formal sum `[x t, t x]` — the resource-level `2x`. -/
theorem exampleSquare_derivative (replacement : ResourceTerm) :
    linearSubst 0 replacement exampleSquare
      = [ResourceTerm.app (ResourceTerm.var 0) replacement,
         ResourceTerm.app replacement (ResourceTerm.var 0)] := rfl

/-- The derivative of `x²` has two summands (linearity: degree `2` matches the occurrence count). -/
theorem exampleSquare_derivative_length (replacement : ResourceTerm) :
    (linearSubst 0 replacement exampleSquare).length = 2 := rfl

end FX1Poly.Core
