import LeanFX2.Graded.Semiring

/-! # Graded/GradeVector — pointwise grade product

A `GradeVector dimensions` carries one grade per registered
dimension.  Pointwise `+`, `*`, `≤`, `0`, `1` lift from each
dimension's `GradeSemiring`.

## Encoding

We use a heterogeneous-list-style encoding: a `Dimension` packs a
carrier type with its `GradeSemiring` instance, and `GradeVector`
is a recursively-built sigma whose `i`-th component is at the
`i`-th dimension's carrier.

## Status

Phase 12.A.5: ships a fixed-arity `nil` / `cons` GradeVector with
pointwise ops and lifted laws.  Variable-arity (∀ Fin n) form
ships in Phase 12.A.6 once Decidable instances are needed for
the elab/checker.

Zero-axiom verified per declaration. -/

namespace LeanFX2.Graded

/-- A registered dimension: carrier type + `GradeSemiring` instance.
The grade vector is parameterized by a `List Dimension`, with one
position per element. -/
structure Dimension : Type 1 where
  carrier  : Type
  semiring : GradeSemiring carrier

/-- A grade vector carrying one grade per dimension.  Built
recursively from a `List Dimension`: empty list → unit (no grades),
cons → product of head's carrier with tail's vector. -/
def GradeVector : List Dimension → Type
  | [] => Unit
  | head :: tail => head.carrier × GradeVector tail

/-! ## Pointwise operations -/

/-- The zero grade vector: each position is the corresponding
dimension's `zero`. -/
def GradeVector.zero : ∀ {dimensions : List Dimension}, GradeVector dimensions
  | [] => ()
  | head :: tail => (head.semiring.zero, @GradeVector.zero tail)

/-- The one grade vector: each position is the corresponding
dimension's `one`. -/
def GradeVector.one : ∀ {dimensions : List Dimension}, GradeVector dimensions
  | [] => ()
  | head :: tail => (head.semiring.one, @GradeVector.one tail)

/-- Pointwise addition: `(g1 + g2) i = g1 i + g2 i`. -/
def GradeVector.add : ∀ {dimensions : List Dimension},
    GradeVector dimensions → GradeVector dimensions → GradeVector dimensions
  | [], _, _ => ()
  | head :: tail, (firstHead, firstTail), (secondHead, secondTail) =>
      (head.semiring.add firstHead secondHead,
       @GradeVector.add tail firstTail secondTail)

/-- Pointwise multiplication: `(g1 * g2) i = g1 i * g2 i`. -/
def GradeVector.mul : ∀ {dimensions : List Dimension},
    GradeVector dimensions → GradeVector dimensions → GradeVector dimensions
  | [], _, _ => ()
  | head :: tail, (firstHead, firstTail), (secondHead, secondTail) =>
      (head.semiring.mul firstHead secondHead,
       @GradeVector.mul tail firstTail secondTail)

/-- Pointwise preorder: `g1 ≤ g2` iff `g1 i ≤ g2 i` at every
dimension. -/
def GradeVector.le : ∀ {dimensions : List Dimension},
    GradeVector dimensions → GradeVector dimensions → Prop
  | [], _, _ => True
  | head :: tail, (firstHead, firstTail), (secondHead, secondTail) =>
      head.semiring.le firstHead secondHead ∧
      @GradeVector.le tail firstTail secondTail

/-! ## Lifted semiring laws

Each pointwise op inherits the corresponding law from per-position
semirings.  Proofs are by structural induction on the dimensions
list, with each cons case combining the per-position law with the
recursive call. -/

/-- Pair-equality helper: `(a, c) = (b, d)` from componentwise
equalities.  Propext-clean via `subst` on the input hypotheses. -/
theorem prodMkEq {alpha beta : Type}
    {firstLeft secondLeft : alpha} {firstRight secondRight : beta}
    (leftEq : firstLeft = secondLeft) (rightEq : firstRight = secondRight) :
    Prod.mk firstLeft firstRight = Prod.mk secondLeft secondRight := by
  subst leftEq
  subst rightEq
  rfl

/-- Pointwise addition is associative.  Lifted from
`add_assoc` at each dimension. -/
theorem GradeVector.add_assoc :
    ∀ {dimensions : List Dimension}
      (firstVec secondVec thirdVec : GradeVector dimensions),
      GradeVector.add (GradeVector.add firstVec secondVec) thirdVec =
        GradeVector.add firstVec (GradeVector.add secondVec thirdVec)
  | [], _, _, _ => rfl
  | dimHead :: _, (firstHead, firstTail), (secondHead, secondTail),
                  (thirdHead, thirdTail) =>
      prodMkEq
        (dimHead.semiring.add_assoc firstHead secondHead thirdHead)
        (GradeVector.add_assoc firstTail secondTail thirdTail)

/-- Pointwise addition is commutative. -/
theorem GradeVector.add_comm :
    ∀ {dimensions : List Dimension}
      (firstVec secondVec : GradeVector dimensions),
      GradeVector.add firstVec secondVec = GradeVector.add secondVec firstVec
  | [], _, _ => rfl
  | dimHead :: _, (firstHead, firstTail), (secondHead, secondTail) =>
      prodMkEq
        (dimHead.semiring.add_comm firstHead secondHead)
        (GradeVector.add_comm firstTail secondTail)

/-- Left identity for addition: `0 + v = v`. -/
theorem GradeVector.add_zero_left :
    ∀ {dimensions : List Dimension} (someVec : GradeVector dimensions),
      GradeVector.add GradeVector.zero someVec = someVec
  | [], () => rfl
  | dimHead :: _, (someHead, someTail) =>
      prodMkEq
        (dimHead.semiring.add_zero_left someHead)
        (GradeVector.add_zero_left someTail)

/-- Right identity for addition: `v + 0 = v`. -/
theorem GradeVector.add_zero_right :
    ∀ {dimensions : List Dimension} (someVec : GradeVector dimensions),
      GradeVector.add someVec GradeVector.zero = someVec
  | [], () => rfl
  | dimHead :: _, (someHead, someTail) =>
      prodMkEq
        (dimHead.semiring.add_zero_right someHead)
        (GradeVector.add_zero_right someTail)

/-- Pointwise multiplication is associative. -/
theorem GradeVector.mul_assoc :
    ∀ {dimensions : List Dimension}
      (firstVec secondVec thirdVec : GradeVector dimensions),
      GradeVector.mul (GradeVector.mul firstVec secondVec) thirdVec =
        GradeVector.mul firstVec (GradeVector.mul secondVec thirdVec)
  | [], _, _, _ => rfl
  | dimHead :: _, (firstHead, firstTail), (secondHead, secondTail),
                  (thirdHead, thirdTail) =>
      prodMkEq
        (dimHead.semiring.mul_assoc firstHead secondHead thirdHead)
        (GradeVector.mul_assoc firstTail secondTail thirdTail)

/-- Left identity for multiplication: `1 * v = v`. -/
theorem GradeVector.mul_one_left :
    ∀ {dimensions : List Dimension} (someVec : GradeVector dimensions),
      GradeVector.mul GradeVector.one someVec = someVec
  | [], () => rfl
  | dimHead :: _, (someHead, someTail) =>
      prodMkEq
        (dimHead.semiring.mul_one_left someHead)
        (GradeVector.mul_one_left someTail)

/-- Right identity for multiplication: `v * 1 = v`. -/
theorem GradeVector.mul_one_right :
    ∀ {dimensions : List Dimension} (someVec : GradeVector dimensions),
      GradeVector.mul someVec GradeVector.one = someVec
  | [], () => rfl
  | dimHead :: _, (someHead, someTail) =>
      prodMkEq
        (dimHead.semiring.mul_one_right someHead)
        (GradeVector.mul_one_right someTail)

/-- Left annihilation: `0 * v = 0`. -/
theorem GradeVector.mul_zero_left :
    ∀ {dimensions : List Dimension} (someVec : GradeVector dimensions),
      GradeVector.mul GradeVector.zero someVec = GradeVector.zero
  | [], () => rfl
  | dimHead :: _, (someHead, someTail) =>
      prodMkEq
        (dimHead.semiring.mul_zero_left someHead)
        (GradeVector.mul_zero_left someTail)

/-- Right annihilation: `v * 0 = 0`. -/
theorem GradeVector.mul_zero_right :
    ∀ {dimensions : List Dimension} (someVec : GradeVector dimensions),
      GradeVector.mul someVec GradeVector.zero = GradeVector.zero
  | [], () => rfl
  | dimHead :: _, (someHead, someTail) =>
      prodMkEq
        (dimHead.semiring.mul_zero_right someHead)
        (GradeVector.mul_zero_right someTail)

/-- Pointwise preorder is reflexive. -/
theorem GradeVector.le_refl :
    ∀ {dimensions : List Dimension} (someVec : GradeVector dimensions),
      GradeVector.le someVec someVec
  | [], () => True.intro
  | head :: tail, (someHead, someTail) =>
      ⟨head.semiring.le_refl someHead, GradeVector.le_refl someTail⟩

/-- Pointwise preorder is transitive. -/
theorem GradeVector.le_trans :
    ∀ {dimensions : List Dimension}
      (firstVec secondVec thirdVec : GradeVector dimensions),
      GradeVector.le firstVec secondVec → GradeVector.le secondVec thirdVec →
      GradeVector.le firstVec thirdVec
  | [], _, _, _, _, _ => True.intro
  | head :: tail, (firstHead, firstTail), (secondHead, secondTail),
                  (thirdHead, thirdTail), ⟨headLe1, tailLe1⟩, ⟨headLe2, tailLe2⟩ =>
      ⟨head.semiring.le_trans firstHead secondHead thirdHead headLe1 headLe2,
       GradeVector.le_trans firstTail secondTail thirdTail tailLe1 tailLe2⟩

/-! ## Smoke: trivial 0-dimension vector

A grade vector at the empty dimension list is just `Unit` — the
"no grades tracked" case.  All laws hold trivially. -/

example : GradeVector [] = Unit := rfl
example : (GradeVector.zero : GradeVector []) = () := rfl
example : (GradeVector.one : GradeVector []) = () := rfl

/-! ## Smoke: 1-dimension Unit-valued vector

The Unit-semiring instance from `Semiring.lean` lets us instantiate
GradeVector at a single dimension where everything collapses. -/

private def unitDimension : Dimension :=
  { carrier := Unit, semiring := inferInstance }

example : GradeVector [unitDimension] = (Unit × Unit) := rfl
example : (GradeVector.zero : GradeVector [unitDimension]) = ((), ()) := rfl

/-- The two-component vector at the unit dimension is associative
under pointwise addition (trivially, since unit has only one
element). -/
example
    (firstVec secondVec thirdVec : GradeVector [unitDimension]) :
    GradeVector.add (GradeVector.add firstVec secondVec) thirdVec
      = GradeVector.add firstVec (GradeVector.add secondVec thirdVec) :=
  GradeVector.add_assoc firstVec secondVec thirdVec

end LeanFX2.Graded
