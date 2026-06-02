import FX1Poly.OmegacE.WordFreeMonoid

/-! # FX1Poly/OmegacE/WordFreeMonoidUniversal
    — the universal property of the dimension-1 free monoid on ωcE scaffold words.

`WordFreeMonoid.lean` proved that `OmegacEWord` is a monoid under `append`/`empty` (the dimension-1
one-object free category, the arena of Makkai's word-problem recursion).  This file supplies its **universal
property**: `OmegacEWord` is the *free* monoid on its generators — for any target monoid and any
interpretation of generators, there is a UNIQUE monoid homomorphism out of the word monoid extending that
interpretation.

This is the categorical characterization of "free": it is exactly how one maps OUT of the free structure —
the basis for any future decision/normal-form target of the Makkai/Forest word problem (Path B,
polycell.md §2.3 / §3.9).  The target monoid is given by explicit `multiply`/`unit` + the monoid laws
(associativity, two-sided unit) as hypotheses — no Mathlib `Monoid` typeclass, keeping the zero-dependency
discipline.

* `OmegacEWord.foldOut` — the candidate universal map (fold the generators out, right-to-left).
* `foldOut_empty` / `foldOut_append` — `foldOut` is a monoid homomorphism (unit + multiplication halves).
* `foldOut_singleton` — `foldOut` extends the generator interpretation.
* `foldOut_unique` — **uniqueness**: any monoid homomorphism extending the interpretation IS `foldOut`.

It does NOT yet introduce the dimension-2 rewriting relations that make the word problem non-trivial (word
equality modulo relations) — that is the next genuine step on Path B.

## Zero-axiom verification

`foldOut` is `List.foldr`; the homomorphism/uniqueness laws are structural list inductions
(`foldOut_append` uses the target associativity + left unit; `foldOut_singleton` the right unit;
`foldOut_unique` reconstructs each word as `append (singleton head) tail` definitionally).  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Gated per declaration in
`FX1PolyAudit/AuditOmegacE.lean`.
-/

namespace FX1Poly.OmegacE
namespace OmegacEWord

variable {dimension : Nat} {Target : Type _}

/-- Fold a scaffold word out into any target carrier: interpret each generator and multiply, right-to-left
from the unit.  The candidate universal map out of the free monoid. -/
def foldOut (multiply : Target → Target → Target) (unit : Target)
    (interpretCell : OmegacECell dimension → Target) (word : OmegacEWord dimension) : Target :=
  word.cells.foldr (fun cell accumulated => multiply (interpretCell cell) accumulated) unit

/-- `foldOut` sends the empty word to the unit — the unit half of the monoid homomorphism. -/
theorem foldOut_empty (multiply : Target → Target → Target) (unit : Target)
    (interpretCell : OmegacECell dimension → Target) :
    foldOut multiply unit interpretCell (empty dimension) = unit := rfl

/-- `foldOut` carries word concatenation to the target multiplication — the multiplication half of the
monoid homomorphism (needs target associativity + left unit). -/
theorem foldOut_append (multiply : Target → Target → Target) (unit : Target)
    (interpretCell : OmegacECell dimension → Target)
    (associative : ∀ first second third : Target,
      multiply (multiply first second) third = multiply first (multiply second third))
    (leftUnit : ∀ element : Target, multiply unit element = element)
    (firstWord secondWord : OmegacEWord dimension) :
    foldOut multiply unit interpretCell (append firstWord secondWord)
      = multiply (foldOut multiply unit interpretCell firstWord)
          (foldOut multiply unit interpretCell secondWord) := by
  cases firstWord with
  | mk firstCells =>
    cases secondWord with
    | mk secondCells =>
      dsimp only [append, foldOut]
      induction firstCells with
      | nil => exact (leftUnit _).symm
      | cons headCell tailCells inductionHypothesis =>
          show multiply (interpretCell headCell)
              (List.foldr (fun cell accumulated => multiply (interpretCell cell) accumulated) unit
                (tailCells ++ secondCells))
            = multiply (multiply (interpretCell headCell)
                (List.foldr (fun cell accumulated => multiply (interpretCell cell) accumulated) unit
                  tailCells))
              (List.foldr (fun cell accumulated => multiply (interpretCell cell) accumulated) unit
                secondCells)
          rw [inductionHypothesis, associative]

/-- `foldOut` extends the generator interpretation: a one-generator word folds to its interpretation (needs
the target right unit). -/
theorem foldOut_singleton (multiply : Target → Target → Target) (unit : Target)
    (interpretCell : OmegacECell dimension → Target)
    (rightUnit : ∀ element : Target, multiply element unit = element)
    (cell : OmegacECell dimension) :
    foldOut multiply unit interpretCell (singleton cell) = interpretCell cell := by
  dsimp only [singleton, foldOut]
  exact rightUnit _

/-- **Uniqueness half of the free-monoid universal property.**  Any monoid homomorphism out of the word
monoid that extends the generator interpretation IS `foldOut`.  Together with `foldOut_empty`/
`foldOut_append`/`foldOut_singleton`, `foldOut` is THE unique extending homomorphism — `OmegacEWord` is the
free monoid on its generators. -/
theorem foldOut_unique (multiply : Target → Target → Target) (unit : Target)
    (interpretCell : OmegacECell dimension → Target)
    (homomorphism : OmegacEWord dimension → Target)
    (homEmpty : homomorphism (empty dimension) = unit)
    (homAppend : ∀ firstWord secondWord : OmegacEWord dimension,
      homomorphism (append firstWord secondWord)
        = multiply (homomorphism firstWord) (homomorphism secondWord))
    (homSingleton : ∀ cell : OmegacECell dimension,
      homomorphism (singleton cell) = interpretCell cell)
    (word : OmegacEWord dimension) :
    homomorphism word = foldOut multiply unit interpretCell word := by
  cases word with
  | mk cells =>
    induction cells with
    | nil => exact homEmpty
    | cons headCell tailCells inductionHypothesis =>
        calc homomorphism (OmegacEWord.mk (headCell :: tailCells))
            = multiply (homomorphism (singleton headCell))
                (homomorphism (OmegacEWord.mk tailCells)) :=
              homAppend (singleton headCell) (OmegacEWord.mk tailCells)
          _ = multiply (interpretCell headCell)
                (foldOut multiply unit interpretCell (OmegacEWord.mk tailCells)) := by
              rw [homSingleton, inductionHypothesis]
          _ = foldOut multiply unit interpretCell (OmegacEWord.mk (headCell :: tailCells)) := rfl

/-- **Homomorphism extensionality.**  Two monoid homomorphisms out of the word monoid that agree on the
generators are equal — a direct corollary of `foldOut_unique` (both equal the fold of their common generator
action).  This is the universal property's "uniqueness" packaged for direct use: to compare two maps out of
the free monoid, compare them on generators. -/
theorem hom_ext (multiply : Target → Target → Target) (unit : Target)
    (firstHom secondHom : OmegacEWord dimension → Target)
    (firstEmpty : firstHom (empty dimension) = unit)
    (secondEmpty : secondHom (empty dimension) = unit)
    (firstAppend : ∀ firstWord secondWord : OmegacEWord dimension,
      firstHom (append firstWord secondWord) = multiply (firstHom firstWord) (firstHom secondWord))
    (secondAppend : ∀ firstWord secondWord : OmegacEWord dimension,
      secondHom (append firstWord secondWord) = multiply (secondHom firstWord) (secondHom secondWord))
    (agreeOnGenerators : ∀ cell : OmegacECell dimension,
      firstHom (singleton cell) = secondHom (singleton cell))
    (word : OmegacEWord dimension) :
    firstHom word = secondHom word :=
  (foldOut_unique multiply unit (fun cell => firstHom (singleton cell)) firstHom
      firstEmpty firstAppend (fun _cell => rfl) word).trans
    (foldOut_unique multiply unit (fun cell => firstHom (singleton cell)) secondHom
      secondEmpty secondAppend (fun cell => (agreeOnGenerators cell).symm) word).symm

/-- **Word length is the canonical free-monoid homomorphism into `(ℕ, +, 0)`.**  Sending every generator to
`1`, `length` is THE unique monoid homomorphism extending that interpretation — the textbook instance of the
universal property.  Proved by `foldOut_unique` on the shipped `length_empty`/`length_append`/
`length_singleton`. -/
theorem length_eq_foldOut (word : OmegacEWord dimension) :
    word.length = foldOut Nat.add 0 (fun _cell => 1) word :=
  foldOut_unique Nat.add 0 (fun _cell => 1) (fun candidateWord => candidateWord.length)
    (length_empty dimension) length_append (fun cell => length_singleton cell) word

end OmegacEWord
end FX1Poly.OmegacE
