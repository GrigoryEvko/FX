import FX1Poly.OmegacE.Word

/-! # FX1Poly/OmegacE/WordFreeMonoid
    — the dimension-1 free-monoid (one-object free-category) structure on ωcE scaffold words.

The Makkai/Forest word-problem route (Path B, polycell.md §2.3 / §3.9) decides cell-equality in the **free
ω-category** over a finite generator polygraph.  Before any word *equality* can be posed, the arena it lives
in must exist: at dimension 1 the free ω-category over a one-object signature is the **free monoid** on the
generators — words under concatenation, with associativity and a two-sided identity.

`Word.lean` shipped the words (`OmegacEWord` / `OmegacEWordCode`) and their list-lifted operations
(`append`, `empty`, `suspend`, the encode/decode serialization) but proved only *length*/*projection*
distribution — no algebraic laws.  This file supplies the missing algebraic structure: the words form a
**monoid**, and suspension + the word-code serialization are **monoid homomorphisms**.  This is the
recursion base of Makkai's algorithm (dimension 1), the first genuine substrate atom of the SN-via-words leg.

It does **not** yet decide word equality modulo rewriting, nor prove termination/confluence of the FX
presentation — those are the body of Path B still owed (polycell.md §2.3: "termination, confluence, and
finite generator enumeration" remain for the certified profile).

* `OmegacEWord.append_assoc` / `empty_append` / `append_empty` — the monoid laws on words.
* `OmegacEWord.suspend_empty` / `suspend_append` — suspension is a monoid homomorphism.
* `OmegacEWordCode.append_assoc` / `empty_append` / `append_empty` — the monoid laws on word codes.
* `OmegacEWordCode.ofWord_empty` / `toWord_empty` — the serialization preserves the unit (with the
  `ofWord_append` / `toWord_append` of `Word.lean`, `ofWord` and `toWord` are monoid homomorphisms).

## Zero-axiom verification

The monoid laws reduce to list associativity and right-identity, proved here by **structural induction**
(`listAppendAssoc` / `listAppendNil`) rather than Lean core's `List.append_assoc` / `List.append_nil`,
which carry `propext` in this Init-only setting.  Everything else is `rfl` / `congrArg`.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Gated per declaration in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.OmegacE

/-- List associativity by structural induction — propext-free, unlike core `List.append_assoc`. -/
private theorem listAppendAssoc {elementType : Type _}
    (firstList secondList thirdList : List elementType) :
    (firstList ++ secondList) ++ thirdList
      = firstList ++ (secondList ++ thirdList) := by
  induction firstList with
  | nil => rfl
  | cons head _tail inductionHypothesis =>
      exact congrArg (List.cons head) inductionHypothesis

/-- Right identity for list append by structural induction — propext-free, unlike core `List.append_nil`. -/
private theorem listAppendNil {elementType : Type _} (listValue : List elementType) :
    listValue ++ [] = listValue := by
  induction listValue with
  | nil => rfl
  | cons head _tail inductionHypothesis =>
      exact congrArg (List.cons head) inductionHypothesis

namespace OmegacEWord

variable {dimension : Nat}

/-- **Associativity of word concatenation** — the free monoid's associative law. -/
theorem append_assoc (firstWord secondWord thirdWord : OmegacEWord dimension) :
    append (append firstWord secondWord) thirdWord
      = append firstWord (append secondWord thirdWord) :=
  congrArg OmegacEWord.mk
    (listAppendAssoc firstWord.cells secondWord.cells thirdWord.cells)

/-- **Left identity**: the empty word is a left unit for concatenation. -/
theorem empty_append (word : OmegacEWord dimension) :
    append (empty dimension) word = word := by
  cases word with
  | mk _cells => rfl

/-- **Right identity**: the empty word is a right unit for concatenation. -/
theorem append_empty (word : OmegacEWord dimension) :
    append word (empty dimension) = word :=
  congrArg OmegacEWord.mk (listAppendNil word.cells)

/-- Suspension sends the empty word to the empty word — the unit half of the homomorphism. -/
theorem suspend_empty (dimension : Nat) :
    (empty dimension).suspend = empty (dimension + 1) := rfl

/-- Suspension distributes over concatenation — the multiplication half of the homomorphism. -/
theorem suspend_append (firstWord secondWord : OmegacEWord dimension) :
    (append firstWord secondWord).suspend
      = append firstWord.suspend secondWord.suspend :=
  congrArg OmegacEWord.mk (suspend_append_cells firstWord secondWord)

end OmegacEWord

namespace OmegacEWordCode

/-- **Associativity of word-code concatenation** — the free monoid's associative law on codes. -/
theorem append_assoc (firstCode secondCode thirdCode : OmegacEWordCode) :
    append (append firstCode secondCode) thirdCode
      = append firstCode (append secondCode thirdCode) :=
  congrArg OmegacEWordCode.mk
    (listAppendAssoc firstCode.slotValues secondCode.slotValues thirdCode.slotValues)

/-- **Left identity**: the empty word code is a left unit for concatenation. -/
theorem empty_append (code : OmegacEWordCode) :
    append empty code = code := by
  cases code with
  | mk _slotValues => rfl

/-- **Right identity**: the empty word code is a right unit for concatenation. -/
theorem append_empty (code : OmegacEWordCode) :
    append code empty = code :=
  congrArg OmegacEWordCode.mk (listAppendNil code.slotValues)

/-- The encoder sends the empty word to the empty code — the unit half of the serialization homomorphism
(its multiplication half is `Word.lean`'s `ofWord_append`). -/
theorem ofWord_empty (dimension : Nat) :
    ofWord (OmegacEWord.empty dimension) = empty := rfl

/-- The decoder sends the empty code to the empty word — the unit half of the deserialization homomorphism
(its multiplication half is `Word.lean`'s `toWord_append`). -/
theorem toWord_empty (dimension : Nat) :
    (empty).toWord dimension = OmegacEWord.empty dimension := rfl

end OmegacEWordCode

end FX1Poly.OmegacE
