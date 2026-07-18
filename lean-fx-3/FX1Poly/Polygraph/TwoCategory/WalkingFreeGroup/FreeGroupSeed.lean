import FX1Poly.Polygraph.TwoCategory.WalkingCommutativeMonoid.MultisetCommutativeMonoidSeed

/-! # WalkingFreeGroup/FreeGroupSeed — the walking free (NON-abelian) group on an ARBITRARY alphabet ℕ:
free-reduction to reduced words over signed generators

The non-abelian successor of the free-abelian rung (`ColourAbelianGroupSeed`, whose class is a ℤᵏ winding
VECTOR decided by a CROSS-ADDED multiset).  Dropping commutativity, a tree's class in the free **group** on
the colour set `ℕ` is a REDUCED WORD over signed generators (a colour with a polarity) — the free monoid on
`{gen, gen⁻¹}` modulo cancellation of adjacent inverse pairs.  Because that reduced word is a COMPLETE
invariant and every word has a UNIQUE reduced form, the word problem is decided by plain equality of reduced
`List SignedGen`s.

## ★ Why this walker is FULLY DECIDED (arbitrary alphabet) — and why it is NON-abelian

The reducer is a right fold of `reduceCons` — prepend a generator to an already-reduced word, cancelling it
against the head when it is its inverse.  `reduceWord = foldr reduceCons []` (here spelled as the direct
recursion `appendReduce word []`).  The genuinely hard part is **free-reduction confluence** — that reducing a
prefix first does not change the final reduction — which lands here as ASSOCIATIVITY of `appendReduce`
(`appendReduceAssoc`), the Church-Rosser property of the cancellation rewriting.  Its heart is the
cancel/uncancel lemma `reduceConsCancelInverse` (`g (h w) = w` when `g, h` are inverse and `w` is reduced),
fed through the reduced-accumulator swap `appendReduceReduceConsSwap`.

Crucially, the reducer is order-SENSITIVE: `m(leaf 0, leaf 1)` and `m(leaf 1, leaf 0)` reduce to the DISTINCT
words `[(0,+),(1,+)]` and `[(1,+),(0,+)]`, so they are NOT convertible — the free group SEES order, unlike the
abelian ℤᵏ walker (`freeGroupNonCommutative`).  The inverse-homomorphism law is REVERSED (`i(m a b) ≈
m(i b, i a)`): there is no `commSwap`.

This file ships **soundness** (convertible trees have equal reduced word `wordOf`), **normalization** (every
tree reduces to the comb of its reduced word), **completeness** (equal reduced word ⟹ convertible), and **the
decision** (the convertibility ⟺ `List SignedGen`-equality biconditional plus a genuine `Decidable`).

### Honest correction to the naive confluence statement

The unrestricted `appendReduce (reduceWord x) y = appendReduce x y` is FALSE for a non-reduced accumulator `y`
(with `g` the inverse of `h`, take `x = [g, h]`, `y = [g, h]`: the left side is `y = [g, h]` but the right side
reduces to `[]`).  The TRUE theorem — the one this file ships — carries `IsReduced y`; every application is to a
`wordOf` output, which `wordOfIsReduced` certifies reduced, so the hypothesis is always dischargeable.

Raw Lean 4 + Init; the convertibility is an inductive `Prop`; per-declaration `#assert_no_axioms` gated in the
audit twin.  Free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`, `Int`, `Nat.sub`
— the colour comparison is `Nat.beq` (hand-proved reflexivity/soundness), everything is cons-only, and no
`List.append` (`++`) appears anywhere (the inverse is a cons-only accumulator `invertInto`, the end-append is a
cons-only `snoc`). -/

namespace FX1Poly.Polygraph

/-! ## Zero-axiom `Bool`/`Nat` kit (the colour-equality and polarity primitives) -/

/-- Structural reflexivity of the core Boolean equality `Nat.beq`: `Nat.beq value value = true`.  (Named
`natBeqSelfTrue` to avoid colliding with `ColourAbelianGroupSeed.natBeqRefl` in the shared namespace.) -/
theorem natBeqSelfTrue : (value : Nat) → Nat.beq value value = true
  | 0 => rfl
  | Nat.succ predecessor => natBeqSelfTrue predecessor

/-- Soundness of `Nat.beq`: `Nat.beq first second = true` forces `first = second`.  Structural recursion on
both arguments; the mixed corners fall to `Bool.noConfusion`. -/
theorem natBeqImpliesEq : (first second : Nat) → Nat.beq first second = true → first = second
  | 0, 0, _ => rfl
  | 0, Nat.succ _, hbeq => Bool.noConfusion hbeq
  | Nat.succ _, 0, hbeq => Bool.noConfusion hbeq
  | Nat.succ firstPredecessor, Nat.succ secondPredecessor, hbeq =>
      congrArg Nat.succ (natBeqImpliesEq firstPredecessor secondPredecessor hbeq)

/-- Symmetry of `Nat.beq` as a Boolean equality: `Nat.beq first second = Nat.beq second first`. -/
theorem natBeqSymmEq : (first second : Nat) → Nat.beq first second = Nat.beq second first
  | 0, 0 => rfl
  | 0, Nat.succ _ => rfl
  | Nat.succ _, 0 => rfl
  | Nat.succ firstPredecessor, Nat.succ secondPredecessor => natBeqSymmEq firstPredecessor secondPredecessor

/-- Double-negation of `Bool` is the identity: `!(!value) = value`. -/
theorem boolNotInvol : (value : Bool) → (! (! value)) = value
  | true => rfl
  | false => rfl

/-- `!true = false`. -/
theorem boolNotTrue : (! true) = false := rfl

/-- `!false = true`. -/
theorem boolNotFalse : (! false) = true := rfl

/-- `!value = true` forces `value = false`. -/
theorem boolNotEqTrueImpliesFalse (value : Bool) (hnot : (! value) = true) : value = false := by
  cases value with
  | true => exact Bool.noConfusion hnot
  | false => rfl

/-- `!value = false` forces `value = true`. -/
theorem boolNotEqFalseImpliesTrue (value : Bool) (hnot : (! value) = false) : value = true := by
  cases value with
  | true => rfl
  | false => exact Bool.noConfusion hnot

/-- `x && y = true` extracts the left conjunct `x = true` (propext-free; case on `x`). -/
theorem boolAndTrueLeft (left right : Bool) (hand : (left && right) = true) : left = true := by
  cases left with
  | true => rfl
  | false => exact Bool.noConfusion hand

/-- `x && y = true` extracts the right conjunct `y = true` (propext-free; case on `x`). -/
theorem boolAndTrueRight (left right : Bool) (hand : (left && right) = true) : right = true := by
  cases left with
  | true => exact hand
  | false => exact Bool.noConfusion hand

/-- The **polarity-difference** predicate on `Bool`: `boolDiffer p q = true` exactly when `p` and `q` differ
(a full-enumeration exclusive-or, avoiding every `BEq`/`!=` instance). -/
def boolDiffer : Bool → Bool → Bool
  | true, true => false
  | true, false => true
  | false, true => true
  | false, false => false

/-- `boolDiffer` is symmetric. -/
theorem boolDifferComm : (left right : Bool) → boolDiffer left right = boolDiffer right left
  | true, true => rfl
  | true, false => rfl
  | false, true => rfl
  | false, false => rfl

/-- `boolDiffer` on doubly-negated arguments equals `boolDiffer` on the originals. -/
theorem boolDifferNotBoth : (left right : Bool) → boolDiffer (! left) (! right) = boolDiffer left right
  | true, true => rfl
  | true, false => rfl
  | false, true => rfl
  | false, false => rfl

/-- A value and its negation always differ: `boolDiffer (!value) value = true`. -/
theorem boolDifferNotSelfLeft : (value : Bool) → boolDiffer (! value) value = true
  | true => rfl
  | false => rfl

/-- `boolDiffer left right = true` forces `left = !right`. -/
theorem boolDifferTrueImpliesNot (left right : Bool) (hdiff : boolDiffer left right = true) :
    left = ! right := by
  cases left with
  | true =>
    cases right with
    | true => exact Bool.noConfusion hdiff
    | false => rfl
  | false =>
    cases right with
    | true => rfl
    | false => exact Bool.noConfusion hdiff

/-! ## The signed-generator alphabet + the reducer (cons-only, NO `List.append`) -/

/-- A **signed generator**: a colour in `ℕ` with a polarity (`isPositive = true` is the generator, `false` its
inverse).  A word over these — modulo cancellation of adjacent inverse pairs — is an element of the free group
on the colour alphabet. -/
structure SignedGen where
  /-- The colour (which generator of the alphabet). -/
  colour : Nat
  /-- The polarity: `true` = the generator, `false` = its formal inverse. -/
  isPositive : Bool
deriving DecidableEq

/-- Two signed generators are **inverse** iff same colour, opposite polarity. -/
def isInverseGen (left right : SignedGen) : Bool :=
  Nat.beq left.colour right.colour && boolDiffer left.isPositive right.isPositive

/-- The **flip** of a signed generator (its formal inverse): same colour, opposite polarity. -/
def flipGen (gen : SignedGen) : SignedGen := ⟨gen.colour, ! gen.isPositive⟩

/-- Flipping is involutive: `flipGen (flipGen gen) = gen`. -/
theorem flipGenInvol (gen : SignedGen) : flipGen (flipGen gen) = gen := by
  cases gen with
  | mk colour isPositive =>
    show (⟨colour, ! (! isPositive)⟩ : SignedGen) = ⟨colour, isPositive⟩
    rw [boolNotInvol isPositive]

/-- `isInverseGen` is symmetric. -/
theorem isInverseGenComm (left right : SignedGen) :
    isInverseGen left right = isInverseGen right left := by
  show (Nat.beq left.colour right.colour && boolDiffer left.isPositive right.isPositive)
     = (Nat.beq right.colour left.colour && boolDiffer right.isPositive left.isPositive)
  rw [natBeqSymmEq left.colour right.colour, boolDifferComm left.isPositive right.isPositive]

/-- If two generators are inverse then the left is the flip of the right. -/
theorem isInverseGenToFlip (left right : SignedGen) (hinv : isInverseGen left right = true) :
    left = flipGen right := by
  cases left with
  | mk leftColour leftPositive =>
    cases right with
    | mk rightColour rightPositive =>
      have hcol : leftColour = rightColour :=
        natBeqImpliesEq leftColour rightColour (boolAndTrueLeft _ _ hinv)
      have hpol : leftPositive = ! rightPositive :=
        boolDifferTrueImpliesNot leftPositive rightPositive (boolAndTrueRight _ _ hinv)
      show (⟨leftColour, leftPositive⟩ : SignedGen) = ⟨rightColour, ! rightPositive⟩
      rw [hcol, hpol]

/-- `isInverseGen` is invariant under flipping both arguments. -/
theorem isInverseGenFlipBoth (left right : SignedGen) :
    isInverseGen (flipGen left) (flipGen right) = isInverseGen left right := by
  show (Nat.beq left.colour right.colour && boolDiffer (! left.isPositive) (! right.isPositive))
     = (Nat.beq left.colour right.colour && boolDiffer left.isPositive right.isPositive)
  rw [boolDifferNotBoth left.isPositive right.isPositive]

/-- A generator's flip is its inverse (left form): `isInverseGen (flipGen gen) gen = true`. -/
theorem isInverseGenFlipLeftTrue (gen : SignedGen) : isInverseGen (flipGen gen) gen = true := by
  show (Nat.beq gen.colour gen.colour && boolDiffer (! gen.isPositive) gen.isPositive) = true
  rw [natBeqSelfTrue gen.colour, boolDifferNotSelfLeft gen.isPositive]
  rfl

/-- Prepend a generator to an ALREADY-REDUCED word, cancelling against the head if it is its inverse. -/
def reduceCons (gen : SignedGen) : List SignedGen → List SignedGen
  | [] => [gen]
  | head :: tail =>
      match isInverseGen gen head with
      | true => tail
      | false => gen :: head :: tail

/-- Equation: when `gen` is the inverse of `head`, `reduceCons` cancels and drops the head. -/
theorem reduceConsConsTrue (gen head : SignedGen) (tail : List SignedGen)
    (hinv : isInverseGen gen head = true) :
    reduceCons gen (head :: tail) = tail := by
  show (match isInverseGen gen head with
        | true => tail
        | false => gen :: head :: tail) = tail
  rw [hinv]

/-- Equation: when `gen` is not the inverse of `head`, `reduceCons` prepends it. -/
theorem reduceConsConsFalse (gen head : SignedGen) (tail : List SignedGen)
    (hinv : isInverseGen gen head = false) :
    reduceCons gen (head :: tail) = gen :: head :: tail := by
  show (match isInverseGen gen head with
        | true => tail
        | false => gen :: head :: tail) = gen :: head :: tail
  rw [hinv]

/-- Append-and-reduce two words: prepend the first (right-to-left) onto the second via `reduceCons`.  Direct
recursion, definitionally the right fold `foldr reduceCons right left`. -/
def appendReduce : List SignedGen → List SignedGen → List SignedGen
  | [], right => right
  | leftHead :: leftRest, right => reduceCons leftHead (appendReduce leftRest right)

/-- The **reduced normal form** of a word: reduce it against the empty accumulator. -/
def reduceWord (word : List SignedGen) : List SignedGen := appendReduce word []

/-- Cons-only end-append: put a generator at the very end of a list (no `List.append`). -/
def snoc : List SignedGen → SignedGen → List SignedGen
  | [], gen => [gen]
  | head :: tail, gen => head :: snoc tail gen

/-- Cons-only reverse-and-flip accumulator: prepend the flip of each consumed generator onto `acc`. -/
def invertInto : List SignedGen → List SignedGen → List SignedGen
  | acc, [] => acc
  | acc, head :: tail => invertInto (flipGen head :: acc) tail

/-- The **inverse** of a word: reverse it and flip every generator (via the cons-only `invertInto`). -/
def invertWord (word : List SignedGen) : List SignedGen := invertInto [] word

/-- Smoke: a generator immediately followed by its inverse cancels to the empty word. -/
theorem reduceWordCancelsInversePair :
    reduceWord [(⟨0, true⟩ : SignedGen), ⟨0, false⟩] = [] := rfl

/-- Smoke: two distinct positive generators do not cancel — the reduced word keeps both, in order. -/
theorem reduceWordKeepsDistinct :
    reduceWord [(⟨0, true⟩ : SignedGen), ⟨1, true⟩] = [(⟨0, true⟩ : SignedGen), ⟨1, true⟩] := rfl

/-- Smoke: inverting reverses the word and flips every polarity. -/
theorem invertWordReversesFlips :
    invertWord [(⟨0, true⟩ : SignedGen), ⟨1, false⟩] = [(⟨1, true⟩ : SignedGen), ⟨0, false⟩] := rfl

/-! ## The reducedness predicate (no adjacent inverse pair) -/

/-- A word **is reduced** when no two adjacent generators are inverse.  Structural: `[]` and singletons are
reduced; `gen :: next :: rest` is reduced iff `gen` and `next` are not inverse and `next :: rest` is reduced. -/
inductive IsReduced : List SignedGen → Prop where
  /-- The empty word is reduced. -/
  | nil : IsReduced []
  /-- Every singleton word is reduced. -/
  | singleton (gen : SignedGen) : IsReduced [gen]
  /-- A cons is reduced when its head is not the inverse of the next generator and the tail is reduced. -/
  | cons (gen next : SignedGen) (rest : List SignedGen) :
      isInverseGen gen next = false → IsReduced (next :: rest) → IsReduced (gen :: next :: rest)

/-- The tail of a reduced word is reduced. -/
theorem isReducedTail (headGen : SignedGen) (tailWord : List SignedGen)
    (hreduced : IsReduced (headGen :: tailWord)) : IsReduced tailWord := by
  cases hreduced with
  | singleton _onlyGen => exact IsReduced.nil
  | cons _firstGen _secondGen restWord _hne hredTail => exact hredTail

/-! ## The cancellation kit (the confluence crux) -/

/-- `reduceCons` preserves reducedness. -/
theorem reduceConsPreservesReduced (gen : SignedGen) (word : List SignedGen)
    (hreduced : IsReduced word) : IsReduced (reduceCons gen word) := by
  cases word with
  | nil => exact IsReduced.singleton gen
  | cons head tail =>
    cases hinv : isInverseGen gen head with
    | true =>
      rw [reduceConsConsTrue gen head tail hinv]
      exact isReducedTail head tail hreduced
    | false =>
      rw [reduceConsConsFalse gen head tail hinv]
      exact IsReduced.cons gen head tail hinv hreduced

/-- `appendReduce` preserves reducedness of its accumulator. -/
theorem appendReducePreservesReduced (word target : List SignedGen)
    (hReducedTarget : IsReduced target) : IsReduced (appendReduce word target) := by
  induction word with
  | nil => exact hReducedTarget
  | cons head tail ih =>
    show IsReduced (reduceCons head (appendReduce tail target))
    exact reduceConsPreservesReduced head (appendReduce tail target) ih

/-- ★ **Cancel/uncancel** — prepending a generator then its inverse (or vice versa) onto a REDUCED word is the
identity: `reduceCons gen (reduceCons top word) = word` when `gen, top` are inverse and `word` is reduced.  The
heart of free-reduction confluence.  Case analysis on the reduced structure of `word`; the inverse relations
`isInverseGenToFlip` collapse the crossing corners. -/
theorem reduceConsCancelInverse (gen top : SignedGen) (word : List SignedGen)
    (hreduced : IsReduced word) (hinv : isInverseGen gen top = true) :
    reduceCons gen (reduceCons top word) = word := by
  cases hreduced with
  | nil =>
    exact reduceConsConsTrue gen top [] hinv
  | singleton only =>
    cases htop : isInverseGen top only with
    | true =>
      rw [reduceConsConsTrue top only [] htop]
      have hgeq : gen = only :=
        (isInverseGenToFlip gen top hinv).trans
          ((congrArg flipGen (isInverseGenToFlip top only htop)).trans (flipGenInvol only))
      rw [hgeq]
      rfl
    | false =>
      rw [reduceConsConsFalse top only [] htop]
      exact reduceConsConsTrue gen top [only] hinv
  | cons first second rest hfs _hredTail =>
    cases htop : isInverseGen top first with
    | true =>
      rw [reduceConsConsTrue top first (second :: rest) htop]
      have hgeq : gen = first :=
        (isInverseGenToFlip gen top hinv).trans
          ((congrArg flipGen (isInverseGenToFlip top first htop)).trans (flipGenInvol first))
      rw [hgeq]
      exact reduceConsConsFalse first second rest hfs
    | false =>
      rw [reduceConsConsFalse top first (second :: rest) htop]
      exact reduceConsConsTrue gen top (first :: second :: rest) hinv

/-- The reduced-accumulator **swap**: `reduceCons` commutes out of an `appendReduce` when the accumulator is
reduced.  The cancel corner routes through `reduceConsCancelInverse`; the non-cancel corner is definitional. -/
theorem appendReduceReduceConsSwap (gen : SignedGen) (word target : List SignedGen)
    (hReducedTarget : IsReduced target) :
    appendReduce (reduceCons gen word) target = reduceCons gen (appendReduce word target) := by
  cases word with
  | nil => rfl
  | cons head tail =>
    cases hinv : isInverseGen gen head with
    | false =>
      rw [reduceConsConsFalse gen head tail hinv]
      rfl
    | true =>
      rw [reduceConsConsTrue gen head tail hinv]
      exact (reduceConsCancelInverse gen head (appendReduce tail target)
              (appendReducePreservesReduced tail target hReducedTarget) hinv).symm

/-- ★ **Associativity of `appendReduce`** for a reduced right operand — the confluence / Church-Rosser
property of the cancellation rewriting.  Induction on the first word using the reduced-accumulator swap.  (The
`IsReduced target` hypothesis is essential: the unrestricted associativity is FALSE for non-reduced targets.) -/
theorem appendReduceAssoc (aWord bWord cWord : List SignedGen) (hReducedC : IsReduced cWord) :
    appendReduce (appendReduce aWord bWord) cWord
      = appendReduce aWord (appendReduce bWord cWord) := by
  induction aWord with
  | nil => rfl
  | cons head tail ih =>
    show appendReduce (reduceCons head (appendReduce tail bWord)) cWord
       = reduceCons head (appendReduce tail (appendReduce bWord cWord))
    rw [appendReduceReduceConsSwap head (appendReduce tail bWord) cWord hReducedC, ih]

/-- A reduced word is a fixed point of `reduceWord`. -/
theorem reduceWordReducedFixed (word : List SignedGen) (hreduced : IsReduced word) :
    reduceWord word = word := by
  induction hreduced with
  | nil => rfl
  | singleton only => rfl
  | cons first second rest hfs _hredTail ih =>
    show reduceCons first (reduceWord (second :: rest)) = first :: second :: rest
    rw [ih, reduceConsConsFalse first second rest hfs]

/-- ★ **Free-reduction confluence (left form)** — reducing a prefix first does not change the final reduction,
for a reduced target: `appendReduce (reduceWord word) target = appendReduce word target`.  (The `IsReduced
target` hypothesis is essential; without it the statement is false, e.g. `word = [g, flipGen g]` with a
non-reduced target.) -/
theorem appendReduceReduceLeft (word target : List SignedGen) (hReducedTarget : IsReduced target) :
    appendReduce (reduceWord word) target = appendReduce word target := by
  induction word with
  | nil => rfl
  | cons head tail ih =>
    show appendReduce (reduceCons head (reduceWord tail)) target
       = reduceCons head (appendReduce tail target)
    rw [appendReduceReduceConsSwap head (reduceWord tail) target hReducedTarget, ih]

/-! ## The `snoc` / `invertWord` algebra (cons-only end-append and reverse-flip) -/

/-- Pushing an `appendReduce` past a `snoc` moves the appended generator onto the accumulator. -/
theorem appendReduceSnoc (xs : List SignedGen) (endGen : SignedGen) (target : List SignedGen) :
    appendReduce (snoc xs endGen) target = appendReduce xs (reduceCons endGen target) := by
  induction xs with
  | nil => rfl
  | cons head tail ih =>
    show reduceCons head (appendReduce (snoc tail endGen) target)
       = reduceCons head (appendReduce tail (reduceCons endGen target))
    rw [ih]

/-- The **last-not-inverse** seam predicate: `true` when the last generator of the list is not the inverse of
`gen` (vacuously `true` for the empty list).  A full-enumeration structural fold. -/
def isLastNotInverse : List SignedGen → SignedGen → Bool
  | [], _gen => true
  | [only], gen => ! (isInverseGen only gen)
  | _first :: second :: rest, gen => isLastNotInverse (second :: rest) gen

/-- If the appended generator is not the inverse of `gen`, the `snoc`ed list has a clean end seam. -/
theorem isLastNotInverseOfSnoc (xs : List SignedGen) (endGen gen : SignedGen)
    (hne : isInverseGen endGen gen = false) :
    isLastNotInverse (snoc xs endGen) gen = true := by
  induction xs with
  | nil =>
    show (! (isInverseGen endGen gen)) = true
    rw [hne, boolNotFalse]
  | cons head tail ih =>
    cases tail with
    | nil =>
      show (! (isInverseGen endGen gen)) = true
      rw [hne, boolNotFalse]
    | cons second rest =>
      show isLastNotInverse (second :: snoc rest endGen) gen = true
      exact ih

/-- Appending a single reduced-seam generator via `appendReduce` is exactly `snoc`: `appendReduce ys [e] =
snoc ys e` when `ys` is reduced and `e` does not cancel `ys`'s last generator. -/
theorem appendReduceSingletonSnoc (ys : List SignedGen) (endGen : SignedGen)
    (hreduced : IsReduced ys) :
    isLastNotInverse ys endGen = true → appendReduce ys [endGen] = snoc ys endGen := by
  induction hreduced with
  | nil => intro _hseam; rfl
  | singleton only =>
    intro hseam
    have hseamUnfolded : (! (isInverseGen only endGen)) = true := hseam
    have hne : isInverseGen only endGen = false :=
      boolNotEqTrueImpliesFalse (isInverseGen only endGen) hseamUnfolded
    exact reduceConsConsFalse only endGen [] hne
  | cons first second rest hfs _hredTail ih =>
    intro hseam
    have htail : appendReduce (second :: rest) [endGen] = snoc (second :: rest) endGen := ih hseam
    show reduceCons first (appendReduce (second :: rest) [endGen]) = snoc (first :: second :: rest) endGen
    rw [htail]
    exact reduceConsConsFalse first second (snoc rest endGen) hfs

/-- Commuting `invertInto` past a `snoc` on its accumulator. -/
theorem invertIntoSnocComm (word : List SignedGen) :
    (acc : List SignedGen) → (endGen : SignedGen) →
    invertInto (snoc acc endGen) word = snoc (invertInto acc word) endGen := by
  induction word with
  | nil => intro acc endGen; rfl
  | cons head tail ih =>
    intro acc endGen
    show invertInto (flipGen head :: snoc acc endGen) tail
       = snoc (invertInto (flipGen head :: acc) tail) endGen
    exact ih (flipGen head :: acc) endGen

/-- `invertWord` on a cons: the flip of the head goes to the very end. -/
theorem invertWordCons (gen : SignedGen) (tail : List SignedGen) :
    invertWord (gen :: tail) = snoc (invertWord tail) (flipGen gen) := by
  show invertInto (flipGen gen :: []) tail = snoc (invertInto [] tail) (flipGen gen)
  exact invertIntoSnocComm tail [] (flipGen gen)

/-- `invertWord` on a `snoc`: the flip of the appended generator moves to the front. -/
theorem invertWordSnoc (xs : List SignedGen) (endGen : SignedGen) :
    invertWord (snoc xs endGen) = flipGen endGen :: invertWord xs := by
  induction xs with
  | nil =>
    show invertWord [endGen] = flipGen endGen :: invertWord []
    rw [invertWordCons endGen []]
    rfl
  | cons head tail ih =>
    show invertWord (head :: snoc tail endGen) = flipGen endGen :: invertWord (head :: tail)
    rw [invertWordCons head (snoc tail endGen), ih, invertWordCons head tail]
    rfl

/-- `invertWord` is involutive: `invertWord (invertWord word) = word` (for every word). -/
theorem invertWordInvolution (word : List SignedGen) : invertWord (invertWord word) = word := by
  induction word with
  | nil => rfl
  | cons gen tail ih =>
    rw [invertWordCons gen tail, invertWordSnoc (invertWord tail) (flipGen gen), flipGenInvol gen, ih]

/-- `snoc` preserves reducedness when the appended generator has a clean end seam. -/
theorem snocPreservesReduced (xs : List SignedGen) (endGen : SignedGen) (hreduced : IsReduced xs) :
    isLastNotInverse xs endGen = true → IsReduced (snoc xs endGen) := by
  induction hreduced with
  | nil => intro _hseam; exact IsReduced.singleton endGen
  | singleton only =>
    intro hseam
    have hseamUnfolded : (! (isInverseGen only endGen)) = true := hseam
    have hne : isInverseGen only endGen = false :=
      boolNotEqTrueImpliesFalse (isInverseGen only endGen) hseamUnfolded
    exact IsReduced.cons only endGen [] hne (IsReduced.singleton endGen)
  | cons first second rest hfs _hredTail ih =>
    intro hseam
    have htail : IsReduced (snoc (second :: rest) endGen) := ih hseam
    exact IsReduced.cons first second (snoc rest endGen) hfs htail

/-- `invertWord` preserves reducedness. -/
theorem invertPreservesReduced (word : List SignedGen) (hreduced : IsReduced word) :
    IsReduced (invertWord word) := by
  induction hreduced with
  | nil => exact IsReduced.nil
  | singleton only =>
    show IsReduced (invertWord [only])
    rw [invertWordCons only []]
    exact IsReduced.singleton (flipGen only)
  | cons first second rest hfs hredTail ih =>
    show IsReduced (invertWord (first :: second :: rest))
    rw [invertWordCons first (second :: rest)]
    apply snocPreservesReduced (invertWord (second :: rest)) (flipGen first) ih
    rw [invertWordCons second rest]
    apply isLastNotInverseOfSnoc (invertWord rest) (flipGen second) (flipGen first)
    rw [isInverseGenFlipBoth second first, isInverseGenComm second first]
    exact hfs

/-! ## The inverse-cancellation and reversed inverse-homomorphism word lemmas -/

/-- ★ **Left inverse cancellation**: a reduced word's inverse cancels it on the left, `appendReduce (invertWord
word) word = []`.  Induction on the reduced structure; `appendReduceSnoc` peels the trailing flip and the head
cancels via `reduceConsConsTrue`. -/
theorem appendReduceInvertLeft (word : List SignedGen) (hreduced : IsReduced word) :
    appendReduce (invertWord word) word = [] := by
  induction hreduced with
  | nil => rfl
  | singleton only =>
    rw [invertWordCons only []]
    show reduceCons (flipGen only) [only] = []
    exact reduceConsConsTrue (flipGen only) only [] (isInverseGenFlipLeftTrue only)
  | cons first second rest hfs _hredTail ih =>
    show appendReduce (invertWord (first :: second :: rest)) (first :: second :: rest) = []
    rw [invertWordCons first (second :: rest),
        appendReduceSnoc (invertWord (second :: rest)) (flipGen first) (first :: second :: rest),
        reduceConsConsTrue (flipGen first) first (second :: rest) (isInverseGenFlipLeftTrue first)]
    exact ih

/-- **Right inverse cancellation**: `appendReduce word (invertWord word) = []` for reduced `word`.  Derived from
the left form via the `invertWord` involution (applied to `invertWord word`, which is reduced). -/
theorem appendReduceInvertRight (word : List SignedGen) (hreduced : IsReduced word) :
    appendReduce word (invertWord word) = [] := by
  have hinvRed : IsReduced (invertWord word) := invertPreservesReduced word hreduced
  have key : appendReduce (invertWord (invertWord word)) (invertWord word) = [] :=
    appendReduceInvertLeft (invertWord word) hinvRed
  rw [invertWordInvolution word] at key
  exact key

/-- `invertWord` distributes over `reduceCons` as an end-append (for a reduced word): `invertWord (reduceCons
gen word) = appendReduce (invertWord word) [flipGen gen]`.  The building block of the reversed
inverse-homomorphism. -/
theorem invertReduceCons (gen : SignedGen) (word : List SignedGen) (hreduced : IsReduced word) :
    invertWord (reduceCons gen word) = appendReduce (invertWord word) [flipGen gen] := by
  cases word with
  | nil =>
    show invertWord [gen] = appendReduce [] [flipGen gen]
    rw [invertWordCons gen []]
    rfl
  | cons head tail =>
    cases hinv : isInverseGen gen head with
    | true =>
      rw [reduceConsConsTrue gen head tail hinv, invertWordCons head tail,
          appendReduceSnoc (invertWord tail) (flipGen head) [flipGen gen]]
      have hinvFlip : isInverseGen (flipGen head) (flipGen gen) = true := by
        rw [isInverseGenFlipBoth head gen, isInverseGenComm head gen]; exact hinv
      rw [reduceConsConsTrue (flipGen head) (flipGen gen) [] hinvFlip]
      have htailRed : IsReduced tail := isReducedTail head tail hreduced
      exact (reduceWordReducedFixed (invertWord tail) (invertPreservesReduced tail htailRed)).symm
    | false =>
      rw [reduceConsConsFalse gen head tail hinv, invertWordCons gen (head :: tail)]
      have hhtRed : IsReduced (invertWord (head :: tail)) := invertPreservesReduced (head :: tail) hreduced
      have hseam : isLastNotInverse (invertWord (head :: tail)) (flipGen gen) = true := by
        rw [invertWordCons head tail]
        apply isLastNotInverseOfSnoc (invertWord tail) (flipGen head) (flipGen gen)
        rw [isInverseGenFlipBoth head gen, isInverseGenComm head gen]
        exact hinv
      exact (appendReduceSingletonSnoc (invertWord (head :: tail)) (flipGen gen) hhtRed hseam).symm

/-- ★ **Reversed inverse-homomorphism at the word level**: `invertWord (appendReduce a b) = appendReduce
(invertWord b) (invertWord a)` for reduced `a, b` — the group law `(ab)⁻¹ = b⁻¹a⁻¹`.  Induction on the reduced
structure of `a`, threading `invertReduceCons`, `appendReduceAssoc` (target the reduced singleton `[flipGen
firstA]`), and `appendReduceSingletonSnoc`. -/
theorem invertAppendReduceReversed (aWord bWord : List SignedGen)
    (hReducedA : IsReduced aWord) (hReducedB : IsReduced bWord) :
    invertWord (appendReduce aWord bWord)
      = appendReduce (invertWord bWord) (invertWord aWord) := by
  induction hReducedA with
  | nil =>
    show invertWord bWord = appendReduce (invertWord bWord) []
    exact (reduceWordReducedFixed (invertWord bWord) (invertPreservesReduced bWord hReducedB)).symm
  | singleton onlyA =>
    show invertWord (reduceCons onlyA bWord) = appendReduce (invertWord bWord) (invertWord [onlyA])
    rw [invertReduceCons onlyA bWord hReducedB, invertWordCons onlyA []]
    rfl
  | cons firstA secondA restA hfsA hredA ih =>
    show invertWord (reduceCons firstA (appendReduce (secondA :: restA) bWord))
       = appendReduce (invertWord bWord) (invertWord (firstA :: secondA :: restA))
    have hXRed : IsReduced (appendReduce (secondA :: restA) bWord) :=
      appendReducePreservesReduced (secondA :: restA) bWord hReducedB
    have hseam : isLastNotInverse (invertWord (secondA :: restA)) (flipGen firstA) = true := by
      rw [invertWordCons secondA restA]
      apply isLastNotInverseOfSnoc (invertWord restA) (flipGen secondA) (flipGen firstA)
      rw [isInverseGenFlipBoth secondA firstA, isInverseGenComm secondA firstA]
      exact hfsA
    rw [invertReduceCons firstA (appendReduce (secondA :: restA) bWord) hXRed, ih,
        invertWordCons firstA (secondA :: restA),
        appendReduceAssoc (invertWord bWord) (invertWord (secondA :: restA)) [flipGen firstA]
          (IsReduced.singleton (flipGen firstA)),
        appendReduceSingletonSnoc (invertWord (secondA :: restA)) (flipGen firstA)
          (invertPreservesReduced (secondA :: restA) hredA) hseam]

/-! ## The carrier + the reduced-word fold -/

/-- ★ The **tree carrier** of the walking free group on an arbitrary alphabet: an un-indexed tree over
colour-indexed input slots plus the three group generators.  `leaf colour` is an arity-1 input slot;
`unitOp` is the nullary unit `e`; `invOp` applies the unary inverse `i`; `mulOp` grafts under the binary `m`. -/
inductive FreeGroupTree where
  /-- An arity-1 input slot tagged with a colour in `ℕ`. -/
  | leaf (colour : Nat)
  /-- The nullary generator `e` (the group unit). -/
  | unitOp
  /-- The unary generator `i` (the group inverse) applied to a subtree. -/
  | invOp : FreeGroupTree → FreeGroupTree
  /-- The binary generator `m` grafting two subtrees. -/
  | mulOp : FreeGroupTree → FreeGroupTree → FreeGroupTree

/-- The **reduced word** of a tree — its complete convertibility invariant.  `leaf` is a positive generator,
`unitOp` the empty word, `invOp` inverts, `mulOp` appends-and-reduces. -/
def wordOf : FreeGroupTree → List SignedGen
  | .leaf colour => [⟨colour, true⟩]
  | .unitOp => []
  | .invOp inner => invertWord (wordOf inner)
  | .mulOp left right => appendReduce (wordOf left) (wordOf right)

/-- Every tree's reduced word is genuinely reduced (each fold step preserves reducedness). -/
theorem wordOfIsReduced (tree : FreeGroupTree) : IsReduced (wordOf tree) := by
  induction tree with
  | leaf colour => exact IsReduced.singleton ⟨colour, true⟩
  | unitOp => exact IsReduced.nil
  | invOp inner ih => exact invertPreservesReduced (wordOf inner) ih
  | mulOp left right _ihLeft ihRight =>
    exact appendReducePreservesReduced (wordOf left) (wordOf right) ihRight

/-! ## The free-group tree convertibility (NON-abelian: NO `commSwap`, REVERSED inverse-homomorphism) -/

/-- ★ The **tree convertibility** of the walking free group on an arbitrary alphabet — the free convertibility
of the `{m, e, i}` signature over colour-tagged generators closed under the group laws (associativity,
left/right unit, left/right inverse, the REVERSED inverse-homomorphism `i(m a b) ≈ m(i b, i a)`, inverse-of-unit,
inverse-involution), the congruences `mulCongr` / `invCongr`, and `refl` / `symm` / `trans`.  There is NO
`commSwap` — the free group is non-commutative. -/
inductive FreeGroupTreeConv : FreeGroupTree → FreeGroupTree → Prop where
  /-- **Associativity** `m(m(left, middle), right) ≈ m(left, m(middle, right))`. -/
  | assoc (left middle right : FreeGroupTree) :
      FreeGroupTreeConv (FreeGroupTree.mulOp (FreeGroupTree.mulOp left middle) right)
        (FreeGroupTree.mulOp left (FreeGroupTree.mulOp middle right))
  /-- **Left unit** `m(e, subtree) ≈ subtree`. -/
  | unitLeft (subtree : FreeGroupTree) :
      FreeGroupTreeConv (FreeGroupTree.mulOp FreeGroupTree.unitOp subtree) subtree
  /-- **Right unit** `m(subtree, e) ≈ subtree`. -/
  | unitRight (subtree : FreeGroupTree) :
      FreeGroupTreeConv (FreeGroupTree.mulOp subtree FreeGroupTree.unitOp) subtree
  /-- **Left inverse** `m(i subtree, subtree) ≈ e`. -/
  | invLeft (subtree : FreeGroupTree) :
      FreeGroupTreeConv (FreeGroupTree.mulOp (FreeGroupTree.invOp subtree) subtree) FreeGroupTree.unitOp
  /-- **Right inverse** `m(subtree, i subtree) ≈ e`. -/
  | invRight (subtree : FreeGroupTree) :
      FreeGroupTreeConv (FreeGroupTree.mulOp subtree (FreeGroupTree.invOp subtree)) FreeGroupTree.unitOp
  /-- **Reversed inverse-homomorphism** `i(m(treeA, treeB)) ≈ m(i treeB, i treeA)` — the inverse of a product
  reverses the factors (the non-abelian law; there is no `commSwap` to un-reverse it). -/
  | invHomReversed (treeA treeB : FreeGroupTree) :
      FreeGroupTreeConv (FreeGroupTree.invOp (FreeGroupTree.mulOp treeA treeB))
        (FreeGroupTree.mulOp (FreeGroupTree.invOp treeB) (FreeGroupTree.invOp treeA))
  /-- **Inverse of unit** `i e ≈ e`. -/
  | invUnit :
      FreeGroupTreeConv (FreeGroupTree.invOp FreeGroupTree.unitOp) FreeGroupTree.unitOp
  /-- **Inverse involution** `i(i subtree) ≈ subtree`. -/
  | invInvol (subtree : FreeGroupTree) :
      FreeGroupTreeConv (FreeGroupTree.invOp (FreeGroupTree.invOp subtree)) subtree
  /-- **Congruence under a grafting node** — into BOTH children. -/
  | mulCongr {leftOld leftNew rightOld rightNew : FreeGroupTree} :
      FreeGroupTreeConv leftOld leftNew → FreeGroupTreeConv rightOld rightNew →
      FreeGroupTreeConv (FreeGroupTree.mulOp leftOld rightOld) (FreeGroupTree.mulOp leftNew rightNew)
  /-- **Congruence under an inverse node**. -/
  | invCongr {innerOld innerNew : FreeGroupTree} :
      FreeGroupTreeConv innerOld innerNew →
      FreeGroupTreeConv (FreeGroupTree.invOp innerOld) (FreeGroupTree.invOp innerNew)
  /-- Reflexivity. -/
  | refl (tree : FreeGroupTree) : FreeGroupTreeConv tree tree
  /-- Symmetry. -/
  | symm {tree1 tree2 : FreeGroupTree} :
      FreeGroupTreeConv tree1 tree2 → FreeGroupTreeConv tree2 tree1
  /-- Transitivity. -/
  | trans {tree1 tree2 tree3 : FreeGroupTree} :
      FreeGroupTreeConv tree1 tree2 → FreeGroupTreeConv tree2 tree3 → FreeGroupTreeConv tree1 tree3

/-! ## Soundness: convertible ⟹ equal reduced word -/

/-- ★ **Soundness** — convertible trees have equal reduced word.  Each group law maps to a word lemma:
associativity to `appendReduceAssoc`, the units to `appendReduce [] / reduceWordReducedFixed`, the inverses to
`appendReduceInvertLeft/Right`, the reversed homomorphism to `invertAppendReduceReversed`, the involution to
`invertWordInvolution`; the congruences to `congrArg`.  Every side condition is a `wordOfIsReduced`. -/
theorem freeGroupTreeConv_sound {source target : FreeGroupTree}
    (conv : FreeGroupTreeConv source target) : wordOf source = wordOf target := by
  induction conv with
  | assoc left middle right =>
    exact appendReduceAssoc (wordOf left) (wordOf middle) (wordOf right) (wordOfIsReduced right)
  | unitLeft subtree => rfl
  | unitRight subtree =>
    exact reduceWordReducedFixed (wordOf subtree) (wordOfIsReduced subtree)
  | invLeft subtree =>
    exact appendReduceInvertLeft (wordOf subtree) (wordOfIsReduced subtree)
  | invRight subtree =>
    exact appendReduceInvertRight (wordOf subtree) (wordOfIsReduced subtree)
  | invHomReversed treeA treeB =>
    exact invertAppendReduceReversed (wordOf treeA) (wordOf treeB)
      (wordOfIsReduced treeA) (wordOfIsReduced treeB)
  | invUnit => rfl
  | invInvol subtree => exact invertWordInvolution (wordOf subtree)
  | @mulCongr leftOld leftNew rightOld rightNew _premiseLeft _premiseRight ihLeft ihRight =>
    exact (congrArg (fun leftWord => appendReduce leftWord (wordOf rightOld)) ihLeft).trans
      (congrArg (appendReduce (wordOf leftNew)) ihRight)
  | @invCongr innerOld innerNew _premise ihInner => exact congrArg invertWord ihInner
  | refl tree => rfl
  | symm _premise ihConv => exact ihConv.symm
  | trans _premiseAB _premiseBC ihConvAB ihConvBC => exact ihConvAB.trans ihConvBC

/-! ## Normalization: every tree reduces to the comb of its reduced word -/

/-- The **tree of a signed generator**: a positive generator is a `leaf`, a negative one is `i(leaf)`. -/
def genTree (gen : SignedGen) : FreeGroupTree :=
  match gen.isPositive with
  | true => FreeGroupTree.leaf gen.colour
  | false => FreeGroupTree.invOp (FreeGroupTree.leaf gen.colour)

/-- Equation: a positive generator's tree is a bare `leaf`. -/
theorem genTreePositive (gen : SignedGen) (hpos : gen.isPositive = true) :
    genTree gen = FreeGroupTree.leaf gen.colour := by
  show (match gen.isPositive with
        | true => FreeGroupTree.leaf gen.colour
        | false => FreeGroupTree.invOp (FreeGroupTree.leaf gen.colour)) = FreeGroupTree.leaf gen.colour
  rw [hpos]

/-- Equation: a negative generator's tree is `i(leaf)`. -/
theorem genTreeNegative (gen : SignedGen) (hneg : gen.isPositive = false) :
    genTree gen = FreeGroupTree.invOp (FreeGroupTree.leaf gen.colour) := by
  show (match gen.isPositive with
        | true => FreeGroupTree.leaf gen.colour
        | false => FreeGroupTree.invOp (FreeGroupTree.leaf gen.colour))
      = FreeGroupTree.invOp (FreeGroupTree.leaf gen.colour)
  rw [hneg]

/-- The **right comb** of a signed word: `[] ↦ e` and `gen :: rest ↦ m(genTree gen, comb rest)`.  The canonical
tree over a signed word; on a reduced word it is the normal form. -/
def combOfWord : List SignedGen → FreeGroupTree
  | [] => FreeGroupTree.unitOp
  | gen :: rest => FreeGroupTree.mulOp (genTree gen) (combOfWord rest)

/-- A pair of inverse generators cancels to the unit: `m(genTree g, genTree h) ≈ e` when `g, h` are inverse.
Cases on `g`'s polarity route to `invRight` (positive) or `invLeft` (negative). -/
theorem genTreeInverseCancels (leftGen rightGen : SignedGen) (hinv : isInverseGen leftGen rightGen = true) :
    FreeGroupTreeConv (FreeGroupTree.mulOp (genTree leftGen) (genTree rightGen)) FreeGroupTree.unitOp := by
  have hcolEq : leftGen.colour = rightGen.colour :=
    natBeqImpliesEq leftGen.colour rightGen.colour (boolAndTrueLeft _ _ hinv)
  have hpolEq : leftGen.isPositive = ! rightGen.isPositive :=
    boolDifferTrueImpliesNot leftGen.isPositive rightGen.isPositive (boolAndTrueRight _ _ hinv)
  cases hleft : leftGen.isPositive with
  | true =>
    have hright : rightGen.isPositive = false := by
      have hnotr : (! rightGen.isPositive) = true := by rw [← hpolEq]; exact hleft
      exact boolNotEqTrueImpliesFalse rightGen.isPositive hnotr
    rw [genTreePositive leftGen hleft, genTreeNegative rightGen hright, hcolEq]
    exact FreeGroupTreeConv.invRight (FreeGroupTree.leaf rightGen.colour)
  | false =>
    have hright : rightGen.isPositive = true := by
      have hnotr : (! rightGen.isPositive) = false := by rw [← hpolEq]; exact hleft
      exact boolNotEqFalseImpliesTrue rightGen.isPositive hnotr
    rw [genTreeNegative leftGen hleft, genTreePositive rightGen hright, hcolEq]
    exact FreeGroupTreeConv.invLeft (FreeGroupTree.leaf rightGen.colour)

/-- Pushing an inverse through a generator's tree yields the flipped generator's tree: `i(genTree gen) ≈
genTree (flipGen gen)`.  Positive routes through `refl`, negative through `invInvol`. -/
theorem invGenTree (gen : SignedGen) :
    FreeGroupTreeConv (FreeGroupTree.invOp (genTree gen)) (genTree (flipGen gen)) := by
  cases hpol : gen.isPositive with
  | true =>
    have hflipNeg : (flipGen gen).isPositive = false := by
      show (! gen.isPositive) = false
      rw [hpol, boolNotTrue]
    rw [genTreePositive gen hpol, genTreeNegative (flipGen gen) hflipNeg]
    show FreeGroupTreeConv (FreeGroupTree.invOp (FreeGroupTree.leaf gen.colour))
      (FreeGroupTree.invOp (FreeGroupTree.leaf gen.colour))
    exact FreeGroupTreeConv.refl (FreeGroupTree.invOp (FreeGroupTree.leaf gen.colour))
  | false =>
    have hflipPos : (flipGen gen).isPositive = true := by
      show (! gen.isPositive) = true
      rw [hpol, boolNotFalse]
    rw [genTreeNegative gen hpol, genTreePositive (flipGen gen) hflipPos]
    show FreeGroupTreeConv (FreeGroupTree.invOp (FreeGroupTree.invOp (FreeGroupTree.leaf gen.colour)))
      (FreeGroupTree.leaf gen.colour)
    exact FreeGroupTreeConv.invInvol (FreeGroupTree.leaf gen.colour)

/-- **Grafting a generator onto a comb realizes one `reduceCons`**: `m(genTree gen, comb word) ≈ comb
(reduceCons gen word)`.  The cancel corner realizes `m(i x, x) ≈ e` via `genTreeInverseCancels`; the non-cancel
corner is definitional. -/
theorem combReduceCons (gen : SignedGen) (word : List SignedGen) :
    FreeGroupTreeConv (FreeGroupTree.mulOp (genTree gen) (combOfWord word))
      (combOfWord (reduceCons gen word)) := by
  cases word with
  | nil => exact FreeGroupTreeConv.refl (FreeGroupTree.mulOp (genTree gen) (combOfWord []))
  | cons head tail =>
    cases hinv : isInverseGen gen head with
    | true =>
      rw [reduceConsConsTrue gen head tail hinv]
      show FreeGroupTreeConv (FreeGroupTree.mulOp (genTree gen)
              (FreeGroupTree.mulOp (genTree head) (combOfWord tail))) (combOfWord tail)
      exact
        (FreeGroupTreeConv.symm
            (FreeGroupTreeConv.assoc (genTree gen) (genTree head) (combOfWord tail))).trans
          ((FreeGroupTreeConv.mulCongr (genTreeInverseCancels gen head hinv)
              (FreeGroupTreeConv.refl (combOfWord tail))).trans
            (FreeGroupTreeConv.unitLeft (combOfWord tail)))
    | false =>
      rw [reduceConsConsFalse gen head tail hinv]
      exact FreeGroupTreeConv.refl (FreeGroupTree.mulOp (genTree gen) (combOfWord (head :: tail)))

/-- **Grafting two combs appends-and-reduces them**: `m(comb x, comb y) ≈ comb (appendReduce x y)`.  Induction
on `x` re-associating the leading generator out and re-absorbing it via `combReduceCons`. -/
theorem combOfWordAppendReduce (xWord yWord : List SignedGen) :
    FreeGroupTreeConv (FreeGroupTree.mulOp (combOfWord xWord) (combOfWord yWord))
      (combOfWord (appendReduce xWord yWord)) := by
  induction xWord with
  | nil => exact FreeGroupTreeConv.unitLeft (combOfWord yWord)
  | cons head tail ih =>
    show FreeGroupTreeConv (FreeGroupTree.mulOp (FreeGroupTree.mulOp (genTree head) (combOfWord tail))
            (combOfWord yWord)) (combOfWord (appendReduce (head :: tail) yWord))
    exact (FreeGroupTreeConv.assoc (genTree head) (combOfWord tail) (combOfWord yWord)).trans
      ((FreeGroupTreeConv.mulCongr (FreeGroupTreeConv.refl (genTree head)) ih).trans
        (combReduceCons head (appendReduce tail yWord)))

/-- **Grafting a generator onto the end of a comb**: `comb (snoc xs e) ≈ m(comb xs, genTree e)`.  Induction on
`xs` re-associating the trailing generator out. -/
theorem combOfWordSnoc (xs : List SignedGen) (endGen : SignedGen) :
    FreeGroupTreeConv (combOfWord (snoc xs endGen))
      (FreeGroupTree.mulOp (combOfWord xs) (genTree endGen)) := by
  induction xs with
  | nil =>
    show FreeGroupTreeConv (FreeGroupTree.mulOp (genTree endGen) FreeGroupTree.unitOp)
      (FreeGroupTree.mulOp FreeGroupTree.unitOp (genTree endGen))
    exact (FreeGroupTreeConv.unitRight (genTree endGen)).trans
      (FreeGroupTreeConv.symm (FreeGroupTreeConv.unitLeft (genTree endGen)))
  | cons head tail ih =>
    show FreeGroupTreeConv (FreeGroupTree.mulOp (genTree head) (combOfWord (snoc tail endGen)))
      (FreeGroupTree.mulOp (FreeGroupTree.mulOp (genTree head) (combOfWord tail)) (genTree endGen))
    exact (FreeGroupTreeConv.mulCongr (FreeGroupTreeConv.refl (genTree head)) ih).trans
      (FreeGroupTreeConv.symm (FreeGroupTreeConv.assoc (genTree head) (combOfWord tail) (genTree endGen)))

/-- **Inverting a comb inverts its word**: `i(comb word) ≈ comb (invertWord word)`.  Induction on `word` via
the reversed homomorphism `invHomReversed`, `invGenTree`, and `combOfWordSnoc`. -/
theorem combOfWordInvert (word : List SignedGen) :
    FreeGroupTreeConv (FreeGroupTree.invOp (combOfWord word)) (combOfWord (invertWord word)) := by
  induction word with
  | nil => exact FreeGroupTreeConv.invUnit
  | cons gen tail ih =>
    show FreeGroupTreeConv (FreeGroupTree.invOp (FreeGroupTree.mulOp (genTree gen) (combOfWord tail)))
      (combOfWord (invertWord (gen :: tail)))
    rw [invertWordCons gen tail]
    exact (FreeGroupTreeConv.invHomReversed (genTree gen) (combOfWord tail)).trans
      ((FreeGroupTreeConv.mulCongr ih (invGenTree gen)).trans
        (FreeGroupTreeConv.symm (combOfWordSnoc (invertWord tail) (flipGen gen))))

/-- ★ **Normalization** — every tree is convertible to the comb of its own reduced word.  Induction on the
tree: `leaf`/`unitOp` reduce by a unit law, `invOp` via `combOfWordInvert`, `mulOp` via
`combOfWordAppendReduce`. -/
theorem freeGroupTreeReducesToComb (tree : FreeGroupTree) :
    FreeGroupTreeConv tree (combOfWord (wordOf tree)) := by
  induction tree with
  | leaf colour =>
    show FreeGroupTreeConv (FreeGroupTree.leaf colour)
      (FreeGroupTree.mulOp (FreeGroupTree.leaf colour) FreeGroupTree.unitOp)
    exact FreeGroupTreeConv.symm (FreeGroupTreeConv.unitRight (FreeGroupTree.leaf colour))
  | unitOp => exact FreeGroupTreeConv.refl FreeGroupTree.unitOp
  | invOp inner ih =>
    show FreeGroupTreeConv (FreeGroupTree.invOp inner) (combOfWord (invertWord (wordOf inner)))
    exact (FreeGroupTreeConv.invCongr ih).trans (combOfWordInvert (wordOf inner))
  | mulOp left right ihLeft ihRight =>
    show FreeGroupTreeConv (FreeGroupTree.mulOp left right)
      (combOfWord (appendReduce (wordOf left) (wordOf right)))
    exact (FreeGroupTreeConv.mulCongr ihLeft ihRight).trans
      (combOfWordAppendReduce (wordOf left) (wordOf right))

/-! ## Completeness and the decision -/

/-- ★ **Completeness** — equal reduced word implies convertibility.  Both trees normalize to the comb of their
(equal) reduced words, so they meet through the common normal form. -/
theorem freeGroupTreeConv_complete {source target : FreeGroupTree}
    (wordsEq : wordOf source = wordOf target) : FreeGroupTreeConv source target := by
  have sourceReduces : FreeGroupTreeConv source (combOfWord (wordOf source)) :=
    freeGroupTreeReducesToComb source
  have targetReduces : FreeGroupTreeConv target (combOfWord (wordOf target)) :=
    freeGroupTreeReducesToComb target
  have combEq : combOfWord (wordOf source) = combOfWord (wordOf target) :=
    congrArg combOfWord wordsEq
  exact FreeGroupTreeConv.trans sourceReduces
    (combEq.symm ▸ FreeGroupTreeConv.symm targetReduces)

/-- ★ **The decision** — convertibility in the walking free group on an arbitrary alphabet is exactly equality
of reduced words.  Since `List SignedGen` equality is decidable (`SignedGen` has `DecidableEq`), this
biconditional decides the word problem. -/
theorem freeGroupTreeConv_iff_reducedWord (source target : FreeGroupTree) :
    FreeGroupTreeConv source target ↔ wordOf source = wordOf target :=
  ⟨freeGroupTreeConv_sound, freeGroupTreeConv_complete⟩

/-- ★ **The decider** — a shipped `Decidable` built from the reduced-word decision: match the derived
`DecidableEq (List SignedGen)`, discharging `isTrue` by completeness and `isFalse` by soundness.  A genuine
decider (not `decidable_of_iff`), propext-free. -/
def decideFreeGroupTreeConv (source target : FreeGroupTree) :
    Decidable (FreeGroupTreeConv source target) :=
  match (inferInstance : Decidable (wordOf source = wordOf target)) with
  | isTrue wordsEq => isTrue (freeGroupTreeConv_complete wordsEq)
  | isFalse wordsNe => isFalse (fun conv => wordsNe (freeGroupTreeConv_sound conv))

/-- The convertibility as a `Decidable` INSTANCE, so `decide` and instance resolution fire on it.  A
definitional alias of the shipped decider, hence propext-free. -/
instance instDecidableFreeGroupTreeConv (source target : FreeGroupTree) :
    Decidable (FreeGroupTreeConv source target) :=
  decideFreeGroupTreeConv source target

/-! ## Groundings -/

/-- ★ **The decision in action (positive, free cancellation)** — `m(m(leaf 0, i leaf 0), leaf 1)` is
convertible to `leaf 1`: the cancelling `m(leaf 0, i leaf 0)` folds away, both winding to the word
`[(1,+)]`, so they meet through completeness with no explicit rewrite path. -/
theorem freeGroupCancellationHolds :
    FreeGroupTreeConv
      (FreeGroupTree.mulOp
        (FreeGroupTree.mulOp (FreeGroupTree.leaf 0) (FreeGroupTree.invOp (FreeGroupTree.leaf 0)))
        (FreeGroupTree.leaf 1))
      (FreeGroupTree.leaf 1) :=
  freeGroupTreeConv_complete rfl

/-- ★ **The headline: the free group SEES order (non-commutativity)** — `m(leaf 0, leaf 1)` is NOT convertible
to `m(leaf 1, leaf 0)`: their reduced words `[(0,+),(1,+)]` and `[(1,+),(0,+)]` differ, so by soundness no
convertibility can exist.  This is the sharp contrast with the abelian ℤᵏ walker, which reorders freely. -/
theorem freeGroupNonCommutative :
    ¬ FreeGroupTreeConv (FreeGroupTree.mulOp (FreeGroupTree.leaf 0) (FreeGroupTree.leaf 1))
        (FreeGroupTree.mulOp (FreeGroupTree.leaf 1) (FreeGroupTree.leaf 0)) := by
  intro conv
  have wordsEq : ([(⟨0, true⟩ : SignedGen), ⟨1, true⟩]) = [(⟨1, true⟩ : SignedGen), ⟨0, true⟩] :=
    freeGroupTreeConv_sound conv
  injection wordsEq with headEq _tailEq
  injection headEq with colourEq _positiveEq
  exact Nat.noConfusion colourEq

/-- ★ **The reversed inverse-homomorphism, directly** — `i(m(leaf 0, leaf 1)) ≈ m(i leaf 1, i leaf 0)`: the
inverse of a product reverses the factors (the constructor `invHomReversed`), the non-abelian law that has no
`commSwap` to un-reverse it. -/
theorem freeGroupInverseHomReversedHolds :
    FreeGroupTreeConv
      (FreeGroupTree.invOp (FreeGroupTree.mulOp (FreeGroupTree.leaf 0) (FreeGroupTree.leaf 1)))
      (FreeGroupTree.mulOp (FreeGroupTree.invOp (FreeGroupTree.leaf 1))
        (FreeGroupTree.invOp (FreeGroupTree.leaf 0))) :=
  FreeGroupTreeConv.invHomReversed (FreeGroupTree.leaf 0) (FreeGroupTree.leaf 1)

/-- ★ **The decision in action (negative)** — a slot of colour `0` is NOT convertible to the unit: their
reduced words `[(0,+)]` and `[]` differ, so by soundness no convertibility can exist. -/
theorem freeGroupRejectsUnit :
    ¬ FreeGroupTreeConv (FreeGroupTree.leaf 0) FreeGroupTree.unitOp := by
  intro conv
  have wordsEq : ([(⟨0, true⟩ : SignedGen)]) = [] := freeGroupTreeConv_sound conv
  cases wordsEq

/-! ## The marker -/

/-- ★ **The walking free (NON-abelian) group on an ARBITRARY alphabet is DECIDED** — the reduced-word decision.
`= true` records that `freeGroupTreeConv_iff_reducedWord` reduces the alphabet-parameterised word problem to
plain equality of reduced `List SignedGen`s: adjoining formal inverses to the free monoid on the colour set and
cancelling adjacent inverse pairs, the free group on `ℕ` has each element a UNIQUE reduced word.  Soundness
(every law preserves the reduced word, the crux being free-reduction confluence = `appendReduceAssoc`),
normalization to the reduced comb, and completeness are all shipped, plus a genuine `Decidable`.  The reducer is
order-SENSITIVE (`freeGroupNonCommutative`), the sharp contrast with the free-abelian ℤᵏ walker.  All zero-axiom:
`Nat.beq` for colour equality (no `Nat.le`/`Nat.ble` lemma), no `Int`, no `Nat.sub`, no `List.append` (`++`). -/
def fxWalkingFreeGroup_hasReducedWordDecision : Bool := true

end FX1Poly.Polygraph
