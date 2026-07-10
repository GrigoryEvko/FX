/-! # FX1Poly/Polygraph/Homology/FreeGroupReducedWord — the free-group reduced-word normal form
    (signed alphabet, right-fold free cancellation, structural reducedness, Bool equality), the
    footing for the crossed-module `pi_2` layer (WP-2GROUP r1, #2199)

The crossed-module footing needs a genuine FREE GROUP, not the positive monoid words the Rewriting
lane ships.  A free-group element is a word over a SIGNED alphabet (`pos g` = the generator, `neg g`
= its inverse) taken up to free reduction: every adjacent inverse pair `g g^-1` / `g^-1 g` cancels.
This module ships the reduced-word normal form and the group operations that ride it.

## The normal form (the propext-armed core)

`reduceWord` is a RIGHT FOLD: `reduceWord (letter :: rest) = consReduced letter (reduceWord rest)`,
where `consReduced` prepends one letter to an already-reduced word, cancelling against the head when
it is the inverse.  The cancellation dispatch is a single FULLY-ENUMERATED `Bool` match through the
guard helper `consReducedGuarded` (never a wildcard `_ =>`, never a `dite`), and generator equality is
`Nat.beq` (kernel-reducible, discharged by `rfl` at literal generators — never the propext-leaking
`Nat.beq_self`).

`reduceWord` is proved to PRODUCE a reduced word (`reduceWordProducesReduced`), to FIX reduced words
(`reduceWordFixesReduced`), and hence to be IDEMPOTENT (`reduceWordIsIdempotent`).  Reducedness is the
structural single-cons predicate `isReducedWord` (via `isReducedFrom`, carrying the previous letter),
so its unfolds are definitional and every lemma closes with `congrArg`/`Eq.trans`/`Bool.noConfusion`.

## r1 scope (honest)

Shipped: the alphabet, the NF, reducedness + its three theorems, the group operations
(`mulWord`/`invWord`/`oneWord`), `Bool` equality, and the concrete evaluation probes.  DEFERRED to a
later round (the genuine cancellation-confluence diamond, NOT needed by the crossed-module witness,
which is a single-word `reduceWord` computation): free-group ASSOCIATIVITY
`mulWord (mulWord a b) c = mulWord a (mulWord b c)` and the inverse laws `mulWord a (invWord a) = []`.

## Zero-axiom design decisions

  * Every match is on the NON-INDEXED inductives `SignedLetter` / `Bool` / `List` — no indexed-match,
    no mutual-index trap.  The cancellation guard is a full-enum `Bool` match; the previous-letter
    reducedness fold recurses on a single cons (definitional unfold).
  * All equality reasoning is `congrArg` / `Eq.trans` / `Bool.noConfusion` over the guard helpers —
    no `simp`, no `decide` on a driver expression, no `dite`.

`Init`-only, structural, zero axioms.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/Polygraph/Homology/FreeGroupReducedWord.lean`. -/

namespace FX1Poly.Polygraph.Homology

/-! ## The signed alphabet -/

/-- A signed letter of the free group: `pos g` is the generator `g`, `neg g` is its inverse.  A
non-indexed two-constructor inductive — clean `Bool` equality, no indexed-match trap. -/
inductive SignedLetter where
  /-- The generator `g` itself. -/
  | pos (generator : Nat)
  /-- The inverse of the generator `g`. -/
  | neg (generator : Nat)

/-- The formal inverse of a single letter — flips the sign, keeps the generator. -/
def inverseLetter : SignedLetter → SignedLetter
  | .pos generator => .neg generator
  | .neg generator => .pos generator

/-- Whether two letters are mutual inverses (`pos g` against `neg g`, or `neg g` against `pos g`).
FULL ENUM over the four sign combinations — same signs never cancel, opposite signs cancel exactly
when the generators agree (`Nat.beq`). -/
def areInverse : SignedLetter → SignedLetter → Bool
  | .pos leftGen, .neg rightGen => Nat.beq leftGen rightGen
  | .neg leftGen, .pos rightGen => Nat.beq leftGen rightGen
  | .pos _, .pos _ => false
  | .neg _, .neg _ => false

/-! ## The reduced-word normal form -/

/-- The guarded prepend: when `shouldCancel` is `true` the incoming letter annihilates the head, so
the tail is returned; otherwise the letter is prepended.  A full-enum `Bool` match — the propext-clean
replacement for a `Bool`-conditioned `if`. -/
def consReducedGuarded (shouldCancel : Bool) (letter topLetter : SignedLetter)
    (restWord : List SignedLetter) : List SignedLetter :=
  match shouldCancel with
  | true => restWord
  | false => letter :: topLetter :: restWord

/-- Prepend one letter to an already-reduced word, cancelling against the head when they are mutual
inverses.  On `[]` the singleton `[letter]`; on `topLetter :: restWord` the guarded prepend keyed by
`areInverse letter topLetter`. -/
def consReduced (letter : SignedLetter) : List SignedLetter → List SignedLetter
  | [] => [letter]
  | topLetter :: restWord => consReducedGuarded (areInverse letter topLetter) letter topLetter restWord

/-- **The free reduction.**  A right fold: reduce the tail, then prepend the head through
`consReduced`.  Structural on the input word. -/
def reduceWord : List SignedLetter → List SignedLetter
  | [] => []
  | letter :: restWord => consReduced letter (reduceWord restWord)

/-! ### Reduced-word rewrite lemmas (the guard helpers made explicit) -/

/-- When the head cancels, `consReduced` drops both letters. -/
theorem consReducedCancel (letter topLetter : SignedLetter) (restWord : List SignedLetter)
    (cancels : areInverse letter topLetter = true) :
    consReduced letter (topLetter :: restWord) = restWord :=
  congrArg (fun flag => consReducedGuarded flag letter topLetter restWord) cancels

/-- When the head does not cancel, `consReduced` prepends the letter. -/
theorem consReducedExtend (letter topLetter : SignedLetter) (restWord : List SignedLetter)
    (doesNotCancel : areInverse letter topLetter = false) :
    consReduced letter (topLetter :: restWord) = letter :: topLetter :: restWord :=
  congrArg (fun flag => consReducedGuarded flag letter topLetter restWord) doesNotCancel

/-! ## Structural reducedness -/

/-- The reject-or-continue step: reject (`false`) when the boundary pair cancels, otherwise carry the
tail's verdict.  A full-enum `Bool` match, so its two collapses are definitional. -/
def isReducedStep (shouldReject tailVerdict : Bool) : Bool :=
  match shouldReject with
  | true => false
  | false => tailVerdict

/-- Reducedness scanning FROM a known previous letter: the empty tail is reduced, and a `next :: rest`
tail is reduced when `prev next` does not cancel and `rest` continues reduced (from `next`).  Single-cons
structural recursion — every unfold is definitional. -/
def isReducedFrom (prev : SignedLetter) : List SignedLetter → Bool
  | [] => true
  | next :: rest => isReducedStep (areInverse prev next) (isReducedFrom next rest)

/-- **A word is reduced** when it has no cancelling adjacent pair — the empty and singleton words
trivially, a `first :: rest` word when `rest` is reduced-from `first`. -/
def isReducedWord : List SignedLetter → Bool
  | [] => true
  | first :: rest => isReducedFrom first rest

/-! ### The reducedness plumbing (propext-clean Bool case analysis) -/

/-- `isReducedStep b t = true` forces the carried tail verdict `t = true`: if `b = true` the step is
`false ≠ true` (vacuous), if `b = false` the step IS `t`. -/
theorem isReducedStepImpliesTail : ∀ (shouldReject tailVerdict : Bool),
    isReducedStep shouldReject tailVerdict = true → tailVerdict = true
  | true, _, stepHolds => Bool.noConfusion stepHolds
  | false, _, stepHolds => stepHolds

/-- `isReducedStep b t = true` forces the reject flag `b = false` (a `true` flag would reject). -/
theorem isReducedStepImpliesFirstFalse : ∀ (shouldReject tailVerdict : Bool),
    isReducedStep shouldReject tailVerdict = true → shouldReject = false
  | false, _, _ => rfl
  | true, _, stepHolds => Bool.noConfusion stepHolds

/-- The tail of a reduced word is reduced. -/
theorem isReducedWordTail : ∀ (first : SignedLetter) (rest : List SignedLetter),
    isReducedWord (first :: rest) = true → isReducedWord rest = true
  | _, [], _ => rfl
  | first, second :: more, whole =>
      isReducedStepImpliesTail (areInverse first second) (isReducedFrom second more) whole

/-- The two leading letters of a reduced word do not cancel. -/
theorem isReducedWordHeadNotCancel (first second : SignedLetter) (rest : List SignedLetter)
    (whole : isReducedWord (first :: second :: rest) = true) : areInverse first second = false :=
  isReducedStepImpliesFirstFalse (areInverse first second) (isReducedFrom second rest) whole

/-- Prepending a non-cancelling letter to a reduced word keeps it reduced. -/
theorem isReducedWordExtendFront (letter top : SignedLetter) (rest : List SignedLetter)
    (doesNotCancel : areInverse letter top = false)
    (tailReduced : isReducedWord (top :: rest) = true) :
    isReducedWord (letter :: top :: rest) = true :=
  (congrArg (fun flag => isReducedStep flag (isReducedFrom top rest)) doesNotCancel).trans tailReduced

/-- **`consReduced` preserves reducedness.**  On `[]` the singleton is reduced; on `top :: rest` the
cancel case drops to the (reduced) tail-of-tail, the extend case prepends a non-cancelling letter. -/
theorem isReducedConsReduced : ∀ (letter : SignedLetter) (word : List SignedLetter),
    isReducedWord word = true → isReducedWord (consReduced letter word) = true
  | _, [], _ => rfl
  | letter, top :: rest, wordReduced =>
      match hCancel : areInverse letter top with
      | true =>
          (congrArg isReducedWord (consReducedCancel letter top rest hCancel)).trans
            (isReducedWordTail top rest wordReduced)
      | false =>
          (congrArg isReducedWord (consReducedExtend letter top rest hCancel)).trans
            (isReducedWordExtendFront letter top rest hCancel wordReduced)

/-! ### The three normal-form theorems -/

/-- ★ **`reduceWord` produces a reduced word** — the normal-form soundness, by structural induction
folding `isReducedConsReduced` over the input. -/
theorem reduceWordProducesReduced : ∀ word : List SignedLetter,
    isReducedWord (reduceWord word) = true
  | [] => rfl
  | letter :: rest =>
      isReducedConsReduced letter (reduceWord rest) (reduceWordProducesReduced rest)

/-- ★ **`reduceWord` fixes already-reduced words** — the normal-form completeness half.  On
`first :: second :: rest` the reduced tail is fixed by induction and the non-cancelling head extends. -/
theorem reduceWordFixesReduced : ∀ word : List SignedLetter,
    isReducedWord word = true → reduceWord word = word
  | [], _ => rfl
  | [_], _ => rfl
  | first :: second :: rest, whole =>
      (congrArg (consReduced first)
        (reduceWordFixesReduced (second :: rest)
          (isReducedWordTail first (second :: rest) whole))).trans
        (consReducedExtend first second rest (isReducedWordHeadNotCancel first second rest whole))

/-- ★ **`reduceWord` is idempotent** — reducing an already-reduced word is a no-op, so a second pass
never changes anything. -/
theorem reduceWordIsIdempotent (word : List SignedLetter) :
    reduceWord (reduceWord word) = reduceWord word :=
  reduceWordFixesReduced (reduceWord word) (reduceWordProducesReduced word)

/-! ## The free-group operations -/

/-- The identity word — the empty reduced word. -/
def oneWord : List SignedLetter := []

/-- The free-group product: concatenate and reduce. -/
def mulWord (leftWord rightWord : List SignedLetter) : List SignedLetter :=
  reduceWord (leftWord ++ rightWord)

/-- The free-group inverse: reverse the word and invert each letter. -/
def invWord (word : List SignedLetter) : List SignedLetter :=
  List.reverse (word.map inverseLetter)

/-! ## Bool equality on words (avoiding a Prop `DecidableEq`) -/

/-- Structural `Bool` equality on letters — same sign and equal generator (`Nat.beq`), otherwise
`false`.  Full enum over the four sign combinations. -/
def signedLetterBeq : SignedLetter → SignedLetter → Bool
  | .pos leftGen, .pos rightGen => Nat.beq leftGen rightGen
  | .neg leftGen, .neg rightGen => Nat.beq leftGen rightGen
  | .pos _, .neg _ => false
  | .neg _, .pos _ => false

/-- Structural `Bool` equality on words — cons-by-cons through `signedLetterBeq`, full enum over the
four shape combinations. -/
def wordBeq : List SignedLetter → List SignedLetter → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | leftLetter :: leftRest, rightLetter :: rightRest =>
      match signedLetterBeq leftLetter rightLetter with
      | true => wordBeq leftRest rightRest
      | false => false

/-! ## Concrete evaluation truth probes (reduce wild words by eval FIRST) -/

/-- Probe — the empty word is already reduced: `reduceWord [] = []`. -/
theorem reduceWordEmptyIsEmpty : reduceWord ([] : List SignedLetter) = [] := rfl

/-- Probe — an adjacent inverse pair cancels: `s s^-1 -> 1`. -/
theorem reduceWordCancelsAdjacentInverse :
    reduceWord [SignedLetter.pos 0, SignedLetter.neg 0] = [] := rfl

/-- ★ Probe — `r r^-1 r -> r`: the middle cancellation leaves the outer letter. -/
theorem reduceWordCancelsInverseTriple :
    reduceWord [SignedLetter.pos 0, SignedLetter.neg 0, SignedLetter.pos 0]
      = [SignedLetter.pos 0] := rfl

/-- ★ Probe — a NESTED cancellation: `s t t^-1 s^-1 -> 1` collapses inside-out to the empty word. -/
theorem reduceWordCancelsNested :
    reduceWord [SignedLetter.pos 0, SignedLetter.pos 1, SignedLetter.neg 1, SignedLetter.neg 0]
      = [] := rfl

/-- Probe — the group product cancels inverses: `mulWord s s^-1 = 1`. -/
theorem mulWordCancelsInverse :
    mulWord [SignedLetter.pos 0] [SignedLetter.neg 0] = [] := rfl

/-- Probe — the inverse reverses and flips: `(s t)^-1 = t^-1 s^-1`. -/
theorem invWordReversesAndFlips :
    invWord [SignedLetter.pos 0, SignedLetter.pos 1]
      = [SignedLetter.neg 1, SignedLetter.neg 0] := rfl

/-- Probe — `Bool` equality agrees on a repeated word and rejects a sign flip. -/
theorem wordBeqReflexiveOnLiteral :
    wordBeq [SignedLetter.pos 0, SignedLetter.pos 0] [SignedLetter.pos 0, SignedLetter.pos 0]
      = true := rfl

/-- Probe — `Bool` equality rejects a sign flip: `pos 0 ≠ neg 0`. -/
theorem wordBeqRejectsSignFlip :
    wordBeq [SignedLetter.pos 0] [SignedLetter.neg 0] = false := rfl

/-- ★ **The reduced-word kit marker.**  Shipped zero-axiom: the signed alphabet, the right-fold free
reduction `reduceWord` (produces-reduced, fixes-reduced, idempotent), the group operations
`mulWord`/`invWord`/`oneWord`, `Bool` word equality, and the concrete cancellation probes.  DEFERRED
(named): free-group associativity and the inverse laws (the cancellation-confluence diamond, not needed
by the crossed-module witness).  Read the meaning from THIS docstring. -/
def freeGroupReducedWordKitIsComplete : Bool := true

end FX1Poly.Polygraph.Homology
