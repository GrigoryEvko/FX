import LeanFX2.Surface.Lex

/-! # Surface/Lex/ByteConservation — L07.4 + L07.5 byte-conservation
invariants for the lexer chain.

Split from `Surface/Lex.lean` (REFACTOR-LEX #1549) — keeps the
Lex impl module under the 1000-line ceiling.

This module ships the unified byte-conservation chain:

* **L07.4** (#1205): trivia skippers (`skipUntilNewline`,
  `skipBlockComment`, `skipTrivia`) conserve bytes.

* **L07.5** (#1545–#1548): lexeme readers + dispatcher conserve
  bytes:
  - `readIdentLexeme` / `readIntLexeme` / `readStringLexeme`
  - `lexOpOrPunct` / `lexOne`

The downstream `lexLoop_error_offset_bounded` (#1536) composes
this byte-conservation chain with `lexOne_error_offset_eq` (in
`Surface/Lex/ErrorOffset.lean`) to prove every `LexError`
produced by `Lex.run chars` has offset bounded by source byte
length.

All declarations zero-axiom under `#print axioms`. -/

namespace LeanFX2.Surface

/-! ## L07.4 — Byte-conservation invariants for trivia skippers

The `lexLoop` arithmetic invariant requires that `skipTrivia`
(and its helpers `skipUntilNewline` / `skipBlockComment`) conserve
bytes: the bytes counted as "skipped" plus the bytes remaining in
the output equal the bytes that came in (plus initial accumulator).

These are the foundation lemmas for the `Lex.run_error_offset_bounded`
runtime theorem. -/

/-- **L07.4a**: `skipUntilNewline` conserves bytes.

For `(skipBytes, restAfter) = skipUntilNewline chars n`, we have
`skipBytes + charsByteLength restAfter = n + charsByteLength chars`.

Proof: induction on `chars`.  Both branches of `if c == '\n'` use
`c.utf8Size` for byte accounting (uniform), so the proof needs
only structural recursion + `Nat.add_assoc`.  No `omega`, no
`decide`, no `of_decide_eq_true` — all propext-clean.

Zero-axiom under `#assert_no_axioms`. -/
theorem Lex.skipUntilNewline_byteLength_invariant :
    ∀ (chars : List Char) (n : Nat),
      let result := skipUntilNewline chars n
      result.fst + charsByteLength result.snd = n + charsByteLength chars
  | [], n => by
    show n + charsByteLength [] = n + charsByteLength []
    rfl
  | firstChar :: restChars, n => by
    show (skipUntilNewline (firstChar :: restChars) n).fst
        + charsByteLength (skipUntilNewline (firstChar :: restChars) n).snd
      = n + charsByteLength (firstChar :: restChars)
    by_cases hNewline : firstChar == '\n'
    · -- Newline branch: function returns (n + firstChar.utf8Size, restChars).
      have stepReduces :
          skipUntilNewline (firstChar :: restChars) n
            = (n + firstChar.utf8Size, restChars) := by
        show (if firstChar == '\n' then (n + firstChar.utf8Size, restChars)
              else skipUntilNewline restChars (n + firstChar.utf8Size))
            = (n + firstChar.utf8Size, restChars)
        rw [if_pos hNewline]
      rw [stepReduces]
      show (n + firstChar.utf8Size) + charsByteLength restChars
        = n + (firstChar.utf8Size + charsByteLength restChars)
      exact Nat.add_assoc n firstChar.utf8Size (charsByteLength restChars)
    · -- Non-newline branch: tail-recurses with n + firstChar.utf8Size.
      have stepReduces :
          skipUntilNewline (firstChar :: restChars) n
            = skipUntilNewline restChars (n + firstChar.utf8Size) := by
        show (if firstChar == '\n' then (n + firstChar.utf8Size, restChars)
              else skipUntilNewline restChars (n + firstChar.utf8Size))
            = skipUntilNewline restChars (n + firstChar.utf8Size)
        rw [if_neg hNewline]
      rw [stepReduces]
      have ihRecursive :
          (skipUntilNewline restChars (n + firstChar.utf8Size)).fst
          + charsByteLength (skipUntilNewline restChars
              (n + firstChar.utf8Size)).snd
            = (n + firstChar.utf8Size) + charsByteLength restChars :=
        Lex.skipUntilNewline_byteLength_invariant
          restChars (n + firstChar.utf8Size)
      rw [ihRecursive]
      show n + firstChar.utf8Size + charsByteLength restChars
        = n + (firstChar.utf8Size + charsByteLength restChars)
      exact Nat.add_assoc n firstChar.utf8Size (charsByteLength restChars)

/-- **L07.4b**: `skipBlockComment` conserves bytes.

For `(skipBytes, restAfter) = skipBlockComment chars n`, we have
`skipBytes + charsByteLength restAfter = n + charsByteLength chars`.

Proof: induction on the 3-pattern flat enumeration of `chars`:
* `[]`: returns `(n, [])` — `rfl`.
* `[c]`: returns `(n + c.utf8Size, [])` — arithmetic via `Nat.add_zero`
  + `Nat.add_assoc`.
* `c :: next :: rest2`: split on `c == '*'` and `next == '/'`:
  - star + slash: closing reached, uniform accounting closes via
    `Nat.add_assoc`.
  - star + non-slash: tail-recurse with `next :: rest2` and
    `n + c.utf8Size`; IH + `Nat.add_assoc` closes.
  - non-star: tail-recurse with `next :: rest2`; IH + `Nat.add_assoc`
    closes.

Zero-axiom — uniform accounting + structural recursion + `Nat.add_assoc`. -/
theorem Lex.skipBlockComment_byteLength_invariant :
    ∀ (chars : List Char) (n : Nat),
      let result := skipBlockComment chars n
      result.fst + charsByteLength result.snd = n + charsByteLength chars
  | [], n => by
    show n + charsByteLength [] = n + charsByteLength []
    rfl
  | firstChar :: [], n => by
    show (n + firstChar.utf8Size) + charsByteLength ([] : List Char)
      = n + charsByteLength (firstChar :: [])
    show (n + firstChar.utf8Size) + 0
      = n + (firstChar.utf8Size + 0)
    rw [Nat.add_zero, Nat.add_zero]
  | firstChar :: nextChar :: rest2, n => by
    by_cases hStar : firstChar == '*'
    · -- firstChar == '*'.  Split on nextChar == '/'.
      by_cases hSlash : nextChar == '/'
      · -- closing */ found.  Returns
        -- (n + firstChar.utf8Size + nextChar.utf8Size, rest2).
        have stepReduces :
            skipBlockComment (firstChar :: nextChar :: rest2) n
              = (n + firstChar.utf8Size + nextChar.utf8Size, rest2) := by
          show (if firstChar == '*' then
                  if nextChar == '/'
                  then (n + firstChar.utf8Size + nextChar.utf8Size, rest2)
                  else skipBlockComment (nextChar :: rest2)
                    (n + firstChar.utf8Size)
                else skipBlockComment (nextChar :: rest2)
                  (n + firstChar.utf8Size))
              = (n + firstChar.utf8Size + nextChar.utf8Size, rest2)
          rw [if_pos hStar, if_pos hSlash]
        rw [stepReduces]
        show n + firstChar.utf8Size + nextChar.utf8Size
            + charsByteLength rest2
          = n + (firstChar.utf8Size
              + (nextChar.utf8Size + charsByteLength rest2))
        rw [Nat.add_assoc (n + firstChar.utf8Size) nextChar.utf8Size
              (charsByteLength rest2),
          Nat.add_assoc n firstChar.utf8Size
            (nextChar.utf8Size + charsByteLength rest2)]
      · -- not closing.  tail-recurse with (n + firstChar.utf8Size).
        have stepReduces :
            skipBlockComment (firstChar :: nextChar :: rest2) n
              = skipBlockComment (nextChar :: rest2)
                  (n + firstChar.utf8Size) := by
          show (if firstChar == '*' then
                  if nextChar == '/'
                  then (n + firstChar.utf8Size + nextChar.utf8Size, rest2)
                  else skipBlockComment (nextChar :: rest2)
                    (n + firstChar.utf8Size)
                else skipBlockComment (nextChar :: rest2)
                  (n + firstChar.utf8Size))
              = skipBlockComment (nextChar :: rest2)
                  (n + firstChar.utf8Size)
          rw [if_pos hStar, if_neg hSlash]
        rw [stepReduces]
        show (skipBlockComment (nextChar :: rest2)
              (n + firstChar.utf8Size)).fst
            + charsByteLength (skipBlockComment (nextChar :: rest2)
                (n + firstChar.utf8Size)).snd
          = n + charsByteLength (firstChar :: nextChar :: rest2)
        have ihRecursive :
            (skipBlockComment (nextChar :: rest2)
                (n + firstChar.utf8Size)).fst
            + charsByteLength (skipBlockComment (nextChar :: rest2)
                (n + firstChar.utf8Size)).snd
              = (n + firstChar.utf8Size)
                + charsByteLength (nextChar :: rest2) :=
          Lex.skipBlockComment_byteLength_invariant
            (nextChar :: rest2) (n + firstChar.utf8Size)
        rw [ihRecursive]
        show (n + firstChar.utf8Size)
            + (nextChar.utf8Size + charsByteLength rest2)
          = n + (firstChar.utf8Size
              + (nextChar.utf8Size + charsByteLength rest2))
        exact Nat.add_assoc n firstChar.utf8Size
          (nextChar.utf8Size + charsByteLength rest2)
    · -- firstChar != '*'.  Tail-recurse with (n + firstChar.utf8Size).
      have stepReduces :
          skipBlockComment (firstChar :: nextChar :: rest2) n
            = skipBlockComment (nextChar :: rest2)
                (n + firstChar.utf8Size) := by
        show (if firstChar == '*' then
                if nextChar == '/'
                then (n + firstChar.utf8Size + nextChar.utf8Size, rest2)
                else skipBlockComment (nextChar :: rest2)
                  (n + firstChar.utf8Size)
              else skipBlockComment (nextChar :: rest2)
                (n + firstChar.utf8Size))
            = skipBlockComment (nextChar :: rest2)
                (n + firstChar.utf8Size)
        rw [if_neg hStar]
      rw [stepReduces]
      show (skipBlockComment (nextChar :: rest2)
            (n + firstChar.utf8Size)).fst
          + charsByteLength (skipBlockComment (nextChar :: rest2)
              (n + firstChar.utf8Size)).snd
        = n + charsByteLength (firstChar :: nextChar :: rest2)
      have ihRecursive :
          (skipBlockComment (nextChar :: rest2)
              (n + firstChar.utf8Size)).fst
          + charsByteLength (skipBlockComment (nextChar :: rest2)
              (n + firstChar.utf8Size)).snd
            = (n + firstChar.utf8Size)
              + charsByteLength (nextChar :: rest2) :=
        Lex.skipBlockComment_byteLength_invariant
          (nextChar :: rest2) (n + firstChar.utf8Size)
      rw [ihRecursive]
      show (n + firstChar.utf8Size)
          + (nextChar.utf8Size + charsByteLength rest2)
        = n + (firstChar.utf8Size
            + (nextChar.utf8Size + charsByteLength rest2))
      exact Nat.add_assoc n firstChar.utf8Size
        (nextChar.utf8Size + charsByteLength rest2)

/-- **L07.4c**: `skipTrivia` conserves bytes.

For `(skipBytes, restAfter) = skipTrivia fuel chars`, we have
`skipBytes + charsByteLength restAfter = charsByteLength chars`.

Note: `skipTrivia` does not take an accumulator — the byte counter
starts at 0 (skipBytes is the total bytes skipped from this call's
start).  This differs from `skipUntilNewline` / `skipBlockComment`
which carry an `n` accumulator.

Proof: induction on the 4-pattern flat enumeration:
* `(0, chars)`: returns `(0, chars)` — `Nat.zero_add`.
* `(_+1, [])`: returns `(0, [])` — `rfl` after both arithmetic.
* `(_+1, [c])`: split on `isWhitespaceChar c`:
  - true: returns `(c.utf8Size, [])` — arithmetic.
  - false: returns `(0, [c])` — `Nat.zero_add`.
* `(_+1, c :: next :: rest2)`: split on:
  - `isWhitespaceChar c`: tail-recurse on `(next :: rest2)`, IH +
    `Nat.add_assoc` closes.
  - `c == '/'` and `next == '/'`: line comment — combine
    `skipUntilNewline_byteLength_invariant` + IH + arithmetic.
  - `c == '/'` and `next == '*'`: block comment — combine
    `skipBlockComment_byteLength_invariant` + IH + arithmetic.
  - else: returns `(0, c :: next :: rest2)` — `Nat.zero_add`.

Zero-axiom — relies only on the two helper invariants and
`Nat.add_assoc` / `Nat.zero_add`. -/
theorem Lex.skipTrivia_byteLength_invariant :
    ∀ (fuel : Nat) (chars : List Char),
      let result := skipTrivia fuel chars
      result.fst + charsByteLength result.snd = charsByteLength chars
  | 0,        chars => by
    show 0 + charsByteLength chars = charsByteLength chars
    exact Nat.zero_add _
  | _ + 1,    [] => by
    show 0 + charsByteLength ([] : List Char) = charsByteLength ([] : List Char)
    exact Nat.zero_add _
  | fuel + 1, c :: [] => by
    by_cases hWhite : isWhitespaceChar c
    · -- whitespace single char.  Returns (c.utf8Size, []).
      have stepReduces :
          skipTrivia (fuel + 1) (c :: [])
            = (c.utf8Size, ([] : List Char)) := by
        show (if isWhitespaceChar c then (c.utf8Size, ([] : List Char))
              else (0, [c]))
            = (c.utf8Size, ([] : List Char))
        rw [if_pos hWhite]
      rw [stepReduces]
      show c.utf8Size + charsByteLength ([] : List Char)
        = charsByteLength (c :: [])
      show c.utf8Size + 0 = c.utf8Size + 0
      rfl
    · -- non-whitespace single char.  Returns (0, [c]).
      have stepReduces :
          skipTrivia (fuel + 1) (c :: [])
            = ((0 : Nat), [c]) := by
        show (if isWhitespaceChar c then (c.utf8Size, ([] : List Char))
              else (0, [c]))
            = (0, [c])
        rw [if_neg hWhite]
      rw [stepReduces]
      show 0 + charsByteLength [c] = charsByteLength (c :: [])
      exact Nat.zero_add _
  | fuel + 1, c :: next :: rest2 => by
    by_cases hWhite : isWhitespaceChar c
    · -- whitespace two-or-more.  tail-recurse on (next :: rest2).
      have stepReduces :
          skipTrivia (fuel + 1) (c :: next :: rest2)
            = (c.utf8Size + (skipTrivia fuel (next :: rest2)).fst,
               (skipTrivia fuel (next :: rest2)).snd) := by
        show (if isWhitespaceChar c then
                let (n, r) := skipTrivia fuel (next :: rest2)
                (c.utf8Size + n, r)
              else if c == '/' then
                if next == '/' then
                  let (lineSkipped, afterLine) :=
                    skipUntilNewline rest2 (c.utf8Size + next.utf8Size)
                  let (n, r) := skipTrivia fuel afterLine
                  (lineSkipped + n, r)
                else if next == '*' then
                  let (blockSkipped, afterBlock) :=
                    skipBlockComment rest2 (c.utf8Size + next.utf8Size)
                  let (n, r) := skipTrivia fuel afterBlock
                  (blockSkipped + n, r)
                else
                  (0, c :: next :: rest2)
              else
                (0, c :: next :: rest2))
            = (c.utf8Size + (skipTrivia fuel (next :: rest2)).fst,
               (skipTrivia fuel (next :: rest2)).snd)
        rw [if_pos hWhite]
      rw [stepReduces]
      show c.utf8Size + (skipTrivia fuel (next :: rest2)).fst
          + charsByteLength (skipTrivia fuel (next :: rest2)).snd
        = charsByteLength (c :: next :: rest2)
      have ihRecursive :
          (skipTrivia fuel (next :: rest2)).fst
          + charsByteLength (skipTrivia fuel (next :: rest2)).snd
            = charsByteLength (next :: rest2) :=
        Lex.skipTrivia_byteLength_invariant fuel (next :: rest2)
      show c.utf8Size + (skipTrivia fuel (next :: rest2)).fst
          + charsByteLength (skipTrivia fuel (next :: rest2)).snd
        = c.utf8Size + charsByteLength (next :: rest2)
      rw [Nat.add_assoc c.utf8Size (skipTrivia fuel (next :: rest2)).fst
            (charsByteLength (skipTrivia fuel (next :: rest2)).snd),
        ihRecursive]
    · -- not whitespace.  Split on c == '/'.
      by_cases hSlash : c == '/'
      · -- c == '/'.  Split on next.
        by_cases hNextSlash : next == '/'
        · -- // line comment.
          have stepReduces :
              skipTrivia (fuel + 1) (c :: next :: rest2)
                = ((skipUntilNewline rest2
                      (c.utf8Size + next.utf8Size)).fst
                    + (skipTrivia fuel (skipUntilNewline rest2
                          (c.utf8Size + next.utf8Size)).snd).fst,
                   (skipTrivia fuel (skipUntilNewline rest2
                      (c.utf8Size + next.utf8Size)).snd).snd) := by
            show (if isWhitespaceChar c then
                    let (n, r) := skipTrivia fuel (next :: rest2)
                    (c.utf8Size + n, r)
                  else if c == '/' then
                    if next == '/' then
                      let (lineSkipped, afterLine) :=
                        skipUntilNewline rest2 (c.utf8Size + next.utf8Size)
                      let (n, r) := skipTrivia fuel afterLine
                      (lineSkipped + n, r)
                    else if next == '*' then
                      let (blockSkipped, afterBlock) :=
                        skipBlockComment rest2 (c.utf8Size + next.utf8Size)
                      let (n, r) := skipTrivia fuel afterBlock
                      (blockSkipped + n, r)
                    else
                      (0, c :: next :: rest2)
                  else
                    (0, c :: next :: rest2))
                = ((skipUntilNewline rest2
                      (c.utf8Size + next.utf8Size)).fst
                    + (skipTrivia fuel (skipUntilNewline rest2
                          (c.utf8Size + next.utf8Size)).snd).fst,
                   (skipTrivia fuel (skipUntilNewline rest2
                      (c.utf8Size + next.utf8Size)).snd).snd)
            rw [if_neg hWhite, if_pos hSlash, if_pos hNextSlash]
          rw [stepReduces]
          -- Use skipUntilNewline invariant + IH + arithmetic.
          have invSkip :
              (skipUntilNewline rest2 (c.utf8Size + next.utf8Size)).fst
              + charsByteLength (skipUntilNewline rest2
                  (c.utf8Size + next.utf8Size)).snd
                = (c.utf8Size + next.utf8Size) + charsByteLength rest2 :=
            Lex.skipUntilNewline_byteLength_invariant rest2
              (c.utf8Size + next.utf8Size)
          have ihRecursive :
              (skipTrivia fuel (skipUntilNewline rest2
                  (c.utf8Size + next.utf8Size)).snd).fst
              + charsByteLength (skipTrivia fuel (skipUntilNewline rest2
                  (c.utf8Size + next.utf8Size)).snd).snd
                = charsByteLength (skipUntilNewline rest2
                    (c.utf8Size + next.utf8Size)).snd :=
            Lex.skipTrivia_byteLength_invariant fuel
              (skipUntilNewline rest2 (c.utf8Size + next.utf8Size)).snd
          show (skipUntilNewline rest2 (c.utf8Size + next.utf8Size)).fst
              + (skipTrivia fuel (skipUntilNewline rest2
                  (c.utf8Size + next.utf8Size)).snd).fst
              + charsByteLength (skipTrivia fuel (skipUntilNewline rest2
                  (c.utf8Size + next.utf8Size)).snd).snd
            = charsByteLength (c :: next :: rest2)
          rw [Nat.add_assoc
                (skipUntilNewline rest2 (c.utf8Size + next.utf8Size)).fst
                (skipTrivia fuel (skipUntilNewline rest2
                    (c.utf8Size + next.utf8Size)).snd).fst
                (charsByteLength (skipTrivia fuel (skipUntilNewline rest2
                    (c.utf8Size + next.utf8Size)).snd).snd),
            ihRecursive, invSkip]
          show (c.utf8Size + next.utf8Size) + charsByteLength rest2
            = c.utf8Size + (next.utf8Size + charsByteLength rest2)
          exact Nat.add_assoc c.utf8Size next.utf8Size
            (charsByteLength rest2)
        · -- c == '/' but next != '/'.  Split on next == '*'.
          by_cases hNextStar : next == '*'
          · -- /* block comment.
            have stepReduces :
                skipTrivia (fuel + 1) (c :: next :: rest2)
                  = ((skipBlockComment rest2
                        (c.utf8Size + next.utf8Size)).fst
                      + (skipTrivia fuel (skipBlockComment rest2
                            (c.utf8Size + next.utf8Size)).snd).fst,
                     (skipTrivia fuel (skipBlockComment rest2
                        (c.utf8Size + next.utf8Size)).snd).snd) := by
              show (if isWhitespaceChar c then
                      let (n, r) := skipTrivia fuel (next :: rest2)
                      (c.utf8Size + n, r)
                    else if c == '/' then
                      if next == '/' then
                        let (lineSkipped, afterLine) :=
                          skipUntilNewline rest2
                            (c.utf8Size + next.utf8Size)
                        let (n, r) := skipTrivia fuel afterLine
                        (lineSkipped + n, r)
                      else if next == '*' then
                        let (blockSkipped, afterBlock) :=
                          skipBlockComment rest2
                            (c.utf8Size + next.utf8Size)
                        let (n, r) := skipTrivia fuel afterBlock
                        (blockSkipped + n, r)
                      else
                        (0, c :: next :: rest2)
                    else
                      (0, c :: next :: rest2))
                  = ((skipBlockComment rest2
                        (c.utf8Size + next.utf8Size)).fst
                      + (skipTrivia fuel (skipBlockComment rest2
                            (c.utf8Size + next.utf8Size)).snd).fst,
                     (skipTrivia fuel (skipBlockComment rest2
                        (c.utf8Size + next.utf8Size)).snd).snd)
              rw [if_neg hWhite, if_pos hSlash, if_neg hNextSlash,
                if_pos hNextStar]
            rw [stepReduces]
            have invSkip :
                (skipBlockComment rest2
                    (c.utf8Size + next.utf8Size)).fst
                + charsByteLength (skipBlockComment rest2
                    (c.utf8Size + next.utf8Size)).snd
                  = (c.utf8Size + next.utf8Size) + charsByteLength rest2 :=
              Lex.skipBlockComment_byteLength_invariant rest2
                (c.utf8Size + next.utf8Size)
            have ihRecursive :
                (skipTrivia fuel (skipBlockComment rest2
                    (c.utf8Size + next.utf8Size)).snd).fst
                + charsByteLength (skipTrivia fuel (skipBlockComment rest2
                    (c.utf8Size + next.utf8Size)).snd).snd
                  = charsByteLength (skipBlockComment rest2
                      (c.utf8Size + next.utf8Size)).snd :=
              Lex.skipTrivia_byteLength_invariant fuel
                (skipBlockComment rest2
                  (c.utf8Size + next.utf8Size)).snd
            show (skipBlockComment rest2
                  (c.utf8Size + next.utf8Size)).fst
                + (skipTrivia fuel (skipBlockComment rest2
                    (c.utf8Size + next.utf8Size)).snd).fst
                + charsByteLength (skipTrivia fuel (skipBlockComment rest2
                    (c.utf8Size + next.utf8Size)).snd).snd
              = charsByteLength (c :: next :: rest2)
            rw [Nat.add_assoc
                  (skipBlockComment rest2 (c.utf8Size + next.utf8Size)).fst
                  (skipTrivia fuel (skipBlockComment rest2
                      (c.utf8Size + next.utf8Size)).snd).fst
                  (charsByteLength (skipTrivia fuel (skipBlockComment rest2
                      (c.utf8Size + next.utf8Size)).snd).snd),
              ihRecursive, invSkip]
            show (c.utf8Size + next.utf8Size) + charsByteLength rest2
              = c.utf8Size + (next.utf8Size + charsByteLength rest2)
            exact Nat.add_assoc c.utf8Size next.utf8Size
              (charsByteLength rest2)
          · -- c == '/' but next is neither / nor *.  Returns (0, c :: next :: rest2).
            have stepReduces :
                skipTrivia (fuel + 1) (c :: next :: rest2)
                  = (0, c :: next :: rest2) := by
              show (if isWhitespaceChar c then
                      let (n, r) := skipTrivia fuel (next :: rest2)
                      (c.utf8Size + n, r)
                    else if c == '/' then
                      if next == '/' then
                        let (lineSkipped, afterLine) :=
                          skipUntilNewline rest2
                            (c.utf8Size + next.utf8Size)
                        let (n, r) := skipTrivia fuel afterLine
                        (lineSkipped + n, r)
                      else if next == '*' then
                        let (blockSkipped, afterBlock) :=
                          skipBlockComment rest2
                            (c.utf8Size + next.utf8Size)
                        let (n, r) := skipTrivia fuel afterBlock
                        (blockSkipped + n, r)
                      else
                        (0, c :: next :: rest2)
                    else
                      (0, c :: next :: rest2))
                  = (0, c :: next :: rest2)
              rw [if_neg hWhite, if_pos hSlash, if_neg hNextSlash,
                if_neg hNextStar]
            rw [stepReduces]
            show 0 + charsByteLength (c :: next :: rest2)
              = charsByteLength (c :: next :: rest2)
            exact Nat.zero_add _
      · -- c != '/' and not whitespace.  Returns (0, c :: next :: rest2).
        have stepReduces :
            skipTrivia (fuel + 1) (c :: next :: rest2)
              = (0, c :: next :: rest2) := by
          show (if isWhitespaceChar c then
                  let (n, r) := skipTrivia fuel (next :: rest2)
                  (c.utf8Size + n, r)
                else if c == '/' then
                  if next == '/' then
                    let (lineSkipped, afterLine) :=
                      skipUntilNewline rest2 (c.utf8Size + next.utf8Size)
                    let (n, r) := skipTrivia fuel afterLine
                    (lineSkipped + n, r)
                  else if next == '*' then
                    let (blockSkipped, afterBlock) :=
                      skipBlockComment rest2 (c.utf8Size + next.utf8Size)
                    let (n, r) := skipTrivia fuel afterBlock
                    (blockSkipped + n, r)
                  else
                    (0, c :: next :: rest2)
                else
                  (0, c :: next :: rest2))
              = (0, c :: next :: rest2)
          rw [if_neg hWhite, if_neg hSlash]
        rw [stepReduces]
        show 0 + charsByteLength (c :: next :: rest2)
          = charsByteLength (c :: next :: rest2)
        exact Nat.zero_add _

/-- **L07.5.1**: `readIdentLexeme` conserves bytes.

For `(_, bytes, remaining) = readIdentLexeme chars acc n`, we have
`bytes + charsByteLength remaining = n + charsByteLength chars`.

Proof: structural induction on `chars`.  Two cases:
* `[]`: returns `(acc, n, [])` — `n + 0 = n + 0` after definitional
  reduction of `charsByteLength`.
* `c :: rest`: split on `isIdentCont c`.  Continue branch tail-
  recurses with `(rest, c :: acc, n + c.utf8Size)`; the IH plus
  `Nat.add_assoc` closes.  Stop branch returns `(acc, n, c :: rest)`
  — `n + charsByteLength (c :: rest)` matches directly.

Zero-axiom — uniform `c.utf8Size` accounting (no `1 = c.utf8Size`
arithmetic). -/
theorem Lex.readIdentLexeme_byteLength_invariant :
    ∀ (chars : List Char) (acc : List Char) (n : Nat),
      let result := readIdentLexeme chars acc n
      result.snd.fst + charsByteLength result.snd.snd
        = n + charsByteLength chars
  | [], acc, n => by
    show n + charsByteLength ([] : List Char)
      = n + charsByteLength ([] : List Char)
    rfl
  | firstChar :: restChars, acc, n => by
    by_cases hCont : isIdentCont firstChar
    · -- continue branch.  tail-recurse.
      have stepReduces :
          readIdentLexeme (firstChar :: restChars) acc n
            = readIdentLexeme restChars (firstChar :: acc)
                (n + firstChar.utf8Size) := by
        show (if isIdentCont firstChar then
                readIdentLexeme restChars (firstChar :: acc)
                  (n + firstChar.utf8Size)
              else (acc, n, firstChar :: restChars))
            = readIdentLexeme restChars (firstChar :: acc)
                (n + firstChar.utf8Size)
        rw [if_pos hCont]
      rw [stepReduces]
      show (readIdentLexeme restChars (firstChar :: acc)
              (n + firstChar.utf8Size)).snd.fst
          + charsByteLength (readIdentLexeme restChars (firstChar :: acc)
              (n + firstChar.utf8Size)).snd.snd
        = n + charsByteLength (firstChar :: restChars)
      have ihRecursive :
          (readIdentLexeme restChars (firstChar :: acc)
              (n + firstChar.utf8Size)).snd.fst
          + charsByteLength (readIdentLexeme restChars (firstChar :: acc)
              (n + firstChar.utf8Size)).snd.snd
            = (n + firstChar.utf8Size) + charsByteLength restChars :=
        Lex.readIdentLexeme_byteLength_invariant restChars
          (firstChar :: acc) (n + firstChar.utf8Size)
      rw [ihRecursive]
      show (n + firstChar.utf8Size) + charsByteLength restChars
        = n + (firstChar.utf8Size + charsByteLength restChars)
      exact Nat.add_assoc n firstChar.utf8Size (charsByteLength restChars)
    · -- stop branch.  Returns (acc, n, firstChar :: restChars).
      have stepReduces :
          readIdentLexeme (firstChar :: restChars) acc n
            = (acc, n, firstChar :: restChars) := by
        show (if isIdentCont firstChar then
                readIdentLexeme restChars (firstChar :: acc)
                  (n + firstChar.utf8Size)
              else (acc, n, firstChar :: restChars))
            = (acc, n, firstChar :: restChars)
        rw [if_neg hCont]
      rw [stepReduces]

/-- **L07.5.2**: `readIntLexeme` conserves bytes.

For `(_, bytes, remaining) = readIntLexeme chars acc n`, we have
`bytes + charsByteLength remaining = n + charsByteLength chars`.

Proof: identical pattern to `readIdentLexeme_byteLength_invariant`
— structural induction with `isDigitChar c` split, IH +
`Nat.add_assoc`. -/
theorem Lex.readIntLexeme_byteLength_invariant :
    ∀ (chars : List Char) (acc : List Char) (n : Nat),
      let result := readIntLexeme chars acc n
      result.snd.fst + charsByteLength result.snd.snd
        = n + charsByteLength chars
  | [], acc, n => by
    show n + charsByteLength ([] : List Char)
      = n + charsByteLength ([] : List Char)
    rfl
  | firstChar :: restChars, acc, n => by
    by_cases hDigit : isDigitChar firstChar
    · -- continue branch.  tail-recurse.
      have stepReduces :
          readIntLexeme (firstChar :: restChars) acc n
            = readIntLexeme restChars (firstChar :: acc)
                (n + firstChar.utf8Size) := by
        show (if isDigitChar firstChar then
                readIntLexeme restChars (firstChar :: acc)
                  (n + firstChar.utf8Size)
              else (acc, n, firstChar :: restChars))
            = readIntLexeme restChars (firstChar :: acc)
                (n + firstChar.utf8Size)
        rw [if_pos hDigit]
      rw [stepReduces]
      show (readIntLexeme restChars (firstChar :: acc)
              (n + firstChar.utf8Size)).snd.fst
          + charsByteLength (readIntLexeme restChars (firstChar :: acc)
              (n + firstChar.utf8Size)).snd.snd
        = n + charsByteLength (firstChar :: restChars)
      have ihRecursive :
          (readIntLexeme restChars (firstChar :: acc)
              (n + firstChar.utf8Size)).snd.fst
          + charsByteLength (readIntLexeme restChars (firstChar :: acc)
              (n + firstChar.utf8Size)).snd.snd
            = (n + firstChar.utf8Size) + charsByteLength restChars :=
        Lex.readIntLexeme_byteLength_invariant restChars
          (firstChar :: acc) (n + firstChar.utf8Size)
      rw [ihRecursive]
      show (n + firstChar.utf8Size) + charsByteLength restChars
        = n + (firstChar.utf8Size + charsByteLength restChars)
      exact Nat.add_assoc n firstChar.utf8Size (charsByteLength restChars)
    · -- stop branch.  Returns (acc, n, firstChar :: restChars).
      have stepReduces :
          readIntLexeme (firstChar :: restChars) acc n
            = (acc, n, firstChar :: restChars) := by
        show (if isDigitChar firstChar then
                readIntLexeme restChars (firstChar :: acc)
                  (n + firstChar.utf8Size)
              else (acc, n, firstChar :: restChars))
            = (acc, n, firstChar :: restChars)
        rw [if_neg hDigit]
      rw [stepReduces]

/-- **L07.5.3**: `readStringLexeme` conserves bytes, conditional on
the `some` result.

For any `readStringLexeme chars acc n = some (revBody, bytes, remaining)`,
we have `bytes + charsByteLength remaining = n + charsByteLength chars`.

Proof structure (mirrors the 3-pattern flat def):
* `[]`: returns `none`, vacuous.
* `[c]`: split on `c == '"'`.  Closing-quote arm gives
  `(n + c.utf8Size) + 0 = n + (c.utf8Size + 0)` via `Nat.add_assoc`.
  Else returns `none`.
* `c :: c2 :: rest2`: split three-way:
  - `c == '"'`: closing quote, single `Nat.add_assoc`.
  - `c == '\\'`: split on `resolveEscapeChar c2` — `none` vacuous,
    `some` recurses with byte count `n + c.utf8Size + c2.utf8Size`
    and closes via IH + two `Nat.add_assoc` applications.
  - else: tail-recurse on `c2 :: rest2` with `n + c.utf8Size`, IH +
    `Nat.add_assoc`.

Zero-axiom. -/
theorem Lex.readStringLexeme_byteLength_invariant :
    ∀ (chars : List Char) (acc : List Char) (n : Nat),
      match readStringLexeme chars acc n with
      | some (_, bytes, remaining) =>
        bytes + charsByteLength remaining = n + charsByteLength chars
      | none => True
  | [], _, _ => by trivial
  | c :: [], acc, n => by
    by_cases hQuote : c == '"'
    · -- Closing quote.  Returns some (acc, n + c.utf8Size, []).
      have stepReduces :
          readStringLexeme (c :: []) acc n
            = some (acc, n + c.utf8Size, ([] : List Char)) := by
        show (if c == '"' then some (acc, n + c.utf8Size, ([] : List Char))
              else (none : Option _))
            = some (acc, n + c.utf8Size, ([] : List Char))
        rw [if_pos hQuote]
      rw [stepReduces]
      show (n + c.utf8Size) + charsByteLength ([] : List Char)
        = n + charsByteLength (c :: [])
      show (n + c.utf8Size) + 0 = n + (c.utf8Size + 0)
      exact Nat.add_assoc n c.utf8Size 0
    · -- Not closing quote.  Returns none.
      have stepReduces :
          readStringLexeme (c :: []) acc n = (none : Option _) := by
        show (if c == '"' then some (acc, n + c.utf8Size, ([] : List Char))
              else (none : Option _))
            = none
        rw [if_neg hQuote]
      rw [stepReduces]
      trivial
  | c :: c2 :: rest2, acc, n => by
    by_cases hQuote : c == '"'
    · -- Closing quote.
      have stepReduces :
          readStringLexeme (c :: c2 :: rest2) acc n
            = some (acc, n + c.utf8Size, c2 :: rest2) := by
        show (if c == '"' then some (acc, n + c.utf8Size, c2 :: rest2)
              else if c == '\\' then
                match resolveEscapeChar c2 with
                | some ch =>
                  readStringLexeme rest2 (ch :: acc)
                    (n + c.utf8Size + c2.utf8Size)
                | none => none
              else
                readStringLexeme (c2 :: rest2) (c :: acc) (n + c.utf8Size))
            = some (acc, n + c.utf8Size, c2 :: rest2)
        rw [if_pos hQuote]
      rw [stepReduces]
      show (n + c.utf8Size) + charsByteLength (c2 :: rest2)
        = n + charsByteLength (c :: c2 :: rest2)
      show (n + c.utf8Size) + (c2.utf8Size + charsByteLength rest2)
        = n + (c.utf8Size + (c2.utf8Size + charsByteLength rest2))
      exact Nat.add_assoc n c.utf8Size (c2.utf8Size + charsByteLength rest2)
    · -- Not closing quote.  Split on c == '\\'.
      by_cases hBack : c == '\\'
      · -- Backslash escape.  Case on resolveEscapeChar c2.
        cases hEsc : resolveEscapeChar c2 with
        | none =>
          have stepReduces :
              readStringLexeme (c :: c2 :: rest2) acc n
                = (none : Option _) := by
            show (if c == '"' then some (acc, n + c.utf8Size, c2 :: rest2)
                  else if c == '\\' then
                    match resolveEscapeChar c2 with
                    | some ch =>
                      readStringLexeme rest2 (ch :: acc)
                        (n + c.utf8Size + c2.utf8Size)
                    | none => none
                  else
                    readStringLexeme (c2 :: rest2) (c :: acc) (n + c.utf8Size))
                = none
            rw [if_neg hQuote, if_pos hBack, hEsc]
          rw [stepReduces]
          trivial
        | some ch =>
          have stepReduces :
              readStringLexeme (c :: c2 :: rest2) acc n
                = readStringLexeme rest2 (ch :: acc)
                    (n + c.utf8Size + c2.utf8Size) := by
            show (if c == '"' then some (acc, n + c.utf8Size, c2 :: rest2)
                  else if c == '\\' then
                    match resolveEscapeChar c2 with
                    | some ch' =>
                      readStringLexeme rest2 (ch' :: acc)
                        (n + c.utf8Size + c2.utf8Size)
                    | none => none
                  else
                    readStringLexeme (c2 :: rest2) (c :: acc) (n + c.utf8Size))
                = readStringLexeme rest2 (ch :: acc)
                    (n + c.utf8Size + c2.utf8Size)
            rw [if_neg hQuote, if_pos hBack, hEsc]
          rw [stepReduces]
          have ihRecursive :
              match readStringLexeme rest2 (ch :: acc)
                      (n + c.utf8Size + c2.utf8Size) with
              | some (_, bytes, remaining) =>
                bytes + charsByteLength remaining
                  = (n + c.utf8Size + c2.utf8Size) + charsByteLength rest2
              | none => True :=
            Lex.readStringLexeme_byteLength_invariant rest2 (ch :: acc)
              (n + c.utf8Size + c2.utf8Size)
          cases hRec : readStringLexeme rest2 (ch :: acc)
                        (n + c.utf8Size + c2.utf8Size) with
          | none => trivial
          | some triple =>
            rw [hRec] at ihRecursive
            obtain ⟨_, bytes, remaining⟩ := triple
            show bytes + charsByteLength remaining
              = n + charsByteLength (c :: c2 :: rest2)
            rw [ihRecursive]
            show (n + c.utf8Size + c2.utf8Size) + charsByteLength rest2
              = n + (c.utf8Size + (c2.utf8Size + charsByteLength rest2))
            rw [Nat.add_assoc (n + c.utf8Size) c2.utf8Size
                  (charsByteLength rest2),
              Nat.add_assoc n c.utf8Size
                (c2.utf8Size + charsByteLength rest2)]
      · -- Normal char (neither '"' nor '\\').  tail-recurse on c2 :: rest2.
        have stepReduces :
            readStringLexeme (c :: c2 :: rest2) acc n
              = readStringLexeme (c2 :: rest2) (c :: acc)
                  (n + c.utf8Size) := by
          show (if c == '"' then some (acc, n + c.utf8Size, c2 :: rest2)
                else if c == '\\' then
                  match resolveEscapeChar c2 with
                  | some ch =>
                    readStringLexeme rest2 (ch :: acc)
                      (n + c.utf8Size + c2.utf8Size)
                  | none => none
                else
                  readStringLexeme (c2 :: rest2) (c :: acc)
                    (n + c.utf8Size))
              = readStringLexeme (c2 :: rest2) (c :: acc)
                  (n + c.utf8Size)
          rw [if_neg hQuote, if_neg hBack]
        rw [stepReduces]
        have ihRecursive :
            match readStringLexeme (c2 :: rest2) (c :: acc)
                    (n + c.utf8Size) with
            | some (_, bytes, remaining) =>
              bytes + charsByteLength remaining
                = (n + c.utf8Size) + charsByteLength (c2 :: rest2)
            | none => True :=
          Lex.readStringLexeme_byteLength_invariant (c2 :: rest2) (c :: acc)
            (n + c.utf8Size)
        cases hRec : readStringLexeme (c2 :: rest2) (c :: acc)
                      (n + c.utf8Size) with
        | none => trivial
        | some triple =>
          rw [hRec] at ihRecursive
          obtain ⟨_, bytes, remaining⟩ := triple
          show bytes + charsByteLength remaining
            = n + charsByteLength (c :: c2 :: rest2)
          rw [ihRecursive]
          show (n + c.utf8Size) + charsByteLength (c2 :: rest2)
            = n + (c.utf8Size + charsByteLength (c2 :: rest2))
          exact Nat.add_assoc n c.utf8Size (charsByteLength (c2 :: rest2))

/-- **L07.5.4-helper**: `lexOpOrPunct` conserves bytes.

`lexOpOrPunct` returns either `LexStep.token` (two-char or single-
char success) or `LexStep.error` (no match — `unexpectedChar`).
In every non-`eof` case, the emitted bytes plus
`charsByteLength remaining` equals
`charsByteLength (firstChar :: restChars)`.

The `LexStep.eof` arm is vacuous — `lexOpOrPunct` never returns
`eof`.  Including it keeps the theorem statement uniform with
`lexOne_byteLength_invariant`.

Proof: case-split on `restChars` to expose `lexTwoCharPeek`'s
reduction (empty rest gives `none`, cons rest reduces to the
inner `lexTwoCharOp` lookup).  Then case-split on the inner
lookup results.  Each of the four resulting paths (two-char
success, single-char success on empty, single-char success on
cons, error) closes via either `rfl`
(`firstChar.utf8Size + charsByteLength rest = charsByteLength
(firstChar :: rest)` is definitional) or `Nat.add_assoc`
(two-char success has shape
`(a + b) + c = a + (b + c)`).

Zero-axiom — uniform `Char.utf8Size` accounting throughout. -/
theorem Lex.lexOpOrPunct_byteLength_invariant
    (offset : Nat) (firstChar : Char) (restChars : List Char) :
    match lexOpOrPunct offset firstChar restChars with
    | LexStep.eof => True
    | LexStep.token _ bytes remaining =>
      bytes + charsByteLength remaining = charsByteLength (firstChar :: restChars)
    | LexStep.error _ bytes remaining =>
      bytes + charsByteLength remaining = charsByteLength (firstChar :: restChars) := by
  match restChars with
  | [] =>
    -- `lexTwoCharPeek firstChar [] = none` → fall through to single-char dispatch.
    cases hPunct : lexSingleCharPunct firstChar with
    | some tok =>
      have hReduces :
          lexOpOrPunct offset firstChar []
            = LexStep.token tok firstChar.utf8Size [] := by
        unfold lexOpOrPunct lexTwoCharPeek
        rw [hPunct]
      rw [hReduces]
      show firstChar.utf8Size + charsByteLength ([] : List Char)
        = charsByteLength (firstChar :: [])
      rfl
    | none =>
      have hReduces :
          lexOpOrPunct offset firstChar []
            = LexStep.error (LexError.unexpectedChar offset firstChar)
                firstChar.utf8Size [] := by
        unfold lexOpOrPunct lexTwoCharPeek
        rw [hPunct]
      rw [hReduces]
      show firstChar.utf8Size + charsByteLength ([] : List Char)
        = charsByteLength (firstChar :: [])
      rfl
  | secondChar :: more =>
    -- `lexTwoCharPeek firstChar (secondChar :: more)` definitionally
    -- reduces by the cons arm of its body — `rfl` clean.  We rewrite
    -- with this equation INSIDE `unfold lexOpOrPunct` to expose the
    -- inner `lexTwoCharOp firstChar secondChar` for case analysis.
    have hPeekReduces :
        lexTwoCharPeek firstChar (secondChar :: more)
          = match lexTwoCharOp firstChar secondChar with
            | some tok => some (tok, secondChar, more)
            | none => none := rfl
    cases hOp : lexTwoCharOp firstChar secondChar with
    | some tok =>
      have hReduces :
          lexOpOrPunct offset firstChar (secondChar :: more)
            = LexStep.token tok (firstChar.utf8Size + secondChar.utf8Size) more := by
        unfold lexOpOrPunct
        rw [hPeekReduces, hOp]
      rw [hReduces]
      show (firstChar.utf8Size + secondChar.utf8Size) + charsByteLength more
        = charsByteLength (firstChar :: secondChar :: more)
      show (firstChar.utf8Size + secondChar.utf8Size) + charsByteLength more
        = firstChar.utf8Size + (secondChar.utf8Size + charsByteLength more)
      exact Nat.add_assoc firstChar.utf8Size secondChar.utf8Size
        (charsByteLength more)
    | none =>
      cases hPunct : lexSingleCharPunct firstChar with
      | some tok =>
        have hReduces :
            lexOpOrPunct offset firstChar (secondChar :: more)
              = LexStep.token tok firstChar.utf8Size (secondChar :: more) := by
          unfold lexOpOrPunct
          rw [hPeekReduces, hOp, hPunct]
        rw [hReduces]
        show firstChar.utf8Size + charsByteLength (secondChar :: more)
          = charsByteLength (firstChar :: secondChar :: more)
        rfl
      | none =>
        have hReduces :
            lexOpOrPunct offset firstChar (secondChar :: more)
              = LexStep.error (LexError.unexpectedChar offset firstChar)
                  firstChar.utf8Size (secondChar :: more) := by
          unfold lexOpOrPunct
          rw [hPeekReduces, hOp, hPunct]
        rw [hReduces]
        show firstChar.utf8Size + charsByteLength (secondChar :: more)
          = charsByteLength (firstChar :: secondChar :: more)
        rfl

/-- **L07.5.4**: `lexOne` conserves bytes.

For every input `chars`, the emitted byte count plus
`charsByteLength` of the remaining characters equals
`charsByteLength chars`.  This is the unified per-step byte-
conservation invariant — `lexLoop` lifts it across iterations
to prove `Lex.run`'s end-to-end byte invariant (`L07.5`).

Cases:
* `chars = []` → `lexOne offset [] = LexStep.eof`; `eof` arm is
  trivially `True`.
* `chars = firstChar :: restChars` → 4-way if-cascade.  Each
  branch delegates to a helper whose byte-conservation is
  already proven:
    - `isIdentStart firstChar` → `lexIdentBranch` →
      `readIdentLexeme_byteLength_invariant`.
    - `isDigitChar firstChar` → `lexDigitBranch` →
      `readIntLexeme_byteLength_invariant`.
    - `firstChar == '"'` → `lexStringBranch` →
      `readStringLexeme_byteLength_invariant` (success) OR
      error byte = `1 = '"'.utf8Size`.
    - else → `lexOpOrPunct` →
      `lexOpOrPunct_byteLength_invariant`.

Zero-axiom — every branch closes either via `rfl` (when the
helper output is structurally a `LexStep.token` whose byte count
is already in canonical form) or via `Nat.add_assoc` /
`Nat.add_comm` arithmetic.

The string-error branch's `1` reduces to `'"'.utf8Size = 1` via
`rfl` (ASCII char ≤ 0x7F gives a single UTF-8 byte). -/
theorem Lex.lexOne_byteLength_invariant
    (offset : Nat) (chars : List Char) :
    match lexOne offset chars with
    | LexStep.eof => True
    | LexStep.token _ bytes remaining =>
      bytes + charsByteLength remaining = charsByteLength chars
    | LexStep.error _ bytes remaining =>
      bytes + charsByteLength remaining = charsByteLength chars := by
  match chars with
  | [] => trivial
  | firstChar :: restChars =>
    show match lexOne offset (firstChar :: restChars) with
         | LexStep.eof => True
         | LexStep.token _ bytes remaining =>
           bytes + charsByteLength remaining
             = charsByteLength (firstChar :: restChars)
         | LexStep.error _ bytes remaining =>
           bytes + charsByteLength remaining
             = charsByteLength (firstChar :: restChars)
    by_cases hIdent : isIdentStart firstChar = true
    · -- Identifier branch.
      have hReduces :
          lexOne offset (firstChar :: restChars)
            = lexIdentBranch firstChar restChars := by
        show (if isIdentStart firstChar = true then
                lexIdentBranch firstChar restChars
              else if isDigitChar firstChar = true then
                lexDigitBranch firstChar restChars
              else if firstChar == '"' then
                lexStringBranch offset firstChar restChars
              else
                lexOpOrPunct offset firstChar restChars)
            = lexIdentBranch firstChar restChars
        rw [if_pos hIdent]
      rw [hReduces]
      -- `lexIdentBranch` always returns `LexStep.token`.
      show match lexIdentBranch firstChar restChars with
           | LexStep.eof => True
           | LexStep.token _ bytes remaining =>
             bytes + charsByteLength remaining
               = charsByteLength (firstChar :: restChars)
           | LexStep.error _ bytes remaining =>
             bytes + charsByteLength remaining
               = charsByteLength (firstChar :: restChars)
      have hIdentResult :
          (readIdentLexeme (firstChar :: restChars) [] 0).snd.fst
            + charsByteLength (readIdentLexeme (firstChar :: restChars) [] 0).snd.snd
              = 0 + charsByteLength (firstChar :: restChars) :=
        Lex.readIdentLexeme_byteLength_invariant (firstChar :: restChars) [] 0
      show match (let identResult := readIdentLexeme (firstChar :: restChars) [] 0
                  LexStep.token (classifyIdent identResult.fst)
                    identResult.snd.fst identResult.snd.snd) with
           | LexStep.eof => True
           | LexStep.token _ bytes remaining =>
             bytes + charsByteLength remaining
               = charsByteLength (firstChar :: restChars)
           | LexStep.error _ bytes remaining =>
             bytes + charsByteLength remaining
               = charsByteLength (firstChar :: restChars)
      show (readIdentLexeme (firstChar :: restChars) [] 0).snd.fst
            + charsByteLength (readIdentLexeme (firstChar :: restChars) [] 0).snd.snd
          = charsByteLength (firstChar :: restChars)
      rw [hIdentResult]
      exact Nat.zero_add (charsByteLength (firstChar :: restChars))
    · by_cases hDigit : isDigitChar firstChar = true
      · -- Digit branch.
        have hReduces :
            lexOne offset (firstChar :: restChars)
              = lexDigitBranch firstChar restChars := by
          show (if isIdentStart firstChar = true then
                  lexIdentBranch firstChar restChars
                else if isDigitChar firstChar = true then
                  lexDigitBranch firstChar restChars
                else if firstChar == '"' then
                  lexStringBranch offset firstChar restChars
                else
                  lexOpOrPunct offset firstChar restChars)
              = lexDigitBranch firstChar restChars
          rw [if_neg hIdent, if_pos hDigit]
        rw [hReduces]
        show match lexDigitBranch firstChar restChars with
             | LexStep.eof => True
             | LexStep.token _ bytes remaining =>
               bytes + charsByteLength remaining
                 = charsByteLength (firstChar :: restChars)
             | LexStep.error _ bytes remaining =>
               bytes + charsByteLength remaining
                 = charsByteLength (firstChar :: restChars)
        have hDigitResult :
            (readIntLexeme (firstChar :: restChars) [] 0).snd.fst
              + charsByteLength (readIntLexeme (firstChar :: restChars) [] 0).snd.snd
                = 0 + charsByteLength (firstChar :: restChars) :=
          Lex.readIntLexeme_byteLength_invariant (firstChar :: restChars) [] 0
        show (readIntLexeme (firstChar :: restChars) [] 0).snd.fst
              + charsByteLength (readIntLexeme (firstChar :: restChars) [] 0).snd.snd
            = charsByteLength (firstChar :: restChars)
        rw [hDigitResult]
        exact Nat.zero_add (charsByteLength (firstChar :: restChars))
      · by_cases hQuote : firstChar == '"'
        · -- String branch.  The refactored `lexStringBranch firstChar`
          -- uses `firstChar.utf8Size` for byte counts, so we don't need
          -- to derive `firstChar = '"'` (which would require
          -- `eq_of_beq`'s propext-leaking `of_decide_eq_true` for Char).
          have hReduces :
              lexOne offset (firstChar :: restChars)
                = lexStringBranch offset firstChar restChars := by
            show (if isIdentStart firstChar = true then
                    lexIdentBranch firstChar restChars
                  else if isDigitChar firstChar = true then
                    lexDigitBranch firstChar restChars
                  else if firstChar == '"' then
                    lexStringBranch offset firstChar restChars
                  else
                    lexOpOrPunct offset firstChar restChars)
                = lexStringBranch offset firstChar restChars
            rw [if_neg hIdent, if_neg hDigit, if_pos hQuote]
          rw [hReduces]
          show match lexStringBranch offset firstChar restChars with
               | LexStep.eof => True
               | LexStep.token _ bytes remaining =>
                 bytes + charsByteLength remaining
                   = charsByteLength (firstChar :: restChars)
               | LexStep.error _ bytes remaining =>
                 bytes + charsByteLength remaining
                   = charsByteLength (firstChar :: restChars)
          unfold lexStringBranch
          have hStringResult :
              match readStringLexeme restChars [] firstChar.utf8Size with
              | some (_, bytes, remaining) =>
                bytes + charsByteLength remaining
                  = firstChar.utf8Size + charsByteLength restChars
              | none => True :=
            Lex.readStringLexeme_byteLength_invariant restChars []
              firstChar.utf8Size
          cases hRead : readStringLexeme restChars [] firstChar.utf8Size with
          | none =>
            -- Error branch: bytes = firstChar.utf8Size, remaining = restChars.
            show firstChar.utf8Size + charsByteLength restChars
              = charsByteLength (firstChar :: restChars)
            rfl
          | some triple =>
            obtain ⟨_, bytes, remaining⟩ := triple
            rw [hRead] at hStringResult
            show bytes + charsByteLength remaining
              = charsByteLength (firstChar :: restChars)
            rw [hStringResult]
            show firstChar.utf8Size + charsByteLength restChars
              = charsByteLength (firstChar :: restChars)
            rfl
        · -- Op/punct branch.
          have hReduces :
              lexOne offset (firstChar :: restChars)
                = lexOpOrPunct offset firstChar restChars := by
            show (if isIdentStart firstChar = true then
                    lexIdentBranch firstChar restChars
                  else if isDigitChar firstChar = true then
                    lexDigitBranch firstChar restChars
                  else if firstChar == '"' then
                    lexStringBranch offset firstChar restChars
                  else
                    lexOpOrPunct offset firstChar restChars)
                = lexOpOrPunct offset firstChar restChars
            rw [if_neg hIdent, if_neg hDigit, if_neg hQuote]
          rw [hReduces]
          exact Lex.lexOpOrPunct_byteLength_invariant offset firstChar restChars


end LeanFX2.Surface
