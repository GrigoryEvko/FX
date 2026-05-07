import LeanFX2.Surface.Lex

/-! # Surface/Lex/EofTermination — L02 + L03 audit theorems

Split from `Surface/Lex.lean` (REFACTOR-LEX #1549) — keeps the
Lex impl module under the 1000-line ceiling.

This module ships:

* **L02** (#1200): `classifyIdent kind.toLexemeChars.reverse`
  recovers the canonical token for every keyword.

* **L03** (#1201): every successful `Lex.run chars` output ends
  with a `Token.eof` sentinel — the load-bearing contract
  between the lexer and downstream parser.

All declarations zero-axiom under `#print axioms`. -/

namespace LeanFX2.Surface

/-! ## Audit L03 — `Lex.run`'s success branch is EOF-terminated

The lemmas below establish that whenever `Lex.run` returns
`Except.ok tokens`, the underlying token list ends with a
`Token.eof` sentinel.  This is the load-bearing contract between
the lexer and downstream parser: the parser may rely on the
`eof` sentinel as an unconditional end-of-input marker.

Stated via `tokens.toList.getLast?` rather than `Array.back?` to
avoid Lean 4 v4.29.1's `Array.back?_push` / `Array.size_push`
simp lemmas, both of which transitively depend on `propext` and
would force the production `Surface.Lex` module out of zero-
axiom territory.  `Array.toList` is a structure projection
(`a.toList = a.toList`, `rfl`) and `List.getLast?` is built from
plain pattern matching, so the routes through them are clean.

All zero-axiom under `#print axioms`. -/

/-- Appending an element to a list via `List.concat` makes that
element the `getLast?` of the result.  Proved by structural
recursion; no `simp` lemmas (which leak `propext` via Lean's
match compiler when applied to `List.concat`'s `brecOn` body). -/
theorem List.concat_getLast?_eq {alpha : Type} :
    ∀ (initialList : List alpha) (lastElem : alpha),
      (initialList.concat lastElem).getLast? = some lastElem
  | [], _ => rfl
  | head :: rest, lastElem => by
    show (head :: rest.concat lastElem).getLast? = some lastElem
    match concatEq : rest.concat lastElem with
    | [] =>
        -- `rest.concat lastElem` is non-empty by case analysis on `rest`.
        have concatNonEmpty : rest.concat lastElem ≠ [] := by
          cases rest with
          | nil => intro hContra; cases hContra
          | cons _ _ => intro hContra; cases hContra
        exact absurd concatEq concatNonEmpty
    | nextHead :: nextTail =>
        show (head :: nextHead :: nextTail).getLast? = some lastElem
        have ihRecursive : (rest.concat lastElem).getLast? = some lastElem :=
          List.concat_getLast?_eq rest lastElem
        rw [concatEq] at ihRecursive
        exact ihRecursive

/-- Pushing an element onto an `Array` makes that element the
last entry of `toList`.  Direct corollary of
`List.concat_getLast?_eq` plus the definitional equation
`(arr.push x).toList = arr.toList.concat x` (which holds by
`rfl` since `Array.push` is defined as `⟨a.toList.concat v⟩`). -/
theorem Array.push_toList_getLast?_eq {alpha : Type}
    (arrInput : Array alpha) (lastElem : alpha) :
    (arrInput.push lastElem).toList.getLast? = some lastElem := by
  show (arrInput.toList.concat lastElem).getLast? = some lastElem
  exact List.concat_getLast?_eq arrInput.toList lastElem

/-- **Audit L03**: every successful `Lex.run` output ends with a
`Token.eof` sentinel.  Whenever `Lex.run chars` returns
`Except.ok tokens`, the last positioned token in `tokens.toList`
exists and carries `Token.eof` as its token field.

Proof outline:

1. Unfold `Lex.run` to expose its body — a `let-match-if` over
   `lexLoop`'s pair return.
2. Destructure the `lexLoop` pair into `(lexTokens, lexErrors)`
   via `match`; this reduces the wrapping `match` arm.
3. Rewrap the post-match expression at its actual type via a
   `have ... := runOk2` cast — this shrinks the goal to a plain
   `if-then-else`.
4. Branch on `lexErrors.isEmpty`:
   * `true`: `runOk` says `lexTokens.push eofPos = tokens`; supply
     the pushed `eofPos` as the existential witness, discharge
     the `getLast?` claim via `Array.push_toList_getLast?_eq`.
   * `false`: `runOk` becomes `Except.error _ = Except.ok _`;
     `cases` discharges the contradiction.

Zero-axiom under `#print axioms`. -/
theorem Lex.run_eof_terminated
    (chars : List Char) (tokens : Array PositionedToken)
    (runOk : Lex.run chars = Except.ok tokens) :
    ∃ eofPos : PositionedToken,
      tokens.toList.getLast? = some eofPos ∧ eofPos.token = Token.eof := by
  -- Step 1: unfold via an explicit `rfl` witness to keep the `match`
  -- visible after rewrite (plain `unfold` produces a `have`-binding
  -- form that blocks subsequent destructuring).
  have eqRun : Lex.run chars =
    (match lexLoop (chars.length + 1) 0 chars #[] #[] with
    | (lexTokens, lexErrors) =>
      if lexErrors.isEmpty = true then
        Except.ok (lexTokens.push
          ({ token := Token.eof,
             startPos := { offset := charsByteLength chars } } :
             PositionedToken))
      else Except.error lexErrors) := rfl
  rw [eqRun] at runOk
  -- Step 2: destructure the pair returned by lexLoop.
  match lexLoopEq : lexLoop (chars.length + 1) 0 chars #[] #[], runOk with
  | (lexTokens, lexErrors), runOkPair =>
    -- Step 3: reduce the wrapping `match (lexTokens, lexErrors) with ...`
    -- by ascription — both sides are definitionally equal.
    have runOkIf :
        (if lexErrors.isEmpty = true then
            Except.ok (lexTokens.push
              ({ token := Token.eof,
                 startPos := { offset := charsByteLength chars } } :
                 PositionedToken))
          else Except.error lexErrors)
        = Except.ok tokens := runOkPair
    -- Step 4: branch on the `if`.
    by_cases hErrorsEmpty : lexErrors.isEmpty = true
    · rw [if_pos hErrorsEmpty] at runOkIf
      let eofPos : PositionedToken :=
        { token := Token.eof, startPos := { offset := charsByteLength chars } }
      have tokensEq : lexTokens.push eofPos = tokens := by
        injection runOkIf
      refine ⟨eofPos, ?_, rfl⟩
      rw [← tokensEq]
      exact Array.push_toList_getLast?_eq _ eofPos
    · rw [if_neg hErrorsEmpty] at runOkIf
      cases runOkIf

/-! ## L02: classifyIdent reverses correctly (#1200)

`classifyIdent` consumes the lexeme in REVERSED order (last
char read = head of list) and reverses internally.  Composed
with `KeywordKind.toLexemeChars` (which yields the FORWARD
spelling), feeding `kind.toLexemeChars.reverse` into
`classifyIdent` recovers the keyword token.

Three cases: `trueK` and `falseK` decode to `Token.boolLit`
(per `classifyIdent`'s special-case for boolean literals);
every other keyword decodes to `kind.toToken`. -/

/-- L02 case A: `trueK`'s lexeme `['t','r','u','e']` reversed
through `classifyIdent` recovers the `boolLit true` token
(NOT `Token.kwTrue`, because `classifyIdent` prefers the
literal form for downstream parser convenience). -/
theorem Lex.classifyIdent_kwTrue :
    classifyIdent KeywordKind.trueK.toLexemeChars.reverse
      = Token.boolLit true := by
  decide

/-- L02 case B: `falseK`'s lexeme `['f','a','l','s','e']` reversed
through `classifyIdent` recovers the `boolLit false` token. -/
theorem Lex.classifyIdent_kwFalse :
    classifyIdent KeywordKind.falseK.toLexemeChars.reverse
      = Token.boolLit false := by
  decide

/-- L02 case C: every keyword OTHER than `trueK`/`falseK`
decodes through `classifyIdent` back to its canonical
`Token.toToken` form.  The reversal cancels and the
`fromCharsExact_toLexemeChars` round-trip recovers the
original `KeywordKind`; the two `decide` guards both
evaluate to `false` per the hypotheses. -/
theorem Lex.classifyIdent_keyword_toToken (kind : KeywordKind)
    (notTrue : kind ≠ KeywordKind.trueK)
    (notFalse : kind ≠ KeywordKind.falseK) :
    classifyIdent kind.toLexemeChars.reverse = kind.toToken := by
  cases kind <;> first
    | (exact absurd rfl notTrue)
    | (exact absurd rfl notFalse)
    | rfl

end LeanFX2.Surface
