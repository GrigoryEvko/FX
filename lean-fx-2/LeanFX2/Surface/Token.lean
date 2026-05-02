/-! # Surface/Token — token alphabet for the FX surface lexer

Per `fx_lexer.md` §2-§3.  All keywords are common English words; punctuation
is ASCII; literals cover integers, decimals, booleans, strings, bit/trit,
identifiers.

## Structure

* `Trit` — balanced ternary digit (`-1`, `0`, `+1`)
* `StrKind` — regular / format / raw / bytes
* `Token` — flat enum over all token forms

All zero-axiom (the inductive definitions and DecidableEq derivations
only reach core Lean elimination, no propext / Quot.sound).
-/

namespace LeanFX2.Surface

/-- Balanced-ternary digit.  Used in trit literals like `0t10T` (digits
1, 0, -1).  Per `fx_lexer.md` §3.4. -/
inductive Trit : Type
  | negOne
  | zero
  | posOne
  deriving DecidableEq, Repr

/-- String literal flavor: regular / format-string / raw / bytes.
Per `fx_lexer.md` §3.5. -/
inductive StrKind : Type
  | regular   -- "..."
  | fstring   -- f"..."  (interpolation)
  | raw       -- r"..."  (no escapes)
  | bytes     -- b"..."  (UTF-8 byte literal)
  deriving DecidableEq, Repr

/-- Surface token alphabet.  Per `fx_lexer.md` §2-§3 + `fx_design.md`
§2.3 keyword list (92 global keywords).

Categories:
* Identifiers & literals
* Keywords (92 global per fx_design.md Appendix A)
* Punctuation, operators, brackets

Notes:
* `ident`/`uident` distinction matches FX's casing rule (snake_case
  vs PascalCase) — the LEXER classifies based on the first character.
* Literal payloads carry the parsed value plus optional type-suffix
  (e.g. `42u8` → `intLit 42 (some "u8")`).
* Bit literal: `Nb<digits>` (explicit width prefix) or unsuffixed
  binary like `0b1010` (width = digit count).
* Backtick-escape (``` `let` ```) becomes `ident "let"` directly
  without keyword classification — handled in lexer post-pass. -/
inductive Token : Type
  -- Identifiers
  | ident (name : String)         -- snake_case identifier
  | uident (name : String)        -- PascalCase (types/ctors/modules)

  -- Numeric and string literals
  | intLit (value : Int) (suffix : Option String)
  | decLit (mantissa : String) (suffix : Option String)
  | floatLit (mantissa : String) (suffix : String)  -- f32/f64 always suffix
  | strLit (value : String) (kind : StrKind)
  | bitLit (width : Nat) (value : Nat)
  | tritLit (digits : List Trit)
  | boolLit (value : Bool)

  -- Keywords (92 global, per fx_design.md §2.3 / Appendix A)
  -- Block 1: declaration and binding
  | kwFn | kwLet | kwConst | kwVal | kwType | kwEffect | kwClass | kwInstance
  | kwImpl | kwModule | kwOpen | kwInclude | kwExtern | kwImport
  | kwAxiom | kwLemma | kwTheorem | kwDefn

  -- Block 2: control flow
  | kwIf | kwElse | kwFor | kwWhile | kwBreak | kwContinue
  | kwReturn | kwYield | kwAwait | kwSpawn
  | kwMatch | kwDo | kwBegin | kwEnd | kwIn

  -- Block 3: structural / specification
  | kwPub | kwRec | kwHandle | kwSelect | kwSession | kwReceive | kwSend
  | kwTry | kwCatch | kwAssert | kwHint | kwBy | kwCalc
  | kwPre | kwPost | kwDecreases | kwExports | kwSelf
  | kwExists | kwForall | kwLabel | kwIs | kwAs | kwWhere | kwWith

  -- Block 4: ownership / mode
  | kwOwn | kwRef | kwMut | kwAffine | kwLinear | kwGhost | kwDrop

  -- Block 5: security / verification / refinement
  | kwSorry | kwProof | kwTainted | kwSanitize | kwSecret | kwDeclassify
  | kwVerify | kwTest | kwBench

  -- Block 6: meta / dimension / contract / decorator
  | kwMachine | kwContract | kwDimension | kwDecorator
  | kwComptime | kwCode | kwDual | kwCodata
  | kwException | kwException2  -- placeholder split for future
  | kwDefer

  -- Block 7: polymorphism / closing
  | kwAnd | kwOr | kwNot

  -- Boolean literal keyword (also classified as boolLit)
  | kwTrue | kwFalse

  -- Punctuation
  | lparen | rparen
  | lbrace | rbrace
  | lbracket | rbracket

  -- Operators (single)
  | comma | semicolon | colon
  | dot | dotdot | dotdotdotdot       -- `.`, `..`, `...`
  | dotdotEq                            -- `..=`
  | equals                              -- `=`
  | arrow                               -- `->`
  | fatArrow                            -- `=>`
  | pipe                                -- `|>`
  | atSign                              -- `@`
  | atBracket                           -- `@[`
  | hash                                -- `#`
  | underscore                          -- `_`
  | backtick                            -- `` ` ``

  -- Comparison
  | eqEq | notEq | lt | gt | le | ge

  -- Arithmetic
  | plus | minus | star | slash | percent

  -- Bitwise
  | amp | bar | caret | tilde | shiftLeft | shiftRight

  -- Logical (propositional)
  | implies   -- ==>
  | iff       -- <==>

  -- Sentinel
  | eof
  deriving DecidableEq, Repr

/-- Width of a Trit when packed into a `t6`/`t12`/`t24`/`t48` literal:
each Trit slot occupies the bits needed to encode 3 values (~1.585
bits = 2 bits in practice).  Per `fx_lexer.md` §3.4. -/
@[reducible] def Trit.bitsPerDigit : Nat := 2

/-- Convert a Trit to its signed integer value: `negOne ↦ -1`,
`zero ↦ 0`, `posOne ↦ 1`. -/
def Trit.toInt : Trit → Int
  | .negOne => -1
  | .zero   => 0
  | .posOne => 1

end LeanFX2.Surface
