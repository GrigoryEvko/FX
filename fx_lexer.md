# FX Lexer Specification

Rules for converting a UTF-8 byte stream into a typed token stream.
This document specifies WHAT tokens are produced and the transformer
passes that run between the lexer and parser.  It is the spec for
implementing the FX tokenizer.


## 1. Source Encoding

FX source files are UTF-8.  Extension: `.fx`.

- BOM: skip a leading UTF-8 BOM (EF BB BF) if present.
- Null bytes: rejected.  Null in source is a lexer error.
- Newlines: LF (0x0A), CR (0x0D), CRLF (0x0D 0x0A), and Unicode
  line separators (U+2028, U+2029) are all recognized.  Internally
  normalized to LF for line counting.
- Encoding errors: invalid UTF-8 sequences produce a lexer error
  with the byte offset.

ASCII only in code.  Unicode is permitted only inside string
literals and comments.  An identifier, keyword, operator, or
number containing a non-ASCII byte outside a string or comment is
a lexer error.


## 2. Whitespace and Comments

### 2.1 Whitespace

Space (0x20), tab (0x09), vertical tab (0x0B), form feed (0x0C),
and Unicode space separators (Zs category, U+00A0, U+FEFF) are
whitespace.  Whitespace is insignificant — it separates tokens but
carries no meaning.  There is no significant indentation.

### 2.2 Line Comments

`//` begins a line comment.  Everything from `//` to the next
newline is ignored.  The newline itself is not part of the comment.

```
let x = 42;  // this is a comment
```

### 2.3 Block Comments

`/*` begins a block comment.  `*/` ends it.  Block comments do NOT
nest.  A `/*` inside a block comment is treated as ordinary text.

```
/* this is a block comment */
/* this /* does not nest */ and this is outside */
```

An unterminated block comment (EOF before `*/`) is a lexer error.

### 2.4 Documentation Comments

`///` begins a documentation comment.  It extends to end of line
and attaches as a `@[doc("...")]` attribute to the following
declaration.

```
/// Sorts the list in ascending order.
pub fn sort<a: type>(xs: list(a)) : list(a)
  where Ord(a);
```

Multiple consecutive `///` lines are joined into a single doc
attribute with newlines preserved.


## 3. Identifiers and Keywords

### 3.1 Identifier Scanning

```
lower_ident  = [a-z_][a-zA-Z0-9_]*
upper_ident  = [A-Z][a-zA-Z0-9_]*
```

Maximal munch: the lexer consumes as many identifier characters as
possible.  `format` is one token, not `for` + `mat`.

No single quote `'` in identifiers.  No Unicode letters.  ASCII
only.

### 3.2 Keyword Lookup

After scanning an identifier, the lexer checks the keyword table.
If the identifier matches a keyword, it produces the keyword token.
Otherwise it produces `IDENT` (lowercase start) or `UIDENT`
(uppercase start).

92 global keywords — see fx_grammar.md §2.2 for the complete list.

### 3.3 Backtick Escaping

A backtick-escaped identifier: `` `keyword` `` bypasses keyword
lookup.  The content between backticks becomes a plain identifier.

```
`fn`          → IDENT "fn"
`match`       → IDENT "match"
`SomeClass`   → UIDENT "SomeClass"
```

Rules:
- Opening `` ` `` must be followed by at least one character.
- Closing `` ` `` terminates the identifier.
- No newlines inside backtick identifiers.
- Any ASCII printable character is allowed between backticks.
- Unterminated backtick identifier (EOF before closing `` ` ``) is
  a lexer error.


## 4. Number Literals

### 4.1 Integer Literals

```
decimal:    [0-9] [0-9_]*                     prefix: none
binary:     "0b" [01] [01_]*                  prefix: 0b
ternary:    "0t" [01T] [01T_]*               prefix: 0t
octal:      "0o" [0-7] [0-7_]*              prefix: 0o
hex:        "0x" [0-9a-fA-F] [0-9a-fA-F_]*  prefix: 0x
```

Scanning rule: after consuming the prefix, the lexer requires at
least one valid digit before underscores or suffixes.  `0b` alone
(no digits) is a lexer error.  `0x_FF` (underscore before first
digit) is a lexer error.

### 4.2 Decimal Literals (Exact Fractional)

```
decimal_lit = digits "." digits
            | digits exponent
            | digits "." digits exponent

digits      = [0-9] [0-9_]*
exponent    = ("e"|"E") ("+"|"-")? digits
```

Dotted numeric literals are EXACT DECIMALS, not IEEE floats.
`0.1 + 0.2 == 0.3` is always true.  There is no floating-point
rounding unless the programmer explicitly requests `f32`/`f64`.

**Critical disambiguation:** A dot after digits is a decimal point
ONLY if followed by another digit.  `42.field` is integer `42` +
dot + identifier `field`.  `42.0` is decimal literal.  `42.` with
no following digit is integer `42` + dot (start of method call or
field access).

Rule: **the lexer peeks one character after the dot.  If it is a
digit, consume as decimal literal.  Otherwise, emit integer token
and leave the dot for the next scan.**

### 4.3 Underscore Separators

Underscores are allowed between any two digits in any base:

```
1_000_000        decimal
0xFF_FF_FF       hex
0b1010_0011      binary
0t10_T0_1T       ternary
3.141_592_653    decimal fractional
1_000.00         decimal fractional
```

Rules:
- NOT allowed at the start of a number (that is an identifier).
- NOT allowed immediately after a base prefix: `0b_1010` is an error.
- NOT allowed immediately before a suffix: `42_u32` is an error.
- NOT allowed as the last character before the dot: `42_.0` is an
  error.
- Consecutive underscores are allowed: `1__000` is valid (but the
  style guide discourages it).
- Underscores are stripped before the value is interpreted.

### 4.4 Type Suffixes

Suffixes attach greedily to the preceding number literal.  The
lexer produces a single typed token, not separate number + suffix.

**Integer suffixes:**

```
u8  i8  u16  i16  u32  i32  u64  i64
u128  i128  u256  i256  u512  i512  u1024  i1024
usize  isize
```

Widths up to 128 bits map to hardware instructions on modern
targets.  Widths 256-1024 compile to multi-word arithmetic with
statically known register allocation — no heap, fully unrolled.

Attach to any integer literal (decimal, binary, octal, hex):

```
42u8         → TYPED_INT("42", "u8")
0xFFu32      → TYPED_INT("0xFF", "u32")
0b1010i8     → TYPED_INT("0b1010", "i8")
0xFFu256     → TYPED_INT("0xFF", "u256")
```

**Decimal suffixes (fixed-width exact):**

```
d32  d64  d96  d128  d256  d512  d1024
```

`d96` is a sweet spot on x86 (fits in one SSE register, ~4x faster
than `d128`).  Widths 256-1024 use multi-word arithmetic.

Attach to decimal literals:

```
3.14d128     → TYPED_DECIMAL("3.14", "d128")
19.99d64     → TYPED_DECIMAL("19.99", "d64")
1.0d96       → TYPED_DECIMAL("1.0", "d96")
```

**Float suffixes (IEEE 754 approximate):**

```
f32   f64
```

Attach to decimal literals:

```
3.14f64      → TYPED_FLOAT("3.14", "f64")
1.0e10f32    → TYPED_FLOAT("1.0e10", "f32")
```

**Ternary suffixes:**

```
t6   t12   t24   t48
```

Attach to ternary literals:

```
0t10Tt6      → TYPED_TERNARY("10T", "t6")
0t1T0T01t24  → TYPED_TERNARY("1T0T01", "t24")
```

**Suffix scanning rule:** After scanning a complete number literal,
the lexer attempts to match a suffix.  Suffixes are tried longest
first (e.g., `usize` before `u8`).  If the characters after the
number form a valid suffix, they are consumed as part of the token.
If they form an identifier start but not a valid suffix, it is a
lexer error: `42foo` is rejected (not two tokens `42` + `foo`).

### 4.5 Unsuffixed Literal Types

| Literal | Token | Default type |
|---|---|---|
| `42` | INT_LIT | `int` (arbitrary precision, warns N001 without context) |
| `3.14` | DECIMAL_LIT | `decimal` (exact, arbitrary precision, warns N001) |
| `0xFF` | INT_LIT | `int` (inferred from context, or bits) |
| `0b1010` | INT_LIT | `int` (inferred, or bits(4)) |
| `0t10T` | TERNARY_LIT | `trits` (inferred width) |
| `0o755` | INT_LIT | `int` (inferred, or bits) |

When an unsuffixed literal appears where a fixed-width type is
expected, the compiler resolves it to that type at compile time
with no warning.  `let x : u8 = 42;` produces no N001 warning.
Only unresolved `int` triggers the warning.


## 5. String Literals

All strings use double quotes `"`.  There is no single-quote
character literal.  Characters are represented as `"c"` with type
`char` inferred from context.

### 5.1 Regular Strings

```
"hello, world"
"line 1\nline 2"
"tab\there"
```

The lexer scans from the opening `"` to the closing `"`, processing
escape sequences.  Newlines are allowed inside regular strings
(they become literal newlines in the value).

### 5.2 Escape Sequences

| Escape | Value | Available in |
|---|---|---|
| `\\` | backslash | regular, format, byte |
| `\"` | double quote | regular, format, byte |
| `\n` | newline (LF) | regular, format, byte |
| `\t` | tab | regular, format, byte |
| `\r` | carriage return | regular, format, byte |
| `\0` | null | regular, format, byte |
| `\b` | backspace | regular, format, byte |
| `\f` | form feed | regular, format, byte |
| `\v` | vertical tab | regular, format, byte |
| `\xHH` | hex byte | regular, format, byte |
| `\uHHHH` | 4-digit unicode | regular, format |
| `\u{H+}` | variable unicode | regular, format |
| `\` + newline | line continuation | regular, format |

An invalid escape sequence (e.g., `\q`) is a lexer error.

### 5.3 Format Strings

```
f"hello {name}, you are {age} years old"
f"result: {compute(x: 1, y: 2)}"
f"escaped braces: {{ and }}"
```

Prefix: `f"`.  Interpolation: `{expr}`.  Escaped braces: `{{`
produces literal `{`, `}}` produces literal `}`.

The lexer does NOT parse the interpolated expressions.  It scans
the f-string content as a single `FSTRING` token containing the
raw text including `{...}` delimiters.  The token transformer
(§8.4) expands interpolation into a sequence of STRING + CARET +
LPAREN + expr tokens + RPAREN.

Brace depth tracking: `{` increments depth, `}` decrements.  The
interpolation ends when depth returns to zero.  Nested braces
inside expressions (e.g., record literals) are handled correctly.

### 5.4 Raw Strings

```
r"no \escape \processing"
r"C:\Users\name\file.txt"
```

Prefix: `r"`.  No escape processing.  Backslashes are literal.
The string ends at the first unescaped `"`.

Hash-delimited raw strings allow embedded double quotes:

```
r#"this contains "quotes" inside"#
```

The string ends at `"#`, not at the first `"`.

### 5.5 Byte Strings

```
b"byte data\x00\xFF"
```

Prefix: `b"`.  Only byte-level escapes: `\xHH`, `\\`, `\"`, `\0`,
`\n`, `\t`, `\r`, `\b`, `\f`, `\v`.  No Unicode escapes (`\u` is
an error inside byte strings).  The value is a byte array, not a
Unicode string.

### 5.6 Triple-Quoted Strings

All four string variants support triple-quote form for multiline
content:

```
"""
  first line
  second line
"""

f"""
  name: {name}
  age: {age}
"""

r"""
  no \escapes
  at all
"""

b"""
  raw \x00 bytes
"""
```

Whitespace stripping rules:
1. The first newline after the opening `"""` is stripped.
2. Trailing whitespace before the closing `"""` is stripped.
3. Common leading indentation is removed from all lines.
   The minimum indentation across non-blank lines is subtracted
   from every line.


## 6. Operators and Punctuation

### 6.1 Multi-Character Operators

Scanned by longest match.  Order matters — longer sequences are
tried before shorter ones.

```
Operator   Token          Operator   Token
--------   -----          --------   -----
==         EQ_EQ          <==>       IFF
!=         NEQ            ==>        IMPLIES
<=         LEQ            ..=        RANGE_INCL
>=         GEQ            ...        SPREAD
<<         LSHIFT         |>         PIPE_RIGHT
>>         RSHIFT         ->         ARROW
..         RANGE          =>         FAT_ARROW
@[         AT_LBRACK
```

### 6.2 Single-Character Operators and Punctuation

```
+  PLUS        -  MINUS       *  STAR        /  SLASH
%  PERCENT     <  LT          >  GT          =  EQUALS
&  AMP         |  PIPE        ^  CARET       ~  TILDE
:  COLON       ;  SEMICOLON   ,  COMMA       .  DOT
#  HASH        @  AT
(  LPAREN      )  RPAREN      [  LBRACK      ]  RBRACK
{  LBRACE      }  RBRACE
```

### 6.3 Tokens NOT in FX

The following characters and sequences are NOT tokens in FX.  Their
presence outside a string or comment is a lexer error:

```
!          use not keyword
?          errors are effects (Fail)
'          no single quotes in FX
`          only valid as backtick escape delimiters
$          not used
\          only valid inside string escapes
```


## 7. Contextual Keyword: `ref`

`ref` is both a keyword (borrow mode on parameters) and a valid
identifier (the `ref()` constructor for mutable cells).  The lexer
always emits `REF_KW`.  The parser accepts `REF_KW` in identifier
position so that `ref(value)`, `type ref`, etc. continue to work.
Only in mode position (`REF_KW lower_ident COLON type`) does it
act as a keyword.

This is purely a parser-level disambiguation.  The lexer does not
need context — it always emits `REF_KW` for the string `ref`.


## 8. Token Transformer

Between the lexer and parser, four transformation passes run on the
token stream.  The parser sees the transformed stream, not the raw
lexer output.

### 8.1 ELSE IF Merging

When the transformer sees `ELSE` followed by `IF`, it replaces both
tokens with a single `ELIF` token.  This enables `else if` chains
without special grammar rules:

```
Input:   ELSE  IF  expr  SEMI  ...
Output:  ELIF  expr  SEMI  ...
```

The `ELIF` token's span covers both original tokens.

### 8.2 DOT Disambiguation

The raw lexer always emits `DOT` for `.`.  The transformer replaces
`DOT` with `DOT_PROJ` (field projection) based on the preceding
token:

- After `UIDENT`: keep as `DOT` (qualified name: `Module.name`)
- After anything else: replace with `DOT_PROJ` (field access: `x.field`)

This eliminates shift/reduce conflicts between qualified name paths
and field projection in the parser grammar.

### 8.3 Trailing Comma Stripping

When the transformer sees `COMMA` followed by a closing delimiter
(`RPAREN`, `RBRACK`, `RBRACE`), it drops the `COMMA`:

```
Input:   arg1  COMMA  arg2  COMMA  RPAREN
Output:  arg1  COMMA  arg2  RPAREN
```

This allows trailing commas in all list, argument, and field
contexts without grammar rules for optional trailing commas.

### 8.4 F-String Interpolation Expansion

When the transformer sees an `FSTRING` token, it parses the content
into text segments and expression segments, then expands into a
token sequence:

```
FSTRING "hello {name}, age {age}"

expands to:

LPAREN  STRING "hello "  CARET  LPAREN  IDENT "name"  RPAREN
        CARET  STRING ", age "  CARET  LPAREN  IDENT "age"  RPAREN  RPAREN
```

Rules:
- `{expr}` segments are re-lexed to produce their token sequences.
- `{{` in the content produces literal `{` in a STRING segment.
- `}}` in the content produces literal `}` in a STRING segment.
- Empty text segments (between adjacent interpolations) are dropped.
- A pure-text f-string (no `{`) is emitted as a plain `STRING`.
- The entire expansion is wrapped in `LPAREN ... RPAREN`.


## 9. Error Recovery

When the lexer encounters an invalid character or malformed token,
it produces an error diagnostic and attempts to continue:

- **Invalid character:** Emit error, skip one byte, resume scanning.
- **Unterminated string:** Emit error at EOF, produce a STRING token
  with the content scanned so far.
- **Unterminated block comment:** Emit error at EOF.
- **Unterminated backtick identifier:** Emit error at EOF.
- **Malformed number:** `42foo` — emit error, produce INT_LIT for
  the numeric prefix, leave `foo` for the next scan.
- **Invalid escape:** `"\q"` — emit error, include the literal `\q`
  in the string value, continue scanning.
- **Invalid underscore in number:** `0b_1010` — emit error, produce
  the number without the misplaced underscore.

Errors are collected, not fatal.  The lexer continues to produce
tokens after an error so the parser can report additional errors.


## 10. Position Tracking

The lexer maintains a source position for every token:

```
file:    string      source file path
line:    nat         1-based line number
column:  nat         0-based byte offset from line start
offset:  nat         0-based byte offset from file start
```

Positions are tracked through:
- Newline normalization (all newline forms advance the line counter)
- Multi-line strings (newlines inside strings advance the counter)
- Block comments (newlines inside comments advance the counter)
- Tab characters (advance column by 1, not by tab stops — column
  is a byte offset, not a display column)

Every token carries a span: `(start_pos, end_pos)`.  The span is
used for error messages, IDE integration, and comment attachment.


## 11. Token Summary

Complete token inventory produced by the lexer:

```
Identifiers:     IDENT  UIDENT

Literals:        INT_LIT  TYPED_INT  DECIMAL_LIT  TYPED_DECIMAL
                 TYPED_FLOAT  TERNARY_LIT  TYPED_TERNARY
                 STRING  FSTRING  RSTRING  BSTRING
                 TRUE  FALSE

Keywords:        92 keyword tokens (one per keyword)

Operators:       PLUS  MINUS  STAR  SLASH  PERCENT
                 EQ_EQ  NEQ  LT  GT  LEQ  GEQ
                 AMP  PIPE  CARET  TILDE  LSHIFT  RSHIFT
                 ARROW  FAT_ARROW  RANGE  RANGE_INCL  SPREAD
                 PIPE_RIGHT  DOT  DOT_PROJ  EQUALS
                 COLON  SEMICOLON  COMMA  HASH  AT
                 AT_LBRACK  IFF  IMPLIES

Delimiters:      LPAREN  RPAREN  LBRACK  RBRACK  LBRACE  RBRACE

Derived:         ELIF (from transformer)
                 CARET (used in f-string expansion)

Special:         DOC_COMMENT  EOF
```

Total: ~120 distinct token types.
