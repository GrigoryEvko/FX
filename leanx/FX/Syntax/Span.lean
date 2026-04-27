/-!
# Source positions and spans

Per `fx_lexer.md` §10.  Every lexer token carries a span.  Spans
are used for:

  * diagnostic messages (line/column underlining)
  * IDE integration (go-to-definition, hover)
  * doc-comment attachment (`///` binds to the following decl)
  * deterministic source-location hashes for proof caching

## Position tracking

`column` is a **byte offset** from line start, not a display
column.  Tab characters advance column by 1, not by tab stops.
This is a deliberate choice per fx_lexer.md §10: agents and IDEs
are better served by a byte-accurate position than by one that
depends on terminal tab-stop configuration.

`offset` is a byte offset from file start.  `line` is 1-based;
`column` and `offset` are 0-based.
-/

namespace FX.Syntax

/--
A source position.  All three fields track bytes, not codepoints,
matching `fx_lexer.md` §10.
-/
structure Position where
  line   : Nat := 1
  column : Nat := 0
  offset : Nat := 0
  deriving Repr, BEq, DecidableEq, Inhabited

namespace Position

/-- The start-of-file position. -/
def zero : Position := {}

/--
Advance a position past a single byte.  If the byte is an ASCII
newline (`\n`, 0x0A), the line counter increments and column
resets to zero.

CR (`\r`, 0x0D) is treated as column-advancing here, **not** as
a line terminator.  A pure byte-at-a-time function cannot see the
paired `\n` of a CRLF sequence, so the spec-mandated behavior
("all newline forms advance the line counter" — `fx_lexer.md`
§10) lives one layer up in `FX.Syntax.Lexer.LexState.advance` /
`skipHSpaceAndNewlines`, where CR/CRLF lookahead is possible.
CR-only ("classic Mac") newlines are thus recognized by the
lexer; this helper is for callers that have already normalized
their input to LF.

Unicode continuation bytes (0x80–0xBF) advance column only; they
do not start new logical lines.
-/
def nextByte (position : Position) (byte : UInt8) : Position :=
  if byte = 0x0A then
    { line := position.line + 1, column := 0, offset := position.offset + 1 }
  else
    { line := position.line, column := position.column + 1, offset := position.offset + 1 }

end Position

/--
A source span covering a lexed token.  `stop` points **one past**
the last byte of the token (standard half-open interval).  An empty
span (e.g., EOF) has `start = stop`.
-/
structure Span where
  start : Position
  stop  : Position
  deriving Repr, BEq, DecidableEq, Inhabited

namespace Span

/-- The empty span at the start of file. -/
def zero : Span := { start := Position.zero, stop := Position.zero }

/-- A point span at `p` (zero-width). -/
def point (position : Position) : Span := { start := position, stop := position }

/--
Merge two spans: take the earlier start and the later stop.
Comparison is on `offset` since that is totally ordered (unlike
`(line, column)` pairs, which require lexicographic comparison
and are redundant given `offset`).

The two branches use `≤` / `≥` (not `<` / `>`) so that `merge s s
= s` for any `s` — idempotence matters in the parser when the
same span is folded over the same list of children twice.
-/
def merge (leftSpan rightSpan : Span) : Span :=
  { start := if leftSpan.start.offset ≤ rightSpan.start.offset then leftSpan.start else rightSpan.start
  , stop  := if leftSpan.stop.offset  ≥ rightSpan.stop.offset  then leftSpan.stop  else rightSpan.stop }

/--
Byte length of a span.  Since `stop` is one-past-the-last byte
(half-open interval — see the `Span` docstring), the length is
`stop.offset - start.offset`.  `Nat` subtraction truncates at
zero, which matches the intended semantics for degenerate spans
where `stop.offset < start.offset` (these are malformed but
should not crash callers).
-/
def length (span : Span) : Nat := span.stop.offset - span.start.offset

/--
A span is empty when `start = stop` — it covers zero bytes.
This is the shape of EOF tokens and of synthetic spans inserted
by the transformer passes.
-/
def isEmpty (span : Span) : Bool := span.start.offset == span.stop.offset

end Span

end FX.Syntax
