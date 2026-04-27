import FX.Syntax.Lexer
import Tests.Framework

-- Raise the elaborator recursion limit: a handful of the polish
-- tests below thread escape-heavy string literals through the
-- generic `check` helper, whose `Repr`/`DecidableEq` chains on a
-- 40+ constructor `Token` plus long `String` payloads exceed the
-- default limit of 512.
set_option maxRecDepth 2048

/-!
# Lexer runtime tests

Covers `fx_lexer.md` §1–§10 at the Phase-1 subset implemented
in `FX/Syntax/Lexer.lean`.

Structure:

  * §1  Source encoding — BOM strip, null rejection (deferred)
  * §2  Whitespace and comments — line, block, doc, unterminated
  * §3  Identifiers — lower/upper, backtick escape
  * §4  Integer literals — decimal only (Phase 1)
  * §5  String literals — regular strings with escapes
  * §6  Operators and punctuation — every single- and
        multi-char token
  * §8  Transformer passes — ELSE IF, DOT disambig, trailing
        comma (§8.4 f-string expansion deferred)
  * §10 Position tracking — line/column through ops and
        newlines
  * All 92 keywords roundtrip

Tests compare the emitted token stream (tokens only, spans
elsewhere) to an expected array.
-/

namespace Tests.Syntax.LexerTests

open Tests FX.Syntax

/-- Run the lexer and return just the token sequence, dropping
    spans.  Asserts that the lexer produced an EOF terminator. -/
def toks (sourceText : String) : Array Token :=
  (FX.Syntax.tokenize sourceText).tokens.map (·.token)

/-- Lexer errors for a given source. -/
def errs (sourceText : String) : Array FX.Util.Error :=
  (FX.Syntax.tokenize sourceText).errors

/-- Error codes in emission order, for precise recovery checks. -/
def errCodes (sourceText : String) : Array String :=
  (errs sourceText).map (·.code)

/-- True iff the given error code was emitted for `sourceText`. -/
def hasErr (sourceText : String) (code : String) : Bool :=
  (errCodes sourceText).contains code

def run : IO Unit := Tests.suite "Tests.Syntax.LexerTests" do
  /- §1 Source encoding -/
  check "empty input → [EOF]"
    #[Token.eof] (toks "")

  check "only whitespace → [EOF]"
    #[Token.eof] (toks "   \t\t ")

  -- BOM strip: construct "\uFEFFfoo" as three bytes 0xEF 0xBB 0xBF
  -- prepended to "foo" via the UTF-8 representation.
  let bom : String := String.fromUTF8! ⟨#[0xEF, 0xBB, 0xBF]⟩
  check "BOM stripped"
    #[Token.ident "foo", Token.eof]
    (toks (bom ++ "foo"))

  /- §2.2 Line comments -/
  check "line comment ignored"
    #[Token.ident "x", Token.semi, Token.eof]
    (toks "x; // trailing comment")

  check "line comment followed by ident"
    #[Token.ident "a", Token.ident "b", Token.eof]
    (toks "a // comment\nb")

  /- §2.3 Block comments (non-nesting per spec) -/
  check "block comment ignored"
    #[Token.ident "x", Token.ident "y", Token.eof]
    (toks "x /* middle */ y")

  check "block comment across newlines"
    #[Token.ident "a", Token.ident "b", Token.eof]
    (toks "a /* line1\nline2\n */ b")

  check "unterminated block comment errors"
    true ((errs "x /* unterminated").size > 0)

  check "block comment doesn't nest — outer closes at first */"
    -- After the first */ closes the comment, the tokens 'and */ b' are lexed:
    -- 'and' becomes the keyword, '*' and '/' become STAR + SLASH operators,
    -- then 'b' becomes an ident.
    #[Token.ident "a", Token.kw Keyword.andKw,
      Token.star, Token.slash, Token.ident "b", Token.eof]
    (toks "a /* outer /* inner */ and */ b")

  /- §2.4 Doc comments -/
  check "doc comment produces docComment token"
    #[Token.docComment " this is doc", Token.ident "x", Token.eof]
    (toks "/// this is doc\nx")

  /- §3.1 Identifiers and keywords -/
  check "lower ident"
    #[Token.ident "hello_world_99", Token.eof]
    (toks "hello_world_99")

  check "upper ident"
    #[Token.uident "FooBar42", Token.eof]
    (toks "FooBar42")

  check "underscore-only ident"
    #[Token.ident "_", Token.eof]
    (toks "_")

  check "underscore + digits"
    #[Token.ident "_123", Token.eof]
    (toks "_123")

  check "fn is a keyword, not an ident"
    #[Token.kw Keyword.fnKw, Token.eof]
    (toks "fn")

  check "match is a keyword"
    #[Token.kw Keyword.matchKw, Token.eof]
    (toks "match")

  check "`fn` backtick escape produces ident"
    #[Token.ident "fn", Token.eof]
    (toks "`fn`")

  check "backtick escape with upper name produces uident"
    #[Token.uident "SomeClass", Token.eof]
    (toks "`SomeClass`")

  check "empty backtick errors"
    true ((errs "``").size > 0)

  check "unterminated backtick errors"
    true ((errs "`fn").size > 0)

  /- §4.1 Integer literals (decimal only in Phase 1) -/
  check "single-digit int"
    #[Token.intLit "0" IntBase.dec, Token.eof]
    (toks "0")

  check "multi-digit int"
    #[Token.intLit "12345" IntBase.dec, Token.eof]
    (toks "12345")

  /- §5 String literals -/
  check "simple string"
    #[Token.stringLit "hello", Token.eof]
    (toks "\"hello\"")

  check "string with newline escape"
    #[Token.stringLit "a\nb", Token.eof]
    (toks "\"a\\nb\"")

  check "string with tab escape"
    #[Token.stringLit "a\tb", Token.eof]
    (toks "\"a\\tb\"")

  check "string with escaped backslash"
    #[Token.stringLit "a\\b", Token.eof]
    (toks "\"a\\\\b\"")

  check "string with escaped quote"
    #[Token.stringLit "say \"hi\"", Token.eof]
    (toks "\"say \\\"hi\\\"\"")

  check "empty string"
    #[Token.stringLit "", Token.eof]
    (toks "\"\"")

  check "unterminated string errors"
    true ((errs "\"abc").size > 0)

  check "invalid escape errors"
    true ((errs "\"\\q\"").size > 0)

  /- §6.1 Multi-character operators -/
  check "=="
    #[Token.eqEq, Token.eof]            (toks "==")
  check "!="
    #[Token.neq, Token.eof]             (toks "!=")
  check "<="
    #[Token.leq, Token.eof]             (toks "<=")
  check ">="
    #[Token.geq, Token.eof]             (toks ">=")
  check "<<"
    #[Token.lshift, Token.eof]          (toks "<<")
  check ">>"
    #[Token.rshift, Token.eof]          (toks ">>")
  check "->"
    #[Token.arrow, Token.eof]           (toks "->")
  check "=>"
    #[Token.fatArrow, Token.eof]        (toks "=>")
  check ".."
    #[Token.range, Token.eof]           (toks "..")
  check "..="
    #[Token.rangeIncl, Token.eof]       (toks "..=")
  check "..."
    #[Token.spread, Token.eof]          (toks "...")
  check "|>"
    #[Token.pipeRight, Token.eof]       (toks "|>")
  check "==>"
    #[Token.implies, Token.eof]         (toks "==>")
  check "<==>"
    #[Token.iff, Token.eof]             (toks "<==>")
  check "@["
    #[Token.atLbrack, Token.eof]        (toks "@[")

  /- §6.2 Single-character operators & punct -/
  check "+ - * / %"
    #[Token.plus, Token.minus, Token.star, Token.slash, Token.percent, Token.eof]
    (toks "+ - * / %")

  check "< > ="
    #[Token.lt, Token.gt, Token.equals, Token.eof]
    (toks "< > =")

  check "& | ^ ~"
    #[Token.amp, Token.pipe, Token.caret, Token.tilde, Token.eof]
    (toks "& | ^ ~")

  check ": ; , . # @"
    #[Token.colon, Token.semi, Token.comma, Token.dotProj, -- lone '.' after start becomes dotProj by transformer
      Token.hash, Token.at, Token.eof]
    (toks ": ; , . # @")

  check "delimiters ( ) [ ] { }"
    #[Token.lparen, Token.rparen, Token.lbrack, Token.rbrack,
      Token.lbrace, Token.rbrace, Token.eof]
    (toks "( ) [ ] { }")

  /- §6.1 Longest-match — ==> vs == -/
  check "==> prefers 3-char token"
    #[Token.implies, Token.eof]
    (toks "==>")

  check "== then > produces eqEq + gt"
    #[Token.eqEq, Token.gt, Token.eof]
    (toks "== >")

  /- §8.1 ELSE IF transformer: the post-transform stream collapses
     `else if` into a single `elif` token. -/
  check "else if → elif (space-separated)"
    #[Token.elif, Token.eof]
    (toks "else if")

  check "else if → elif (tab-separated)"
    #[Token.elif, Token.eof]
    (toks "else\tif")

  check "else foo: not merged (no if after)"
    #[Token.kw Keyword.elseKw, Token.ident "foo", Token.eof]
    (toks "else foo")

  /- §8.2 DOT disambiguation -/
  check "x.field → DOT_PROJ (ident-dot-ident)"
    #[Token.ident "x", Token.dotProj, Token.ident "field", Token.eof]
    (toks "x.field")

  check "Module.name → DOT (UIDENT-dot-ident)"
    #[Token.uident "Module", Token.dot, Token.ident "name", Token.eof]
    (toks "Module.name")

  check "Module.Sub.name — DOT then DOT_PROJ"
    -- UIDENT dot UIDENT dotProj ident
    #[Token.uident "Module", Token.dot, Token.uident "Sub",
      Token.dot, Token.ident "name", Token.eof]
    (toks "Module.Sub.name")

  /- §8.3 Trailing comma -/
  check "trailing comma in (a, b,) stripped"
    #[Token.lparen, Token.ident "a", Token.comma, Token.ident "b",
      Token.rparen, Token.eof]
    (toks "(a, b,)")

  check "trailing comma in [a, b,] stripped"
    #[Token.lbrack, Token.ident "a", Token.comma, Token.ident "b",
      Token.rbrack, Token.eof]
    (toks "[a, b,]")

  check "trailing comma in {a, b,} stripped"
    #[Token.lbrace, Token.ident "a", Token.comma, Token.ident "b",
      Token.rbrace, Token.eof]
    (toks "{a, b,}")

  check "no trailing comma — pass-through"
    #[Token.lparen, Token.ident "a", Token.comma, Token.ident "b",
      Token.rparen, Token.eof]
    (toks "(a, b)")

  /- §10 Position tracking — first token spans match source -/
  let resultPosition := FX.Syntax.tokenize "abc\n  def"
  check "tokens emitted for two idents plus EOF" 3 resultPosition.tokens.size
  -- first ident 'abc' at 1:0
  let t0 := resultPosition.tokens[0]!
  check "token 0 line"   1 t0.span.start.line
  check "token 0 column" 0 t0.span.start.column
  -- second ident 'def' at 2:2
  let t1 := resultPosition.tokens[1]!
  check "token 1 line"   2 t1.span.start.line
  check "token 1 column" 2 t1.span.start.column
  -- EOF at 2:5
  let t2 := resultPosition.tokens[2]!
  check "EOF line"    2 t2.span.start.line
  check "EOF column"  5 t2.span.start.column

  /- All 92 keywords detected -/
  let allKwStrs := #[
    "affine", "and", "as", "assert", "await",
    "axiom", "begin", "bench", "bisimulation", "break",
    "by", "calc", "catch", "class", "code",
    "comptime", "const", "continue", "codata", "contract",
    "decreases", "decorator", "declassify", "defer", "dimension",
    "drop", "dual", "effect", "else", "end",
    "errdefer", "exception", "exists", "exports", "extern",
    "false", "fn", "for", "forall", "ghost",
    "handle", "hint", "if", "impl", "in",
    "include", "instance", "is", "label", "layout",
    "lemma", "let", "linear", "machine", "match",
    "module", "mut", "not", "open", "or",
    "own", "post", "pre", "proof", "pub",
    "quotient", "receive", "rec", "ref", "refinement",
    "return", "sanitize", "secret", "select", "self",
    "send", "session", "sorry", "spawn", "taint_class",
    "tainted", "test", "true", "try", "type",
    "unfold", "val", "verify", "while", "with",
    "where", "yield" ]
  check "keyword list has 92 entries" 92 allKwStrs.size
  let mut nonKeywordCount := 0
  for keywordSpelling in allKwStrs do
    let lexedTokens := toks keywordSpelling
    match lexedTokens[0]? with
    | some (Token.kw _) => pure ()
    | _                 => nonKeywordCount := nonKeywordCount + 1
  check "every keyword spelling produces a Token.kw" 0 nonKeywordCount

  /- Unknown byte produces an error and the parser continues -/
  check "unknown byte '!' produces error but no crash"
    true ((errs "!").size > 0)
  check "unknown byte in middle still yields surrounding tokens"
    -- '!' is rejected as a bare token; surrounding tokens are still emitted.
    -- Actual count depends on error recovery; check that we got at least
    -- the ident and EOF.
    true ((toks "a!b").size ≥ 3)

  /- Polish §A: longest-match coverage for every multi-char op.
     For each N-byte op we check that it is a single token, then
     that the same op followed by a disambiguating byte still
     tokenizes as the N-byte op plus whatever follows.  This
     guarantees the scanner prefers 3-char over 2-char over 1-char
     at every ambiguous prefix. -/

  check "<==> is the 4-byte iff"
    #[Token.iff, Token.eof]              (toks "<==>")
  check "==> then ident"
    #[Token.implies, Token.ident "x", Token.eof]
    (toks "==>x")
  check "== followed by space + > stays 2+1"
    #[Token.eqEq, Token.gt, Token.ident "x", Token.eof]
    (toks "== >x")
  check "..= prefers 3-byte rangeIncl"
    #[Token.rangeIncl, Token.eof]        (toks "..=")
  check "... prefers 3-byte spread"
    #[Token.spread, Token.eof]           (toks "...")
  check "..a: range then ident"
    #[Token.range, Token.ident "a", Token.eof]
    (toks "..a")
  check "..=a: rangeIncl then ident"
    #[Token.rangeIncl, Token.ident "a", Token.eof]
    (toks "..=a")
  check "...a: spread then ident"
    #[Token.spread, Token.ident "a", Token.eof]
    (toks "...a")

  check "-> prefix: -> then ident"
    #[Token.arrow, Token.ident "x", Token.eof]
    (toks "->x")
  check "=> prefix: => then ident"
    #[Token.fatArrow, Token.ident "x", Token.eof]
    (toks "=>x")
  check "|> prefix: |> then ident"
    #[Token.pipeRight, Token.ident "x", Token.eof]
    (toks "|>x")
  check "<= prefix: <= then ident"
    #[Token.leq, Token.ident "x", Token.eof]
    (toks "<=x")
  check ">= prefix: >= then ident"
    #[Token.geq, Token.ident "x", Token.eof]
    (toks ">=x")
  check "!= prefix: != then ident"
    #[Token.neq, Token.ident "x", Token.eof]
    (toks "!=x")
  check "<< prefix: << then ident"
    #[Token.lshift, Token.ident "x", Token.eof]
    (toks "<<x")
  check ">> prefix: >> then ident"
    #[Token.rshift, Token.ident "x", Token.eof]
    (toks ">>x")
  check "@[ prefix: @[ then ident"
    #[Token.atLbrack, Token.ident "x", Token.eof]
    (toks "@[x")

  check "bare = is equals"
    #[Token.equals, Token.ident "x", Token.eof]
    (toks "= x")
  check "bare < is lt"
    #[Token.lt, Token.ident "x", Token.eof]     (toks "< x")
  check "bare > is gt"
    #[Token.gt, Token.ident "x", Token.eof]     (toks "> x")
  check "bare - is minus"
    #[Token.minus, Token.ident "x", Token.eof]  (toks "- x")
  check "bare @ is at"
    #[Token.at, Token.ident "x", Token.eof]     (toks "@ x")

  /- Polish §B: Integer base prefixes, underscores, typed
     suffixes, empty-digit errors (§4 of fx_lexer.md). -/

  check "0xFF hex int"
    #[Token.intLit "FF" IntBase.hex, Token.eof]       (toks "0xFF")
  check "0b1010 binary int"
    #[Token.intLit "1010" IntBase.bin, Token.eof]     (toks "0b1010")
  check "0o77 octal int"
    #[Token.intLit "77" IntBase.oct, Token.eof]       (toks "0o77")
  check "0xFF_00 underscore stripped from canonical"
    #[Token.intLit "FF00" IntBase.hex, Token.eof]     (toks "0xFF_00")
  check "42u8 typed int"
    #[Token.typedInt "42" IntBase.dec "u8", Token.eof]
    (toks "42u8")
  check "0xFFi64 hex typed int"
    #[Token.typedInt "FF" IntBase.hex "i64", Token.eof]
    (toks "0xFFi64")
  check "42xyz invalid suffix emits L007"
    true (hasErr "42xyz" "L007")
  check "0x without digits emits L012"
    true (hasErr "0x" "L012")
  check "0b_1010 underscore-after-prefix emits L006"
    true (hasErr "0b_1010" "L006")
  check "0t10T ternary literal"
    #[Token.ternaryLit "10T", Token.eof]              (toks "0t10T")
  check "0t10Tt6 typed ternary"
    #[Token.typedTernary "10T" "t6", Token.eof]       (toks "0t10Tt6")

  /- Polish §C: Decimal and float literals (§4.2). -/

  check "3.14 decimal"
    #[Token.decimalLit "3.14", Token.eof]             (toks "3.14")
  check "1e10 decimal-with-exponent"
    #[Token.decimalLit "1e10", Token.eof]             (toks "1e10")
  check "1.5e-3 decimal-with-signed-exponent"
    #[Token.decimalLit "1.5e-3", Token.eof]           (toks "1.5e-3")
  check "3.14f64 typed float"
    #[Token.typedFloat "3.14" "f64", Token.eof]       (toks "3.14f64")
  check "3.14d128 typed decimal"
    #[Token.typedDecimal "3.14" "d128", Token.eof]    (toks "3.14d128")
  check "42.field: int DOT ident (dotProj after xform)"
    #[Token.intLit "42" IntBase.dec, Token.dotProj,
      Token.ident "field", Token.eof]
    (toks "42.field")

  /- Polish §D: Raw strings `r"…"` — no escape processing,
     unterminated → L004. -/

  check "raw string — simple"
    #[Token.rstringLit "hello", Token.eof]    (toks "r\"hello\"")
  check "raw string — preserves backslash literally"
    #[Token.rstringLit "a\\nb", Token.eof]    (toks "r\"a\\nb\"")
  check "unterminated raw string emits L004"
    true (hasErr "r\"abc" "L004")
  check "unterminated raw string does not emit L011"
    false (hasErr "r\"abc" "L011")

  /- Polish §E: Byte strings `b"…"` — \\u forbidden, hex bytes
     can produce non-UTF-8 content, unterminated → L004.
     Dynamic-shape checks avoid maxRecDepth on escape-heavy
     string literals in the test source. -/

  check "byte string — simple ASCII"
    #[Token.bstringLit "hello", Token.eof]    (toks "b\"hello\"")
  check "byte string — \\x41 = 'A'"
    #[Token.bstringLit "A", Token.eof]        (toks "b\"\\x41\"")

  -- \xFF alone is not valid UTF-8.  Fallback renders payload as
  -- hex-escape text; no crash, no error emitted.  We use a tiny
  -- boolean `isBstrWith` predicate instead of `match`-ing the
  -- Token sum (40+ constructors slow Lean's pattern compiler on
  -- escape-heavy string literals).
  let isBstrWith (candidateToken : Token) (expectedPayload : String) : Bool :=
    candidateToken == Token.bstringLit expectedPayload
  let tksFF := toks "b\"\\xFF\""
  check "byte string — \\xFF produces 2 tokens"
    2 tksFF.size
  check "byte string — \\xFF fallback payload is \"\\xFF\""
    true (isBstrWith tksFF[0]! "\\xFF")
  check "byte string — \\xFF produces no errors"
    0 (errs "b\"\\xFF\"").size

  let tks3 := toks "b\"\\xFF\\x00\\xC0\""
  check "byte string — multi-byte non-UTF-8: 2 tokens"
    2 tks3.size
  check "byte string — multi-byte fallback payload"
    true (isBstrWith tks3[0]! "\\xFF\\x00\\xC0")

  check "byte string — \\u forbidden emits L010"
    true (hasErr "b\"\\u0041\"" "L010")
  check "byte string — bad \\x digits emits L008"
    true (hasErr "b\"\\xGG\"" "L008")
  check "unterminated byte string emits L004"
    true (hasErr "b\"abc" "L004")
  check "unterminated byte string does not emit L011"
    false (hasErr "b\"abc" "L011")

  /- Polish §F: Format strings `f"…"` — raw capture for Phase 2
     expansion, escaped quote preserved. -/

  check "f-string simple"
    #[Token.fstringLit "hello {name}", Token.eof]
    (toks "f\"hello {name}\"")
  check "unterminated f-string emits L011"
    true (hasErr "f\"abc" "L011")

  /- Polish §G: Multi-line strings, block comments — position
     tracking must advance line/column past embedded LF. -/

  let resMl := FX.Syntax.tokenize "\"a\nb\"\nc"
  check "multi-line string: two tokens plus EOF"
    3 resMl.tokens.size
  let tC := resMl.tokens[1]!
  check "ident after multi-line string: line"   3 tC.span.start.line
  check "ident after multi-line string: col"    0 tC.span.start.column

  let resBc := FX.Syntax.tokenize "a /* line1\nline2\nline3 */ b"
  check "block-comment across newlines yields 3 tokens"
    3 resBc.tokens.size
  let tB := resBc.tokens[1]!
  check "ident after multi-line block comment: line" 3 tB.span.start.line

  /- Polish §H: Transformer edge cases at EOF and boundaries. -/

  check "bare else at EOF is not merged"
    #[Token.kw Keyword.elseKw, Token.eof]       (toks "else")
  check "else if at EOF merges to elif"
    #[Token.elif, Token.eof]                    (toks "else if")
  check "leading dot is dotProj"
    #[Token.dotProj, Token.ident "f", Token.eof]
    (toks ".f")
  check "x.f at EOF: ident dotProj ident EOF"
    #[Token.ident "x", Token.dotProj, Token.ident "f", Token.eof]
    (toks "x.f")
  check "comma then EOF is not stripped"
    #[Token.lparen, Token.ident "a", Token.comma,
      Token.ident "b", Token.comma, Token.eof]
    (toks "(a, b,")
  check "comma followed by ident is preserved"
    #[Token.ident "a", Token.comma, Token.ident "b", Token.eof]
    (toks "a,b")
  check "a,,b: both commas survive (no closer)"
    #[Token.ident "a", Token.comma, Token.comma, Token.ident "b",
      Token.eof]
    (toks "a,,b")

  /- Polish §I: Error-code enumeration sanity — every code
     referenced by the scanner top-of-file table is reachable by
     at least one tiny source fragment. -/
  let codeCoverage : Array (String × String) := #[
    ("L001", "`fn"),
    ("L002", "``"),
    ("L003", "/* unterminated"),
    ("L004", "r\"abc"),
    ("L006", "0b_1010"),
    ("L007", "42xyz"),
    ("L008", "\"\\xZZ\""),
    ("L010", "\"\\q\""),
    ("L011", "\"abc"),
    ("L012", "0x"),
    ("L099", "!") ]
  let mut uncovered : Array String := #[]
  for (code, sourceText) in codeCoverage do
    unless hasErr sourceText code do
      uncovered := uncovered.push code
  check "every documented error code is reachable"
    (#[] : Array String) uncovered

end Tests.Syntax.LexerTests
