import FX.Syntax.Span

/-!
# Tokens

The token ADT produced by `FX.Syntax.Lexer`.  Matches
`fx_grammar.md` §2 exactly (92 global keywords, the full operator
and delimiter set, six literal kinds, identifier kinds) and
`fx_lexer.md` §11 (the token summary — `IDENT UIDENT INT_LIT …
EOF`, ~120 distinct token types).  Two synthetic tokens used by
the transformer passes (`dotProj` per §8.2, `elif` per §8.1) are
included.

## Constructor naming

Every keyword constructor gets a `Kw` suffix — `affineKw`,
`fnKw`, `matchKw`, etc.  This dodges clashes with Lean 4's own
keyword set (`class`, `end`, `else`, `if`, `in`, `instance`,
`let`, `match`, `mut`, `open`, `return`, `sorry`, `true`,
`false`, `try`, `type`, `where`, `with`) and gives a uniform
visual distinction from identifiers in pattern matches.

The surface spellings are preserved in `Keyword.toString` and in
the reverse lookup `Keyword.ofString?`; only the Lean-level name
changes.

## Contextual keywords

Contextual keywords (`hardware`, `pipeline`, `state`, `field`,
`RW`, …) are **not** in this file.  They are lexed as `ident`
(or `uident`) and the parser recognizes them by position.  See
`fx_grammar.md` §2.2 "Contextual keywords".

## Synthetic tokens

  * `dotProj` — emitted by the DOT→DOT_PROJ transformer pass for
    field accesses.  Raw `dot` remains in qualified-name position
    (`Module.name`).  Per `fx_lexer.md` §8.2.
  * `elif`   — emitted by the `else if` merge pass.  Per
    `fx_lexer.md` §8.1.
-/

namespace FX.Syntax

/--
A keyword token variant.  92 values matching `fx_grammar.md`
§2.2 exactly.  Suffix `Kw` on every name to avoid Lean keyword
collisions.
-/
inductive Keyword : Type where
  | affineKw | andKw | asKw | assertKw | awaitKw
  | axiomKw | beginKw | benchKw | bisimulationKw | breakKw
  | byKw | calcKw | catchKw | classKw | codeKw
  | comptimeKw | constKw | continueKw | codataKw | contractKw
  | decreasesKw | decoratorKw | declassifyKw | deferKw | dimensionKw
  | dropKw | dualKw | effectKw | elseKw | endKw
  | errdeferKw | exceptionKw | existsKw | exportsKw | externKw
  | falseKw | fnKw | forKw | forallKw | ghostKw
  | handleKw | hintKw | ifKw | implKw | inKw
  | includeKw | instanceKw | isKw | labelKw | layoutKw
  | lemmaKw | letKw | linearKw | machineKw | matchKw
  | moduleKw | mutKw | notKw | openKw | orKw
  | ownKw | postKw | preKw | proofKw | pubKw
  | quotientKw | receiveKw | recKw | refKw | refinementKw
  | returnKw | sanitizeKw | secretKw | selectKw | selfKw
  | sendKw | sessionKw | sorryKw | spawnKw | taintClassKw
  | taintedKw | testKw | trueKw | tryKw | typeKw
  | unfoldKw | valKw | verifyKw | whileKw | withKw
  | whereKw | yieldKw
  deriving Repr, BEq, DecidableEq

namespace Keyword

/--
Map an identifier string to its keyword token, or `none` if the
string is not a keyword.  Case-sensitive per `fx_lexer.md` §3.2.
Total function; unmatched input returns `none`.

The surface spelling `taint_class` contains an underscore; the
Lean constructor is `taintClassKw`.
-/
def ofString? : String → Option Keyword
  | "affine"       => some affineKw
  | "and"          => some andKw
  | "as"           => some asKw
  | "assert"       => some assertKw
  | "await"        => some awaitKw
  | "axiom"        => some axiomKw
  | "begin"        => some beginKw
  | "bench"        => some benchKw
  | "bisimulation" => some bisimulationKw
  | "break"        => some breakKw
  | "by"           => some byKw
  | "calc"         => some calcKw
  | "catch"        => some catchKw
  | "class"        => some classKw
  | "code"         => some codeKw
  | "comptime"     => some comptimeKw
  | "const"        => some constKw
  | "continue"     => some continueKw
  | "codata"       => some codataKw
  | "contract"     => some contractKw
  | "decreases"    => some decreasesKw
  | "decorator"    => some decoratorKw
  | "declassify"   => some declassifyKw
  | "defer"        => some deferKw
  | "dimension"    => some dimensionKw
  | "drop"         => some dropKw
  | "dual"         => some dualKw
  | "effect"       => some effectKw
  | "else"         => some elseKw
  | "end"          => some endKw
  | "errdefer"     => some errdeferKw
  | "exception"    => some exceptionKw
  | "exists"       => some existsKw
  | "exports"      => some exportsKw
  | "extern"       => some externKw
  | "false"        => some falseKw
  | "fn"           => some fnKw
  | "for"          => some forKw
  | "forall"       => some forallKw
  | "ghost"        => some ghostKw
  | "handle"       => some handleKw
  | "hint"         => some hintKw
  | "if"           => some ifKw
  | "impl"         => some implKw
  | "in"           => some inKw
  | "include"      => some includeKw
  | "instance"     => some instanceKw
  | "is"           => some isKw
  | "label"        => some labelKw
  | "layout"       => some layoutKw
  | "lemma"        => some lemmaKw
  | "let"          => some letKw
  | "linear"       => some linearKw
  | "machine"      => some machineKw
  | "match"        => some matchKw
  | "module"       => some moduleKw
  | "mut"          => some mutKw
  | "not"          => some notKw
  | "open"         => some openKw
  | "or"           => some orKw
  | "own"          => some ownKw
  | "post"         => some postKw
  | "pre"          => some preKw
  | "proof"        => some proofKw
  | "pub"          => some pubKw
  | "quotient"     => some quotientKw
  | "receive"      => some receiveKw
  | "rec"          => some recKw
  | "ref"          => some refKw
  | "refinement"   => some refinementKw
  | "return"       => some returnKw
  | "sanitize"     => some sanitizeKw
  | "secret"       => some secretKw
  | "select"       => some selectKw
  | "self"         => some selfKw
  | "send"         => some sendKw
  | "session"      => some sessionKw
  | "sorry"        => some sorryKw
  | "spawn"        => some spawnKw
  | "taint_class"  => some taintClassKw
  | "tainted"      => some taintedKw
  | "test"         => some testKw
  | "true"         => some trueKw
  | "try"          => some tryKw
  | "type"         => some typeKw
  | "unfold"       => some unfoldKw
  | "val"          => some valKw
  | "verify"       => some verifyKw
  | "while"        => some whileKw
  | "with"         => some withKw
  | "where"        => some whereKw
  | "yield"        => some yieldKw
  | _              => none

/-- Surface spelling of a keyword, for diagnostics. -/
def toString : Keyword → String
  | affineKw       => "affine"
  | andKw          => "and"
  | asKw           => "as"
  | assertKw       => "assert"
  | awaitKw        => "await"
  | axiomKw        => "axiom"
  | beginKw        => "begin"
  | benchKw        => "bench"
  | bisimulationKw => "bisimulation"
  | breakKw        => "break"
  | byKw           => "by"
  | calcKw         => "calc"
  | catchKw        => "catch"
  | classKw        => "class"
  | codeKw         => "code"
  | comptimeKw     => "comptime"
  | constKw        => "const"
  | continueKw     => "continue"
  | codataKw       => "codata"
  | contractKw     => "contract"
  | decreasesKw    => "decreases"
  | decoratorKw    => "decorator"
  | declassifyKw   => "declassify"
  | deferKw        => "defer"
  | dimensionKw    => "dimension"
  | dropKw         => "drop"
  | dualKw         => "dual"
  | effectKw       => "effect"
  | elseKw         => "else"
  | endKw          => "end"
  | errdeferKw     => "errdefer"
  | exceptionKw    => "exception"
  | existsKw       => "exists"
  | exportsKw      => "exports"
  | externKw       => "extern"
  | falseKw        => "false"
  | fnKw           => "fn"
  | forKw          => "for"
  | forallKw       => "forall"
  | ghostKw        => "ghost"
  | handleKw       => "handle"
  | hintKw         => "hint"
  | ifKw           => "if"
  | implKw         => "impl"
  | inKw           => "in"
  | includeKw      => "include"
  | instanceKw     => "instance"
  | isKw           => "is"
  | labelKw        => "label"
  | layoutKw       => "layout"
  | lemmaKw        => "lemma"
  | letKw          => "let"
  | linearKw       => "linear"
  | machineKw      => "machine"
  | matchKw        => "match"
  | moduleKw       => "module"
  | mutKw          => "mut"
  | notKw          => "not"
  | openKw         => "open"
  | orKw           => "or"
  | ownKw          => "own"
  | postKw         => "post"
  | preKw          => "pre"
  | proofKw        => "proof"
  | pubKw          => "pub"
  | quotientKw     => "quotient"
  | receiveKw      => "receive"
  | recKw          => "rec"
  | refKw          => "ref"
  | refinementKw   => "refinement"
  | returnKw       => "return"
  | sanitizeKw     => "sanitize"
  | secretKw       => "secret"
  | selectKw       => "select"
  | selfKw         => "self"
  | sendKw         => "send"
  | sessionKw      => "session"
  | sorryKw        => "sorry"
  | spawnKw        => "spawn"
  | taintClassKw   => "taint_class"
  | taintedKw      => "tainted"
  | testKw         => "test"
  | trueKw         => "true"
  | tryKw          => "try"
  | typeKw         => "type"
  | unfoldKw       => "unfold"
  | valKw          => "val"
  | verifyKw       => "verify"
  | whileKw        => "while"
  | withKw         => "with"
  | whereKw        => "where"
  | yieldKw        => "yield"

instance : ToString Keyword := ⟨Keyword.toString⟩

/--
Is this keyword a **contextual** keyword (i.e., one that is
recognized only inside specific block kinds — `hardware`,
`state`, `field`, `RW`, …)?

Constantly `false`: the `Keyword` inductive holds only the 92
*global* keywords of `fx_grammar.md` §2.2.  Contextual keywords
(§2.2 "Contextual keywords" — `hardware`, `pipeline`, `state`,
`field`, `register_file`, `RW`, `RO`, `W1C`, `driven_by`,
`refines`, `via`, `struct`, `emits`, `on_event`, `requires`,
`ensures`, etc.) tokenize as ordinary `ident`/`uident` and are
promoted by the parser based on position.  Keeping them out of
this ADT means a function that takes a `Keyword` cannot
accidentally receive a contextual keyword — the type rules it
out.

This function exists as a witness of that invariant.  If a
contextual keyword ever creeps into the inductive, this should be
updated to return `true` for those cases; until then, its
uniform `false` documents the invariant.
-/
def isContextual (_ : Keyword) : Bool := false

end Keyword

/--
Numeric base for integer literals.  The base is carried on the
token so the parser/elaborator can reproduce the original
spelling in diagnostics.
-/
inductive IntBase : Type where
  | dec | hex | oct | bin
  deriving Repr, BEq, DecidableEq

/--
A token produced by the lexer.  The span is attached separately
in `LocatedToken` to keep this ADT focused on content.
-/
inductive Token : Type where
  -- Identifiers
  /-- `lower_ident` — variables, fields, effect variables, functions. -/
  | ident   (name : String) : Token
  /-- `upper_ident` — types, constructors, modules, classes. -/
  | uident  (name : String) : Token

  -- Keywords
  | kw (keyword : Keyword) : Token

  -- Literals
  /-- Unsuffixed integer literal; `text` is the raw slice without
      underscores; `base` records the original base. -/
  | intLit       (text : String) (base : IntBase) : Token
  /-- Integer literal with a typed suffix (`42u8`, `0xFFi64`). -/
  | typedInt     (text : String) (base : IntBase) (suffix : String) : Token
  /-- Unsuffixed decimal literal; exact arbitrary-precision. -/
  | decimalLit   (text : String) : Token
  /-- Decimal literal with `dN` suffix. -/
  | typedDecimal (text : String) (suffix : String) : Token
  /-- Decimal literal with `f32`/`f64` suffix. -/
  | typedFloat   (text : String) (suffix : String) : Token
  /-- Unsuffixed ternary literal (`0t10T`). -/
  | ternaryLit   (text : String) : Token
  /-- Ternary literal with `tN` suffix. -/
  | typedTernary (text : String) (suffix : String) : Token
  /-- Regular double-quoted string.  Escapes already processed. -/
  | stringLit    (text : String) : Token
  /-- Format string.  Raw content including `{…}` delimiters,
      unexpanded.  Transformer pass expands per `fx_lexer.md` §8.4. -/
  | fstringLit   (text : String) : Token
  /-- Raw string (`r"…"`, `r#"…"#`).  No escape processing. -/
  | rstringLit   (text : String) : Token
  /-- Byte string (`b"…"`).  Bytes only. -/
  | bstringLit   (text : String) : Token

  -- Multi-character operators
  | eqEq | neq | leq | geq | lshift | rshift
  | arrow | fatArrow | range | rangeIncl | spread
  | pipeRight | implies | iff | atLbrack

  -- Single-character operators and punctuation
  | plus | minus | star | slash | percent
  | lt | gt | equals
  | amp | pipe | caret | tilde
  | colon | semi | comma | dot | hash | at

  -- Delimiters
  | lparen | rparen | lbrack | rbrack | lbrace | rbrace

  -- Synthetic (transformer output)
  /-- Post-transform field projection `.`. -/
  | dotProj
  /-- Post-transform `else if` merge. -/
  | elif

  -- Special
  /-- Attached documentation comment (`///…`).  The content is the
      stripped body (leading `/// ` removed, lines joined with LF). -/
  | docComment (content : String) : Token
  /-- End of file — emitted exactly once at the stream tail. -/
  | eof
  deriving Repr, BEq, DecidableEq

namespace Token

/--
Is this token a literal that stands alone as an atomic expression?

Covers every `literal` production from `fx_grammar.md` §6.4 — int,
decimal, float, ternary (all suffixed and unsuffixed variants),
regular / format / raw / byte strings, boolean literals, and the
`type` keyword (accepted as the universe-literal atom in FX's
unified expression-and-type grammar).  Used by the parser's
`parseAtom` so the large alternation of literal token shapes has
one named predicate instead of a pattern disjunction inline.

Adding a new literal token kind requires adding an arm here and
an arm in the parser's literal-case.  Two edits at two known
sites is better than threading a matcher across many call sites.
-/
def isLiteralAtom : Token → Bool
  | .intLit _ _       => true
  | .typedInt _ _ _   => true
  | .decimalLit _     => true
  | .typedDecimal _ _ => true
  | .typedFloat _ _   => true
  | .ternaryLit _     => true
  | .typedTernary _ _ => true
  | .stringLit _      => true
  | .fstringLit _     => true
  | .rstringLit _     => true
  | .bstringLit _     => true
  | .kw .trueKw       => true
  | .kw .falseKw      => true
  | .kw .typeKw       => true
  | _                 => false

end Token

/--
A token together with its source span.  Lexer output is
`Array LocatedToken`.
-/
structure LocatedToken where
  token : Token
  span  : Span
  deriving Repr

/-- Default `Token` is `eof` — unreachable in a well-formed
    stream since the lexer emits EOF exactly once at the tail. -/
instance : Inhabited Token where
  default := .eof

/-- Default placeholder so `Array.get!` / `ts[i]!` can synthesize
    an `Inhabited` instance.  Returns an `eof` token at the zero
    span — unreachable in a well-formed array. -/
instance : Inhabited LocatedToken where
  default := { token := .eof, span := Span.zero }

end FX.Syntax
