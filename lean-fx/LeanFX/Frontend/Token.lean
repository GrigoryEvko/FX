namespace LeanFX.Frontend

/-! # Indexed tokens

The token layer is the first frontend boundary: every token carries a
span indexed by the source byte length, so out-of-source positions are
unrepresentable. -/

/-- A byte position inside a source buffer. -/
structure SourcePos (sourceLength : Nat) where
  byteOffset : Fin sourceLength
deriving DecidableEq

/-- A token span whose endpoints are inside the source and ordered. -/
structure TokenSpan (sourceLength : Nat) where
  startPos : SourcePos sourceLength
  stopPos : SourcePos sourceLength
  isOrdered : startPos.byteOffset ≤ stopPos.byteOffset
deriving DecidableEq

/-- Global keywords from `fx_grammar.md` section 2.2. -/
inductive Keyword where
  | affine | and | as | assert | await
  | axiom | begin | bench | bisimulation | break
  | by | calc | catch | class | code
  | comptime | const | continue | codata | contract
  | decreases | decorator | declassify | defer | dimension
  | drop | dual | effect | else | endKeyword
  | errdefer | exception | exists | exports | extern
  | falseKeyword | fn | forKeyword | forall | ghost
  | handle | hint | ifKeyword | impl | inKeyword
  | include | instance | is | label | layout
  | lemma | letKeyword | linear | machine | matchKeyword
  | moduleKeyword | mut | not | openKeyword | or
  | own | post | pre | proof | pub
  | quotient | receive | recKeyword | ref | refinement
  | returnKeyword | sanitize | secret | select | self
  | send | session | sorry | spawn | taintClass
  | tainted | test | trueKeyword | try | typeKeyword
  | unfold | val | verify | whileKeyword | withKeyword
  | whereKeyword | yieldKeyword
deriving DecidableEq

/-- Contextual keywords are lexed as identifiers and promoted by the parser. -/
inductive ContextualKeyword where
  | refines | via
  | hardware | pipeline | stage | registerFile | wire | reg
  | rising | falling | emit | stall | flush | forward
  | redirect | onehot | field | virtual | drivenBy | whenKeyword
  | writeOrder | at | rw | ro | wo | w1c | w1s | rc | rs | rsvd
  | sized | structKeyword
  | state | transition | initial | terminal | emits | onEvent | onSignal
  | priority | concurrency | atomic | idempotent | commutative | inverse
  | onFail | after | cancels | preempts | actor | rollback
  | goto | stay | recoverable | critical | requires | ensures | from
  | version | migration | compatibility | access | format | invariant
  | errors | add | remove | rename | defaultKeyword
  | multishot | subsumes | law
  | assertErr | assertWithin | assertRaises | caseKeyword
  | expectCompileError | expectAccepted | matches
  | testMachine | testContract | testTheory | testMetatheory
deriving DecidableEq

/-- Identifier class after maximal-munch scanning and keyword lookup. -/
inductive IdentifierKind where
  | lower
  | upper
  | escaped
  | contextual (keyword : ContextualKeyword)
deriving DecidableEq

/-- Numeric literal categories from the lexer spec. -/
inductive NumericKind where
  | integer
  | typedInteger
  | decimal
  | typedDecimal
  | typedFloat
  | ternary
  | typedTernary
deriving DecidableEq

/-- String literal categories from the lexer spec. -/
inductive StringKind where
  | ordinary
  | format
  | raw
  | bytes
deriving DecidableEq

/-- Symbolic operators. Logical operators are keywords, not symbols. -/
inductive Operator where
  | plus | minus | star | slash | percent
  | equalsEquals | bangEquals | lessThan | greaterThan
  | lessEquals | greaterEquals
  | ampersand | pipe | caret | tilde | shiftLeft | shiftRight
  | arrow | fatArrow | rangeExclusive | rangeInclusive
  | spread | pipeForward | dot
deriving DecidableEq

/-- Delimiters and punctuation that are not operators. -/
inductive Punctuation where
  | leftParen | rightParen
  | leftBracket | rightBracket
  | leftBrace | rightBrace
  | colon | semicolon | comma | equal | hash | at | attributeStart
deriving DecidableEq

/-- Comment token categories. Comments can be preserved for tooling even
when later parser phases ignore them. -/
inductive CommentKind where
  | line
  | block
  | documentation
deriving DecidableEq

/-- Tokens indexed by source byte length. The lexer may preserve
whitespace and comments so printer roundtrips can be stated exactly. -/
inductive Token : Nat → Type
  | identifier : {sourceLength : Nat} →
      (span : TokenSpan sourceLength) →
      (kind : IdentifierKind) →
      (text : String) →
      Token sourceLength
  | numeric : {sourceLength : Nat} →
      (span : TokenSpan sourceLength) →
      (kind : NumericKind) →
      (text : String) →
      Token sourceLength
  | stringLiteral : {sourceLength : Nat} →
      (span : TokenSpan sourceLength) →
      (kind : StringKind) →
      (text : String) →
      Token sourceLength
  | keyword : {sourceLength : Nat} →
      (span : TokenSpan sourceLength) →
      (keyword : Keyword) →
      Token sourceLength
  | operator : {sourceLength : Nat} →
      (span : TokenSpan sourceLength) →
      (operator : Operator) →
      Token sourceLength
  | punctuation : {sourceLength : Nat} →
      (span : TokenSpan sourceLength) →
      (punctuation : Punctuation) →
      Token sourceLength
  | whitespace : {sourceLength : Nat} →
      (span : TokenSpan sourceLength) →
      (text : String) →
      Token sourceLength
  | comment : {sourceLength : Nat} →
      (span : TokenSpan sourceLength) →
      (kind : CommentKind) →
      (text : String) →
      Token sourceLength
deriving DecidableEq

namespace SmokeTestToken

/-- A one-byte source position. -/
def singleByteStart : SourcePos 1 :=
  ⟨⟨0, Nat.zero_lt_succ 0⟩⟩

/-- A one-byte token span. -/
def singleByteSpan : TokenSpan 1 where
  startPos := singleByteStart
  stopPos := singleByteStart
  isOrdered := Nat.le_refl 0

/-- The keyword `fn` as a token. -/
example : Token 1 :=
  Token.keyword singleByteSpan Keyword.fn

/-- An identifier token with its source span. -/
example : Token 1 :=
  Token.identifier singleByteSpan IdentifierKind.lower "x"

/-- A decimal literal token. -/
example : Token 1 :=
  Token.numeric singleByteSpan NumericKind.integer "0"

end SmokeTestToken

end LeanFX.Frontend
