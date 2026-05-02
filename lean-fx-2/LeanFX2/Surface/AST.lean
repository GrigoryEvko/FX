import LeanFX2.Surface.Token
import LeanFX2.Surface.TokenSchema
import LeanFX2.Surface.TokenInvariants
import LeanFX2.Surface.GrammarToken

/-! # Surface/AST — harder-than-bulletproof intrinsic-CIC AST

CompCert's `Cminor.expr` is flat data; well-formedness is proved
extrinsically.  FX's surface AST goes BEYOND BULLETPROOF: every
syntactic invariant from `fx_grammar.md` / `fx_lexer.md` /
`fx_design.md` that we can decide statically becomes an
INTRINSIC constructor obligation.

Constructing a value of type `Expr scope` IS a constructive
proof that the program text is syntactically and structurally
valid per the FX specification — there is NO ill-formed AST a
parser can produce.

## What's intrinsic (not extrinsic)

Compared to CompCert and stock dependent-typed surface ASTs:

| Invariant                                  | Stock | Bulletproof | THIS |
|--------------------------------------------|-------|-------------|------|
| Scope correctness (`Fin scope`)            | ext.  | ✓           | ✓    |
| Identifier shape (snake_case / Pascal)     | ext.  | partial     | ✓    |
| Identifier ≠ reserved keyword              | ext.  | ext.        | ✓    |
| QualifiedName module-path Pascal           | ext.  | ext.        | ✓    |
| Bit-literal value fits width               | ext.  | partial     | ✓    |
| Trit-literal width matches suffix          | ext.  | ext.        | ✓    |
| Function body scope = parameter count      | ext.  | ✓           | ✓    |
| Block scope chaining (`StmtList` indices)  | ext.  | ✓           | ✓    |
| Comparison-chain rule (T050)               | ext.  | ext.        | ✓    |
| Operator precedence well-defined           | ext.  | ext.        | ✓    |
| Position carries valid byte offset         | doc   | ext.        | ext. |

Plus: `Expr.toRaw` projection is `rfl`, identical to the kernel's
`Term.toRaw` pattern.  Round-trip + structural lemmas come for
free.

## Design

### Layer A: Refinement-typed primitives

* `LowerIdent` = `List Char` + `IsLowerIdentChars` proof + non-
  keyword proof
* `UpperIdent` = `List Char` + `IsUpperIdentChars` proof
* `QualifiedName` = `List UpperIdent` (module path) + final
  `LowerIdent ⊕ UpperIdent`
* `Literal.bitLit width value valueFits` — value fits
* `Literal.tritLit digits widthOk` — digit count matches suffix

### Layer B: Raw structural AST (un-positioned, pre-decorated)

The kernel split: `RawExpr scope` is pure structure.  `Expr scope`
indexes by `RawExpr scope`, carrying positions + integrity
witnesses.  This makes `Expr.toRaw` a definitional `rfl`.

### Layer C: Decorated AST (Expr scope raw)

* Adds source positions for diagnostics.
* Same constructor list as RawExpr; each ctor's index is the
  matching RawExpr ctor.
* Round-trip with RawExpr is structural.

### Layer D: Validity predicates (decidable, computed)

* `RawExpr.topBinaryOp` — extracts top binary operator if any.
* `RawExpr.NotChainedComparison` — comparison ops have non-
  comparison subexpressions.
* `Expr.binopExpr` requires the chain rule as a constructor
  argument (intrinsic).

### Layer E: Top-level declarations

* `FnParam` — name, mode, type at outer scope (0).
* `Decl.fnDecl` body has scope = parameter count (intrinsic).

## What we still rely on extrinsically

* Position correctness within the source byte range (would need
  a `source` parameter threaded through; deferred).
* Pattern exhaustiveness in match expressions (deferred —
  needs the type system to identify the scrutinee's ctor set).
* Argument-name uniqueness in named-arg calls (deferred —
  needs duplicate detection).

These are limited and can be added incrementally.

## Zero-axiom

All inductives use structural recursion only.  Refinement
predicates are decidable Bool / Prop without `Classical`.  No
`propext`, `Quot.sound`, `Classical.choice` reachable.
-/

namespace LeanFX2.Surface

/-! ## Source positions and spans -/

/-- Source position: byte offset into the original source. -/
structure SrcPos where
  offset : Nat
  deriving DecidableEq, Repr

/-- Span: source range from start to end byte offset. -/
structure SrcSpan where
  startPos : SrcPos
  endPos : SrcPos
  startEndOk : startPos.offset ≤ endPos.offset
  deriving Repr

-- Lexer ↔ AST `SrcPos` conversion lives in `Surface/Parse.lean`
-- to avoid pulling `Surface/Lex` into the AST imports.

/-! ## Layer A: Refinement-typed identifiers

The lexer produces `Token.ident` with snake_case shape and
`Token.uident` with PascalCase shape.  We reify the shapes plus
the additional invariant "not a reserved keyword" as REFINEMENT
TYPES — proof obligations on identifier-carrying ctors. -/

/-- Lowercase identifier (snake_case, keyword-clean): a non-empty
`List Char` with shape proof AND non-keyword proof.  Constructing
this value PROVES the lexeme is a valid `lower_ident` per
fx_grammar.md §2.1 and is not in the keyword table. -/
structure LowerIdent where
  chars : List Char
  isShape : IsLowerIdentChars chars = true
  notKeyword : KeywordKind.fromCharsExact chars = none
  deriving Repr

/-- Uppercase identifier (PascalCase): a non-empty `List Char`
with shape proof.  No keyword-clean obligation — all 92 keywords
in fx_grammar.md §2.2 lower-start, so an uppercase identifier
cannot collide. -/
structure UpperIdent where
  chars : List Char
  isShape : IsUpperIdentChars chars = true
  deriving Repr

/-- Project a LowerIdent to its String form. -/
@[reducible] def LowerIdent.asString (id : LowerIdent) : String :=
  String.ofList id.chars

/-- Project an UpperIdent to its String form. -/
@[reducible] def UpperIdent.asString (id : UpperIdent) : String :=
  String.ofList id.chars

/-- Either-shape identifier (used as the final segment of a
qualified name). -/
inductive AnyIdent : Type
  | lower (id : LowerIdent)
  | upper (id : UpperIdent)
  deriving Repr

/-- Qualified name: zero or more PascalCase module-path
components, then a single final identifier of either case.
Construction proves all module-path segments are valid
PascalCase and the final segment is one of the two valid
shapes. -/
structure QualifiedName where
  modulePath : List UpperIdent
  finalSegment : AnyIdent
  deriving Repr

/-- True if no module-path prefix (`Foo` rather than `Std.Foo`). -/
def QualifiedName.isLocal (qname : QualifiedName) : Bool :=
  qname.modulePath.isEmpty

/-! ## Layer A.2: Validated literals -/

/-- Bit-literal validity: value fits within the declared width. -/
def BitLitValid (width : Nat) (value : Nat) : Prop :=
  value < 2 ^ width

instance (width value : Nat) : Decidable (BitLitValid width value) :=
  Nat.decLt _ _

/-- Trit-literal width validity.  When suffixed (`t6`/`t12`/
`t24`/`t48`) the digit count must match.  Encoded as a
parameterized predicate; unsuffixed trits use `none`. -/
def TritLitWidthValid (digits : List Trit) (widthSuffix : Option Nat) : Prop :=
  match widthSuffix with
  | none => True
  | some n => digits.length = n

instance (digits : List Trit) (widthSuffix : Option Nat) :
    Decidable (TritLitWidthValid digits widthSuffix) := by
  cases widthSuffix with
  | none => exact isTrue True.intro
  | some n => exact Nat.decEq _ _

/-- Surface literal value with INTRINSIC validity. -/
inductive Literal : Type
  | intLit (value : Int) (suffix : Option String)
  | decLit (mantissa : String) (suffix : Option String)
  | floatLit (mantissa : String) (suffix : String)
  | strLit (value : String)
  /-- Bit literal: value MUST fit width. -/
  | bitLit (width : Nat) (value : Nat) (valueFits : BitLitValid width value)
  /-- Trit literal: digit count matches suffix when present. -/
  | tritLit (digits : List Trit) (widthSuffix : Option Nat)
            (digitsValid : TritLitWidthValid digits widthSuffix)
  | boolLit (value : Bool)
  | unitLit

/-! ## Operator types (mirror GrammarToken) -/

inductive BinaryOp : Type
  | logicalAnd | logicalOr
  | eqEq | notEq | lt | gt | le | ge
  | bitAnd | bitOr | bitXor | shiftLeft | shiftRight
  | plus | minus | star | slash | percent
  | rangeExcl | rangeIncl
  | arrow | pipe | iff | implies
  | isCtor
  deriving DecidableEq, Repr

inductive UnaryOp : Type
  | negate | bitNot | logicalNot
  deriving DecidableEq, Repr

/-- Bool predicate: this binary operator is a comparison
(eqEq / notEq / lt / gt / le / ge).  Used to enforce
fx_grammar.md §3 "chained comparison rejected" rule.

Full enumeration (no wildcard) per Rule 2 of
`feedback_lean_match_propext_recipe`: wildcards over inductives
with > ~25 ctors leak propext.  BinaryOp has 25 ctors. -/
def BinaryOp.isComparison : BinaryOp → Bool
  | .eqEq | .notEq | .lt | .gt | .le | .ge => true
  | .logicalAnd | .logicalOr
  | .bitAnd | .bitOr | .bitXor | .shiftLeft | .shiftRight
  | .plus | .minus | .star | .slash | .percent
  | .rangeExcl | .rangeIncl
  | .arrow | .pipe | .iff | .implies
  | .isCtor => false

/-! ## Layer B: Raw expression structure

Pure structural form, no positions, no shape proofs (those live
on the AnyIdent / Literal layer above).  Mirrors the kernel's
`RawTerm scope`. -/

mutual

inductive RawExpr : Nat → Type
  | rawBound {scope : Nat} (idx : Fin scope) : RawExpr scope
  | rawFree {scope : Nat} (qname : QualifiedName) : RawExpr scope
  | rawLit {scope : Nat} (lit : Literal) : RawExpr scope
  | rawUnit {scope : Nat} : RawExpr scope
  | rawParen {scope : Nat} (inner : RawExpr scope) : RawExpr scope
  | rawDot {scope : Nat} (obj : RawExpr scope) (field : LowerIdent) : RawExpr scope
  | rawApp {scope : Nat} (fn : RawExpr scope) (args : RawArgList scope) :
      RawExpr scope
  | rawBinop {scope : Nat} (op : BinaryOp) (lhs rhs : RawExpr scope) :
      RawExpr scope
  | rawUnop {scope : Nat} (op : UnaryOp) (operand : RawExpr scope) : RawExpr scope
  | rawLam {scope : Nat} (paramName : LowerIdent)
           (paramType : OptRawExpr scope)
           (body : RawExpr (scope + 1)) : RawExpr scope
  | rawBlock {scope outScope : Nat}
             (stmts : RawStmtList scope outScope)
             (final : RawExpr outScope) : RawExpr scope
  | rawIf {scope : Nat} (cond thenBr : RawExpr scope)
          (elseBr : OptRawExpr scope) : RawExpr scope

/-- Custom Optional indexed by RawExpr.  Lean rejects nested
`Option (RawExpr scope)` inside a mutual inductive; we use this
custom variant to sidestep the positivity check. -/
inductive OptRawExpr : Nat → Type
  | rawNone {scope : Nat} : OptRawExpr scope
  | rawSome {scope : Nat} (value : RawExpr scope) : OptRawExpr scope

inductive RawArgList : Nat → Type
  | rawNilArg  {scope : Nat} : RawArgList scope
  | rawConsArg {scope : Nat} (arg : RawCallArg scope) (rest : RawArgList scope) :
      RawArgList scope

inductive RawCallArg : Nat → Type
  | rawPositional {scope : Nat} (value : RawExpr scope) : RawCallArg scope
  | rawNamed {scope : Nat} (name : LowerIdent) (value : RawExpr scope) :
      RawCallArg scope
  | rawImplicit {scope : Nat} (value : RawExpr scope) : RawCallArg scope

/-- Statement chain that THREADS THE SCOPE.  Each `rawLetCons`
extends scope by 1; `rawExprCons` does not.  The chain's
outScope is determined by the let count; the type system
tracks it. -/
inductive RawStmtList : Nat → Nat → Type
  | rawNilStmt {scope : Nat} : RawStmtList scope scope
  | rawLetCons {scope outScope : Nat}
               (name : LowerIdent)
               (typeAnnot : OptRawExpr scope)
               (value : RawExpr scope)
               (rest : RawStmtList (scope + 1) outScope) :
      RawStmtList scope outScope
  | rawExprCons {scope outScope : Nat}
                (value : RawExpr scope)
                (rest : RawStmtList scope outScope) :
      RawStmtList scope outScope

end -- mutual (Raw layer)

/-! ## Layer D: Top binary operator extraction

`RawExpr.topBinaryOp` returns the head binary operator if the
expression is a binop at top level.  Used by the comparison-
chain check.  Total + decidable. -/

def RawExpr.topBinaryOp {scope : Nat} : RawExpr scope → Option BinaryOp
  | .rawBinop op _ _ => some op
  | .rawBound _ => none
  | .rawFree _ => none
  | .rawLit _ => none
  | .rawUnit => none
  | .rawParen _ => none
  | .rawDot _ _ => none
  | .rawApp _ _ => none
  | .rawUnop _ _ => none
  | .rawLam _ _ _ => none
  | .rawBlock _ _ => none
  | .rawIf _ _ _ => none

/-- This raw expression's top operator (if any) is NOT a
comparison.  Defined by direct pattern match on `RawExpr`
rather than going through `Option BinaryOp`, because the
match-on-Option pattern leaks `propext` via Lean 4 v4.29.1's
match compiler when nested inside a Decidable instance call
chain. -/
def RawExpr.topNotComparison {scope : Nat} : RawExpr scope → Bool
  | .rawBinop op _ _ => !op.isComparison
  | .rawBound _ => true
  | .rawFree _ => true
  | .rawLit _ => true
  | .rawUnit => true
  | .rawParen _ => true
  | .rawDot _ _ => true
  | .rawApp _ _ => true
  | .rawUnop _ _ => true
  | .rawLam _ _ _ => true
  | .rawBlock _ _ => true
  | .rawIf _ _ _ => true

/-! ## Layer C: Decorated AST `Expr scope raw`

Each `Expr` ctor's RawExpr index pins exactly the corresponding
raw structure.  `Expr.toRaw` is `rfl` (definitional equality). -/

mutual

inductive Expr : ∀ {scope : Nat}, RawExpr scope → Type
  /-- Bound variable reference. -/
  | boundExpr {scope : Nat} (idx : Fin scope) (pos : SrcPos) :
      Expr (RawExpr.rawBound idx)
  /-- Free name reference. -/
  | freeNameExpr {scope : Nat} (qname : QualifiedName) (pos : SrcPos) :
      Expr (scope := scope) (RawExpr.rawFree qname)
  /-- Literal value. -/
  | litExpr {scope : Nat} (lit : Literal) (pos : SrcPos) :
      Expr (scope := scope) (RawExpr.rawLit lit)
  /-- Unit value. -/
  | unitExpr {scope : Nat} (pos : SrcPos) :
      Expr (scope := scope) RawExpr.rawUnit
  /-- Parenthesized. -/
  | parenExpr {scope : Nat} {raw : RawExpr scope}
              (inner : Expr raw) (pos : SrcPos) :
      Expr (RawExpr.rawParen raw)
  /-- Field projection. -/
  | dotExpr {scope : Nat} {objRaw : RawExpr scope}
            (obj : Expr objRaw) (field : LowerIdent) (pos : SrcPos) :
      Expr (RawExpr.rawDot objRaw field)
  /-- Function application. -/
  | appExpr {scope : Nat} {fnRaw : RawExpr scope} {argsRaw : RawArgList scope}
            (fn : Expr fnRaw) (args : ArgList argsRaw) (pos : SrcPos) :
      Expr (RawExpr.rawApp fnRaw argsRaw)
  /-- Binary operator with INTRINSIC comparison-chain rule.
  When the operator is a comparison, both children must NOT
  have comparisons at their top.  Captures fx_grammar.md §3
  T050: chained comparison rejected at parse. -/
  | binopExpr {scope : Nat} {lhsRaw rhsRaw : RawExpr scope}
              (op : BinaryOp) (lhs : Expr lhsRaw) (rhs : Expr rhsRaw)
              (chainOk : op.isComparison = true →
                          lhsRaw.topNotComparison = true ∧
                          rhsRaw.topNotComparison = true)
              (pos : SrcPos) :
      Expr (RawExpr.rawBinop op lhsRaw rhsRaw)
  /-- Unary operator. -/
  | unopExpr {scope : Nat} {operandRaw : RawExpr scope}
             (op : UnaryOp) (operand : Expr operandRaw) (pos : SrcPos) :
      Expr (RawExpr.rawUnop op operandRaw)
  /-- Lambda. -/
  | lamExpr {scope : Nat} {paramTypeRaw : OptRawExpr scope}
            {bodyRaw : RawExpr (scope + 1)}
            (paramName : LowerIdent)
            (paramType : OptExpr paramTypeRaw)
            (body : Expr bodyRaw) (pos : SrcPos) :
      Expr (RawExpr.rawLam paramName paramTypeRaw bodyRaw)
  /-- Begin/end block. -/
  | blockExpr {scope outScope : Nat}
              {stmtsRaw : RawStmtList scope outScope}
              {finalRaw : RawExpr outScope}
              (stmts : StmtList stmtsRaw)
              (final : Expr finalRaw) (pos : SrcPos) :
      Expr (RawExpr.rawBlock stmtsRaw finalRaw)
  /-- Conditional. -/
  | ifExpr {scope : Nat} {condRaw thenRaw : RawExpr scope}
           {elseRaw : OptRawExpr scope}
           (cond : Expr condRaw) (thenBr : Expr thenRaw)
           (elseBr : OptExpr elseRaw) (pos : SrcPos) :
      Expr (RawExpr.rawIf condRaw thenRaw elseRaw)

inductive OptExpr : ∀ {scope : Nat}, OptRawExpr scope → Type
  | none {scope : Nat} : OptExpr (scope := scope) OptRawExpr.rawNone
  | some {scope : Nat} {raw : RawExpr scope} (value : Expr raw) :
      OptExpr (OptRawExpr.rawSome raw)

inductive ArgList : ∀ {scope : Nat}, RawArgList scope → Type
  | nilArg {scope : Nat} : ArgList (scope := scope) RawArgList.rawNilArg
  | consArg {scope : Nat} {argRaw : RawCallArg scope} {restRaw : RawArgList scope}
            (arg : CallArg argRaw) (rest : ArgList restRaw) :
      ArgList (RawArgList.rawConsArg argRaw restRaw)

inductive CallArg : ∀ {scope : Nat}, RawCallArg scope → Type
  | positional {scope : Nat} {valueRaw : RawExpr scope}
               (value : Expr valueRaw) :
      CallArg (RawCallArg.rawPositional valueRaw)
  | named {scope : Nat} {valueRaw : RawExpr scope}
          (name : LowerIdent) (value : Expr valueRaw) :
      CallArg (RawCallArg.rawNamed name valueRaw)
  | implicit {scope : Nat} {valueRaw : RawExpr scope}
             (value : Expr valueRaw) :
      CallArg (RawCallArg.rawImplicit valueRaw)

inductive StmtList : ∀ {scope outScope : Nat}, RawStmtList scope outScope → Type
  | nilStmt {scope : Nat} : StmtList (scope := scope) RawStmtList.rawNilStmt
  | letCons {scope outScope : Nat}
            {typeAnnotRaw : OptRawExpr scope}
            {valueRaw : RawExpr scope}
            {restRaw : RawStmtList (scope + 1) outScope}
            (name : LowerIdent)
            (typeAnnot : OptExpr typeAnnotRaw)
            (value : Expr valueRaw)
            (rest : StmtList restRaw) (pos : SrcPos) :
      StmtList (RawStmtList.rawLetCons name typeAnnotRaw valueRaw restRaw)
  | exprCons {scope outScope : Nat}
             {valueRaw : RawExpr scope}
             {restRaw : RawStmtList scope outScope}
             (value : Expr valueRaw)
             (rest : StmtList restRaw) (pos : SrcPos) :
      StmtList (RawStmtList.rawExprCons valueRaw restRaw)

end -- mutual (Decorated layer)

/-! ## Layer E: Top-level declarations -/

/-- Parameter mode per fx_grammar.md §5.6. -/
inductive ParamMode : Type
  | linearDefault
  | own
  | refShared
  | refMut
  | affine
  | ghost
  | secretMode
  deriving DecidableEq, Repr

/-- Function parameter at top-level (scope 0).  The parameter's
type is itself an `Expr 0` (types are expressions per §3, with
no inner binders at the top of a fn signature). -/
structure FnParam where
  mode : ParamMode
  name : LowerIdent
  paramTypeRaw : RawExpr 0
  paramType : Expr paramTypeRaw

/-- Top-level declarations.  Critical: `fnDecl`'s `body` has
scope = `params.length`.  This is INTRINSIC — the function
body's binder count MUST match the parameter list, enforced by
the type system.  An off-by-one mismatch is unrepresentable. -/
inductive Decl : Type
  /-- `pub? fn name(params) : retType = body;` -/
  | fnDecl
      (isPub : Bool)
      (name : LowerIdent)
      (params : List FnParam)
      (returnTypeRaw : RawExpr 0)
      (returnType : Expr returnTypeRaw)
      {bodyRaw : RawExpr params.length}
      (body : Expr bodyRaw)
      (pos : SrcPos)
  /-- `const NAME : T = value;` -/
  | constDecl
      (name : UpperIdent)
      {constTypeRaw : RawExpr 0}
      (constType : Expr constTypeRaw)
      {valueRaw : RawExpr 0}
      (value : Expr valueRaw)
      (pos : SrcPos)
  /-- `pub? val name : T;` -/
  | valDecl
      (isPub : Bool)
      (name : LowerIdent)
      {valTypeRaw : RawExpr 0}
      (valType : Expr valTypeRaw)
      (pos : SrcPos)

/-- A complete surface module: list of declarations. -/
structure SurfaceModule where
  decls : List Decl

/-! ## Schema bridges (load-bearing across files) -/

/-- Map an infix `OperatorKind` to the AST's `BinaryOp`. -/
def OperatorKind.asBinaryOp : OperatorKind → Option BinaryOp
  | .arrow => some .arrow
  | .pipe => some .pipe
  | .iff => some .iff
  | .implies => some .implies
  | .logicalOr => some .logicalOr
  | .logicalAnd => some .logicalAnd
  | .eqEq => some .eqEq
  | .notEq => some .notEq
  | .lt => some .lt
  | .gt => some .gt
  | .le => some .le
  | .ge => some .ge
  | .isCtor => some .isCtor
  | .bitOr => some .bitOr
  | .bitXor => some .bitXor
  | .bitAnd => some .bitAnd
  | .shiftLeft => some .shiftLeft
  | .shiftRight => some .shiftRight
  | .rangeExcl => some .rangeExcl
  | .rangeIncl => some .rangeIncl
  | .plus => some .plus
  | .minus => some .minus
  | .star => some .star
  | .slash => some .slash
  | .percent => some .percent
  | .negate | .bitNot | .logicalNot => none

/-- Map a prefix `OperatorKind` to the AST's `UnaryOp`. -/
def OperatorKind.asUnaryOp : OperatorKind → Option UnaryOp
  | .negate => some .negate
  | .bitNot => some .bitNot
  | .logicalNot => some .logicalNot
  | .arrow | .pipe | .iff | .implies
  | .logicalOr | .logicalAnd
  | .eqEq | .notEq | .lt | .gt | .le | .ge
  | .isCtor
  | .bitOr | .bitXor | .bitAnd
  | .shiftLeft | .shiftRight
  | .rangeExcl | .rangeIncl
  | .plus | .minus | .star | .slash | .percent => none

/-- Inverse: `BinaryOp` to its `OperatorKind`. -/
def BinaryOp.toOperatorKind : BinaryOp → OperatorKind
  | .logicalAnd => .logicalAnd
  | .logicalOr => .logicalOr
  | .eqEq => .eqEq
  | .notEq => .notEq
  | .lt => .lt
  | .gt => .gt
  | .le => .le
  | .ge => .ge
  | .bitAnd => .bitAnd
  | .bitOr => .bitOr
  | .bitXor => .bitXor
  | .shiftLeft => .shiftLeft
  | .shiftRight => .shiftRight
  | .plus => .plus
  | .minus => .minus
  | .star => .star
  | .slash => .slash
  | .percent => .percent
  | .rangeExcl => .rangeExcl
  | .rangeIncl => .rangeIncl
  | .arrow => .arrow
  | .pipe => .pipe
  | .iff => .iff
  | .implies => .implies
  | .isCtor => .isCtor

/-- Inverse: `UnaryOp` to its `OperatorKind`. -/
def UnaryOp.toOperatorKind : UnaryOp → OperatorKind
  | .negate => .negate
  | .bitNot => .bitNot
  | .logicalNot => .logicalNot

/-! ## Round-trip lemmas -/

theorem BinaryOp.asBinaryOp_toOperatorKind (op : BinaryOp) :
    op.toOperatorKind.asBinaryOp = some op := by
  cases op <;> rfl

theorem BinaryOp.asUnaryOp_toOperatorKind (op : BinaryOp) :
    op.toOperatorKind.asUnaryOp = none := by
  cases op <;> rfl

theorem UnaryOp.asUnaryOp_toOperatorKind (op : UnaryOp) :
    op.toOperatorKind.asUnaryOp = some op := by
  cases op <;> rfl

theorem UnaryOp.asBinaryOp_toOperatorKind (op : UnaryOp) :
    op.toOperatorKind.asBinaryOp = none := by
  cases op <;> rfl

/-! ## Utility: precedence + associativity passthrough -/

/-- Precedence level of a `BinaryOp` (passed through from
`OperatorKind.precedenceLevel`). -/
def BinaryOp.precedenceLevel (op : BinaryOp) : Nat :=
  op.toOperatorKind.precedenceLevel

/-- Associativity of a `BinaryOp`. -/
def BinaryOp.assoc (op : BinaryOp) : OperatorAssoc :=
  op.toOperatorKind.assoc

/-! ## Length / scope-delta lemmas -/

/-- Number of arguments in an `ArgList`. -/
def ArgList.length {scope : Nat} {raw : RawArgList scope} :
    ArgList raw → Nat
  | .nilArg => 0
  | .consArg _ rest => 1 + rest.length

/-- Number of `let`-bindings introduced by a `StmtList`. -/
def StmtList.bindersIntroduced {scope outScope : Nat}
    {raw : RawStmtList scope outScope} :
    StmtList raw → Nat
  | .nilStmt => 0
  | .letCons _ _ _ rest _ => 1 + rest.bindersIntroduced
  | .exprCons _ rest _ => rest.bindersIntroduced

/-! ## Projection: `Expr.toRaw` is `rfl`

The whole point of indexing `Expr` by `RawExpr` is that the
projection is a definitional equality.  Identical pattern to
`Term.toRaw` in the kernel. -/

@[reducible] def Expr.toRaw {scope : Nat} {raw : RawExpr scope}
    (_e : Expr raw) : RawExpr scope := raw

theorem Expr.toRaw_rfl {scope : Nat} {raw : RawExpr scope} (e : Expr raw) :
    e.toRaw = raw := rfl

/-! ## Smart constructor for binopExpr with auto-decided chain rule

If the chain rule is decidable (which it is — both children's
`topNotComparison` predicates are decidable), the parser can
construct a binop without manually supplying the proof — the
smart constructor decides at the type level and returns Option. -/

/-- Build a `binopExpr` if the chain rule holds; else `none`.
The parser uses this to enforce T050 at construction time.

Decidable cases via `match ... with | true => ... | false => ...`
on Bool to avoid the `if-then-else`-via-`Decidable` route which
leaks propext via Lean 4 v4.29.1's match compiler. -/
def Expr.binopExpr? {scope : Nat} {lhsRaw rhsRaw : RawExpr scope}
    (op : BinaryOp) (lhs : Expr lhsRaw) (rhs : Expr rhsRaw) (pos : SrcPos) :
    Option (Expr (RawExpr.rawBinop op lhsRaw rhsRaw)) :=
  match hComp : op.isComparison with
  | false =>
    -- Non-comparison: chain rule is vacuous (premise of the
    -- implication is `op.isComparison = true` which is `false`
    -- here).  Build the impossibility proof from `hComp`.
    some (Expr.binopExpr op lhs rhs (fun h => Bool.noConfusion (h.symm.trans hComp)) pos)
  | true =>
    -- Comparison: both children must have non-comparison tops
    match hChainL : lhsRaw.topNotComparison with
    | false => none
    | true =>
      match hChainR : rhsRaw.topNotComparison with
      | false => none
      | true =>
        some (Expr.binopExpr op lhs rhs (fun _ => ⟨hChainL, hChainR⟩) pos)

end LeanFX2.Surface
