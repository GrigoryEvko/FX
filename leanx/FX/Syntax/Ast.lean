import FX.Syntax.Token

/-!
# Surface AST (Phase 1 subset)

The parser produces values of the types in this file.  Matches
a strict subset of `fx_grammar.md` §5–§8 — enough to round-trip
top-level function declarations, simple `let`/`const`/`module`
declarations, and the common expression forms (variables,
literals, application, lambda, let-in, if-then-else, blocks,
binops, field access).

## What's here, what's deferred

**In**:
  * File with an array of top-level `Decl`s
  * `Decl`: moduleDecl, openDecl, constDecl, fnDecl, unimplemented
  * `Expr`: var/literal/app/lam/arrow/letBind/match/if/block/field/
    binop/prefix/tuple/unit/sorry
  * `Pattern`: wildcard/var/ctor/literal/tuple
  * `Stmt`: letStmt/exprStmt

**Deferred**:
  * Full grammar: machine/contract/hardware/codata/session/effect/
    class/instance/impl/test/bench/lemma/axiom/extern decls
  * Full expressions: comprehensions, records, try/handle/select,
    calc/verify, comptime/quote/unfold
  * Full patterns: or/as/record/list
  * Refinement types, GADT constructors, type parameters with
    kinds, variance

## Style

Everything is one `mutual` block of plain inductives.  Structures
inside `mutual` blocks don't compose well with inductives in
Lean 4.29, so we use `.mk`-style constructors and pattern-match
for field access.  Named-field accessors can be added later
once the AST stabilizes.

Every leaf node carries a `Span` as the final constructor field
— consistent placement makes error reporting mechanical.
-/

namespace FX.Syntax.Ast

open FX.Syntax

/-- An unqualified identifier carrying its source span. -/
structure Ident where
  name : String
  span : Span
  deriving Repr, Inhabited

/-- A qualified path `Module.Sub.final`.  `parts` is the
    prefix chain of upper identifiers; `final` may be upper or
    lower. -/
structure QualIdent where
  parts : Array String
  final : String
  span  : Span
  deriving Repr, Inhabited

/-- Parameter mode — `fx_design.md` §7.1. -/
inductive ParamMode : Type where
  | default_       -- linear (no explicit mode)
  | own
  | ref_
  | refMut
  | affine
  | ghost
  | secret
  | linear
  deriving Repr, BEq, DecidableEq

/-- Visibility modifier. -/
inductive Visibility : Type where
  | public_
  | private_
  deriving Repr, BEq, DecidableEq

mutual

/--
Expression node.  FX types are also expressions — there is no
separate grammar for types (`fx_grammar.md` §7).  The elaborator
distinguishes type-position uses from value-position uses.
-/
inductive Expr : Type where
  /-- A qualified or unqualified name reference. -/
  | var    (qualIdent : QualIdent)                               : Expr
  /-- The `()` unit value. -/
  | unit   (span : Span)                                         : Expr
  /-- A literal (int, decimal, string, bool, …).  The full token
      carries base/suffix information that may matter for
      elaboration. -/
  | literal (literalToken : Token) (span : Span)                 : Expr
  /-- Function application `f(arg1, arg2, …)`.  Arguments may be
      positional, named (`name: val`), or implicit type args
      (`#ty`) represented by the prefix bool. -/
  | app    (fnExpr : Expr) (args : Array CallArg) (span : Span)  : Expr
  /-- Anonymous lambda `fn (p1, p2) => body`. -/
  | lam    (params : Array LamParam) (body : Expr) (span : Span) : Expr
  /-- Function type `A -> B`. -/
  | arrow  (domain : Expr) (codomain : Expr) (span : Span)       : Expr
  /-- `let p = value in body` — expression form produced by
      parsing a tail-`let` inside a block. -/
  | letBind (pattern : Pattern) (typeAnnotation : Option Expr)
            (value : Expr) (body : Expr) (span : Span)           : Expr
  /-- `match scrutinee; pat => body; … end match`. -/
  | match_  (scrutinee : Expr) (arms : Array MatchArm) (span : Span) : Expr
  /-- `if cond; then_ else else_ end if`.  `elseIfs` holds
      additional `else if` chains; `elseBranch` is the final
      `else` body (if any). -/
  | ifExpr (cond : Expr) (thenBranch : Expr)
           (elseIfs : Array (Expr × Expr))
           (elseBranch : Option Expr) (span : Span)               : Expr
  /-- `for LOOPVAR in LO..HI; BODY end for` (task B10).  Only
      exclusive ranges (`..`) in this phase; `..=` is a future
      extension.  The elaborator desugars to `Term.indRec "Nat"`
      with a non-dependent `Unit`-returning motive and requires
      `lo` to be a literal `0` until Nat addition is threaded at
      elab time.  BODY must elaborate to `Unit`. -/
  | forRange (loopVar : String) (lo : Expr) (hi : Expr)
             (body : Expr) (span : Span)                          : Expr
  /-- `while COND; BODY end while` (task B10).  Parses but
      currently rejects at elab time with code E013, pending the
      `Div` effect + termination analysis (tasks E-3, E-6).
      Pinning the AST surface now means later wiring is a pure
      elaboration change. -/
  | whileLoop (cond : Expr) (body : Expr) (span : Span)            : Expr
  /-- `begin … end begin` block.  `tail` is the final expression
      (every block yields a value). -/
  | block  (stmts : Array Stmt) (tail : Expr) (span : Span)       : Expr
  /-- Postfix field access `obj.field`.  Uses the `dotProj` token
      produced by the lexer's DOT disambiguation. -/
  | field  (receiver : Expr) (name : String) (span : Span)        : Expr
  /-- Postfix indexing `obj[idx]`. -/
  | index  (receiver : Expr) (indexExpr : Expr) (span : Span)     : Expr
  /-- Dot shorthand `.field` in function-argument position
      (`fx_design.md` §4.2 rule 25).  Lowered by the elaborator
      to `fn(it) => it.field`. -/
  | dotShorthand (name : String) (span : Span)                    : Expr
  /-- §4.2 pipe `lhs |> rhs`.  Left-associative, lower
      precedence than `->`.  Preserved as its own AST node (not
      parse-time desugared to `Expr.app`) so diagnostics can
      cite the pipe position by name — e.g. "in pipe RHS: not
      a function" instead of the bare application error the
      synthesized app would emit.

      Elaboration rewrites to a function application with `lhs`
      prepended as positional arg 0 of the RHS's call-arg array:

        * `x |> f`                 => `f(x)`
        * `x |> f(a: va, b: vb)`   => `f(x, a: va, b: vb)`
        * `x |> f(pos1, a: va)`    => `f(x, pos1, a: va)`

      (The mixed-arg rewrite in `Elab/NamedArgs.lean` handles
      the positional-into-named promotion when `f` declares all
      params named.) -/
  | pipe   (lhs : Expr) (rhs : Expr) (span : Span)                : Expr
  /-- Binary operator; the operator is stored as its original
      token so we can round-trip to source for diagnostics. -/
  | binop  (operator : Token) (lhs : Expr) (rhs : Expr) (span : Span) : Expr
  /-- Unary prefix operator (`-`, `~`). -/
  | prefix_ (operator : Token) (operand : Expr) (span : Span)         : Expr
  /-- §2.6 logical `not`: surface `not body`.  Preserved as its
      own AST node so error messages, pretty-printers, and
      future lints can refer to the `not` keyword directly
      rather than reasoning about a synthesized `if-then-else`.
      Elaborates to `indRec Bool` with false-branch = True and
      true-branch = False. -/
  | logicalNot (body : Expr) (span : Span)                             : Expr
  /-- §2.6 logical `and`: surface `lhs and rhs`.  Left-assoc.
      Elaborates to `indRec Bool` with false-branch = False and
      true-branch = rhs (short-circuit: rhs never reduced when
      lhs is False).  Preserved as its own AST node for the
      same reason as `logicalNot`. -/
  | logicalAnd (lhs : Expr) (rhs : Expr) (span : Span)                 : Expr
  /-- §2.6 logical `or`: surface `lhs or rhs`.  Left-assoc.
      Elaborates to `indRec Bool` with false-branch = rhs and
      true-branch = True (short-circuit: rhs never reduced when
      lhs is True). -/
  | logicalOr  (lhs : Expr) (rhs : Expr) (span : Span)                 : Expr
  /-- §2.6 constructor-test `scrutinee is CTOR_REF`, returns
      `Bool.True` when the scrutinee's constructor tag matches
      `ctorRef`, `Bool.False` otherwise.  Preserved as its own
      AST node (not parse-time desugared) so diagnostics can
      cite the `is` keyword by name and future tooling can
      distinguish it from a hand-written match.

      Elaboration desugars to a two-arm match — `Ctor(_...) =>
      True` plus a wildcard catch-all `_ => False` — so the
      existing pattern-match elaborator handles ctor resolution,
      exhaustiveness, and indRec codegen uniformly. -/
  | isCheck    (scrutinee : Expr) (ctorRef : QualIdent) (span : Span)  : Expr
  /-- §2.6 propositional implies `lhs ==> rhs`.  Classical
      `lhs → rhs` ≡ `not lhs or rhs` — evaluates `rhs` only when
      `lhs` is `Bool.True`, short-circuiting to `Bool.True`
      otherwise.  Right-associative: `a ==> b ==> c` parses as
      `a ==> (b ==> c)`.

      Spec §2.6 lists `==>` as a propositional operator "used in
      `pre`/`post`/`invariant`/temporal logic."  At Phase 2 it
      elaborates to a Bool-valued `indRec "Bool"` — the
      specification layer (Prop-level reasoning) is deferred
      to the verify layer. -/
  | logicalImplies (lhs : Expr) (rhs : Expr) (span : Span)             : Expr
  /-- §2.6 propositional iff `lhs <==> rhs`.  Returns
      `Bool.True` when both sides have the same Bool value,
      `Bool.False` when they differ.  Non-chained: `a <==> b
      <==> c` emits P042 (the reading is ambiguous in the
      standard literature; explicit parenthesization required). -/
  | logicalIff (lhs : Expr) (rhs : Expr) (span : Span)                 : Expr
  /-- §3.7 list literal `[a, b, c]` — surface sugar for the
      `Cons`/`Nil` chain over the prelude `List` spec.  The
      element type is inferred from the `expected` Pi's
      `List(T)` at elab time; without an expected element
      type the elaborator emits E010 with a hint.

      Elaborates to `Cons(a, Cons(b, Cons(c, Nil)))` at the
      kernel level — `[]` becomes a bare `Nil`. -/
  | listLit (items : Array Expr) (span : Span)                         : Expr
  /-- `try EXPR` prefix form per `fx_design.md` §4.9 control-flow
      effects (task E-3).  Marks a call whose callee has `Fail(E)`
      or `Exn(E)` in its effect row; the failure propagates to
      the nearest enclosing `try-catch` handler.  Elaborator half
      (E042 emission when a Fail-effecting call appears without a
      surrounding `try`) is a follow-on — this node is parser-only
      for the moment. -/
  | tryPrefix (body : Expr) (span : Span)                         : Expr
  /-- `handle EXPR (return NAME => EXPR ;)? OP_ARM+ end handle` —
      effect handler form per `fx_design.md` §9.6 (task E-5,
      parser half).  Provides implementations for an effect's
      operations, removing it from the body's effect row.

      `returnClause` is optional: when omitted, the handler uses
      the identity return `return x => x` (§9.6 "return clause
      is optional when identity").  The arms are keyed by
      operation name and the last parameter is by convention the
      continuation `k` that the handler may invoke.

      Elaborator half (handler typing rule per §9.6 + delimited-
      continuation encoding per Appendix H or handler desugaring
      to kernel terms) is a follow-on — this node is parser-only
      for the moment and the elaborator passes through to `body`
      alone. -/
  | handleExpr (body : Expr)
               (returnClause : Option (String × Expr))
               (arms : Array HandleOpArm)
               (span : Span)                                       : Expr
  /-- Tuple literal. -/
  | tuple  (items : Array Expr) (span : Span)                     : Expr
  /-- `sorry` placeholder. -/
  | sorryExpr (span : Span)                                       : Expr
  /-- Parser placeholder for a form recognized but not yet fully
      parsed in Phase 1.  The `note` identifies which form. -/
  | unimplemented (note : String) (span : Span)                   : Expr

/-- One argument of a function call. -/
inductive CallArg : Type where
  | pos      (argExpr : Expr)                      : CallArg
  | named    (name : String) (argExpr : Expr)      : CallArg
  | implicit (argExpr : Expr)                      : CallArg

/-- A lambda parameter.  Types are optional; the elaborator
    infers from context where omitted. -/
inductive LamParam : Type where
  | plain       (name : String)                    : LamParam
  | typed       (name : String) (typeExpr : Expr)  : LamParam
  | wildcard                                       : LamParam
  | destructure (pattern : Pattern)                : LamParam

/-- One arm of a `match` expression. -/
inductive MatchArm : Type where
  | mk (pattern : Pattern) (guard : Option Expr) (body : Expr) (span : Span)
      : MatchArm

/-- One operation arm inside a `handle ... end handle` (§9.6).
    Shape: `OP_NAME(param1, ..., k) => body ;` where the last
    parameter is typically the continuation `k`.  The list of
    params uses `LamParam` so both plain and typed binders
    compose with the surrounding lambda syntax. -/
inductive HandleOpArm : Type where
  | mk (opName : String) (params : Array LamParam)
       (body : Expr) (span : Span)                               : HandleOpArm

/-- Pattern node. -/
inductive Pattern : Type where
  | wildcard  (span : Span)                                              : Pattern
  | var       (name : String) (span : Span)                              : Pattern
  | ctor      (name : QualIdent) (args : Array Pattern) (span : Span)    : Pattern
  | tuple     (items : Array Pattern) (span : Span)                      : Pattern
  | literal   (literalToken : Token) (span : Span)                       : Pattern
  | ascribed  (inner : Pattern) (typeExpr : Expr) (span : Span)          : Pattern
  /-- `pat as name` — per `fx_design.md` §4.3 / `fx_grammar.md` §8.
      Binds `name` to the scrutinee value when `inner` matches.  Parsed
      at any pattern level; the elaborator restricts where `as`
      bindings are accepted (top-of-arm-pattern only in Q84). -/
  | asPattern (inner : Pattern) (name : String) (span : Span)            : Pattern
  /-- `p1 | p2 | ... | pk` — an or-pattern, per `fx_grammar.md` §8
      rule `OrPattern = AsPattern ("|" AsPattern)*`.  Matches the
      scrutinee against each alternative in order; succeeds on first
      match.  `alternatives.size >= 2` by construction — the parser
      never emits a single-alternative or-pattern (it returns the
      inner pattern unwrapped).  Maranget's row-expansion pre-pass
      (N5) flattens these into separate matrix rows before Compile
      runs, so the matrix operations never see `orPattern` directly. -/
  | orPattern (alternatives : Array Pattern) (span : Span)               : Pattern

/-- A statement inside a block (or top-level in Phase 1 parser
    contexts where a block is expected). -/
inductive Stmt : Type where
  | letStmt  (pattern : Pattern) (typeAnnotation : Option Expr)
             (value : Expr) (span : Span)                               : Stmt
  | exprStmt (expr : Expr) (span : Span)                                : Stmt
  /-- Local fn declaration inside a block (`fn double(x: i64) : i64 =
      x * 2;`).  Per §4.7 rule 18, a local fn is `Tot` by default
      and does NOT inherit the enclosing function's effects — its
      effect row comes entirely from its own `with …` clause (or
      empty, meaning `Tot`).  Elaborates by desugaring to a let-
      binding whose value is the elaborated closure.
      Fields mirror the non-attrs/non-visibility subset of
      `Decl.fnDecl` (local fns are always private to their block
      and don't carry attribute metadata in Phase 2). -/
  | fnStmt   (name : String) (params : Array FnParam) (retType : Expr)
             (effects : Array Expr) (specs : Array SpecClause)
             (body : FnBody) (span : Span)                              : Stmt

/-- A specification clause on a fn declaration, per fx_design.md
    §5.1 ordering: `where <constraint>`, `pre <pred>`, `post
    <binder> => <pred>`, `decreases <measure>`.  Phase-2 parses
    and stores them on the fnDecl AST; the elaborator validates
    ordering and elaborates the expressions in scope of the
    fn's parameters (plus the return-value binder for `post`).
    SMT discharge lands with Stream E (E1-E4); until then the
    elaborated clauses are carried through as metadata. -/
inductive SpecClause : Type where
  /-- `where <constraint>;` — type-class constraint on a type
      parameter.  Discharged by instance resolution (M7). -/
  | whereCstr (constraint : Expr) (span : Span)                          : SpecClause
  /-- `pre <predicate>;` — precondition.  The predicate is
      evaluated in the fn's parameter scope; SMT discharges at
      every call site given the caller's context. -/
  | preCond   (predicate : Expr) (span : Span)                           : SpecClause
  /-- `post <binder> => <predicate>;` — postcondition.  `binder`
      names the return value (no magic `result`); the predicate
      is evaluated in the fn's parameter scope plus that
      binder.  Multiple `post` clauses are conjoined. -/
  | postCond  (returnBinder : String) (predicate : Expr) (span : Span)   : SpecClause
  /-- `decreases <measure>;` — termination measure.  Required on
      every `rec` fn absent `with Div`.  The measure must
      well-order in the structural order — SMT proves it
      decreases on every recursive call. -/
  | decreases (measure : Expr) (span : Span)                             : SpecClause

/-- Top-level declaration.  Phase-1 subset. -/
inductive Decl : Type where
  | moduleDecl    (path : QualIdent) (span : Span)                    : Decl
  | openDecl      (path : QualIdent) (alias_ : Option String) (span : Span) : Decl
  | includeDecl   (path : QualIdent) (span : Span)                    : Decl
  | constDecl     (name : String) (typeExpr : Expr) (value : Expr) (span : Span) : Decl
  /-- `val NAME : TYPE ;` — forward declaration per §5.10 / grammar
      §5.10.  No body; registers the name with its declared type
      so callers compile against the signature.  Trust propagates
      as `external` — release builds require an accompanying
      implementation elsewhere (Phase-6 cross-file modules). -/
  | valDecl       (name : String) (typeExpr : Expr) (span : Span)     : Decl
  /-- Function declaration.  `effects` is the parsed `with …` row
      after the return type (may be empty = `Tot`).  Each entry is
      a surface `Expr` so effect variables (`eff`), type-applied
      effects (`eff(T)`), and bare identifiers (`IO`, `State`)
      all ride through the same AST.  The elaborator's A12 check
      translates names into `Grade.Effect` for subsumption via
      the bridge in `FX/Kernel/Grade/Effect.lean`. -/
  | fnDecl        (attrs : Array Expr) (visibility : Visibility)
                  (name : String) (params : Array FnParam)
                  (retType : Expr) (effects : Array Expr)
                  (specs : Array SpecClause)
                  (body : FnBody) (span : Span)                        : Decl
  /-- `type NAME <typeParams>? VariantCtor+ end type;` — variant
      algebraic data type declaration per fx_grammar.md §5.9 and
      fx_design.md §3.3.  Elaborates to a kernel `IndSpec` registered
      on the global env's `userSpecs` so subsequent decls can
      reference `NAME` as a type and each ctor as a value.

      `attrs` captures the optional `@[...]` block parsed before
      the `type` keyword.  The elaborator recognizes `@[copy]`
      (§7.8) and propagates it to `IndSpec.isCopy`; other names
      ride through unchanged as pure metadata per §17.4 for
      future comptime-code generators. -/
  | typeDecl      (attrs : Array Expr) (name : String)
                  (typeParams : Array FnParam)
                  (ctors : Array VariantCtor) (span : Span)           : Decl
  /-- `impl TypeName fn-members end impl;` — method bundle per
      fx_design.md §16.1.  Each `member` is a regular `fnDecl`
      parsed with its own signature; the `typeName` is the
      enclosing type the methods attach to.  Phase-2 expansion
      (in `FX.Elab.checkFile`) flattens every member into a
      top-level fn named `TypeName.methodName`, preserving
      signatures end-to-end.  Dot syntax (`x.method(args)`)
      resolution (§4.10 / §16.3) is separate elab work. -/
  | implDecl      (typeName : String) (members : Array Decl)
                  (span : Span)                                        : Decl
  | sorryDecl     (span : Span)                                        : Decl
  /-- `session NAME<typeParams>? (rec LABEL;)? step+ end session;` —
      binary session-type declaration per `fx_grammar.md §11` /
      `fx_design.md §11.2`.  Parser-level (S10); elaboration to
      kernel `CoindSpec`s via `FX.Derived.Session.translate` is
      S11's job.  `recBinder` is `some LABEL` when the body opens
      with `rec LABEL;` for recursive sessions; `continueStep`s
      inside the body reference this label. -/
  | sessionDecl   (name : String) (typeParams : Array FnParam)
                  (recBinder : Option String)
                  (steps : Array SessionStep) (span : Span)            : Decl
  /-- `effect NAME<typeParams>? op+ end effect;` — user-defined
      effect declaration per `fx_grammar.md §5.12` /
      `fx_design.md §9.5`.  Task E-4 parser half: syntax +
      AST only; elaborator registration into the kernel effect
      row lands once the effect record becomes extensible
      (today's `FX.Kernel.Grade.Effect` is a fixed 8-field
      struct).  Until then the decl is parsed, pretty-printable,
      and surfaced to tools but does NOT register a new effect
      label — calls using the effect-row bump into the fixed
      built-in set at elaboration.

      `subsumes` relations (§5.12) are deferred to the
      elaborator half as well; the parser here accepts only the
      operation-signature form. -/
  | effectDecl    (name : String) (typeParams : Array FnParam)
                  (ops : Array EffectOp) (span : Span)                 : Decl
  /-- Parser placeholder for a form recognized but not yet fully
      parsed (e.g., class/instance/machine/contract/hardware). -/
  | unimplemented (note : String) (span : Span)                        : Decl

/-- A function parameter.  Simplified Phase-1 form — no default
    values, no implicit `#` params yet. -/
inductive FnParam : Type where
  | mk (mode : ParamMode) (name : String) (typeExpr : Expr) (span : Span)
      : FnParam

/-- One operation signature inside an `effect` block (§9.5).
    Operations are the capabilities a handler must implement;
    each has a name, parameter telescope, return type, and an
    optional effect row declaring which other effects the
    operation itself uses.  No body — the body is supplied by
    a handler via `handle ... op(args, k) => body ...`
    (§9.6; task E-5). -/
inductive EffectOp : Type where
  | mk (name : String) (params : Array FnParam)
       (returnType : Expr) (effects : Array Expr) (span : Span)
      : EffectOp

/-- One constructor in an ADT declaration.  `name` is PascalCase
    (lexer's UIDENT); `args` is the positional/named argument
    telescope — each entry's `name` is a synthetic `_arg_N` for
    positional args or the declared label for named-field form.
    Self-references to the enclosing type appear inside each arg's
    `typeExpr` as `.var (QualIdent.noParts typeName)`; the elaborator
    translates them into kernel self-refs. -/
inductive VariantCtor : Type where
  | mk (name : String) (args : Array FnParam) (span : Span) : VariantCtor

/-- Function body form.  Either a one-liner `= expr;` or a block
    `begin fn stmt* return expr; end fn`. -/
inductive FnBody : Type where
  | oneLiner (bodyExpr : Expr)                                      : FnBody
  | block    (stmts : Array Stmt) (returnExpr : Expr)               : FnBody

/-- One step inside a session declaration body.  Mirrors
    `fx_grammar.md §11`'s `session_step` production.  Each
    variant carries a `Span` for diagnostics.

    The AST does NOT yet resolve to `FX.Derived.Session.Binary.
    SessionType` — the elaborator (task S11) makes that bridge,
    running the payload `Expr`s through type elaboration and
    producing a `SessionType` tree that S9's translator then
    lifts to `CoindSpec`s. -/
inductive SessionStep : Type where
  /-- `send(NAME : TYPE);` — outgoing message. -/
  | sendStep     (payloadName : String) (payloadType : Expr)
                 (span : Span)                                   : SessionStep
  /-- `receive(NAME : TYPE);` — incoming message. -/
  | recvStep     (payloadName : String) (payloadType : Expr)
                 (span : Span)                                   : SessionStep
  /-- `branch ARM+ end branch;` — offer side.  Peer picks a
      labeled arm; each arm is a sub-session-step list. -/
  | branchStep   (arms : Array SessionBranchArm) (span : Span)   : SessionStep
  /-- `select ARM+ end select;` — choose side.  Structural
      dual of branch; at the AST level they differ only in the
      constructor tag. -/
  | selectStep   (arms : Array SessionBranchArm) (span : Span)   : SessionStep
  /-- `LABEL;` — reference to the enclosing `rec LABEL`
      binder.  Resolved against the session decl's `recBinder`
      at elab time. -/
  | continueStep (labelName : String) (span : Span)              : SessionStep
  /-- `end;` — session terminator (one-shot protocol complete). -/
  | endStep      (span : Span)                                   : SessionStep
  deriving Inhabited

/-- One arm of a `branch` or `select` block: `LABEL => steps*
    end;`.  `steps` is the arm's session continuation. -/
inductive SessionBranchArm : Type where
  | mk (label : String) (steps : Array SessionStep) (span : Span)
      : SessionBranchArm
  deriving Inhabited

end  -- mutual

-- Derive `Repr` on every mutual inductive individually — Lean 4.29
-- doesn't support `deriving` inside a mutual block.
deriving instance Repr for Expr
deriving instance Repr for CallArg
deriving instance Repr for LamParam
deriving instance Repr for MatchArm
deriving instance Repr for HandleOpArm
deriving instance Repr for Pattern
deriving instance Repr for Stmt
deriving instance Repr for SpecClause
deriving instance Repr for Decl
deriving instance Repr for FnParam
deriving instance Repr for VariantCtor
deriving instance Repr for FnBody
deriving instance Repr for EffectOp

-- Manual `Inhabited` instances for every mutual inductive.
-- The parser uses `partial def` for its recursive functions,
-- which requires `Inhabited` on the return type so Lean can
-- synthesize a default for the non-terminating branch.  Every
-- default below is a wildcard/stub that the parser never
-- actually constructs on a successful parse.
instance : Inhabited Expr := ⟨.unimplemented "inhabited stub" Span.zero⟩
instance : Inhabited CallArg := ⟨.pos (default : Expr)⟩
instance : Inhabited LamParam := ⟨.wildcard⟩
instance : Inhabited MatchArm :=
  ⟨.mk (Pattern.wildcard Span.zero) none (default : Expr) Span.zero⟩
instance : Inhabited HandleOpArm :=
  ⟨.mk "_" #[] (default : Expr) Span.zero⟩
instance : Inhabited Pattern := ⟨.wildcard Span.zero⟩
instance : Inhabited Stmt :=
  ⟨.exprStmt (default : Expr) Span.zero⟩
instance : Inhabited SpecClause :=
  ⟨.preCond (default : Expr) Span.zero⟩
instance : Inhabited FnParam :=
  ⟨.mk ParamMode.default_ "_" (default : Expr) Span.zero⟩
instance : Inhabited VariantCtor := ⟨.mk "_" #[] Span.zero⟩
instance : Inhabited FnBody := ⟨.oneLiner (default : Expr)⟩
instance : Inhabited EffectOp :=
  ⟨.mk "_" #[] (default : Expr) #[] Span.zero⟩
instance : Inhabited Decl := ⟨.unimplemented "inhabited stub" Span.zero⟩

/-! ## §4.2 rule 25 — dot-shorthand lifting through composable expressions

`fx_design.md` §4.2 disambig rule 25 specifies that in a
function-argument position, `.field` without a receiver is
surface sugar for `fn(it) => it.field`.  The spec explicitly
extends this across composable expressions:

> Multiple dots in the same expression refer to the SAME
> implicit element: `.active and .age >= 18` desugars to
> `fn(it) => it.active and it.age >= 18`.

Q61 landed the bare-`.field` case (where `.dotShorthand` is the
whole arg).  The lifting helpers below enable the full rule 25:
`containsDotShorthand` detects whether a composite expression
carries at least one dot deep inside; `substDotShorthand`
performs the `.field ↦ it.field` replacement so the outer
call-site can wrap the arg in a single lambda shared by every
occurrence.

## Scope boundary policy

The walk descends only through *composable* expression nodes
that don't introduce a new binder — binop, prefix, logical
not/and/or, pipe, try-prefix, if/else, field, index.  It stops
at lambdas, matches, for/while, handle-blocks, and begin-blocks;
dots inside those forms either belong to their own arg-position
scope (nested call in a lambda body) or are syntactically invalid
(dot-at-scrutinee, dot-at-loop-condition) and will surface E010
from the existing bare-`.dotShorthand` elab path.

Rationale: the spec's examples all fit the narrow "arithmetic-
and-comparison composite" pattern.  Broader scope extension
(e.g., lifting across lambda boundaries) would change implicit-
binding semantics in ways the spec doesn't explicitly sanction. -/

/-- True iff `expr` contains a `.dotShorthand` node reachable
    through composable-expression children.  See the section
    docstring above for the scope-boundary policy. -/
partial def Expr.containsDotShorthand : Expr → Bool
  | .dotShorthand _ _          => true
  | .binop _ lhs rhs _         =>
    lhs.containsDotShorthand || rhs.containsDotShorthand
  | .prefix_ _ operand _       => operand.containsDotShorthand
  | .logicalNot body _         => body.containsDotShorthand
  | .logicalAnd lhs rhs _      =>
    lhs.containsDotShorthand || rhs.containsDotShorthand
  | .logicalOr  lhs rhs _      =>
    lhs.containsDotShorthand || rhs.containsDotShorthand
  | .pipe       lhs rhs _      =>
    lhs.containsDotShorthand || rhs.containsDotShorthand
  | .tryPrefix  body _         => body.containsDotShorthand
  | .ifExpr     cond thenBranch elsifs elseOpt _ =>
    cond.containsDotShorthand
    || thenBranch.containsDotShorthand
    || elsifs.any (fun (c, b) => c.containsDotShorthand || b.containsDotShorthand)
    || (match elseOpt with
        | some elseExpr => elseExpr.containsDotShorthand
        | none          => false)
  | .field      receiver _ _   => receiver.containsDotShorthand
  | .index      receiver idx _ =>
    receiver.containsDotShorthand || idx.containsDotShorthand
  | .isCheck    scrutinee _ _  => scrutinee.containsDotShorthand
  | .logicalImplies lhs rhs _  =>
    lhs.containsDotShorthand || rhs.containsDotShorthand
  | .logicalIff lhs rhs _      =>
    lhs.containsDotShorthand || rhs.containsDotShorthand
  | _                          => false

/-- Replace every `.dotShorthand name span` node reachable
    through composable children with `.field (.var itName)
    name span` — the implicit-element's field access.  Used by
    the call-arg elab to lift a dot-containing argument into
    `fn(itName) => substituted_expr` when the formal param type
    is a Pi.  Stops at the same scope boundaries as
    `containsDotShorthand`. -/
partial def Expr.substDotShorthand (itName : String) : Expr → Expr
  | .dotShorthand fieldName fieldSpan =>
    let itIdent : QualIdent :=
      { parts := #[], final := itName, span := fieldSpan }
    .field (.var itIdent) fieldName fieldSpan
  | .binop opToken lhs rhs span =>
    .binop opToken (lhs.substDotShorthand itName) (rhs.substDotShorthand itName) span
  | .prefix_ opToken operand span =>
    .prefix_ opToken (operand.substDotShorthand itName) span
  | .logicalNot body span =>
    .logicalNot (body.substDotShorthand itName) span
  | .logicalAnd lhs rhs span =>
    .logicalAnd (lhs.substDotShorthand itName) (rhs.substDotShorthand itName) span
  | .logicalOr lhs rhs span =>
    .logicalOr (lhs.substDotShorthand itName) (rhs.substDotShorthand itName) span
  | .pipe lhs rhs span =>
    .pipe (lhs.substDotShorthand itName) (rhs.substDotShorthand itName) span
  | .tryPrefix body span =>
    .tryPrefix (body.substDotShorthand itName) span
  | .ifExpr cond thenBranch elsifs elseOpt span =>
    let substCond   := cond.substDotShorthand itName
    let substThen   := thenBranch.substDotShorthand itName
    let substElsifs := elsifs.map fun (c, b) =>
      (c.substDotShorthand itName, b.substDotShorthand itName)
    let substElseOpt := elseOpt.map (·.substDotShorthand itName)
    .ifExpr substCond substThen substElsifs substElseOpt span
  | .field receiver fieldName span =>
    .field (receiver.substDotShorthand itName) fieldName span
  | .index receiver idx span =>
    .index (receiver.substDotShorthand itName)
           (idx.substDotShorthand itName) span
  | .isCheck scrutinee ctorRef span =>
    .isCheck (scrutinee.substDotShorthand itName) ctorRef span
  | .logicalImplies lhs rhs span =>
    .logicalImplies (lhs.substDotShorthand itName) (rhs.substDotShorthand itName) span
  | .logicalIff lhs rhs span =>
    .logicalIff (lhs.substDotShorthand itName) (rhs.substDotShorthand itName) span
  | other => other

/-! ## File-level AST -/

/-- Top-level parse result.  `errors` collects non-fatal parse
    diagnostics; partial ASTs are still emitted when possible. -/
structure File where
  decls  : Array Decl
  span   : Span
  deriving Repr

end FX.Syntax.Ast
