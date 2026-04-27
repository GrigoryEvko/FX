# FX Grammar

Formal grammar for the FX programming language.  EBNF notation.
Every production is a parsing rule.  Every token is defined.
The grammar is LALR(1)-compatible.


## 1. Notation

```
KEYWORD       terminal keyword token (bold lowercase)
SYMBOL        terminal symbol token
name          nonterminal
name?         optional (zero or one)
name*         zero or more
name+         one or more
name % SEP    one or more separated by SEP
a | b         ordered choice (first match)
( ... )       grouping
"text"        literal string
```


## 2. Lexical Tokens

### 2.1 Identifiers

```
ident         = [a-zA-Z_][a-zA-Z0-9_]*
lower_ident   = [a-z_][a-zA-Z0-9_]*       // variables, functions, fields
upper_ident   = [A-Z][a-zA-Z0-9_]*        // types, constructors, modules
```

No single quote `'` in identifiers.  ASCII only.

### 2.2 Keywords (92)

```
affine        and          as           assert       await
axiom         begin        bench        bisimulation break
by            calc         catch        class        code
comptime      const        continue     codata       contract
decreases     decorator    declassify   defer        dimension
drop          dual         effect       else         end
errdefer      exception    exists       exports      extern
false         fn           for          forall       ghost
handle        hint         if           impl         in
include       instance     is           label        layout
lemma         let          linear       machine      match
module        mut          not          open         or
own           post         pre          proof        pub
quotient      receive      rec          ref          refinement
return        sanitize     secret       select       self
send          session      sorry        spawn        taint_class
tainted       test         true         try          type
unfold        val          verify       while        with
where         yield
```

`lift` was removed in Proposal 13 — it was a dead keyword with no
grammar production; effect subtyping now uses §9.3 lattice plus
user-declared `subsumes` edges inside `effect` blocks.

`cell` is a stdlib type and constructor function (§4.6 of the design
spec), not a keyword.  Like `option`, `list`, `result`, it lives in
the prelude and can be locally shadowed.  The grammar has no
dedicated production for `cell(...)` — it parses as an ordinary
function call.

**Contextual keywords** — these are lexed as identifiers and
recognized by the parser only in specific positions (never at the
top level of expressions or types).  Using them elsewhere is
permitted — they remain ordinary identifiers outside their
context.

```
Refinement blocks (§5.19):      refines   via

Hardware blocks (§5.16):        hardware  pipeline  stage
                                register_file  wire  reg  rising
                                falling  emit  stall  flush  forward
                                redirect  onehot  field  virtual
                                driven_by  when  write_order  at
                                RW  RO  WO  W1C  W1S  RC  RS  RSVD

Codata expressions (§6.9):      sized  (also as spec clause)

Module functor args (§5.17):    struct

Machine blocks (§10):           state  transition  initial  terminal
                                emits  on_event  on_signal  priority
                                concurrency  atomic  idempotent
                                commutative  inverse  on_fail  after
                                cancels  preempts  actor  rollback
                                goto  stay  recoverable  critical
                                requires  ensures  from

Contract blocks (§11):          version  migration  compatibility
                                access  format  invariant  errors
                                add  remove  rename  default

Effect blocks (§5.12):          multishot  subsumes

Class blocks (§5.13):           law

Test blocks (§12, §23):         assert_err  assert_within
                                assert_raises  case
                                expect_compile_error  expect_accepted
                                matches  test_machine  test_contract
                                test_theory  test_metatheory
```

### 2.3 Literals

```
int_lit       = [0-9][0-9_]*
              | "0x" [0-9a-fA-F][0-9a-fA-F_]*
              | "0b" [01][01_]*
              | "0o" [0-7][0-7_]*

typed_int     = int_lit ("u8"|"i8"|"u16"|"i16"|"u32"|"i32"|"u64"|"i64"
              |"u128"|"i128"|"u256"|"i256"|"u512"|"i512"|"u1024"|"i1024"
              |"usize"|"isize")

decimal_lit   = [0-9][0-9_]* "." [0-9][0-9_]*
              | [0-9][0-9_]* ("e"|"E") ("+"|"-")? [0-9][0-9_]*
              | [0-9][0-9_]* "." [0-9][0-9_]* ("e"|"E") ("+"|"-")? [0-9][0-9_]*

typed_decimal = decimal_lit ("d32"|"d64"|"d96"|"d128"|"d256"|"d512"|"d1024")
typed_float   = decimal_lit ("f32"|"f64")

ternary_lit   = "0t" [01T][01T_]*
typed_ternary = ternary_lit ("t6"|"t12"|"t24"|"t48")

string_lit    = '"' string_char* '"'
fstring_lit   = 'f"' fstring_char* '"'
rstring_lit   = 'r"' [^"]* '"'
bstring_lit   = 'b"' bstring_char* '"'

bool_lit      = TRUE | FALSE
```

No single-quoted character literals.  `"c"` typed as `char` by context.

Bit literal width rule: a binary literal `0b...` produces `bits(n)`
where `n` = digit count (underscores excluded, leading zeros
significant).  `0b1010`=bits(4), `0b00001010`=bits(8).  No `Nb`
width prefix.  Type ascription or a `uN`/`iN` suffix overrides and
zero-extends; a literal whose digit count exceeds the ascribed width
is compile error T051.

No apostrophe token.  Region parameters use kind form `<r: region>`
(§3.13); references at use site are `ref(r) T`.  `static` is the
top-of-lattice region constant.

### 2.4 Symbols and Operators

```
Arithmetic:     +  -  *  /  %
Comparison:     ==  !=  <  >  <=  >=
Bitwise:        &  |  ^  ~  <<  >>
Arrow:          ->  =>
Range:          ..  ..=
Spread:         ...
Pipe:           |>
Dot:            .
Delimiters:     (  )  [  ]  {  }
Punctuation:    :  ;  ,  =  #  @
Attribute:      @[
```

Logical operators are keywords: `not`, `and`, `or`, `is`.

No `:=`, `::`, `!`, `?`, `?.`, `&&`, `||`, `<|`, `'`.

### 2.5 Comments

```
line_comment  = "//" [^\n]*
block_comment = "/*" ... "*/"              // non-nesting
doc_comment   = "///" [^\n]*              // attaches to next declaration
```


## 3. Precedence (lowest to highest)

```
Level  Operators / Keywords    Assoc        Role
-----  ---------------------   ----------   --------------------------
  1    ->                      right        function type arrow
  2    |>                      left         pipe
  3    <==>                    right        iff (propositional)
  4    ==>                     right        implies (propositional)
  5    or                      left         logical disjunction
  6    and                     left         logical conjunction
  7    not                     prefix       boolean negation (below
                                            all comparisons, §2.6)
  8    == != < > <= >=         non-chaining comparison (T050 on chain)
  9    is                      left         constructor test
 10    |                       left         bitwise OR
 11    ^                       left         bitwise XOR
 12    &                       left         bitwise AND
 13    << >>                   left         shift
 14    ..  ..=                 nonassoc     range
 15    + -                     left         additive
 16    * / %                   left         multiplicative
```

Above all infix except `not`: prefix `-` (negate), `~` (bitwise NOT).
Above prefix: postfix `.field`, `.method()`, `[index]`, `(args)`.

**Chained comparison is rejected.**  `0 < x < 10` is compile error
T050; write `0 < x and x < 10`.  This makes `bool < nat` type errors
impossible to mask behind a chain and forces LLM-generated code to
be unambiguous.

**`not` binds below comparisons.**  `not x is None` parses as
`not (x is None)`; `not x > 5` parses as `not (x > 5)`.  This
matches Python's model.  Below `and`, `not x and y` is still
`(not x) and y`.


## 4. File Structure

```
file
  = decl*
  ;
```


## 5. Declarations

```
decl
  = module_decl
  | module_type_decl                  // §5.17
  | module_functor_decl               // §5.17
  | import_decl
  | fn_decl
  | hardware_fn_decl                  // §5.16
  | hardware_module_decl              // §5.16
  | pipeline_decl                     // §5.16
  | register_file_decl                // §5.16
  | type_decl
  | quotient_decl                     // §3.7
  | codata_decl                       // §5.14
  | session_decl                      // §5.15
  | val_decl
  | const_decl
  | effect_decl
  | class_decl
  | instance_decl
  | impl_decl
  | machine_decl
  | contract_decl
  | layout_decl
  | refinement_decl                   // §5.19
  | bisimulation_decl                 // §5.19
  | dimension_decl                    // §5.18
  | taint_class_decl                  // §5.18
  | test_decl
  | bench_decl
  | lemma_decl
  | axiom_decl
  | exception_decl
  | extern_decl
  | sorry_decl
  | pragma
  ;
```

### 5.1 Visibility and Attributes

```
visibility
  = PUB
  | (* empty — private by default *)
  ;

attributes
  = ( "@[" attr_expr % "," "]" )*
  ;

attr_expr
  = qualident
  | qualident "(" attr_arg % "," ")"
  | string_lit
  | int_lit
  ;

attr_arg
  = expr
  ;
```

Every `decl` can be preceded by `attributes` and `visibility`:

```
decorated_decl
  = attributes visibility decl
  ;
```

### 5.2 Module and Imports

```
module_decl
  = MODULE qualident ";"
  ;

import_decl
  = OPEN qualident restriction? ";"
  | OPEN qualident AS upper_ident ";"
  | INCLUDE qualident restriction? ";"
  ;

restriction
  = "{" (ident ("," ident)*)? "}"
  ;
```

### 5.3 Constants

```
const_decl
  = CONST upper_ident ":" type "=" expr ";"
  ;
```

Always module-private.  Always compile-time evaluated.  `pub const` is
a compile error.

### 5.4 Function Declarations

```
fn_decl
  = FN lower_ident type_params? fn_params ":" type
      effect_annot? spec_clauses?
      fn_body
  | FN REC fn_rec_binding (AND fn_rec_binding)* ";"
  ;

fn_body
  = "=" expr proof_block? ";"
  | BEGIN FN stmt* RETURN expr ";" END FN proof_block? ";"
  | BEGIN FN stmt* RETURN ";" END FN proof_block? ";"    // return; = return ();
  ;

fn_rec_binding
  = lower_ident type_params? fn_params ":" type
      effect_annot? spec_clauses?
      fn_body_no_semi
  ;

fn_body_no_semi
  = "=" expr proof_block?
  | BEGIN FN stmt* RETURN expr ";" END FN proof_block?
  | BEGIN FN stmt* RETURN ";" END FN proof_block?        // return; = return ();
  ;

proof_block
  = PROOF stmt* END PROOF                                 // §10.17 Proof Work;
                                                          //   contained stmts are
                                                          //   restricted at
                                                          //   elaboration to ghost
                                                          //   grade + Tot effect
  ;
```

### 5.5 Type Parameters

```
type_params
  = "<" type_param % "," ">"
  ;

type_param
  = lower_ident ":" kind
  | "+" lower_ident ":" kind          // covariant
  | "-" lower_ident ":" kind          // contravariant
  ;

kind
  = TYPE                               // type parameter
  | NAT                                // compile-time natural
  | REGION                             // memory region
  | EFFECT                             // effect variable
  | kind "->" kind                     // higher-kinded
  | qualident                          // named kind
  ;
```

Every type parameter has a mandatory kind annotation.  `TYPE`, `NAT`,
`REGION`, `EFFECT` are the built-in kinds and correspond to the global
keywords `type`, `effect` plus the built-in type names `nat`, `region`.

### 5.6 Function Parameters

```
fn_params
  = "(" fn_param % "," ")"
  | "(" ")"                            // unit params
  ;

fn_param
  = mode? lower_ident ":" type ("=" expr)?   // optional default value
  | "#" lower_ident ":" type           // implicit
  | "#" lower_ident                    // implicit, inferred
  ;

mode
  = OWN
  | REF
  | REF MUT
  | AFFINE
  | GHOST
  | SECRET
  | LINEAR
  ;
```

### 5.7 Effect Annotations

```
effect_annot
  = WITH effect_row
  ;

effect_row
  = effect_term % ","
  ;

effect_term
  = upper_ident                        // IO, Async, Div
  | upper_ident "(" type % "," ")"    // Fail(error), State(s)
  | lower_ident                        // effect variable
  ;
```

### 5.8 Specification Clauses

```
spec_clauses
  = spec_clause*
  ;

spec_clause
  = where_clause
  | pre_clause
  | post_clause
  | decreases_clause
  ;

where_clause
  = WHERE constraint % "," ";"
  ;

pre_clause
  = PRE expr ";"
  ;

post_clause
  = POST lower_ident "=>" expr ";"
  ;

decreases_clause
  = DECREASES expr ";"
  ;

constraint
  = upper_ident "(" type % "," ")"    // Ord(a), Show(a)
  ;
```

Clause ordering is fixed: `where`, `pre`, `post`, `decreases`.
Misordering is a compile error.

### 5.9 Type Declarations

```
type_decl
  = TYPE type_rec_binding (AND type_rec_binding)* ";"
  ;

quotient_decl
  = QUOTIENT TYPE lower_ident type_params? "=" type
      BY expr ";"
  ;

type_rec_binding
  = lower_ident type_params? "=" type
  | lower_ident type_params? "{" record_fields "}"
  | lower_ident type_params? variant_ctor+ END TYPE
  ;

record_fields
  = record_field (";" record_field)* ";"?
  ;

record_field
  = lower_ident ":" type
  ;

variant_ctor
  = upper_ident ";"
  | upper_ident "(" ctor_field % "," ")" ";"
  | upper_ident "{" record_fields "}" ";"
  | upper_ident ":" type ";"                   // GADT constructor
  ;

ctor_field
  = lower_ident ":" type
  | type                                        // positional
  ;
```

No `of` keyword.  No `|` bars.  Constructors use `()` matching
their use-site syntax.

**Mutually recursive types.**  Types that reference each other
are declared in a single `type ... and ... and ...;` group:

```
type expr
  Num(int);
  Var(string);
  App(expr, expr);
  Let(string, expr, expr);
  Branch(branches);
end type
and branches
  Empty;
  Arm(pattern, expr, branches);
end type;
```

All bindings in the group share a single trailing `;` after the
last `end type` (or `}` for records).  OCaml precedent.  Non-
recursive `type foo = bar;` is just a one-binding group.

**GADT constructors.**  A constructor whose declared return type
differs from the naive inductive type is a GADT constructor:

```
type term<a: type>
  Lit : int -> term<int>;
  Bool : bool -> term<bool>;
  Pair<b: type, c: type> : term<b> -> term<c> -> term<(b, c)>;
  If : term<bool> -> term<a> -> term<a> -> term<a>;
end type;
```

The `upper_ident ":" type` variant_ctor form allows the return
type to refine the inductive family's type parameters.  Pattern
matching on a GADT refines `a` per the matched constructor's
return type.  Standard GADT semantics (Haskell/OCaml/Idris).

### 5.10 Val, Axiom, Exception, Extern

```
val_decl
  = VAL lower_ident type_params? ":" type ";"
  ;

axiom_decl
  = AXIOM lower_ident type_params? "(" fn_param % "," ")" ":" type
      spec_clauses?
      ";"
  ;

exception_decl
  = EXCEPTION upper_ident ";"
  | EXCEPTION upper_ident "(" type % "," ")" ";"
  ;

extern_decl
  = EXTERN string_lit? FN lower_ident type_params?
      "(" fn_param % "," ")" ":" type effect_annot? ";"
  | EXTERN string_lit extern_member+ END EXTERN ";"
  ;

extern_member
  = FN lower_ident type_params?
      "(" fn_param % "," ")" ":" type effect_annot? ";"
  | VAL lower_ident ":" type ";"
  ;

sorry_decl
  = SORRY ";"
  ;
```

### 5.11 Lemma Declarations

```
lemma_decl
  = LEMMA lower_ident type_params? fn_params
      (":" type)? effect_annot? spec_clauses?
      fn_body
  ;
```

### 5.12 Effect Declarations

```
effect_decl
  = EFFECT upper_ident type_params?
      (effect_op | effect_relation)+ END EFFECT ";"
  ;

effect_op
  = FN lower_ident fn_params ":" type ";"
  ;

effect_relation
  = SUBSUMES qualident ";"           // user-declared subtyping edge —
                                      //   values with this effect
                                      //   satisfy contexts expecting
                                      //   the named effect (§9.5)
  ;
```

`degrades_to` was removed in Proposal 13 as the converse of
`subsumes`.  A single directional form suffices: `A subsumes B`
declares the edge.  The inverse statement `B subsumes A` is a
different edge in the opposite direction; it is not automatically
implied and must be declared separately if intended.

### 5.13 Class and Instance

```
class_decl
  = CLASS upper_ident type_params?
      class_member+ END CLASS ";"
  ;

class_member
  = FN lower_ident impl_fn_params ":" type
      effect_annot? spec_clauses? class_fn_body
  | VAL lower_ident ":" type ";"
  | LAW lower_ident ":" type ";"                // inside class only
  ;

class_fn_body
  = ";"                                           // abstract method —
                                                  //   instances must
                                                  //   supply a body
  | fn_body                                       // default method body —
                                                  //   instances may
                                                  //   override
  ;

instance_decl
  = INSTANCE upper_ident FOR type
      (WHERE constraint ("," constraint)* ";")?   // instance constraints
                                                  //   e.g. `where Ord(a)`
      instance_member+ END INSTANCE ";"
  ;

instance_member
  = FN lower_ident impl_fn_params (":" type)?
      effect_annot? spec_clauses? fn_body
  ;

impl_decl
  = IMPL type
      impl_member+ END IMPL ";"
  ;

impl_member
  = FN lower_ident impl_fn_params (":" type)?
      effect_annot? spec_clauses? fn_body
  ;

impl_fn_params
  = "(" self_param ("," fn_param)* ")"            // instance method —
                                                  //   leading self
  | "(" fn_param ("," fn_param)* ")"              // static method — no
                                                  //   self; mode rules
                                                  //   apply normally
  | "("                                    ")"    // unit — static method
                                                  //   with no params
  ;

self_param
  = SELF                                           // self (owning mode;
                                                  //   consumes the value)
  | REF SELF                                      // ref self (shared
                                                  //   borrow)
  | REF MUT SELF                                  // ref mut self
                                                  //   (exclusive borrow)
  | AFFINE SELF                                   // affine self (at most
                                                  //   once)
  ;
```

**Notes on `self`.**  The `self` keyword never carries an explicit
type annotation — the type is inferred from the enclosing `impl T`,
`instance Trait for T`, or `class Trait<T>` block.  Writing
`fn close(self: Connection) ...` inside `impl Connection` is compile
error T064 (`self type is implicit in impl/instance/class block`).
The `self` keyword is usable only as the leading parameter of a
method inside one of those three block forms; using `self` elsewhere
(regular function parameter, let binding, record field) is compile
error T064.  Backtick-escaped `` `self` `` remains available as an
ordinary identifier if required.

**Notes on `class_fn_body`.**  A class declaration lists its
methods with either a signature-only form (`fn to_string(ref self) :
string ;`) marking the method abstract, or with a full body marking
the method as having a default implementation.  An instance of the
class may omit methods that have default bodies; it must implement
every abstract method.  Default bodies type-check at the class
declaration site against the declared signature; the type checker
does not re-verify them at each instance (§16.4).

### 5.14 Codata Declarations

Codata types (§3.5) are declared by their destructors.  Every
codata value is consumed by applying destructors; construction
uses `unfold` (§6.9).

```
codata_decl
  = CODATA lower_ident type_params?
      codata_member+ END CODATA ";"
  ;

codata_member
  = FN lower_ident "(" SELF ")" ":" type
      effect_annot? ";"
  ;
```

Each `codata_member` is a destructor signature.  Destructor
semantics and productivity are specified in §3.5 of the design
spec; the guardedness check (Coppo-Dezani guardedness extended
to copatterns per Abel-Pientka POPL 2013) is enforced by the
kernel axiom Coind-ν (Appendix H.5 of the design spec).

### 5.15 Session Declarations

Session types (§11) describe communication protocols as types.

```
session_decl
  = SESSION lower_ident type_params?
      session_body END SESSION ";"
  ;

session_body
  = session_step+
  | REC upper_ident ";" session_step+
  ;

session_step
  = SEND "(" session_payload % "," ")" ";"
  | RECEIVE "(" session_payload % "," ")" ";"
  | BRANCH branch_arm+ END BRANCH ";"
  | SELECT branch_arm+ END SELECT ";"      // dual of BRANCH
  | upper_ident ";"                          // recursive continuation
  | END ";"                                   // session terminator
  ;

session_payload
  = lower_ident ":" type
  ;

branch_arm
  = lower_ident "=>" session_step* END ";"
  ;
```

Multiparty global session types (§11.5):

```
global_session_decl
  = SESSION lower_ident type_params? "="
      "global_session"
      global_step+ END SESSION ";"
  ;

global_step
  = upper_ident "->" upper_ident ":"
      lower_ident "(" session_payload % "," ")" ";"
  ;
```

Channel operations `send(ch, field: v)`, `receive(ch)`,
`select(ch, label)`, `cancel(ch)` are ordinary function calls
resolved at the stdlib level; no new grammar production is
required.  `receive_branch(ch)` returns a label value matched on
via ordinary `match` (§6.5).

### 5.16 Hardware Declarations

Hardware modules, combinational functions, pipelines, and
register files (§18) are restricted declaration forms whose
bodies must map to gates under the synthesizability rules of
§18.8.

**Hardware combinational function.**  A pure `Tot` function on
bit-vectors synthesizing to combinational logic:

```
hardware_fn_decl
  = HARDWARE FN lower_ident type_params? fn_params
      ":" type
      effect_annot?
      fn_body
  ;
```

Here `HARDWARE` is the contextual keyword `hardware` in prefix
position before `fn`; the lexer emits IDENT and the parser
recognizes the keyword by context.

**Hardware module.**  A sequential block combining registers
and combinational wires:

```
hardware_module_decl
  = HARDWARE MODULE upper_ident type_params?
      effect_annot?
      hardware_module_member*
    END HARDWARE MODULE ";"
  ;

hardware_module_member
  = reg_binding
  | wire_binding
  | on_clock_block
  | fn_decl                            // local fns are Tot by default
  | let_stmt                            // combinational wire via 'let'
  ;

reg_binding
  = REG lower_ident ":" type "=" expr ";"
  ;

wire_binding
  = WIRE lower_ident ":" type "=" expr ";"
  ;

let_stmt
  = LET pattern (":" type)? "=" expr ";"
  ;

on_clock_block
  = ON RISING  "(" lower_ident ")" stmt* END ON ";"
  | ON FALLING "(" lower_ident ")" stmt* END ON ";"
  ;
```

**Pipeline declaration.**  Pipelines generate inter-stage
registers, hazard-detection logic, and forwarding automatically
(§18.11):

```
pipeline_decl
  = PIPELINE lower_ident effect_annot?
      stage_decl+ END PIPELINE ";"
  ;

stage_decl
  = STAGE lower_ident
      stage_member* END STAGE ";"
  ;

stage_member
  = stmt
  | EMIT expr % "," ";"
  | STALL WHEN expr ";"
  | FLUSH lower_ident % "," WHEN expr ";"
  | FORWARD FROM lower_ident TO lower_ident ";"
  | REDIRECT lower_ident WHEN expr ";"
  ;
```

**Register file declaration.**  Groups of hardware registers
with a common base address, field layouts, access modes, and
optional state-machine projections (§18.3-18.5):

```
register_file_decl
  = REGISTER_FILE upper_ident
      (AT expr)?
      register_file_member*
    END REGISTER_FILE ";"
  ;

register_file_member
  = reg_with_fields
  | virtual_reg
  | driven_machine_decl
  ;

reg_with_fields
  = REG lower_ident ":" type AT expr access_mode?
      (WHERE expr ";")*
      (field_decl)*
    END REG ";"
  ;

field_decl
  = FIELD lower_ident ":" bit_spec access_mode
      (WHERE expr)*
      (REQUIRES expr)*
      ";"
  ;

bit_spec
  = "bit" "(" expr ")"
  | "bits" "(" expr ":" expr ")"     // range form
  | "bits" "(" expr ")"
  ;

access_mode
  = "RW" | "RO" | "WO"
  | "W1C" | "W1S"
  | "RC" | "RS"
  | "RSVD"
  ;

virtual_reg
  = VIRTUAL lower_ident ":" type "=" expr
      (WRITE_ORDER lower_ident THEN lower_ident)?
      ";"
  ;

driven_machine_decl
  = MACHINE upper_ident DRIVEN_BY lower_ident
      driven_machine_member* END MACHINE ";"
  ;

driven_machine_member
  = STATE upper_ident WHEN expr ";"
  | state_ref "->" state_ref "=" expr (AFTER expr)? ";"
  | INITIAL upper_ident ";"
  | TERMINAL upper_ident ";"
  ;
```

### 5.17 Module Types and Functors

Module signatures and functors (§5.5):

```
module_type_decl
  = MODULE TYPE upper_ident
      module_type_member*
    END MODULE TYPE ";"
  ;

module_type_member
  = TYPE lower_ident type_params? ";"                  // abstract type
  | TYPE lower_ident type_params? "=" type ";"         // type alias
  | VAL lower_ident ":" type ";"                        // value sig
  | FN lower_ident type_params? fn_params ":" type
      effect_annot? ";"                                   // function sig
  ;

module_functor_decl
  = MODULE FUNCTOR upper_ident
      "(" upper_ident ":" upper_ident ")"
      module_body
    END MODULE FUNCTOR ";"
  ;

module_body
  = (decl)*                             // any declaration form
  ;
```

Functor application is an ordinary module binding; the argument
can be a named module or an anonymous `struct` literal:

```
module_binding
  = MODULE upper_ident "=" module_expr ";"
  ;

module_expr
  = upper_ident                              // named module
  | upper_ident "(" module_expr ")"          // functor application
  | STRUCT module_body END STRUCT             // anonymous module
  ;
```

### 5.18 Dimension and Taint Class Declarations

Named dimensions for physical units (§17.5) and taint classes
for information-flow tracking (§12.3):

```
dimension_decl
  = DIMENSION upper_ident ";"
  ;

taint_class_decl
  = TAINT_CLASS upper_ident ";"
  ;
```

Both are declaration-only — they introduce names that refer to
compiler-managed tracking dimensions.  They cannot carry
parameters or bodies.

### 5.19 Refinement and Bisimulation Declarations

Refinement connects an implementation machine to a specification
machine (§13.6) or a specification function (§18.12); the
compiler discharges the refinement proof obligation.

```
refinement_decl
  = REFINEMENT lower_ident
      REFINES upper_ident
      VIA expr ";"
      (property_clause)*
    END REFINEMENT ";"
  ;

property_clause
  = "property" lower_ident ":" expr ";"
  ;
```

Bisimulation (§13.19) relates two systems via an explicit
relation and a preservation theorem:

```
bisimulation_decl
  = BISIMULATION lower_ident
      bisimulation_clause+
    END BISIMULATION ";"
  ;

bisimulation_clause
  = "relates" upper_ident ":" type "->" type "->" "bool" ";"
  | "initial" ":" expr ";"
  | "step" ":" expr ";"
  ;
```


## 6. Expressions

### 6.1 Statements (in blocks)

```
stmt
  = LET pattern (":" type)? "=" expr ";"         // plain let (irrefutable)
  | LET pattern (":" type)? "=" expr
      ELSE stmt ";"                               // let-else; else branch
                                                  //   must diverge (fail,
                                                  //   return, break,
                                                  //   or a call with ':
                                                  //   never' return type)
  | expr ";"
  | fn_decl                                    // local function
  | LABEL lower_ident ";"                      // loop label
  | DEFER expr ";"                             // cleanup on scope exit
                                               //   (always, per §7.11)
  | ERRDEFER expr ";"                          // cleanup on Fail/Exn
                                               //   scope exit only
                                               //   (per §7.11)
  | import_decl                                 // scoped open/include
                                               //   (§5.5; scoping is
                                               //    block-local automatically)
  ;
```

Every statement ends with `;`.  No exceptions.  Block functions
end with `return expr;` as the last statement.

**Let-else semantics.**  `let pattern = expr else stmt;` binds if
the pattern matches; if it does not match, `stmt` runs.  The
`else` statement must have type `never` — it must diverge.  This
ties into FX's control-flow discipline (§4.9): the else branch
raises a typed `Fail`, calls `return`, `break`, or otherwise
does not fall through.  Kernel translation: desugars to a
single-arm match with a diverging wildcard branch.

**If-let semantics.**  `if let pattern = expr; body else alt
end if` evaluates `expr`, matches against `pattern`, runs `body`
if the match succeeds, otherwise runs `alt`.  Kernel translation:
desugars to a single-arm match with a wildcard fall-through to
`alt`.

### 6.2 Expressions

```
expr
  = pipe_expr
  ;

pipe_expr
  = pipe_expr "|>" infix_expr
  | infix_expr
  ;

infix_expr
  = infix_expr "->" infix_expr               // function type (right)
  | infix_expr "<=>" infix_expr              // iff (right)
  | infix_expr "==>" infix_expr              // implies (right)
  | infix_expr OR infix_expr                  // logical or (left)
  | infix_expr AND infix_expr                 // logical and (left)
  | not_expr
  ;

not_expr
  = NOT not_expr                              // boolean negation (below
                                              //   comparisons, §2.6)
  | compare_expr
  ;

compare_expr
  = bitor_expr comp_op bitor_expr             // EXACTLY ONE comparison;
                                              //   chains are error T050
  | bitor_expr IS upper_ident                 // constructor test (left)
  | bitor_expr
  ;

bitor_expr
  = bitor_expr "|" bitxor_expr                // bitwise or (left)
  | bitxor_expr
  ;

bitxor_expr
  = bitxor_expr "^" bitand_expr               // bitwise xor (left)
  | bitand_expr
  ;

bitand_expr
  = bitand_expr "&" shift_expr                // bitwise and (left)
  | shift_expr
  ;

shift_expr
  = shift_expr shift_op range_expr            // shift (left)
  | range_expr
  ;

range_expr
  = add_expr range_op add_expr (BY add_expr)?  // range (nonassoc),
                                               //   optional stride
  | add_expr
  ;

add_expr
  = add_expr add_op mul_expr                  // additive (left)
  | mul_expr
  ;

mul_expr
  = mul_expr mul_op prefix_expr               // multiplicative (left)
  | prefix_expr
  ;

comp_op   = "==" | "!=" | "<" | ">" | "<=" | ">="  ;
shift_op  = "<<" | ">>"  ;
range_op  = ".." | "..="  ;
add_op    = "+" | "-"  ;
mul_op    = "*" | "/" | "%"  ;

prefix_expr
  = "-" prefix_expr                           // arithmetic negate
  | "~" atomic_expr                           // bitwise NOT / splice
  | postfix_expr
  ;

// Note: chained comparison is rejected at parse time.
//   0 < x < 10  →  error T050 "chained comparison — write
//   '0 < x and x < 10'"
// Because compare_expr accepts exactly ONE comp_op at the top level,
// a second comp_op has no production to match and fails.
//
// Note: `not` lives at its own level, below every comparison and
// every `is` test, above `and`.  This matches Python.  `not x is
// None` parses as `not (x is None)`; `not x > 5` parses as
// `not (x > 5)`.

postfix_expr
  = postfix_expr "." lower_ident              // field access
  | postfix_expr "." lower_ident call_args    // method call
  | postfix_expr "." int_lit                  // tuple indexing:
                                              //   pair.0, trip.2
                                              //   (Rust/Swift-style; int_lit
                                              //    is a bare decimal literal
                                              //    with no suffix and no
                                              //    leading zeros)
  | postfix_expr "[" expr "]"                 // index
  | postfix_expr call_args                    // function call
  | postfix_expr "()"                         // unit call
  | app_expr
  ;

app_expr
  = atomic_expr call_args                     // f(args)
  | atomic_expr "()"                          // f()
  | atomic_expr "[" expr "]"                  // index
  | atomic_expr
  ;
```

### 6.3 Call Arguments

```
call_args
  = "(" call_arg % "," ")"
  ;

call_arg
  = expr                                       // single-param positional
  | lower_ident ":" expr                      // named argument
  | "#" expr                                   // implicit type argument
  ;
```

Functions with more than one parameter require named arguments at
the call site.  `name: value` syntax.  No punning.

### 6.4 Atomic Expressions

```
atomic_expr
  = "(" expr ")"                              // grouping
  | "()"                                       // unit
  | "(" expr "," expr % "," ")"              // tuple
  | qualident                                  // variable or constructor
  | literal
  | "[" expr % "," "]"                        // list literal
  | "[" expr "," "..." expr "]"              // spread prepend
  | "[" "..." expr "," expr "]"              // spread append
  | "[" "..." expr "," "..." expr "]"        // spread concat
  | list_comprehension                         // §4.8 comprehensions
  | "{" field_init % "," "}"                 // record literal
  | "{" "..." expr "}"                        // record copy via spread
  | "{" "..." expr "," field_init % "," "}"  // record update via spread
                                              //   (spread must be first;
                                              //    later field_inits override)
  | "." lower_ident                            // §4.2 rule 25 dot shorthand;
                                              //   valid only in function-
                                              //   argument position (the
                                              //   elaborator checks — wraps
                                              //   into fn(it) => ... with
                                              //   all bare dots sharing it)
  | BEGIN stmt* expr ";" END BEGIN             // block expression
  | match_expr
  | if_expr
  | for_expr
  | while_expr
  | try_expr
  | handle_expr
  | lambda_expr
  | calc_expr
  | verify_expr
  | select_expr
  | comptime_expr                             // §6.7
  | quote_expr                                 // §6.8
  | unfold_expr                                // §6.9
  | SORRY
  | ASSERT expr ";"
  | ASSERT expr USING expr ("," expr)* ";"    // multi-lemma §10.4
  | ASSERT expr BY by_clause ";"              // §10.4 named tactic or hint block
  ;

by_clause
  = lower_ident call_args?                     // single tactic: ring,
                                                //   linarith, smt(solver: z3)
  | BEGIN stmt* END                            // Dafny-style hint block;
                                                //   stmts restricted at
                                                //   elaboration to ghost/Tot
  ;

literal
  = int_lit | typed_int | decimal_lit | typed_decimal | typed_float
  | ternary_lit | typed_ternary
  | string_lit | fstring_lit | rstring_lit | bstring_lit
  | bool_lit
  ;

field_init
  = qualident ":" expr
  ;

list_comprehension
  = "[" expr comprehension_clause+ "]"         // §4.8 comprehensions
  ;

comprehension_clause
  = FOR pattern IN expr                        // source; multiple allowed
  | IF expr                                    // filter; multiple allowed;
                                               //   any position after the
                                               //   first FOR
  ;
```

`[x * x for x in 0..10]` desugars to `(0..10) |> map(fn(x) => x * x)`.
Multi-source `[(x, y) for x in xs for y in ys if x != y]` desugars
to nested `flat_map`/`map`/`filter` per §4.8.

### 6.5 Control Flow Expressions

```
match_expr
  = MATCH expr ";"
      match_arm+
    END MATCH
  ;

match_arm
  = pattern "=>" expr ";"
  | pattern IF infix_expr "=>" expr ";"
  ;

if_expr
  = IF if_head ";"
      stmt* expr ";"
    (ELSE IF if_head ";" stmt* expr ";")*
    (ELSE stmt* expr ";")?
    END IF
  ;

if_head
  = expr                               // ordinary condition
  | LET pattern "=" expr               // if-let destructuring; the
                                       //   branch body is entered iff
                                       //   the pattern matches.  Desugars
                                       //   to a single-arm match with a
                                       //   wildcard fall-through.
  ;

for_expr
  = FOR pattern IN expr ";"            // destructuring allowed:
      stmt*                             //   for (k, v) in map.entries();
    END FOR                             //   for User { name, age, .. } in users;
  ;

while_expr
  = WHILE expr ";"
      stmt*
    END WHILE
  ;

try_expr
  = TRY
      stmt* expr ";"
    CATCH
      match_arm+
    END TRY
  ;

handle_expr
  = HANDLE expr
      (RETURN lower_ident "=>" expr ";")?      // optional; defaults
                                                //   to identity
                                                //   'return x => x'
                                                //   when omitted (§9.6)
      handle_op_arm+
    END HANDLE
  ;

handle_op_arm
  = lower_ident "(" lambda_param % "," ")" "=>" expr ";"
  ;

lambda_expr
  = FN "(" lambda_param % "," ")" "=>" expr
  | FN "(" ")" "=>" expr
  ;

lambda_param
  = lower_ident ":" type
  | lower_ident
  | "_"
  | "(" pattern ")"
  ;

calc_expr
  = CALC "(" calc_rel ")" expr ";"
      calc_step*
    END CALC
  ;

calc_step
  = calc_rel expr (BY by_clause)? ";"         // §10.5 — 'by' justification
                                                //   unified with assert by_clause
  ;

calc_rel
  = "==" | "!=" | "<=" | ">=" | "<" | ">" | "<=>" | "==>"
  ;

verify_expr
  = VERIFY stmt* (EXPORTS expr+ ";")? END VERIFY
  ;

select_expr
  = SELECT select_arm+ END SELECT
  ;

select_arm
  = lower_ident FROM lower_ident "=>" expr ";"
  ;
```

### 6.6 Ref Operations

Mutable references use method syntax, not operators:

```
ref(value)        // create mutable cell
x.get()           // read
x.set(value)      // write
```

These are method calls on the `ref` type.  No special grammar rules.

### 6.7 Comptime Expressions

`comptime` marks an expression, block, or declaration for
compile-time evaluation (§17.1).  The surface kernel is
identical to runtime FX; the compiler evaluates the term at
elaboration time via kernel normalization (§31).

```
comptime_expr
  = COMPTIME expr                              // single expr
  | COMPTIME BEGIN stmt* expr ";" END BEGIN    // block
  | COMPTIME IF expr ";"
      stmt* expr ";"
      (ELSE IF expr ";" stmt* expr ";")*
      (ELSE stmt* expr ";")?
      END IF                                    // comptime conditional
  ;
```

Functions evaluated entirely at compile time carry the
`comptime` modifier before `fn`.  This is handled as an
attribute-flavored prefix on the function declaration:

```
comptime_fn_decl
  = COMPTIME fn_decl
  ;
```

Comptime bindings inside blocks use `comptime let`:

```
comptime_let_stmt
  = COMPTIME LET pattern (":" type)? "=" expr ";"
  ;
```

Added to the `stmt` production in §6.1:

```
stmt
  = ...
  | comptime_let_stmt
  ;
```

### 6.8 Staging (Quote, Splice, Code Type)

`code(T)` is the type of a program fragment producing a value of
type `T` when executed (§17.2).  Quote lifts an expression into
a `code(T)` value; splice inserts one into a surrounding quote.

```
code_type
  = CODE "(" type ")"                          // type constructor
  ;

quote_expr
  = "`" "(" expr ")" "`"                       // backtick-paren quote
  ;

splice_expr
  = "~" atomic_expr                            // splice (prefix, already
                                               //   in prefix_expr as
                                               //   '~' atomic_expr;
                                               //   also serves as bitwise
                                               //   NOT — disambiguated by
                                               //   operand type at
                                               //   elaboration time)
  ;
```

`run(e)` evaluates a `code(T)` value at the enclosing stage.  It
is a stdlib function, not a grammar form.

`code_type` participates as an ordinary type in `atomic_type` via
`qualident` (the name `code` followed by type application).  It
is listed here for clarity; the grammar does not need a dedicated
production.

### 6.9 Unfold Expressions

Codata values (§3.5) are constructed via `unfold`:

```
unfold_expr
  = UNFOLD ("<" expr ">")?
      unfold_arm+
    END UNFOLD
  ;

unfold_arm
  = lower_ident "=>" expr ";"
  ;
```

The optional `<size_expr>` after `UNFOLD` binds the size
parameter for sized codata (§3.5 dim 20).  Each `unfold_arm`
binds a destructor name to its result for one observation.

Productivity (guardedness) is a kernel-level check not expressed
in the grammar (Coind-ν axiom, Appendix H.5 of the design spec).
The parser accepts any `unfold_expr` matching the production; the
typechecker rejects non-productive ones.

### 6.10 Sized Clause

Functions constructing codata carry a `sized` clause declaring
the size parameter (§3.5):

```
sized_clause
  = "sized" lower_ident ";"
  ;
```

Added to `spec_clauses` in §5.8 between `decreases_clause` and
the body:

```
spec_clauses
  = (where_clause | pre_clause | post_clause
  |  decreases_clause | sized_clause)*
  ;
```

`sized` is a contextual keyword — it is only recognized in
signature spec-clause position.


## 7. Types

```
type
  = FORALL "(" fn_param % "," ")" "," type
  | EXISTS "(" fn_param % "," ")" "," type
  | FN "(" lambda_param % "," ")" "=>" type
  | arrow_type
  ;

arrow_type
  = app_type "->" type                        // anonymous arrow
  | "#" app_type "->" type                    // implicit arrow
  | "(" typed_param % "," ")" "->" type      // named arrow
  | app_type ":" type                         // ascription
  | app_type
  ;

typed_param
  = lower_ident ":" type
  | "#" lower_ident ":" type
  ;

app_type
  = postfix_type "(" type_arg % "," ")"      // application: list(i64)
  | app_type "{" expr "}"                    // refinement on any app_type:
                                              //   i64 { x > 0 }
                                              //   list(i64) { length(x) > 0 }
                                              //   map(k, v) { size(x) <= 256 }
  | lower_ident ":" app_type "{" expr "}"    // named refinement:
                                              //   r: nat { r > x }
                                              //   (dependent return type;
                                              //    binds `r` for the predicate,
                                              //    `x` visible from outer scope)
  | app_type infix_op app_type               // operators in types
  | NOT app_type                              // negation in types
  | "-" app_type                              // negate in types
  | postfix_type
  ;

infix_op
  = "+" | "-" | "*" | "/" | "%"
  | "==" | "!=" | "<" | ">" | "<=" | ">="
  | AND | OR
  | "&" | "|" | "^" | "<<" | ">>"
  ;

type_arg
  = type
  | lower_ident ":" type                      // named: Lemma(post: P)
  ;

postfix_type
  = postfix_type "." lower_ident             // projection: r.field
  | atomic_type
  ;

atomic_type
  = "(" type ")"                              // grouping
  | "()"                                       // unit type
  | "(" lower_ident ":" type ")"             // named type
  | qualident                                  // type name
  | "_"                                        // wildcard / inferred
  | BEGIN stmt* expr ";" END BEGIN             // block in type position
  | match_expr                                 // types are expressions
  | if_expr
  ;
```


## 8. Patterns

```
pattern
  = or_pattern
  ;

or_pattern
  = spread_pattern ("|" spread_pattern)*
  ;

spread_pattern
  = as_pattern
  ;

as_pattern
  = app_pattern (AS lower_ident)?
  ;

app_pattern
  = upper_ident "(" ctor_field_pat % "," ")"  // constructor
  | upper_ident "(" "..." ")"                 // constructor, ignore fields
  | atomic_pattern
  ;

ctor_field_pat
  = pattern
  | lower_ident ":" pattern                   // named field
  | "..."                                      // rest
  ;

atomic_pattern
  = "(" pattern ")"
  | "(" pattern "," pattern % "," ")"        // tuple
  | "()"                                       // unit
  | lower_ident                                // variable binding
  | upper_ident                                // nullary constructor
  | "_"                                        // wildcard
  | literal                                    // constant
  | "-" int_lit                                // negative literal
  | "[" list_pattern "]"                      // list pattern
  | "{" field_pattern % "," "}"              // record pattern
  | "(" pattern ":" type ")"                 // ascribed
  ;

list_pattern
  = (* empty *)                                // []
  | pattern % ","                             // [a, b, c]
  | pattern % "," "," "..." lower_ident      // [a, b, ...rest]
  ;

field_pattern
  = qualident ":" pattern
  | "..."                                      // rest: { x: _, ... }
  ;
```


## 9. Qualified Names

```
qualident
  = (upper_ident ".")*  ident
  ;

ident
  = lower_ident
  | upper_ident
  ;
```


## 10. Machine Declarations

A machine is declared either by giving its members directly or by
composing existing machines via operators (§13.4).

```
machine_decl
  = MACHINE upper_ident type_params?
      machine_member+
    END MACHINE ";"
  | MACHINE upper_ident type_params?
      "=" machine_compose_expr ";"         // composition / alias
  | MACHINE upper_ident type_params?
      "=" machine_transformer_chain ";"    // transformer pipeline
  ;

machine_compose_expr
  = machine_compose_expr "*" machine_term          // product (parallel)
  | machine_compose_expr
      "*sync" "(" lower_ident % "," ")"
      machine_term                                  // sync product
  | machine_compose_expr ">>" machine_term         // sequence
  | machine_compose_expr "*" "{"
      WHILE expr
    "}"                                             // loop
  | match_expr                                      // choice
  | machine_term
  ;

machine_term
  = upper_ident type_args?
  | "(" machine_compose_expr ")"
  ;

machine_transformer_chain
  = machine_term ("|>" transformer_call)+
  ;

transformer_call
  = lower_ident "(" call_arg % "," ")"           // e.g. intercept(logger),
                                                  //       guard(perm),
                                                  //       monitor(metrics)
  ;

type_args
  = "(" type_arg % "," ")"
  ;

machine_member
  = state_decl
  | transition_decl
  | INITIAL upper_ident ";"
  | TERMINAL upper_ident ";"
  | machine_property
  | machine_event
  | CONCURRENCY concurrency_mode ";"
  ;

state_decl
  = STATE upper_ident ";"
  | STATE upper_ident "(" ctor_field % "," ")" ";"
  | STATE upper_ident "{" record_fields "}" ";"
  ;

transition_decl
  = TRANSITION lower_ident ":" state_ref "->" state_ref
      transition_modifier*
      ";"
  ;

state_ref
  = upper_ident
  | "(" upper_ident ("|" upper_ident)+ ")"   // state set
  | "*"                                        // any state
  ;

transition_modifier
  = REQUIRES expr
  | ENSURES expr
  | WITH effect_row
  | INVERSE lower_ident
  | ATOMIC
  | IDEMPOTENT "(" lower_ident ":" expr ")"
  | COMMUTATIVE
  | EMITS upper_ident "(" expr % "," ")"
  | ON_FAIL fail_mode
  | AFTER expr
  ;

fail_mode
  = RECOVERABLE "=>" STAY
  | CRITICAL "=>" GOTO upper_ident
  | ATOMIC "=>" ROLLBACK
  ;

machine_property
  = ASSERT expr ";"
  ;

// §13.5: temporal LTL operators (G, F, X, U) are ordinary identifiers
// imported from std/ltl; structural predicates (deadlock_free,
// deterministic, bounded_size, reachable) are library functions in
// std/machine_props; fairness (weak_fair, strong_fair) is used via
// implication.  No dedicated keyword-clause syntax for property
// categories.

machine_event
  = ON_EVENT lower_ident ":" state_ref "->" state_ref ";"
  | ON_SIGNAL lower_ident "." upper_ident "(" lower_ident ")"
      "=>" expr ";"
  ;

concurrency_mode
  = lower_ident                                // single_thread, exclusive, lock_free, tick_atomic
  ;
```


## 11. Contract Declarations

```
contract_decl
  = CONTRACT upper_ident FOR type
      contract_member+
    END CONTRACT ";"
  ;

contract_member
  = version_decl
  | access_decl
  | format_decl
  | INVARIANT expr ";"
  | ERRORS "{" variant_ctor+ "}" ";"
  | COMPATIBILITY "{" compat_entry+ "}" ";"
  ;

version_decl
  = VERSION int_lit "{" record_fields "}" ";"
  | VERSION int_lit "=" type migration_clause? ";"
  ;

migration_clause
  = MIGRATION migration_op+
  ;

migration_op
  = ADD lower_ident DEFAULT expr ";"
  | REMOVE lower_ident ";"
  | RENAME lower_ident "->" lower_ident ";"
  ;

access_decl
  = ACCESS lower_ident ":" access_mode ";"
  ;

access_mode
  = lower_ident                                // read_only, write_once, append_only, etc.
  ;

format_decl
  = FORMAT lower_ident "{" format_field+ "}" ";"
  ;

format_field
  = lower_ident ":" expr ";"
  ;

// Hardware bit-field layout declaration (§18.1).  Distinct from
// contract-nested format_decl above (§14.4 wire-format binding).
layout_decl
  = LAYOUT upper_ident ":" type ("=" "{" layout_field+ "}")? ";"
  ;

layout_field
  = lower_ident ":" expr ";"
  | VIRTUAL lower_ident ":" type "=" expr ";"
  ;

compat_entry
  = lower_ident "->" lower_ident ":" lower_ident ";"
  ;
```


## 12. Test and Bench

```
test_decl
  = TEST lower_ident effect_annot?
      stmt*
    END TEST ";"
  ;

bench_decl
  = BENCH lower_ident
      bench_member*
    END BENCH ";"
  ;

bench_member
  = stmt
  | CASE string_lit "=" expr ";"             // comparison case (§23.5,
                                              //   with @[compare] attribute
                                              //   on the enclosing bench)
  ;
```


## 13. Pragmas

```
pragma
  = "#" lower_ident string_lit?
  | "#" lower_ident int_lit
  ;
```


## 14. Typed Closers

Every block construct ends with `end KEYWORD`:

```
end begin          end fn              end match           end type
end if             end for             end while           end effect
end handle         end try             end select          end machine
end contract       end class           end instance        end impl
end test           end bench           end calc            end verify
end proof          end codata          end session         end branch
end unfold         end hardware fn     end hardware module end pipeline
end stage          end register_file   end reg             end on
end asm            end module type     end module functor  end struct
end extern         end refinement      end bisimulation
```

The keyword after `end` must match the opening keyword.

Composite closers (`end hardware fn`, `end module type`, etc.)
match the composite opening keyword sequence (§5.16, §5.17).


## 15. Delimiter Summary

```
( )     arguments, grouping, tuples, unit, constructor payloads
< >     type parameter introduction at definition site (with : kind)
[ ]     lists, indexing, attributes (with @ prefix), spread patterns
{ }     records, refinements, format/contract/access blocks
" "     all text: strings, format strings, raw strings, byte strings
` `     backtick escaping for reserved words as identifiers
```

`begin...end` for code blocks.  `{ }` is never a code block.


## 16. Reserved for Future

The following are contextual keywords — reserved only inside their
respective blocks, not globally:

```
Machine:    state transition initial terminal always never
            leads_to eventually responds reachable deadlock_free
            deterministic emits on_event on_signal priority
            concurrency atomic idempotent commutative inverse
            on_fail after requires ensures from goto stay rollback
            recoverable critical
            cancels preempts           // reserved — no current production
            refinement bisimulation    // reserved — no current production
            actor                      // reserved — no current production

Contract:   version migration compatibility access format
            invariant errors add remove rename default

Hardware:   hardware wire reg rising falling stage emit stall
            flush forward redirect pipeline onehot register_file

Register:   field virtual RW RO WO W1C W1S RC RS RSVD

Spec:       using

Effect:     multishot subsumes

Class:      law

Test:       case expect_compile_error expect_accepted matches
            test_machine test_contract test_theory test_metatheory
```
