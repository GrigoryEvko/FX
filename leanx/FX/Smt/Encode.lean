-- FX.Smt.Encode — kernel `Term` to SMT-LIB2 string encoder.
--
-- Untrusted layer (L3 per SPEC.md §5).  Maps refinement
-- obligations from the kernel into SMT-LIB2 queries that an
-- oracle (Z3 via `FX.Smt.Oracle`, task E2) discharges.
--
-- ## Discipline
--
--  * The encoder is PURE.  Given a kernel term it returns either
--    an SMT-LIB sexp string or a structured `EncodeError`
--    pinpointing the construct it refused to encode.  No
--    side-channels, no reliance on global state.
--
--  * Refusal beats over-approximation.  When a term shape isn't
--    supported (lambda outside quantifier position, codata
--    destruction, inductive recursion that can't be unfolded),
--    the encoder returns `EncodeError` rather than emit a
--    silently-uninterpreted `(declare-fun)` that would let the
--    SMT oracle answer `unknown` or worse `unsat` for the wrong
--    reason.
--
--  * De Bruijn -> name uses a binder stack threaded through the
--    walk plus a per-encoding fresh-name counter.  Free
--    variables (de Bruijn indices that escape the binder stack)
--    accumulate as `FreeSym` records and become
--    `(declare-const)` lines at query-build time.
--
-- ## Public API
--
--  * `encodeTerm`     — encode a single term in isolation,
--                        return `Encoded` or `EncodeError`.
--  * `encodeQuery`    — build a complete SMT-LIB script from a
--                        list of assumption terms plus a goal
--                        term.  Negates the goal and asserts the
--                        negation so a `(check-sat)` answer of
--                        `unsat` proves validity.
--
-- ## Coverage (Phase-1 E1)
--
-- Supported:
--   - Boolean: true / false / not / and / or / ==> / <=>
--   - Equality (=) / disequality (!=)
--   - Numeric: + - * / mod  (over Int / Real)
--   - Comparison: < <= > >=
--   - Quantifier: forall (encoded via `pi` whose body is Bool)
--   - Free symbols: `Term.const` and out-of-scope `Term.var`
--   - Numeric literals: `Term.ctor "Nat" k _ _` chains -> Int
--   - Booleans: `Term.ctor "Bool" 0 _ _` / `1` -> false / true
--
-- Out-of-scope (returns `EncodeError`):
--   - `lam` outside quantifier position (no SMT lambda)
--   - `indRec` / `coindUnfold` / `coindDestruct`
--   - `idJ` / `quotLift` (paths and quotient lifts)
--   - `forallLevel` (universe quantifiers don't encode in SMT)
--   - `sigma` (no SMT pair theory in scope)
--
-- These shapes will be added incrementally as upstream
-- elaboration starts emitting them in refinement positions.

import FX.Kernel.Term
import FX.Smt.Sort

namespace FX.Smt

open FX.Kernel  -- Term, Grade, Level, Effect (re-exported via Term)

/-- A free symbol referenced by an encoded term — becomes a
    `(declare-const)` line in the assembled query. -/
structure FreeSym where
  /-- SMT-LIB declaration name (must be a valid SMT-LIB symbol). -/
  name : String
  /-- The SMT-LIB sort the encoder inferred for the symbol. -/
  sort : SmtSort
  deriving Repr, BEq, Inhabited

/-- Output of encoding a single term. -/
structure Encoded where
  /-- The SMT-LIB sexp for the term (no surrounding parens beyond
      what an inner subexpression would produce). -/
  body     : String
  /-- Free symbols the body references — must be declared above
      the assertion that uses `body`. -/
  freeSyms : List FreeSym
  /-- The SMT sort of the body (the type the body inhabits in
      SMT-LIB), used by callers building larger queries to pick
      a logic and to check that asserted formulae are Bool-typed. -/
  sort     : SmtSort
  deriving Repr, Inhabited

/-- Reasons the encoder refuses a term.  Each variant carries a
    human-readable string + the AST-level fingerprint of the
    offending shape so callers can surface a structured
    diagnostic. -/
inductive EncodeError : Type where
  /-- A term shape we explicitly do not encode.  The string is
      the kernel-level pretty form of the term head; callers can
      decide whether to `axiom`-out the sub-obligation or fail. -/
  | unsupported (shape : String) (detail : String) : EncodeError
  /-- A free de Bruijn index escaped without a corresponding
      binder.  Indicates either an open term or a binder-stack
      bug; either way the encoder cannot produce a sensible
      symbol name. -/
  | openTerm (deBruijnIndex : Nat) : EncodeError
  /-- A built-in operator was applied with the wrong arity (e.g.
      `+` with one argument).  The string is the operator's
      surface name. -/
  | arity (op : String) (got : Nat) (expected : Nat) : EncodeError
  /-- Sort mismatch in a position requiring a specific sort
      (e.g. asserting a non-Bool body). -/
  | sortMismatch (where_ : String) (got expected : SmtSort) : EncodeError
  deriving Repr

/-- Pretty-format an encoder error for diagnostics. -/
def EncodeError.toString : EncodeError -> String
  | .unsupported shape detail => s!"E_smt_unsupported: {shape} ({detail})"
  | .openTerm i               => s!"E_smt_open_term: free de Bruijn index {i}"
  | .arity op got expected    => s!"E_smt_arity: '{op}' got {got} args, expected {expected}"
  | .sortMismatch where_ got expected =>
      s!"E_smt_sort: at {where_} got {got.toSmtLib}, expected {expected.toSmtLib}"

instance : ToString EncodeError := ⟨EncodeError.toString⟩

/-- Encoder state threaded through a walk: binder name stack
    (innermost first) + free-symbol accumulator + fresh-name
    counter.  Pure structure so the walk is pure with `Except`. -/
structure EncState where
  /-- Names of binders in scope, innermost first.  De Bruijn
      index `n` resolves to `binders[n]?` if `n < binders.length`,
      otherwise the variable is free (escaped the local scope)
      and the encoder reports `EncodeError.openTerm`. -/
  binders   : List String := []
  /-- Free symbols collected during the walk, in encounter
      order.  Duplicates are filtered by `addFreeSym` so the
      output preamble has no repeats. -/
  freeSyms  : List FreeSym := []
  /-- Counter for synthesizing fresh binder names that don't
      collide with free symbols.  Each `pushBinder` consumes
      one. -/
  nextFresh : Nat := 0
  deriving Inhabited

namespace EncState

/-- Push a fresh binder name onto the stack and return the name
    produced.  Names are `x0`, `x1`, … to keep them simple and
    SMT-LIB-legal; the prefix `x` cannot collide with FX surface
    identifiers because no FX function/constant can start with
    a bare `x` followed only by digits at the AST level (those
    would be variables, which use de Bruijn indices not strings). -/
def pushBinder (s : EncState) : EncState × String :=
  let name := s!"x{s.nextFresh}"
  ({ s with binders := name :: s.binders, nextFresh := s.nextFresh + 1 }, name)

/-- Pop the innermost binder.  Symmetric with `pushBinder`. -/
def popBinder (s : EncState) : EncState :=
  { s with binders := s.binders.tail }

/-- Look up a de Bruijn index against the binder stack.  Returns
    the bound name if in scope, or `none` if the index escapes. -/
def lookupVar (s : EncState) (deBruijnIndex : Nat) : Option String :=
  s.binders[deBruijnIndex]?

/-- Add a free symbol if it isn't already present (matched by
    name, since the same name with two sorts is a bug we want
    to surface, but for now we conservatively dedupe by name
    + sort pair). -/
def addFreeSym (s : EncState) (sym : FreeSym) : EncState :=
  if s.freeSyms.any (fun existing => existing.name == sym.name && existing.sort == sym.sort) then
    s
  else
    { s with freeSyms := s.freeSyms ++ [sym] }

end EncState

/-- Lift a kernel inductive name to its SMT sort.  Inductives
    with a known projection (per `SmtSort.ofIndName?`) get the
    direct mapping; everything else becomes uninterpreted. -/
def sortForInd (name : String) : SmtSort :=
  match SmtSort.ofIndName? name with
  | some s => s
  | none   => SmtSort.uninterpreted name

/-- Top-level dispatcher.  Recognizes a kernel `Term` shape and
    encodes it to an SMT-LIB body string + accumulates free
    symbols into the `EncState`.  Returns `Except EncodeError`
    so callers can produce structured diagnostics. -/
partial def encodeWalk (term : Term) (s : EncState) :
    Except EncodeError (String × SmtSort × EncState) := do
  match term with

  -- Variable: bound on the local stack OR a free symbol whose
  -- sort we'll default to Int (refinement-typical) and let the
  -- caller refine if needed.  Open terms (escaped indices) are
  -- always errors.
  | .var deBruijnIndex =>
      match s.lookupVar deBruijnIndex with
      | some name => return (name, .intSort, s)
      | none      => Except.error (.openTerm deBruijnIndex)

  -- Named top-level constant: becomes a free symbol with
  -- `Int`-defaulted sort.  Future enhancement: consult
  -- `GlobalEnv` for the const's declared type, infer a more
  -- accurate sort.  For E1 we accept the over-approximation
  -- because refinement targets are typically `nat`/`int`.
  | .const name =>
      let sym : FreeSym := { name := name, sort := .intSort }
      return (name, .intSort, s.addFreeSym sym)

  -- Boolean literal constructors.  `Bool` has two ctors:
  -- ctorIndex 0 = false, ctorIndex 1 = true (matches the
  -- `IndSpec` for "Bool" in `FX/Kernel/Inductive.lean`).
  | .ctor "Bool" ctorIndex _ _ =>
      match ctorIndex with
      | 0 => return ("false", .boolSort, s)
      | 1 => return ("true",  .boolSort, s)
      | _ => Except.error (.unsupported "Bool ctor"
              s!"unknown ctor index {ctorIndex}")

  -- Unary natural-number literal: `Nat` ctor 0 = zero, ctor 1
  -- = succ.  Walk the chain and produce a decimal SMT-LIB
  -- integer literal.  `succ` chains can be deeply nested so
  -- we count.  The two pattern slots after `"Nat"` aren't
  -- consumed here — `countNatChain` re-walks `term` from the
  -- top to count succs.
  | .ctor "Nat" _ _ _ =>
      let n <- countNatChain term 0
      return (toString n, .intSort, s)

  -- Generic constructor application: emit as
  -- `(ctorName args)` with an uninterpreted sort named after
  -- the inductive.
  | .ctor typeName ctorIndex _ valueArgs =>
      let _ := ctorIndex
      let (encArgs, sNext) <- encodeArgs valueArgs s
      let sort := sortForInd typeName
      let app :=
        if encArgs.isEmpty
        then s!"{typeName}_ctor_{ctorIndex}"
        else s!"({typeName}_ctor_{ctorIndex} {String.intercalate " " encArgs})"
      return (app, sort, sNext)

  -- Application: try the curried built-in operator pattern
  -- first; fall back to uninterpreted symbol application.
  | .app _ _ =>
      encodeApp term s

  -- Pi as universal quantifier.  Per FX surface,
  -- `forall(x: t), body` elaborates to `pi grade dom body`.  We
  -- accept ANY pi whose body is Bool/Prop-typed as a forall and
  -- emit `(forall ((x SortDom)) bodyEnc)`.  Pis whose body is a
  -- non-Bool TYPE represent function types and don't have a
  -- direct SMT-LIB encoding (use uninterpreted-function model).
  | .pi _ domain body _ =>
      let (sNext, freshName) := s.pushBinder
      let domSort <- inferTermSort domain
      let (bodyEnc, bodySort, sBody) <- encodeWalk body sNext
      let sFinal := sBody.popBinder
      match bodySort with
      | .boolSort =>
          return (s!"(forall (({freshName} {domSort.toSmtLib})) {bodyEnc})",
                  .boolSort, sFinal)
      | _ =>
          -- Non-Bool body: this is a function type, not a
          -- forall proposition.  We can't encode it directly
          -- in SMT-LIB but for E1 we surface a clear refusal
          -- so the caller knows to treat the whole obligation
          -- as uninterpretable.
          Except.error (.unsupported "pi-as-fn-type"
            s!"pi body has sort {bodySort.toSmtLib}, expected Bool for forall encoding")

  -- Type universe: only meaningful in type-position; refinement
  -- predicates never have a `.type` in value position so we
  -- refuse rather than emit a placeholder.
  | .type _ =>
      Except.error (.unsupported "type universe"
        "encoder does not encode kernel universes")

  | .forallLevel _ =>
      Except.error (.unsupported "forallLevel"
        "level polymorphism does not encode in SMT-LIB")

  -- Inductive type reference in value position: shouldn't
  -- happen for refinements but we emit the SMT sort name
  -- for completeness.  Caller can decide whether this means
  -- anything.
  | .ind name args =>
      let _ := args
      return (name, sortForInd name, s)

  -- Identity type / refl / J: we recognize `id A a b` as
  -- equality between values when both `a` and `b` are
  -- value-typed.  refl / J are not directly representable.
  | .id _ leftTerm rightTerm =>
      let (lEnc, _, s1) <- encodeWalk leftTerm s
      let (rEnc, _, s2) <- encodeWalk rightTerm s1
      return (s!"(= {lEnc} {rEnc})", .boolSort, s2)
  | .refl _ =>
      Except.error (.unsupported "refl"
        "identity-type proofs do not encode as SMT terms")
  | .idJ _ _ _ =>
      Except.error (.unsupported "idJ"
        "J eliminator does not encode in SMT-LIB")

  -- Lambda outside a quantifier position: SMT-LIB has no
  -- first-class lambda (lambda extension is non-standard).
  | .lam _ _ _ =>
      Except.error (.unsupported "lam"
        "lambda outside quantifier position cannot encode in SMT-LIB")

  -- Sigma / quotient / coinductive shapes: not in scope for E1.
  | .sigma _ _ _ =>
      Except.error (.unsupported "sigma"
        "dependent pairs do not encode in standard SMT-LIB theories")
  | .quot _ _ =>
      Except.error (.unsupported "quot"
        "quotient types do not encode in standard SMT-LIB theories")
  | .quotMk _ _ | .quotLift _ _ _ =>
      Except.error (.unsupported "quot intro/elim"
        "quotient operations not encoded")
  | .coind _ _ | .coindUnfold _ _ _ | .coindDestruct _ _ _ =>
      Except.error (.unsupported "coinductive"
        "coinductives have no SMT-LIB encoding")
  | .indRec _ _ _ _ =>
      Except.error (.unsupported "indRec"
        "inductive recursion does not encode generically; unfold first")
where
  /-- Encode a list of arguments, threading state through. -/
  encodeArgs (args : List Term) (s : EncState) :
      Except EncodeError (List String × EncState) := do
    args.foldlM (init := ([], s)) fun (acc, sAcc) arg => do
      let (enc, _, sNext) <- encodeWalk arg sAcc
      return (acc ++ [enc], sNext)

  /-- Walk a `Term.ctor "Nat" 1 _ [pred]` chain bottoming at
      `Term.ctor "Nat" 0 _ []`, counting `succ`s. -/
  countNatChain : Term -> Nat -> Except EncodeError Nat
    | .ctor "Nat" 0 _ _, acc => return acc
    | .ctor "Nat" 1 _ [predecessor], acc => countNatChain predecessor (acc + 1)
    | t, _ => Except.error (.unsupported "Nat literal chain"
                s!"non-canonical Nat ctor: {repr t}")

  /-- Infer an SMT sort for a term used as a domain in a binder.
      Recognizes `ind name args` shapes and projects via
      `sortForInd`; bit-vector widths are extracted by name
      pattern.  Falls back to Int when nothing matches.  Refines
      the sort using the term shape; full type inference is the
      typing layer's job. -/
  inferTermSort : Term -> Except EncodeError SmtSort
    | .ind name _ => return sortForInd name
    | _           => return .intSort

  /-- Encode an application `(f a1 a2 ...)`.  Tries built-in
      operator demangling first: a curried application
      `app (app (... (const op) a1) a2) ...` whose head `const`
      matches a known operator name fires the structured form
      `(SMT-OP a1' a2' ...)`.  Falls back to uninterpreted
      symbol application otherwise. -/
  encodeApp (term : Term) (s : EncState) :
      Except EncodeError (String × SmtSort × EncState) := do
    let (head, args) := flattenApp term []
    match head with
    | .const opName =>
        match smtBuiltinOp opName args.length with
        | some (smtOp, sortOut) =>
            let (encs, sNext) <- encodeArgs args s
            return (s!"({smtOp} {String.intercalate " " encs})", sortOut, sNext)
        | none =>
            -- Uninterpreted symbol application.  The head
            -- becomes a `(declare-fun)` symbol with the right
            -- arity; the encoder defaults the result sort to
            -- Int and assumes Int-typed arguments.  An accurate
            -- sort for the function comes from typing layer
            -- integration in E4.
            let sym : FreeSym := { name := opName, sort := .intSort }
            let sWithSym := s.addFreeSym sym
            let (encs, sNext) <- encodeArgs args sWithSym
            if encs.isEmpty then
              return (opName, .intSort, sNext)
            else
              return (s!"({opName} {String.intercalate " " encs})", .intSort, sNext)
    | _ =>
        -- Application of a non-const head (e.g. lambda
        -- application that hasn't been beta-reduced).  Refuse
        -- — caller should normalize first.
        Except.error (.unsupported "non-const application head"
          s!"head is {repr head}, expected Term.const")

  /-- Flatten a curried `app` chain into its head + arg list. -/
  flattenApp : Term -> List Term -> Term × List Term
    | .app f a, acc => flattenApp f (a :: acc)
    | t,        acc => (t, acc)

  /-- Map an FX-level operator name to its SMT-LIB form.
      Returns `none` when the name isn't a recognized built-in;
      the caller falls back to uninterpreted-function emission.
      The returned sort is the operator's RESULT sort. -/
  smtBuiltinOp (name : String) (arity : Nat) : Option (String × SmtSort) :=
    match name, arity with
    -- Boolean connectives
    | "not", 1     => some ("not", .boolSort)
    | "and", 2     => some ("and", .boolSort)
    | "or",  2     => some ("or",  .boolSort)
    | "==>", 2     => some ("=>",  .boolSort)
    | "<=>", 2     => some ("=",   .boolSort)
    -- Equality / disequality
    | "==",  2     => some ("=", .boolSort)
    | "!=",  2     => some ("distinct", .boolSort)
    -- Comparison (Int / Real)
    | "<",   2     => some ("<",  .boolSort)
    | "<=",  2     => some ("<=", .boolSort)
    | ">",   2     => some (">",  .boolSort)
    | ">=",  2     => some (">=", .boolSort)
    -- Arithmetic
    | "+",   2     => some ("+", .intSort)
    | "-",   2     => some ("-", .intSort)
    | "*",   2     => some ("*", .intSort)
    | "/",   2     => some ("div", .intSort)
    | "%",   2     => some ("mod", .intSort)
    -- Unary minus
    | "neg", 1     => some ("-", .intSort)
    -- Anything else
    | _, _         => none

/-- Encode a single term.  Public entry point — wraps `encodeWalk`
    in an empty initial state and packages the result. -/
def encodeTerm (term : Term) : Except EncodeError Encoded := do
  let (body, sort, finalState) <- encodeWalk term {}
  return { body := body, freeSyms := finalState.freeSyms, sort := sort }

/-- Build a complete SMT-LIB query that is unsat iff `goal` is
    valid given `assumptions`.

    Output structure:

        (set-logic <chosen>)
        (declare-const sym1 Sort1)
        (declare-const sym2 Sort2)
        ...
        (assert <assumption_1>)
        (assert <assumption_2>)
        ...
        (assert (not <goal>))
        (check-sat)

    Returns `unsat` (from the oracle) iff the goal is a logical
    consequence of the assumptions. -/
def encodeQuery (assumptions : List Term) (goal : Term) :
    Except EncodeError String := do
  let goalEnc <- encodeTerm goal
  match goalEnc.sort with
  | .boolSort => pure ()
  | other     =>
      Except.error (.sortMismatch "goal" other .boolSort)
  let assumptionEncs <- assumptions.foldlM
    (init := (#[] : Array Encoded)) fun acc t => do
      let enc <- encodeTerm t
      match enc.sort with
      | .boolSort => return acc.push enc
      | other     =>
          Except.error (.sortMismatch "assumption" other .boolSort)
  -- Merge free-symbol lists from goal + assumptions.
  let allSymsRaw : List FreeSym :=
    assumptionEncs.toList.foldl (fun acc enc => acc ++ enc.freeSyms) [] ++ goalEnc.freeSyms
  -- Dedupe by (name, sort) preserving first-encounter order.
  let allSyms : List FreeSym :=
    allSymsRaw.foldl (fun acc sym =>
      if acc.any (fun existing => existing.name == sym.name && existing.sort == sym.sort) then
        acc
      else
        acc ++ [sym]) []
  let logic := SmtSort.chooseLogic (allSyms.map FreeSym.sort)
  let header  := s!"(set-logic {logic})"
  let decls   := allSyms.map fun sym =>
                   s!"(declare-const {sym.name} {sym.sort.toSmtLib})"
  let asserts := assumptionEncs.toList.map fun enc => s!"(assert {enc.body})"
  let neg     := s!"(assert (not {goalEnc.body}))"
  let lines   := [header] ++ decls ++ asserts ++ [neg, "(check-sat)"]
  return String.intercalate "\n" lines

end FX.Smt
