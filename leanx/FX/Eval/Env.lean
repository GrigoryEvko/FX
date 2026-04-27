import FX.Eval.Value
import FX.Kernel.Env

/-!
# Evaluator environment

Per `fx_design.md` §31.7 (kernel translation pattern).  The
evaluator needs two layers of environment:

  * **Local environment (`locals`)** — a stack of runtime values
    indexed by de Bruijn.  Head of the list = index 0 (innermost
    binder).  Every beta-step pushes; every successful reduction
    pops on return.
  * **Global environment (`globals`)** — the `GlobalEnv` from
    `FX/Kernel/Env.lean`, threaded from the elaborator.  Bodies
    are still `Term` at this layer; the evaluator lazily
    elaborates to `Value` via `eval` when a const is demanded
    (task A11's inlining approach means globals get substituted
    at elab time, so the runtime `eval` rarely consults this
    except for debugging).

`EvalEnv` bundles both — the evaluator threads a single
`EvalEnv` through its recursion.
-/

namespace FX.Eval

open FX.Kernel

/-- Runtime environment for the evaluator.  `locals` is the
    de-Bruijn-indexed stack of bound values; `globals` is the
    program-wide declaration registry. -/
structure EvalEnv where
  /-- Bound values in scope, de Bruijn index 0 = head. -/
  locals  : List Value := []
  /-- Top-level decl registry (from `FX/Kernel/Env.lean`). -/
  globals : GlobalEnv  := GlobalEnv.empty
  deriving Repr, Inhabited

namespace EvalEnv

/-- The empty evaluator environment — no locals, no globals. -/
def empty : EvalEnv := {}

/-- An environment seeded with a global registry but no locals.
    This is what `fxi run` starts with before entering main's
    body. -/
def ofGlobals (globalEnv : GlobalEnv) : EvalEnv := { globals := globalEnv }

/-- Push a new local binding; returned evalEnv has `v` at index 0
    and every prior local at index `k+1` where it was at `k`. -/
def extend (value : Value) (evalEnv : EvalEnv) : EvalEnv :=
  { evalEnv with locals := value :: evalEnv.locals }

/-- Push many locals in the order given: the LAST listed value
    ends up at de Bruijn index 0 (it was pushed most recently). -/
def extendAll (values : List Value) (evalEnv : EvalEnv) : EvalEnv :=
  values.foldl (fun accEnv value => accEnv.extend value) evalEnv

/-- Look up the local at de Bruijn index `i`.  Returns `none` if
    out of range (open-variable / free-var case — the evaluator
    returns a `Value.neutral` for this position). -/
def lookupLocal? (localIndex : Nat) (evalEnv : EvalEnv) : Option Value :=
  evalEnv.locals[localIndex]?

/-- Size of the local stack — useful for span tracking when
    closures capture only a prefix. -/
def localSize (evalEnv : EvalEnv) : Nat := evalEnv.locals.length

/-- Replace the locals while preserving globals.  Used when a
    closure enters its captured environment — the outer caller's
    locals are shadowed by the capture. -/
def withLocals (evalEnv : EvalEnv) (newLocals : List Value) : EvalEnv :=
  { evalEnv with locals := newLocals }

end EvalEnv

end FX.Eval
