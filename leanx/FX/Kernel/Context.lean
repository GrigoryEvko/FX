import FX.Kernel.Term
import FX.Kernel.Substitution

/-!
# Typing contexts

Per `fx_design.md` §6.2 (typing rules) and §6.3.1 (practical
grade checking).

A typing context `context` maps each in-scope de Bruijn index to a
triple `(grade, type, nameHint?)`:

  * `grade` is the resource-usage annotation declared at the
    binder (`:_g` in the concrete syntax).
  * `type` is the declared type.
  * `nameHint?` is an optional diagnostic name (purely for
    error messages — index lookups are positional).

## Representation

We use a reversed snoc list: the **head** is index 0 (nearest
binder), the **tail** extends into outer scopes.  Pushing a new
binder prepends to the head; popping a binder removes the head.
Lookup by index is a simple `List.get?`.

## Level-scope tracking (A10)

Universe-polymorphism level scope — how many `Term.forallLevel`
binders enclose the expression being checked — is threaded
through `infer`/`check`/`inferType` as a separate `Nat`
parameter rather than as a context field.  The reasoning: the
existing `abbrev TypingContext := List TypingContextEntry`
design is load-bearing for ~40 test call sites that use `[]` /
`[{...}]` as bare list literals; promoting `TypingContext` to a
struct breaks Coe elaboration (bare `[]` has no element type to
infer), cascading into every test.  Level count lives as a
threaded argument; the change is localized to the
`.forallLevel` and `.type` cases of `infer`.

## Grade context operations

Three operations on whole contexts, each realizing a typing-rule
step:

  * `scale : Usage → TypingContext → TypingContext` — pointwise scalar multiplication
    on usage grades.  Used in the App rule: `p1 + r * p2`.
  * `add   : TypingContext → TypingContext → Option TypingContext` — pointwise addition
    (parallel combine).  Returns `none` when the contexts
    disagree on shape.
  * `divByUsage : Usage → TypingContext → TypingContext` — Wood-Atkey context
    division used in Pi-intro.  `Usage.div g.usage u`.
-/

namespace FX.Kernel

/- `Term`'s structural `BEq` lives in `FX/Kernel/Term.lean`. -/

/--
A single context entry: the grade under which a variable is
declared, its type, and an optional name hint for diagnostics.
-/
structure TypingContextEntry where
  grade    : Grade
  typeTerm : Term
  nameHint : Option String := none
  deriving Repr, Inhabited

/--
A typing context.  Index 0 is the head (nearest binder).
-/
abbrev TypingContext := List TypingContextEntry

namespace TypingContext

/-- The empty context — no bindings. -/
def empty : TypingContext := []

/-- Push a new binding.  `extend grade typeTerm context` prepends
    the entry so the new variable has de Bruijn index 0. -/
def extend (grade : Grade) (typeTerm : Term) (context : TypingContext)
    : TypingContext :=
  { grade := grade, typeTerm := typeTerm } :: context

/-- Push with an optional name hint for diagnostics. -/
def extendNamed (grade : Grade) (typeTerm : Term) (name : String)
    (context : TypingContext) : TypingContext :=
  { grade := grade, typeTerm := typeTerm, nameHint := some name } :: context

/-- Look up the entry at de Bruijn index `index`.  Returns `none`
    when the index is out of range (free variable in malformed
    term). -/
def lookup? (index : Nat) (context : TypingContext) : Option TypingContextEntry := context[index]?

/-- Length of the context — the number of in-scope binders. -/
def size (context : TypingContext) : Nat := context.length

/-! ### Grade context operations -/

/--
Pointwise scale by a `Usage`.  Each entry's `grade.usage` is
replaced by `Usage.mul u g.usage`.  Other grade dimensions are
unchanged — scaling those would demand dimension-specific rules
which Phase-2 defers to the typing-rule layer.
-/
def scale (factor : Usage) (context : TypingContext) : TypingContext :=
  context.map (fun entry => { entry with grade := { entry.grade with usage := Usage.mul factor entry.grade.usage } })

/--
Pointwise grade addition.  Returns `none` if the two contexts
have different shapes (different lengths, mismatched types).

Grade of each entry is combined via `Grade.add`, which is
partial — a partial-op failure (Overflow cross-top, Rep c⊔packed)
propagates to return `none` here.

Types are compared structurally via `Term.structEq`; the typing
layer normalizes before calling `add` when conversion-up-to-beta
is needed.
-/
partial def add : TypingContext → TypingContext → Option TypingContext
  | [], [] => some []
  | leftEntry :: leftRest, rightEntry :: rightRest =>
    if ¬ (leftEntry.typeTerm == rightEntry.typeTerm) then none
    else
      match Grade.add leftEntry.grade rightEntry.grade with
      | none => none
      | some combinedGrade =>
        match add leftRest rightRest with
        | none => none
        | some combinedRest => some ({ leftEntry with grade := combinedGrade } :: combinedRest)
  | _, _ => none

/--
Wood-Atkey context division (per `fx_design.md` §6.2 Lam rule
and §27.1).  Each binding's `grade.usage` is divided by `u`,
where `Usage.div` is total on the three-element carrier
(`1/omega = 0` is the key case blocking Atkey-2018's Lam bug).
Other grade fields are unchanged.
-/
def divByUsage (divisor : Usage) (context : TypingContext) : TypingContext :=
  context.map (fun entry => { entry with grade := { entry.grade with usage := Usage.div entry.grade.usage divisor } })

end TypingContext

end FX.Kernel
