import FX.Kernel.Typing
import FX.Kernel.Reduction
import FX.Kernel.Env

/-!
# Tree-recursive effect inference (E-2)

Implements Appendix B typing rules (E-Pure, E-Sub, E-Seq, E-App)
as a direct structural walk over elaborated `Term` trees,
composing each node's effect via `Effect.add`.

This replaces A12's `bodyConstRefs` union — which was both
over-approximate (every `const` reference counted as a call) and
under-approximate (calls through parameters missed) — with a
precise per-App-site computation that consults the kernel's
`Term.pi` return-effect field (landed in E-1).

## The three-sided rule

For each App site `f(x)` the effect row is the join of:

  1. `funcEff` — the effect of evaluating the function position.
     Usually `Tot` (lookups of consts or vars are pure).
  2. `argEff`  — the effect of evaluating the argument.
  3. `callEff` — the effect annotation on the outermost Pi of
     `f`'s type, consumed by this App.

This is exactly `G ⊢ f(x) : T [e1 ∨ e2 ∨ ef]` per Appendix B.

## Curry chains via `peelAppChain`

For multi-arg applications `f(a, b, c)` elaborated as
`app (app (app f a) b) c`, the head is the same `f` and the
total effect is the sum of each Pi layer's return effect peeled
in sequence.  Rather than recursively typing sub-applications,
we decompose the chain once into `(head, argCount)` and peel
exactly `argCount` Pi layers off the head's type — one effect
contribution per layer.

This gives the right answer for partial applications too:
`f(a)` with `f : A →{Tot} B →{IO} C` peels one Pi (Tot) and
leaves `B →{IO} C` un-fired; the IO is charged when a later
App consumes that arrow.

## Scope and limitations

E-2 (this file) handles **built-in effects** via the kernel's
`Grade.Effect` record, which Pi carries.  User-defined effects
(§9.5, `effect State<s> …`) land in E-4 with their own flow
through the type system; until then, A12's `constRefs` walk
still serves as a fallback for unknown effect names (the
string-subset half).
-/

namespace FX.Elab

open FX.Kernel

namespace EffectInference

/-- Walk an application chain, returning the ultimate function
    head and the number of arguments applied to it.  For
    `app (app (app f a) b) c`, returns `(f, 3)`.  For `f`
    (non-app), returns `(f, 0)`. -/
partial def peelAppChain : Term → Term × Nat
  | .app funcTerm _argTerm =>
    let (head, argCount) := peelAppChain funcTerm
    (head, argCount + 1)
  | other => (other, 0)

/-- Fetch the `returnEffect` of the Nth consecutively-applied Pi
    in a function's type.  `ty` is the function's type; we
    sequentially peel up to `argCount` Pi layers via `whnf`,
    accumulating each layer's return effect.  Non-Pi layers
    silently return the accumulated effect (conservative). -/
partial def peelPiLayers (globalEnv : GlobalEnv) (layerCount : Nat)
    (piType : Term) (accEff : Effect) : Effect :=
  match layerCount with
  | 0 => accEff
  | remaining + 1 =>
    let whnfType := Term.whnf Term.defaultFuel piType globalEnv
    match whnfType with
    | .pi _binderGrade _domain bodyType returnEffect =>
      peelPiLayers globalEnv remaining bodyType (Effect.add accEff returnEffect)
    | _ => accEff

/-- Compute the effect contributed by an application chain whose
    ultimate head is `headTerm` applied to `argCount` arguments.
    Looks up `headTerm`'s type via `GlobalEnv` (for consts) or
    `TypingContext` (for vars), then peels `argCount` Pi layers
    to accumulate their return effects.  Non-const, non-var
    heads (nested apps, lambdas) return `Effect.tot` — a
    conservative under-approximation that E-2's tree walk then
    supplements via the `funcEff` + `argEff` sides. -/
def callEffectOfAppChain (globalEnv : GlobalEnv) (context : TypingContext)
    (headTerm : Term) (argCount : Nat) : Effect :=
  match headTerm with
  | .const declName =>
    match globalEnv.lookupType? declName with
    | some declaredType => peelPiLayers globalEnv argCount declaredType Effect.tot
    | none              => Effect.tot
  | .var deBruijnIndex =>
    match context.lookup? deBruijnIndex with
    | some entry => peelPiLayers globalEnv argCount entry.typeTerm Effect.tot
    | none       => Effect.tot
  | _ => Effect.tot

/-- Fold an `Effect.add` over a list of terms, invoking the
    provided effect-inference function on each.  Used by
    container nodes (ctor args, indRec methods) whose effect is
    the union of their children's. -/
partial def foldEffect (recur : Term → Effect)
    : List Term → Effect :=
  fun terms => terms.foldl (fun acc term => Effect.add acc (recur term)) Effect.tot

/-- Collect the argument terms of an app chain into a list
    (outermost to innermost).  For `app (app (app f a) b) c`
    returns `[a, b, c]`. -/
partial def collectAppArgs : Term → List Term → List Term
  | .app funcTerm argTerm, acc =>
    collectAppArgs funcTerm (argTerm :: acc)
  | _otherwise, acc => acc

/-- Tree-recursive computation of a term's effect row per
    Appendix B.  Composes at each node via `Effect.add`:

      * Variable / const refs: `Tot` (lookup is pure).
      * `app func arg`: E-App as `funcEff ∨ argEff ∨ callEff`
        via `peelAppChain` + `callEffectOfAppChain`.  App chains
        are decomposed once per chain to fire every Pi-layer's
        return effect in a single traversal.
      * Lambdas / types / universes: `Tot` — construction is
        pure; the body's effect becomes the Pi's return-effect
        when this lambda is typed (handled at fn-decl elab site,
        not here).
      * Constructor: union of its type-arg and value-arg
        effects.  The ctor itself is pure data.
      * `indRec`: union of motive, target, and every method arm
        — the match consumer's effect is the join across arms.
      * `id` / `refl` / `idJ`: union of all children.
      * `quot` / `quotMk` / `quotLift`: union of all children.

    Self-recursive (no mutual needed) — the app case inlines
    `peelAppChain` + `collectAppArgs` + arg-effect fold in a
    single pass, threading `termEffect` through sub-traversals. -/
partial def termEffect (globalEnv : GlobalEnv) (context : TypingContext)
    : Term → Effect
  | .var _ => Effect.tot
  | .const _declName =>
    -- Bare name references are pure — reading the name doesn't
    -- invoke the fn.  Effects fire at App sites via Pi-layer
    -- peeling (`peelPiLayers` in `callEffectOfAppChain`).  This
    -- holds uniformly thanks to the §31.7 zero-arg desugaring
    -- in `elabFnSignature`: a fn `fn f() : T with IO` has
    -- declared type `Π (_ :_ghost Unit) → T @ IO`, and the
    -- call site `f()` is elaborated as `f unit_ctor` which is
    -- an App that fires the IO effect the standard way.
    Effect.tot
  | .type _ => Effect.tot
  | .forallLevel _ => Effect.tot
  | .pi _ _ _ _ => Effect.tot
  | .sigma _ _ _ => Effect.tot
  | .lam _ _ _ => Effect.tot
  | .ind _ _ => Effect.tot
  | .coind _ _ => Effect.tot
  | .refl _ => Effect.tot
  | termNode@(.app _ _) =>
    -- E-App composition: head effect + args effects + pi-layer effects
    let (headTerm, _) := peelAppChain termNode
    let argTerms := collectAppArgs termNode []
    let headEff := termEffect globalEnv context headTerm
    let argsEff := argTerms.foldl
      (fun acc arg => Effect.add acc (termEffect globalEnv context arg))
      Effect.tot
    let callEff :=
      callEffectOfAppChain globalEnv context headTerm argTerms.length
    Effect.add headEff (Effect.add argsEff callEff)
  | .ctor _ _ typeArgs valueArgs =>
    (typeArgs ++ valueArgs).foldl
      (fun acc arg => Effect.add acc (termEffect globalEnv context arg))
      Effect.tot
  | .indRec _ motive methods target =>
    let motiveEff := termEffect globalEnv context motive
    let targetEff := termEffect globalEnv context target
    let methodsEff := methods.foldl
      (fun acc method => Effect.add acc (termEffect globalEnv context method))
      Effect.tot
    Effect.add motiveEff (Effect.add targetEff methodsEff)
  | .id baseType lhs rhs =>
    Effect.add (termEffect globalEnv context baseType)
      (Effect.add (termEffect globalEnv context lhs)
        (termEffect globalEnv context rhs))
  | .idJ motive base eqProof =>
    Effect.add (termEffect globalEnv context motive)
      (Effect.add (termEffect globalEnv context base)
        (termEffect globalEnv context eqProof))
  | .quot carrier relation =>
    Effect.add (termEffect globalEnv context carrier)
      (termEffect globalEnv context relation)
  | .quotMk relation witness =>
    Effect.add (termEffect globalEnv context relation)
      (termEffect globalEnv context witness)
  | .quotLift lifted respects target =>
    Effect.add (termEffect globalEnv context lifted)
      (Effect.add (termEffect globalEnv context respects)
        (termEffect globalEnv context target))
  | .coindUnfold _typeName typeArgs arms =>
    -- Unfold introduces the coinductive value.  Its effect is
    -- the union of its sub-term effects; arm bodies are NOT
    -- eagerly evaluated at unfold time (they fire on observation
    -- via `coindDestruct`), but effect annotations still surface
    -- at the introducing fn's signature, so we union them
    -- conservatively rather than treat arms as `Tot`.  Matches
    -- the `ctor` arm's sub-term-union treatment.
    (typeArgs ++ arms).foldl
      (fun acc subTerm => Effect.add acc (termEffect globalEnv context subTerm))
      Effect.tot
  | .coindDestruct _typeName _destructorIndex target =>
    -- A single destructor observation inherits its target's
    -- effects.  The per-destructor effect row lives in the
    -- CoindSpec (future S6 typing work); at the term level,
    -- only the target's effects surface here.
    termEffect globalEnv context target

/-- Peel `paramCount` lambdas off a term, extending the typing
    context with each lambda's (grade, type) entry.  Used to
    enter the body of an elaborated function declaration: the
    top-level `Term.lam` chain encodes the surface parameters,
    and we want to inspect the inner body with those params in
    scope as context binders. -/
partial def peelLamsToBody (paramCount : Nat) (context : TypingContext)
    : Term → TypingContext × Term
  | .lam grade domain body =>
    if paramCount = 0 then (context, .lam grade domain body)
    else peelLamsToBody (paramCount - 1)
           (context.extend grade domain) body
  | otherwise => (context, otherwise)

/-- Top-level entry point: infer the effect row of a fn
    declaration's elaborated body.  `paramCount` tells how many
    lambdas to peel (one per declared surface parameter); those
    become context binders so higher-order references through
    parameters get their types looked up correctly. -/
partial def inferDeclBodyEffect (globalEnv : GlobalEnv) (paramCount : Nat)
    (elaboratedBody : Term) : Effect :=
  let (bodyContext, innerBody) :=
    peelLamsToBody paramCount TypingContext.empty elaboratedBody
  termEffect globalEnv bodyContext innerBody

end EffectInference

end FX.Elab
