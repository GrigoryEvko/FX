import FX.Kernel.Term
import FX.Kernel.Inductive
import FX.Kernel.Coinductive

/-!
# Global definition environment

Per `fx_design.md` §31.8 (Lean reference implementation) and
§10.15 (body-visibility discipline).  A `GlobalEnv` holds the
top-level declarations currently in scope for a typing / eval
session — every `Term.const n` in the kernel refers back to an
entry here by name.

## Phase 2.2 (task A11) scope

  * `GlobalEntry` — type + body + optional transparency marker.
  * `GlobalEnv` — an ordered list of entries plus O(n) `lookup?`
    by name.  List rather than HashMap because the entries are
    few (dozens per module) and the order matters for
    deterministic audit output (`fxi dump --kernel`).
  * `add` / `lookup?` / `size` / `names` — the core API.
  * delta-reduction is NOT automatic at `whnf`: the kernel treats
    every `const n` as opaque unless the typing layer explicitly
    calls `Env.unfold?` — this matches §10.15's opaque-by-default
    body-visibility.  `@[transparent]` on a decl flips the flag.

## Why List, not HashMap

Lean 4's `HashMap` in the current stdlib doesn't derive `Repr`
cleanly, which we want for `fxi dump --kernel` emission.  An
association list with a linear `find?` is fine at the sizes we
see (Phase 2.2 tops out at ~10 decls per file).  A later phase
swaps to a `RBMap` once `fxi test DIR` needs the throughput.
-/

namespace FX.Kernel

/-- One entry in the global environment. -/
structure GlobalEntry where
  name        : String
  type        : Term
  body        : Term
  /-- When `true`, `Env.unfold?` will substitute the body at
      conversion / reduction sites.  Defaults to `false` —
      opaque-by-default per `fx_design.md` §10.15. -/
  transparent : Bool := false
  /-- Declared trust level of this decl (§6.3 dim 9 / §10.6).
      The effective trust `GlobalEnv.transitiveTrust` is the
      `min` of this field and the transitive trust of every
      decl referenced via `Term.const` in the body.  Default is
      `Trust.tested` — the kernel registers a decl only after
      it type-checks, which is stronger than `sorryT`/`assumed`/
      `external` but weaker than `verified` (which requires a
      machine proof).  `@[axiom]` flips to `assumed`; `sorry`
      bodies to `sorryT`; FFI/deserializer outputs to
      `external`; `@[verified]` to `verified`. -/
  trust       : Trust := Trust.tested
  /-- Declared parameter names, in positional order.  Used by
      the elaborator to route named call arguments (§4.1) to
      their positional slots — the kernel doesn't care about
      names (`Term.pi`'s binder has no name), but surface code
      calls `f(a: x, b: y)` and the elab needs the param names
      to reorder.  Empty list for non-fn decls and for fn
      decls with no params. -/
  paramNames  : List String := []
  /-- Declared effect row — the `with IO, Alloc, eff, …` names
      parsed from the fn signature (task A12 / B3 proper).
      Empty means `Tot` (pure + terminating).  The elaborator
      checks that every App site's callee effects ⊆ enclosing
      fn's declared effects.  Stored as raw strings because
      Phase-2 effect names (`IO`, `Alloc`, `Read`, `Write`,
      `Async`, `Div`, `Ghost`, `Exn`) are a closed lowercase
      set; future user-defined effects (§9.5) will require
      kernel-side lookup. -/
  effects     : List String := []
  deriving Repr, Inhabited

/-- The global environment.  Head-prepend means newer decls
    shadow older under `lookup?` (which is `List.find?`).

    `userSpecs` holds inductive families declared in the source
    file (B9 ADT translation).  Registered during elaboration's
    pass 1 and consulted by every kernel site that currently
    calls `Inductive.specByName?` — typing/reduction/eval all
    thread `globalEnv` and pass `globalEnv.userSpecs` down.

    `revealedNames` is the Q45 local-reveal override for
    `fx_design.md` §10.15 `reveal f;` directives inside
    `verify ... exports` blocks.  `unfold?` treats any name in
    this list as if its `transparent` flag were `true` — the
    typing layer populates `revealedNames` before entering a
    verify block's body and resets it at block exit, giving a
    one-level unfold per Lean 4's `simp only [f]` semantics.

    The list is SEPARATE from the decl's `transparent` field so
    that the audit trail stays clean: `fxi dump --kernel` shows
    the original declaration's opacity unchanged; `revealedNames`
    is part of the caller's typing context, not the declaration.
    A reveal is NOT persistent — it must be re-added to
    descendant envs explicitly. -/
structure GlobalEnv where
  entries        : List GlobalEntry := []
  userSpecs      : List IndSpec     := []
  /-- User-declared coinductive specs (S11 session_decl translation
      via `FX.Derived.Session.translate`).  One source-level
      session declaration produces a list of CoindSpecs (one per
      distinct sub-state); they all land here in declaration
      order.  Future S6 / R3 kernel coind typing will consult
      this list at every `Term.coind` reference. -/
  userCoindSpecs : List CoindSpec   := []
  revealedNames  : List String      := []
  deriving Repr, Inhabited

namespace GlobalEnv

/-- The empty environment. -/
def empty : GlobalEnv := {}

/-- Look up an entry by name.  Returns the first match from the
    head of the list (newest binding wins). -/
def lookup? (globalEnv : GlobalEnv) (name : String) : Option GlobalEntry :=
  globalEnv.entries.find? (·.name == name)

/-- True iff a decl with this name is registered. -/
def contains (globalEnv : GlobalEnv) (name : String) : Bool :=
  (globalEnv.lookup? name).isSome

/-- Prepend a new entry.  If the name already exists, the new
    entry shadows the old at `lookup?` but the old stays in the
    list — this keeps `fxi dump --kernel` emission reproducible
    when the same name is re-declared. -/
def add (globalEnv : GlobalEnv) (entry : GlobalEntry) : GlobalEnv :=
  { globalEnv with entries := entry :: globalEnv.entries }

/-- Register a user-declared inductive spec (B9 ADT translation).
    Newer specs shadow older under `specByName?` lookup, matching
    the `add` discipline for value-level entries. -/
def addUserSpec (globalEnv : GlobalEnv) (spec : IndSpec) : GlobalEnv :=
  { globalEnv with userSpecs := spec :: globalEnv.userSpecs }

/-- Look up an inductive spec by name, consulting both user specs
    (registered via `addUserSpec`) and the hardcoded prelude
    specs.  User specs shadow prelude specs — a user-declared
    `type Bool ...` overrides the built-in `Bool` in its scope. -/
def specByName? (globalEnv : GlobalEnv) (name : String) : Option IndSpec :=
  Inductive.specByName? name globalEnv.userSpecs

/-- True iff a spec with this name is registered (user or prelude). -/
def knownSpec (globalEnv : GlobalEnv) (name : String) : Bool :=
  (globalEnv.specByName? name).isSome

/-- Register a user-declared coinductive spec (S11 session_decl
    translation).  Newer specs shadow older under
    `coindSpecByName?`. -/
def addUserCoindSpec (globalEnv : GlobalEnv) (spec : CoindSpec)
    : GlobalEnv :=
  { globalEnv with userCoindSpecs := spec :: globalEnv.userCoindSpecs }

/-- Register many coinductive specs at once, preserving the
    incoming declaration order.  Used by the session-decl
    elaborator: `translate` returns specs in
    reverse-topological order (continuations before referents);
    `addAll` prepends them in iteration order, leaving the
    final list with the LAST-emitted (root) at the head. -/
def addUserCoindSpecs (globalEnv : GlobalEnv) (specs : List CoindSpec)
    : GlobalEnv :=
  specs.foldl (fun envSoFar spec => envSoFar.addUserCoindSpec spec) globalEnv

/-- Look up a coinductive spec by name in the user registry.
    Phase-2 has no prelude coind specs (all coinductives are
    user-declared via `session NAME ... end session;` until
    R2a's productive-coinduction primitives land). -/
def coindSpecByName? (globalEnv : GlobalEnv) (name : String)
    : Option CoindSpec :=
  globalEnv.userCoindSpecs.find? (·.name == name)

/-- True iff a coinductive spec with this name is registered. -/
def knownCoindSpec (globalEnv : GlobalEnv) (name : String) : Bool :=
  (globalEnv.coindSpecByName? name).isSome

/-- Convenience: add an entry from raw fields.  `transparent`,
    `trust`, and `paramNames` default to `false` / `Trust.tested`
    / `[]` respectively — the cold-path defaults for a freshly-
    elaborated decl. -/
def addDecl (globalEnv : GlobalEnv) (name : String) (type body : Term)
    (transparent : Bool := false) (trust : Trust := Trust.tested)
    (paramNames : List String := []) (effects : List String := []) : GlobalEnv :=
  globalEnv.add
    { name := name
    , type := type
    , body := body
    , transparent := transparent
    , trust := trust
    , paramNames := paramNames
    , effects := effects }

/-- Look up the declared effect row of `name` or `none` if
    unregistered.  Empty list = `Tot`. -/
def lookupEffects? (globalEnv : GlobalEnv) (name : String)
    : Option (List String) :=
  (globalEnv.lookup? name).map (·.effects)

/-- Look up the declared parameter names of `name`, or `none` if
    unregistered.  Empty list for non-fn decls. -/
def lookupParamNames? (globalEnv : GlobalEnv) (name : String)
    : Option (List String) :=
  (globalEnv.lookup? name).map (·.paramNames)

/-- Number of entries (counts shadowed duplicates). -/
def size (globalEnv : GlobalEnv) : Nat := globalEnv.entries.length

/-- All registered names in insertion order (newest first). -/
def names (globalEnv : GlobalEnv) : List String :=
  globalEnv.entries.map (·.name)

/-- Look up the type of `name`, or `none` if unregistered. -/
def lookupType? (globalEnv : GlobalEnv) (name : String) : Option Term :=
  (globalEnv.lookup? name).map (·.type)

/-- Look up the body of `name`, or `none` if unregistered. -/
def lookupBody? (globalEnv : GlobalEnv) (name : String) : Option Term :=
  (globalEnv.lookup? name).map (·.body)

/-- delta-unfold: if `name` is registered AND (transparent OR
    revealed), return the body.  Otherwise `none`.  The kernel
    calls this only at explicit unfolding sites — opaque-by-
    default per §10.15.

    Q45 extension: a name listed in `revealedNames` unfolds even
    when the decl's own `transparent` flag is `false`.  This
    implements the §10.15 `reveal f;` directive: the verify
    block's typing loop calls `env.withReveal "f" |> whnf ...`
    so `f` unfolds locally without changing the published
    declaration's opacity. -/
def unfold? (globalEnv : GlobalEnv) (name : String) : Option Term :=
  match globalEnv.lookup? name with
  | some entry =>
    if entry.transparent || globalEnv.revealedNames.contains name then
      some entry.body
    else
      none
  | none       => none

/-- True iff `name` would be unfolded by `unfold?` in this env.
    Exposed for inspection / testing; kernel sites go through
    `unfold?` directly. -/
def isTransparent? (globalEnv : GlobalEnv) (name : String) : Bool :=
  (globalEnv.unfold? name).isSome

/-- Return a new env where `name` is treated as-if-transparent
    for the duration of any `whnf`/`normalize`/`convEq` call
    threaded through the returned env.  The original decl's
    `transparent` field stays unchanged — reveal is a scoping
    override, not a persistent decl edit.

    Idempotent: revealing an already-revealed (or transparent)
    name is a no-op.  Order-insensitive: revealing A then B is
    the same as B then A. -/
def withReveal (globalEnv : GlobalEnv) (name : String) : GlobalEnv :=
  if globalEnv.revealedNames.contains name then
    globalEnv
  else
    { globalEnv with revealedNames := name :: globalEnv.revealedNames }

/-- Reveal a whole batch of names at once.  Matches §10.15's
    multi-reveal pattern:

    ```
    verify
      reveal outer;
      reveal inner_1;
      reveal inner_2;
      assert ...;
    end verify;
    ```

    The surface elaborator folds the reveal list through
    `withReveals` before typing the verify body. -/
def withReveals (globalEnv : GlobalEnv) (names : List String) : GlobalEnv :=
  names.foldl (init := globalEnv) (·.withReveal ·)

/-- Clear all reveals.  Used at verify block exit — the caller
    saves the env, enters with reveals, then restores the
    pre-verify env to re-enforce opacity below the block per
    §10.15 "Facts derived from the unfolded body do not escape
    the block unless listed in `exports`". -/
def clearReveals (globalEnv : GlobalEnv) : GlobalEnv :=
  { globalEnv with revealedNames := [] }

/-- Look up the declared trust of `name`, or `none` if unregistered.  -/
def lookupTrust? (globalEnv : GlobalEnv) (name : String) : Option Trust :=
  (globalEnv.lookup? name).map (·.trust)

end GlobalEnv

/-! ## Trust propagation

Per `fx_design.md` §6.3 dim 9 and §10.6: a declaration's
*effective* trust is the `min` of its declared trust and every
transitively-referenced decl's declared trust.  Calling a decl
with trust `external` from a decl with trust `verified` caps
the caller's effective trust at `external` — the "weakest link"
rule.

Release builds (§10.6: `fxc --release`) gate on
`transitiveTrust ≥ Verified`, enforcing the invariant that no
release shipping code has a `sorry`/`axiom`/`external`
dependency in its closure.  This file provides the walker;
wiring into the CLI's release gate is F5-followup.
-/

namespace Term

/-- Collect every `.const` name appearing anywhere in a term.
    Direct (non-transitive) — use `GlobalEnv.closureConstRefs`
    to walk transitively through bodies.

    `partial def` rather than a structurally-terminating `def`
    because `List.flatMap f` does not expose the per-element
    subterm-structure to Lean's termination checker for the
    `.ind`, `.ctor`, and `.indRec` cases.  The function IS
    structurally recursive — every recursive call is on a
    proper subterm — but proving this via `termination_by` and
    a custom well-founded measure is disproportionate to the
    value.  This matches the pattern used by `Reduction.whnf`
    and `Typing.infer` elsewhere in the kernel. -/
partial def constRefs : Term → List String
  | .const name            => [name]
  | .var _                 => []
  | .type _                => []
  | .forallLevel body      => body.constRefs
  | .coind _ coindArgs     => coindArgs.flatMap constRefs
  | .coindUnfold _ typeArgs arms =>
    typeArgs.flatMap constRefs ++ arms.flatMap constRefs
  | .coindDestruct _ _ target => target.constRefs
  | .app funcTerm argTerm  => funcTerm.constRefs ++ argTerm.constRefs
  | .lam _ domain body     => domain.constRefs ++ body.constRefs
  | .pi _ domain body _    => domain.constRefs ++ body.constRefs
  | .sigma _ domain body   => domain.constRefs ++ body.constRefs
  | .ind _ typeArgs        => typeArgs.flatMap constRefs
  | .ctor _ _ typeArgs ctorArgs =>
    typeArgs.flatMap constRefs ++ ctorArgs.flatMap constRefs
  | .indRec _ motive methods target =>
    motive.constRefs ++ methods.flatMap constRefs ++ target.constRefs
  | .id eqType leftTerm rightTerm =>
    eqType.constRefs ++ leftTerm.constRefs ++ rightTerm.constRefs
  | .refl witness          => witness.constRefs
  | .idJ motive base eqProof =>
    motive.constRefs ++ base.constRefs ++ eqProof.constRefs
  | .quot carrier relation => carrier.constRefs ++ relation.constRefs
  | .quotMk relation witness => relation.constRefs ++ witness.constRefs
  | .quotLift lifted respects target =>
    lifted.constRefs ++ respects.constRefs ++ target.constRefs

end Term

namespace GlobalEnv

/-- Transitive `.const` reference closure from `seedName`, using
    a worklist + visited-set.  Returns the de-duplicated, lowercase-
    sorted list of reachable names — always including `seedName`
    itself (even when unregistered).  Unregistered names in the
    closure are kept so callers can detect missing decls (§10.6
    axiom-audit surfaces these as `UNRESOLVED` refs). -/
partial def closureConstRefs (globalEnv : GlobalEnv) (seedName : String)
    : List String := Id.run do
  let mut worklist : List String := [seedName]
  let mut visited  : List String := []
  while !worklist.isEmpty do
    match worklist with
    | []            => break
    | name :: rest  =>
      worklist := rest
      if visited.contains name then continue
      visited := name :: visited
      match globalEnv.lookupBody? name with
      | some body =>
        for referencedName in body.constRefs do
          if !visited.contains referencedName then
            worklist := referencedName :: worklist
      | none => pure ()
  visited.mergeSort (·.toLower < ·.toLower)

/-- The effective trust of `seedName`: `min` across the declared
    trust of `seedName` and every transitive dependency.
    Unregistered dependencies (e.g., axioms not yet in the env,
    or the seed itself when unknown) contribute `Trust.external`
    (the bottom) — a conservative underestimate that forces
    callers to prove or declare.

    Cycles are handled by `closureConstRefs`'s visited-set — a
    self-referential decl counts its own trust once.

    `closureConstRefs` always includes `seedName` in the result,
    so we fold across the full closure without a separate self-
    inclusion step. -/
def transitiveTrust (globalEnv : GlobalEnv) (seedName : String) : Trust :=
  globalEnv.closureConstRefs seedName
    |>.foldl (init := Trust.verified) fun currentTrust depName =>
      match globalEnv.lookupTrust? depName with
      | some depTrust => Trust.add currentTrust depTrust
      | none          => Trust.add currentTrust Trust.external

/-- Convenience: is the transitive trust at least `Verified`?
    The release-build gate from §10.6. -/
def isReleaseReady (globalEnv : GlobalEnv) (seedName : String) : Bool :=
  match globalEnv.transitiveTrust seedName with
  | Trust.verified => true
  | _              => false

end GlobalEnv

end FX.Kernel
