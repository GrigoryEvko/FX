import FX.Kernel.Context
import FX.Kernel.Conversion
import FX.Kernel.Inductive
import FX.Kernel.Env
import FX.Kernel.Pretty

/-!
# Bidirectional type checker

Per `fx_design.md` §6.2 (typing rules) and Appendix H.

## Judgments

Two mutually-defined operations:

  * `infer  context t     : Except TypeError Term` — synthesize the
    type of `t` in context `context`.
  * `check  context t T   : Except TypeError Unit` — check that `t`
    has the expected type `T` in `context`.

Both return a `TypeError` on failure.  `infer` succeeds when `t`
has a canonical form from which the type is obvious (var, app,
type-former); `check` is used when the expected type is driven
by context (the body of a `lam`, the argument of an `app`).

## Coverage

Phase-2 scope per the design-doc §31.2 ten-Term-form catalog:

  * **Fully handled (infer + check):**
    * `var i`        — lookup in context
    * `type u`       — U-hier: returns `type (succ u)`
    * `pi g A B`     — Pi-form: returns `type (max u_A u_B)`
    * `lam g A b`    — Pi-intro with Wood-Atkey context division
    * `app f a`      — Pi-elim with grade arithmetic
    * `sigma g A B`  — Sigma-form (type only — no pair constructor yet)
    * `id T a b`     — Id-form (type)
    * `refl w`       — Id-intro (A3): `refl w : Id T w w` where `T`
                       is the synthesized type of `w`.  Per H.6.
    * `idJ m b e`    — Id-elim / J eliminator (A3): given eq-proof
                       `e : Id T a b`, produces `app (app (app m a) b) e`.
                       Shape of `m`/`b` is checked via `infer` but
                       not matched against the full motive/base
                       shape — that's T117 (deferred until A10).
    * `quot T R`     — Quot-form (type)
    * `quotMk R w`   — Quot-intro (A4): `quotMk R w : Quot T R`
                       where `T` is the synthesized type of `w`.
                       The stored relation `R` recovers the other
                       half of the type.  Per H.7.
    * `quotLift f p t` — Quot-elim / `Quot.lift` (A4): given
                       `t : Quot T R` and `f : T → U`, returns
                       `openWith t U` (codomain of `f` with the
                       bound slot discharged against `t`).  The
                       respects-proof `p` is type-checked but its
                       shape `Π x y. R x y → Id U (f x) (f y)` is
                       not matched (T118, deferred to A10).
  * **Phase-2 stub, rejected:**
    * `ind`, `coind` — spec is `Unit`; the typing rule requires
      spec content (constructors, indices, guardedness) that
      Phase-2 Term does not carry.  Emits `T100_phase_2_stub`.

## Grade discipline (Phase-2 simplification)

The full §6.2 rules require grade-vector arithmetic at every
binder and every application.  Phase-2 **collects** grades via
`TypingContext.add`/`TypingContext.scale`/`TypingContext.divByUsage` but does **not** enforce
that the resulting grade vectors are linearly-valid — that's a
follow-up pass.  What Phase-2 does enforce:

  * **Structural well-formedness**: types-of-types are types;
    Pi/Sigma domains are types; App arguments match Pi domains
    (up to conversion); Id equates terms of equal types.
  * **Wood-Atkey div in Pi-intro**: the body of a `lam` is
    checked under `context/g` (see §27.1's Lam-bug defense).
  * **beta-conversion**: types are compared via `convEq` (from
    `Conversion.lean`) so the checker accepts `app (lambdax.x) T`
    ≡ `T`.

## Error codes

Aligned with `fx_design.md` §10.10 taxonomy:

  * T001 — not-a-type (expected a type, got something else)
  * T002 — type mismatch (check failed)
  * T003 — expected Pi (App on non-function)
  * T004 — de Bruijn out of range (free var)
  * T010 — malformed term (e.g., Id components of different types)
  * T100 — Phase-2 stub (ind/coind not yet supported)
  * R_fuel — reduction exceeded fuel during conversion
-/

namespace FX.Kernel

/--
A type error.  Kind codes per `fx_design.md` §10.10.  Carries
an optional diagnostic message and an optional sub-term for
context.
-/
structure TypeError where
  code    : String
  message : String
  term    : Option Term := none
  deriving Repr

namespace TypeError

def make (code message : String) : TypeError :=
  { code := code, message := message }

def atTerm (code message : String) (term : Term) : TypeError :=
  { code := code, message := message, term := some term }

end TypeError

/- ## Bidirectional checker -/

namespace Term

/-- The result of a typing judgment.  Either a type (on infer
    success) or a unit (on check success), plus a possible
    error array. -/
abbrev TypeCheck (valueType : Type) := Except TypeError valueType

/- Bidirectional type checker.  Mutually-recursive `infer` and
   `check`.  `infer context term globalEnv? levelCount?`
   synthesizes `term`'s type; `check context term expectedType
   globalEnv? levelCount?` verifies that `term` has type
   `expectedType`.  Optional params:

     * `globalEnv` (default `{}`) — consulted by `Term.const`.
     * `levelCount` (default `0`) — number of enclosing
       `Term.forallLevel` binders (A10 / §31.4 U-poly).  The
       `.type` rule rejects `Level.var n` with `n ≥ levelCount`;
       the `.forallLevel` rule increments it before recursing
       into the body.  All other rules thread it unchanged. -/
mutual

partial def infer (context : TypingContext) (term : Term)
    (globalEnv : GlobalEnv := {}) (levelCount : Nat := 0) : TypeCheck Term :=
  match term with
  | var deBruijnIndex => do
    match context.lookup? deBruijnIndex with
    | none =>
      throw (TypeError.atTerm "T004"
        s!"de Bruijn index {deBruijnIndex} out of range (context size {context.size})"
        (.var deBruijnIndex))
    | some entry =>
      -- The variable's type was stored with indices valid in the
      -- context at the point of binding.  When looking up from a
      -- deeper scope (deBruijnIndex binders nested above), we shift
      -- by deBruijnIndex+1 to bring the type into the current scope.
      return shift 0 (deBruijnIndex + 1) entry.typeTerm
  | const declName => do
    -- `Term.const` resolution: look up the decl's declared type
    -- in `globalEnv`.  Stored types are closed at file scope
    -- (no free vars) so no shift is needed when returning them
    -- into a deeper local context.  Missing registration is
    -- error `T120` — should not occur on elaborator-produced
    -- terms since the elaborator only emits `const` for
    -- registered names.
    match globalEnv.lookupType? declName with
    | some declType => return declType
    | none =>
      throw (TypeError.atTerm "T120"
        s!"unknown global declaration '{declName}'"
        (.const declName))
  | type universeLevel =>
    -- U-hier: `type u : type (succ u)`.
    -- A10: closed-level check.  Every `Level.var n` appearing in
    -- the level must reference a binder enclosed by `levelCount`
    -- `forallLevel` scopes.  Out-of-scope level variables are
    -- rejected with `T060` (formerly silent acceptance).
    if !universeLevel.varsInScope levelCount then
      throw (TypeError.atTerm "T060"
        s!"level variable out of scope: level {repr universeLevel} has a Level.var n with n ≥ levelCount ({levelCount})"
        (.type universeLevel))
    else
      return type (Level.succ universeLevel)
  | forallLevel bodyTerm => do
    -- U-poly (§31.4, Appendix H.1): `Π (k : level). body` is a
    -- type when body is a type under an extended level scope.
    -- The body inhabits `type u` for some level `u`; the
    -- quantifier itself lives at `type u` too (universe
    -- cumulativity: abstracting over a level doesn't raise the
    -- universe of the quantifier, since levels are erased per
    -- §1.5 compile-time erasure).
    --
    -- Phase-2 scope: type-level only.  No value-level `Λ k.
    -- body` abstraction, no `f @ level` application.  This
    -- typing rule admits `forallLevel body` as a well-formed
    -- type; actually CONSTRUCTING or APPLYING a level-
    -- polymorphic value is A10-followup.
    let bodyLevel ← inferType context bodyTerm globalEnv (levelCount + 1)
    return type bodyLevel
  | pi binderGrade domainType codomainType _returnEffect => do
    -- Pi-form: check domain is a type, then codomain in the extended context.
    -- `_returnEffect` is carried as kernel-level metadata for §9
    -- subsumption — E-2 will replace A12's body-walk with a proper
    -- effect inference that consults this field at App sites.
    let domainLevel ← inferType context domainType globalEnv levelCount
    let codomainLevel ← inferType (context.extend binderGrade domainType) codomainType globalEnv levelCount
    return type (Level.max domainLevel codomainLevel)
  | sigma binderGrade domainType codomainType => do
    let domainLevel ← inferType context domainType globalEnv levelCount
    let codomainLevel ← inferType (context.extend binderGrade domainType) codomainType globalEnv levelCount
    return type (Level.max domainLevel codomainLevel)
  | lam binderGrade domainType bodyTerm => do
    -- Pi-intro with Wood-Atkey div: the body is checked under
    -- (context/g, x :_g A).  Usage is extracted from the grade since
    -- the division rule scales only the usage dimension at this
    -- layer (§27.1 simplification; full pointwise division lands
    -- in Phase 3 once all grade dimensions' div laws are in).
    let _domainLevel ← inferType context domainType globalEnv levelCount
    let extendedTypingContext := (context.divByUsage binderGrade.usage).extend binderGrade domainType
    let codomainType ← infer extendedTypingContext bodyTerm globalEnv levelCount
    -- Pi-intro exit check (§6.3.1 / §27.1 linearity): var 0's
    -- actual usage in the body, treating type positions as erased,
    -- must not exceed the binder's declared grade.  Rejects the
    -- Atkey-2018 higher-order witness (§27.2 corpus entry #1).
    --
    -- Phase-2 scope: enforces the "over-use" direction (M001)
    -- only.  The "under-use" direction (M002: declared linear
    -- binder never consumed) is deferred — current kernel
    -- fixtures include type-level `lam`s whose body is a type
    -- (e.g., the `quot` relation template), and those would
    -- trigger spurious M002 since a type body counts zero uses
    -- yet the binder is declared linear.  M002 lands alongside
    -- a relevance-aware lam-vs-type-level-lam distinction.
    let actualUsage := countVarAt 0 bodyTerm
    unless decide (Usage.LessEq actualUsage binderGrade.usage) do
      throw (TypeError.atTerm "M001"
        s!"linear-overuse: binder used with grade {repr actualUsage} in body, declared grade allows only {repr binderGrade.usage}"
        (.lam binderGrade domainType bodyTerm))
    -- Lam synthesizes a Pi type with the binder's grade, the
    -- domain from the surface, the inferred codomain, and a
    -- Tot return-effect by default.  The elaborator overrides
    -- this via `Term.pi` construction with an explicit effect
    -- when the surface signature carries `with …`.  Full
    -- body-effect inference (E-2) will derive the return
    -- effect from the body rather than defaulting.
    return pi binderGrade domainType codomainType Effect.tot
  | app funcTerm argTerm => do
    let funcType ← infer context funcTerm globalEnv levelCount
    -- Reduce to whnf to see if it's a pi.
    let funcTypeWhnf := whnf defaultFuel (globalEnv := globalEnv) funcType
    match funcTypeWhnf with
    | pi _binderGrade domainType codomainType _returnEffect =>
      check context argTerm domainType globalEnv levelCount
      -- Return codomain with the argument substituted for var 0.
      -- E-2 will also join `_returnEffect` into the call-site's
      -- effect row per Appendix B E-App.
      return openWith argTerm codomainType
    | _ =>
      throw (TypeError.atTerm "T003"
        s!"expected function type, got {Term.prettyCompact funcTypeWhnf}" funcTerm)
  | id baseType leftTerm rightTerm => do
    -- Id-form: baseType must be a type; leftTerm, rightTerm must both have type baseType.
    let _baseTypeLevel ← inferType context baseType globalEnv levelCount
    check context leftTerm baseType globalEnv levelCount
    check context rightTerm baseType globalEnv levelCount
    -- Id lives in the same universe as baseType.
    let baseTypeLevel ← inferType context baseType globalEnv levelCount
    return type baseTypeLevel
  | refl witnessTerm => do
    -- Id-intro (H.6): `Γ ⊢ witness : T` ⇒ `Γ ⊢ refl witness : Id T witness witness`.
    -- The type component of the Id is recovered by synthesizing
    -- the witness's type in the current context.
    let witnessType ← infer context witnessTerm globalEnv levelCount
    return .id witnessType witnessTerm witnessTerm
  | idJ motiveTerm baseTerm eqProofTerm => do
    let eqProofType ← infer context eqProofTerm globalEnv levelCount
    match whnf defaultFuel (globalEnv := globalEnv) eqProofType with
    | .id _eqBaseType leftEndpoint rightEndpoint =>
      let _motiveType ← infer context motiveTerm globalEnv levelCount
      let _baseType   ← infer context baseTerm   globalEnv levelCount
      return .app (.app (.app motiveTerm leftEndpoint) rightEndpoint) eqProofTerm
    | otherType =>
      throw (TypeError.atTerm "T010"
        s!"J eliminator expected Id-type proof, got {Term.prettyCompact otherType}"
        eqProofTerm)
  | quot baseType relationTerm => do
    let _baseTypeLevel ← inferType context baseType globalEnv levelCount
    let _relationType ← infer context relationTerm globalEnv levelCount
    let baseTypeLevel ← inferType context baseType globalEnv levelCount
    return type baseTypeLevel
  | quotMk relationTerm witnessTerm => do
    let witnessType ← infer context witnessTerm globalEnv levelCount
    let _relationType ← infer context relationTerm globalEnv levelCount
    return .quot witnessType relationTerm
  | quotLift liftedTerm respectsTerm targetTerm => do
    let targetType ← infer context targetTerm globalEnv levelCount
    match whnf defaultFuel (globalEnv := globalEnv) targetType with
    | .quot _quotCarrier _quotRel =>
      let liftedType ← infer context liftedTerm globalEnv levelCount
      let _respectsType ← infer context respectsTerm globalEnv levelCount
      match whnf defaultFuel (globalEnv := globalEnv) liftedType with
      | .pi _binderGrade _domainType codomainType _returnEffect =>
        return openWith targetTerm codomainType
      | otherType =>
        throw (TypeError.atTerm "T003"
          s!"Quot.lift requires function type for lifted arg, got {Term.prettyCompact otherType}"
          liftedTerm)
    | otherType =>
      throw (TypeError.atTerm "T010"
        s!"Quot.lift target must have quotient type, got {Term.prettyCompact otherType}"
        targetTerm)
  | ind typeName paramArgs => do
    match Inductive.specByName? typeName globalEnv.userSpecs with
    | none =>
      throw (TypeError.atTerm "T110"
        s!"unknown inductive type '{typeName}' (not registered)"
        (.ind typeName paramArgs))
    | some spec =>
      if paramArgs.length ≠ spec.paramCount then
        throw (TypeError.atTerm "T111"
          s!"inductive type '{typeName}' expects {spec.paramCount} params, got {paramArgs.length}"
          (.ind typeName paramArgs))
      else
        let rec checkIndArgs : List Term → TypeCheck Unit
          | []      => return ()
          | paramArg :: restArgs => do
            check context paramArg (.type .zero) globalEnv levelCount
            checkIndArgs restArgs
        checkIndArgs paramArgs
        return .type .zero
  | ctor typeName ctorIndex typeArgs ctorArgs => do
    match Inductive.specByName? typeName globalEnv.userSpecs with
    | none =>
      throw (TypeError.atTerm "T110"
        s!"unknown inductive type '{typeName}' in ctor application"
        (.ctor typeName ctorIndex typeArgs ctorArgs))
    | some spec =>
      if typeArgs.length ≠ spec.paramCount then
        throw (TypeError.atTerm "T111"
          s!"ctor of '{typeName}' expects {spec.paramCount} type params, got {typeArgs.length}"
          (.ctor typeName ctorIndex typeArgs ctorArgs))
      else match spec.ctorAt? ctorIndex with
      | none =>
        throw (TypeError.atTerm "T112"
          s!"ctor index {ctorIndex} out of range for '{typeName}' ({spec.ctorCount} ctors)"
          (.ctor typeName ctorIndex typeArgs ctorArgs))
      | some ctorSpec =>
        if ctorArgs.length ≠ ctorSpec.args.length then
          throw (TypeError.atTerm "T113"
            s!"ctor '{ctorSpec.name}' expects {ctorSpec.args.length} args, got {ctorArgs.length}"
            (.ctor typeName ctorIndex typeArgs ctorArgs))
        else
          -- For parameterized inductives (A10 follow-up): the ctor
          -- spec's arg types are written in the scope of the spec's
          -- parameter telescope.  Substitute the actual `typeArgs`
          -- into each arg type before checking.  For non-parameter-
          -- ized specs (params = []), `substParams` is a no-op.
          let substitutedArgs := ctorSpec.args.map
            (Term.substParams typeArgs)
          let rec checkCtorArgs : List Term → List Term → TypeCheck Unit
            | [], []           => return ()
            | expectedArgType :: restExpectedTypes, actualArg :: restActualArgs => do
              check context actualArg expectedArgType globalEnv levelCount
              checkCtorArgs restExpectedTypes restActualArgs
            | _, _ => throw (TypeError.atTerm "T113" "ctor arg count mismatch"
                                (.ctor typeName ctorIndex typeArgs ctorArgs))
          checkCtorArgs substitutedArgs ctorArgs
          return .ind typeName typeArgs
  | indRec typeName motive methods target => do
    match Inductive.specByName? typeName globalEnv.userSpecs with
    | none =>
      throw (TypeError.atTerm "T110"
        s!"unknown inductive type '{typeName}' in eliminator"
        (.indRec typeName motive methods target))
    | some spec =>
      if methods.length ≠ spec.ctorCount then
        throw (TypeError.atTerm "T114"
          s!"recursor for '{typeName}' expects {spec.ctorCount} methods, got {methods.length}"
          (.indRec typeName motive methods target))
      else
        let targetType ← infer context target globalEnv levelCount
        match whnf defaultFuel (globalEnv := globalEnv) targetType with
        | .ind actualTypeName _ =>
          if actualTypeName ≠ typeName then
            throw (TypeError.atTerm "T115"
              s!"eliminator expects target of type '{typeName}', got '{actualTypeName}'" target)
          else
            let _motiveType ← infer context motive globalEnv levelCount
            return .app motive target
        | otherType =>
          throw (TypeError.atTerm "T115"
            s!"eliminator target must have inductive type, got {Term.prettyCompact otherType}" target)
  | coind coindName coindArgs => do
    -- Coind-form (H.5.1): mirrors Ind-form.  The spec is resolved
    -- through `GlobalEnv.userCoindSpecs` (populated by S11's
    -- session-decl elaborator).  Parameter-arg count must match
    -- `spec.paramCount`; each parameter arg must be a type.
    match globalEnv.coindSpecByName? coindName with
    | none =>
      throw (TypeError.atTerm "T110"
        s!"unknown coinductive type '{coindName}' (not registered)"
        (.coind coindName coindArgs))
    | some spec =>
      if coindArgs.length ≠ spec.paramCount then
        throw (TypeError.atTerm "T111"
          s!"coinductive type '{coindName}' expects {spec.paramCount} params, got {coindArgs.length}"
          (.coind coindName coindArgs))
      else
        let rec checkCoindArgs : List Term → TypeCheck Unit
          | []      => return ()
          | paramArg :: restArgs => do
            check context paramArg (.type .zero) globalEnv levelCount
            checkCoindArgs restArgs
        checkCoindArgs coindArgs
        return .type .zero
  | coindUnfold typeName typeArgs arms => do
    -- Coind-intro (H.5.2): the unfold is the introduction form
    -- for codata.  Each arm must have the corresponding
    -- destructor's `resultType` (with `typeArgs` substituted for
    -- the spec's param telescope).  Checks paralleling `.ctor`:
    --   * spec registered (T110)
    --   * type-arg count matches param count (T111)
    --   * arm count matches destructor count (T113 — parallel to
    --     ctor arg count: same structural mismatch)
    --   * each arm checks against its destructor's result type
    -- Result: `coind typeName typeArgs` — the codata the unfold
    -- introduces a value of.
    match globalEnv.coindSpecByName? typeName with
    | none =>
      throw (TypeError.atTerm "T110"
        s!"unknown coinductive type '{typeName}' in unfold"
        (.coindUnfold typeName typeArgs arms))
    | some spec =>
      if typeArgs.length ≠ spec.paramCount then
        throw (TypeError.atTerm "T111"
          s!"unfold of '{typeName}' expects {spec.paramCount} type params, got {typeArgs.length}"
          (.coindUnfold typeName typeArgs arms))
      else if arms.length ≠ spec.destructorCount then
        throw (TypeError.atTerm "T113"
          s!"unfold of '{typeName}' expects {spec.destructorCount} arms (one per destructor), got {arms.length}"
          (.coindUnfold typeName typeArgs arms))
      else
        -- Each destructor's `resultType` references the spec's
        -- param telescope via de Bruijn; substitute the concrete
        -- `typeArgs` before checking the arm.  For the common
        -- `params = []` case (current session translator) the
        -- substitution is a no-op.
        let rec checkArms : List Term → List CoindDestructor → TypeCheck Unit
          | [], []                                         => return ()
          | armTerm :: restArms, destructor :: restDests => do
            let expectedArmType := Term.substParams typeArgs destructor.resultType
            check context armTerm expectedArmType globalEnv levelCount
            checkArms restArms restDests
          | _, _ => throw (TypeError.atTerm "T113"
                        "unfold arm count / destructor count mismatch"
                        (.coindUnfold typeName typeArgs arms))
        checkArms arms spec.destructors
        return .coind typeName typeArgs
  | coindDestruct typeName destructorIndex target => do
    -- Coind-elim (H.5.3): observing destructor #i on a codata
    -- value of type `coind typeName typeArgs` yields a value of
    -- type `destructor.resultType` with `typeArgs` substituted
    -- for the spec's param telescope.  Mirrors `.indRec`.
    --   * spec registered (T110)
    --   * target's type is `coind typeName _` (T115 — parallel
    --     to indRec's eliminator-target-type check)
    --   * destructor index in range (T112 — parallel to ctor
    --     index out of range)
    -- Result: the destructor's signature type (typically a Π
    -- chain ending in another `coind …`).  Consumers fire the
    -- Π via subsequent App elaboration.
    match globalEnv.coindSpecByName? typeName with
    | none =>
      throw (TypeError.atTerm "T110"
        s!"unknown coinductive type '{typeName}' in destructor"
        (.coindDestruct typeName destructorIndex target))
    | some spec =>
      match spec.destructorAt? destructorIndex with
      | none =>
        throw (TypeError.atTerm "T112"
          s!"destructor index {destructorIndex} out of range for '{typeName}' ({spec.destructorCount} destructors)"
          (.coindDestruct typeName destructorIndex target))
      | some destructor =>
        let targetType ← infer context target globalEnv levelCount
        match whnf defaultFuel (globalEnv := globalEnv) targetType with
        | .coind actualTypeName paramArgs =>
          if actualTypeName ≠ typeName then
            throw (TypeError.atTerm "T115"
              s!"destructor expects target of coinductive type '{typeName}', got '{actualTypeName}'"
              target)
          else
            -- Substitute the concrete params captured from the
            -- target's coind type into the destructor's declared
            -- resultType.  `paramArgs` comes from the value, not
            -- from the surface `typeArgs` argument to `coindDestruct`
            -- — the kernel trusts typing to ensure these match but
            -- the value-side is the authoritative source for what
            -- instantiation the continuation sees.
            return Term.substParams paramArgs destructor.resultType
        | otherType =>
          throw (TypeError.atTerm "T115"
            s!"destructor target must have coinductive type, got {Term.prettyCompact otherType}"
            target)

/--
Infer and ensure the result is a `type _`, returning the level.
-/
partial def inferType (context : TypingContext) (term : Term)
    (globalEnv : GlobalEnv := {}) (levelCount : Nat := 0) : TypeCheck Level := do
  let inferredType ← infer context term globalEnv levelCount
  match whnf defaultFuel (globalEnv := globalEnv) inferredType with
  | type universeLevel => return universeLevel
  | otherType =>
    throw (TypeError.atTerm "T001"
      s!"expected a type, got {Term.prettyCompact otherType}" term)

/--
Check `term` against `expectedType`.  The core move: infer `term`,
then verify the inferred type is convertible to `expectedType`.
-/
partial def check (context : TypingContext) (term : Term)
    (expectedType : Term) (globalEnv : GlobalEnv := {})
    (levelCount : Nat := 0) : TypeCheck Unit := do
  let inferredType ← infer context term globalEnv levelCount
  if subOrConv defaultFuel inferredType expectedType globalEnv then
    return ()
  else
    -- Q57: render the mismatch compactly.  `repr` on a Pi fans
    -- every `Grade` field individually and produces ~60-line
    -- output for a two-arrow signature; `Term.prettyCompact`
    -- collapses default/ghost/shared grades to their
    -- abbreviations and effect rows to comma-separated labels
    -- or `Tot`.  For the error's debuggability what matters is
    -- the structural shape plus any grade that actually
    -- differs — the compact form preserves both.
    throw (TypeError.atTerm "T002"
      s!"type mismatch: inferred {Term.prettyCompact inferredType}, expected {Term.prettyCompact expectedType}" term)

end

end Term

end FX.Kernel
