# WORKING_RULES.md — kernel discipline for lean-fx-2

Empirical patterns distilled from lean-fx (5+ kernel versions of
trial and error).  Following these rules keeps the kernel zero-axiom.
Violating them invites propext / Quot.sound / Classical.choice slip.

## Discipline #1: Match-arity propext trap (`feedback_lean_match_arity_axioms`)

For pattern matches on multi-Nat-indexed inductives (e.g.,
`Ty : Nat → Nat → Type`), the placement of implicits matters for
axiom discipline.

**WRONG** — propext + Quot.sound emitted:
```lean
theorem Ty.subst_compose : ∀ {level s m t : Nat} (T : Ty level s) ..., ...
  | _, _, _, _, .unit, _, _ => rfl
```

**RIGHT** — zero axioms:
```lean
theorem Ty.subst_compose {level : Nat} : ∀ {s m t : Nat} (T : Ty level s) ..., ...
  | _, _, _, .unit, _, _ => rfl
```

**Rule**: For every pattern theorem with N Nat indices (N ≥ 2), keep at most ONE Nat index inside the `∀`.  Move the rest to the theorem header (before `:`).

## Discipline #2: Wildcards always leak propext (`feedback_lean_zero_axiom_match`)

ANY `_ =>` wildcard or named catch-all (`t =>`) in a match emits propext to discharge the redundancy obligation.

**Rule**: Enumerate every constructor explicitly.  Or, when the scrutinee has restricted type index, dispatch via `Term.toRaw`-shape match (see `feedback_lean_zero_axiom_match.md` Rule 5).

## Discipline #3: Function-typed Subst is the axiom-free pattern (`feedback_lean_function_typed_subst`)

Define substitution as `Subst (source target : Nat) := Fin source → Ty target`, NOT as direct index manipulation.  `lift` propagates indices through structural recursion without invoking Nat-arithmetic identities (which would force `Eq.mpr` + propext).

**Rule**: All substitution-shaped operations use function-typed Subst/Renaming.  `Ty.unweaken : Ty (n+1) → Ty n` is forbidden.

## Discipline #4: Mark structural-recursion functions @[reducible] (`feedback_lean_reducible_weaken`)

Functions used in inductive constructor signatures (`Ty.weaken`, `Subst.lift`, `Subst.singleton`, `Term.subst0`, etc.) MUST be `@[reducible]`.  Otherwise Lean's unifier fails to elaborate constructor applications whose types involve them.

**Rule**: `@[reducible] def Ty.weaken := T.rename Renaming.weaken` (analogously for all subst-shape functions).

## Discipline #5: Binder-form match for indexed inductives (`feedback_lean_binder_form`)

Functions over indexed inductives must use binder-form (explicit pattern bound to a name) for the indices, not pattern-form (literal pattern expressions).  Pattern-form silently introduces propext + Quot.sound via match compilation.

**WRONG**:
```lean
def f (x : Foo (n + 1)) : Bar := match x with ...
```

**RIGHT**:
```lean
def f {scope : Nat} (x : Foo scope) : Bar := match x with ... | k + 1 => ...
```

**Rule**: After every new function over an indexed inductive, run `#print axioms FunctionName` to verify zero axioms.

## Discipline #6: Paired-predicate pattern (`feedback_lean_paired_predicate_pattern`)

When proving "X preserves bi-witness" (e.g., `Step.par.subst_compatible_isBi`), do NOT characterize the opaque output via the lemma's body.  Switch to a paired-predicate formulation.

**Rule**: Define `Step.parWithBi := Σ (s : Step.par a b), Step.par.isBi s`, prove `Step.parWithBi.subst_compatible` directly by induction on the underlying isBi witness, constructing fresh paired witnesses at each case.

## Discipline #7: mapStep abstraction (`feedback_lean_mapStep_pattern`)

Cong-rule boilerplate (4-line refl/trans inductions) collapses to 1-line `mapStep` lifter applications.  Apply when defining new cong rules.

**Pattern**:
```lean
theorem X.Foo.cong (chain : X a b) : X (f a) (f b) :=
  X.mapStep f (Step.<ctor>) chain
```

instead of explicit refl/trans induction.

## Discipline #8: Typed source-inversion via toRaw refutation (`feedback_typed_inversion_breakthrough`)

For typed `Step.par` source inversions (e.g., `Step.parStar Term.boolTrue X → X = boolTrue`), HEq-generalized induction + `Term.toRaw` projection refutation discharges them at zero axioms.  Bypasses dep-elim wall.

**Pattern**: `refuteViaToRaw` helper lives in `Tools/Tactics/HEq.lean`.

## Discipline #9: ASCII-only identifiers (`feedback_ascii_only`)

No Greek (Γ, α, β, μ, σ, ρ, π, ω, etc.), no Unicode (∀, ∃, ⊢, ▸, etc.), in identifiers — parameters, variables, theorem names, constructors, fields.

**Allowed exception**: Notation via `instance : LE X` etc. (Lean's `≤` infix is notation, not identifier).  Docstrings MAY cite spec with Unicode.

## Discipline #10: ≥4-character names (`feedback_readable_names`)

Banned: 1-char (`g`, `t`, `e`, `s`, `x`, `i`, `j`) and 2-char (`ty`, `ex`, `fn`, `tc`, `ok`, `nf`) identifiers.  Discouraged: ≤3-char.

**Allowed exceptions**:
* Spec primitives (§31): `shift`, `subst`, `whnf`, `convEq`, `beta`, `eta`, `iota`, `refl`
* Parser terminology: `lhs`/`rhs` for binary-op sides
* Math-convention binders: `∀ x, P x` in lemma signatures where `x` is a universally-quantified element with no role beyond "arbitrary"

## Discipline #11: No task IDs in code (`feedback_no_task_ids_in_code`)

Don't put `Q1`, `A9`, `B7`, `#342`, `W9.B1.x` etc. in source comments.  They rot as the codebase evolves.  Task IDs belong in commit messages and PR descriptions, not in `// TODO` lines.

## Discipline #12: Predicates use telling words

Boolean / Prop / yes-no flag identifiers MUST start with or contain a question verb (`is`, `has`, `should`, `must`, `can`, `will`, `was`, `needs`).  Forbidden: `ok`, `valid`, `good`, `done`, `flag`, `check`, `b`, `p`, `pred`.

## Discipline #13: Auto-derive DecidableEq carefully (`feedback_lean_zero_axiom_match`)

`deriving DecidableEq` works for non-dependent inductives + dep with universal index.  For Nat-indexed dependent families with restricted indices, may leak propext.  Audit with `#print axioms <ctor>.decEq` after deriving.

**Rule**: If derive leaks propext, write manual `instance : DecidableEq` with full ctor enumeration.

## Discipline #14: Universe-constructor blocker workaround (`feedback_lean_universe_constructor_block`)

`Ty.universe (u : Nat) : Ty (u+1) scope` breaks pattern-form match in any theorem whose goal uses the scrutinee through a function.  Use propositional-equation parameter: `(levelEq : level = u + 1)` instead of literal index.

## Discipline #15: Cumulativity is a Conv rule, not a Ty constructor (`feedback_lean_cumul_subst_mismatch`)

Don't add `Ty.cumul base h : Ty levelHigh scope` as a Ty constructor — it can't compose with subst (base's tyVars expect Subst at levelLow, outer call passes Subst at levelHigh).  Cumulativity belongs in Conv (definitional conversion between universe levels).  Same principle generalizes: in CIC deep embeddings, anything that wants to refer Term-from-Ty should live as a metatheoretic rule, not an inductive constructor.

## Discipline #16: Lean 4 mutual-index rule (`feedback_lean_mutual_index_rule`)

Lean 4 v4.29.1's kernel forbids sibling references in *index family signatures* of mutual inductives.  `Term : Ctx → Ty Γ → Type` (textbook intrinsic mutual) cannot resolve sibling names.  Either:
1. Status quo: `Ty : Nat → Type` + `Term : Ctx → Ty scope → Type` (intrinsic but no Term-references-from-Ty)
2. Extrinsic: raw `Ty/Term : Nat → Type` mutual + `HasType : Term → Ty → Prop` after the block
3. Universe codes: `Code → Ty` with decode function

For lean-fx-2: option 1 with raw-aware Term (`Term : Ctx → Ty → RawTerm → Type`).  Identity-type endpoints stay as RawTerm (not typed Term) to sidestep.

## Discipline #17: Parser EOF safety (`project_parser_eof_trap`)

Every recursive-descent loop must check EOF before recursing into a sub-parser that does error-recovery-without-advance.  `TokenStream.advance` is a no-op at EOF.

**Rule**: Use `TokenStream.peekRequireNotEof` at every loop iteration in Surface/Parse.lean.

## Discipline #18: rm safety on root shell (`reference_rm_alias_trap`)

`rm` is aliased to `rm -i` on root shell.  Silently prompts under non-interactive Bash and does NOT delete.  Use `/bin/rm -f` or `\rm -f` for scripted deletions.

## Discipline #19: Implicit-type metavariables unblock typed `cases` (Phase 7.A discovery)

When proving `Term ctx ty (.<ctor> ...) → ty = <expected>`, leave `ty` as an implicit metavariable rather than fixing it concretely.  The Lean 4 dep-pattern matcher needs the type as a metavar to unify with the matched ctor's specific type.  With concrete types like `Ty.unit`, the matcher gets stuck on the `var` case because `varType context position` is opaque to definitional unification, but with implicit type the matcher uses the raw axis (where `RawTerm.var ≠ RawTerm.unit` is decidable by ctor mismatch).

**Wrong** (matcher fails on var case):
```lean
theorem Conv.canonical_unit
    (sourceTerm : Term ctx Ty.unit (RawTerm.unit (scope := scope))) :
    ... := by cases sourceTerm  -- fails
```

**Right** (matcher uses raw axis):
```lean
theorem Conv.canonical_unit
    {sourceType : Ty level scope}
    (sourceTerm : Term ctx sourceType (RawTerm.unit (scope := scope))) :
    ... := by cases sourceTerm  -- works
```

## Discipline #20: cases-cases-cases ordering for parameterized canonical heads (Phase 7.B discovery)

For typed Conv between two parameterized canonical-head terms at potentially different stated types, do all term-level `cases` BEFORE substituting type equalities:

**Right**:
```lean
cases sourceTerm   -- specializes sourceType to Ty.<ctor> e1
cases targetTerm   -- specializes targetType to Ty.<ctor> e2 (still implicit at second cases)
cases sameType     -- Ty.<ctor> e1 = Ty.<ctor> e2 → e1 = e2 by ctor decomposition
exact Conv.refl _
```

**Wrong** (subst prematurely concretizes the type, blocking second cases):
```lean
subst sameType
cases sourceTerm
cases targetTerm  -- fails: targetTerm has concrete type now
```

## Discipline #21: Outer Nat / inner dep-inductive matches must nest (Phase 9.A discovery)

When defining a function with a Nat fuel parameter and a dependent-inductive scrutinee, DO NOT combine into a single multi-discriminator match — the cross-product of cases triggers propext.  Always nest:

**Wrong** (combined match leaks propext):
```lean
def RawTerm.whnf : Nat → RawTerm scope → RawTerm scope
  | 0, term => term
  | _ + 1, .var pos => .var pos
  ...
```

**Right** (outer Nat, inner RawTerm):
```lean
def RawTerm.whnf (fuel : Nat) (term : RawTerm scope) : RawTerm scope :=
  match fuel with
  | 0 => term
  | fuel + 1 =>
    match term with | .var pos => ... | .app fn arg => ...
```

## Discipline #22: β-rule inversion audit

When adding a new elim-form β rule, update the corresponding inversion
lemma before claiming the slice.  A source such as `RawTerm.someElim
payload` no longer has only the congruent target shape once
`RawStep.par.betaSomeElimIntro` exists.

**Required shape**:
```lean
(congruent target branch) ∨ (β-fired target branch)
```

**Rule**: Any new `RawStep.par.beta*` constructor for an eliminator
must be paired with a disjunctive `*_inv` theorem that exposes both
the congruence branch and the β-fired branch.  The `glueElim`,
`refineElim`, and `recordProj` raw cascades are the reference pattern.

## Discipline #23: Raw/typed parity for redex rules

The raw layer is proof-friendly, but it is not the whole typed kernel.
A raw β/ι rule is only a raw slice until the typed layer can form the
same source and target and `Step.par.toRawBridge` projects the typed
rule to the raw rule.

**Rule**: Every new raw `RawStep.par.beta*` or `RawStep.par.iota*`
redex rule must have one of the following in the same commit or a
clearly paired follow-up commit:

* the corresponding typed `Term` constructors, typed `Step.par` rule,
  `Step.toPar` arm, bridge arm, and smoke/audit gates; or
* an explicit blocked-parity note in the commit body naming the missing
  typed constructors or subject-reduction prerequisite.

Do not call a D2/D3 redex task closed from raw evidence alone.

## Audit incantation

After any new function or theorem, run:
```
#print axioms FunctionName
```
Expected: "does not depend on any axioms".  Anything else → debug per the rules above.

For project-wide check:
```
lake build LeanFX2 2>&1 | grep "axiom audit failed"
```
Expected: empty.

## When in doubt

Read the relevant memory entry in `/root/.claude/projects/-root-iprit-FX/memory/`.  Each rule above has its source memory linked.
