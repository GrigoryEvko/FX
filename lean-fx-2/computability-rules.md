# computability-rules.md — invariants and disciplines for kernel-level computability in lean-fx-2

**TL;DR**: A theorem in lean-fx-2 is *genuinely computable* iff (1) it has
no transitive dependency on any axiom, (2) it carries no
non-computability marker (`noncomputable` / `@[extern]` /
`@[implemented_by]` / `opaque`), (3) every match pattern it relies on
respects the rules in §6, (4) every recursive definition in its
dependency graph passes Lean's totality check by constructive measure,
and (5) its proof term resides entirely in the strict harness's
audited surface.

Companion to `AXIOMS.md` (zero-axiom policy) and `WORKING_RULES.md`
(kernel-discipline rules). Where AXIOMS.md focuses on the negative
("which axioms are banned"), this document focuses on the positive
("what computability *is* and how to maintain it").

This document is normative: any new theorem, definition, or kernel
extension must satisfy every rule herein. The strict harness enforces
mechanically; this document explains what the harness checks and why.

---

## 1. Computability — the formal definition

A type theory T is **computable** iff all four properties hold:

| Property | Statement |
|----------|-----------|
| Strong Normalization (SN) | Every well-typed term reduces to a normal form in finitely many steps under any reduction strategy. |
| Confluence (Church-Rosser) | If `t →* a` and `t →* b`, there exists `c` with `a →* c` and `b →* c`. |
| Subject Reduction (SR) | If `Γ ⊢ t : A` and `t →* t'`, then `Γ ⊢ t' : A`. |
| Decidable Type-Checking | Given context `Γ`, term `t`, and type `A`, there is a terminating procedure that decides whether `Γ ⊢ t : A`. |

If any of the four fails, the theory is *not* computable. lean-fx-2's
strict harness enforces all four indirectly: every shipped theorem
elaborates in finite time (decidability), every kernel reduction
preserves typing (SR by construction in the intrinsic kernel),
confluence is proved as part of the metatheory cascade
(`Confluence/RawCdLemma.lean`, `Confluence/RawChurchRosser.lean`), and
SN is the goal of M04 (Tait reducibility).

A *zero-axiom* theorem in lean-fx-2 inherits these properties from
the kernel as long as the conditions in §3-§7 below are met.

## 2. The unifying invariant: constructor-driven dispatch

Beneath the four-fold definition lies a single principle that makes
each property attainable:

> **Every elimination is dispatched by case analysis on its scrutinee's
> constructor structure, with each case specified by an explicit
> computation rule.**

Examples from the kernel:

| Elimination | Scrutinee | Dispatch |
|-------------|-----------|----------|
| `Term.app (Term.lam body) arg` | `lam body` | β: `body[arg/var0]` |
| `Term.boolElim Term.boolTrue t e` | `boolTrue` | ι: `t` |
| `Term.natElim Term.natZero z s` | `natZero` | ι: `z` |
| `Term.transp pathLam src` | `pathLam (piTyCode A B)` | dispatcher in `cdTranspPathLamBody` |
| `Term.modElim (Term.modIntro inner)` | `modIntro inner` | β: `inner` |

Each rule is a constructor of `Step` or `RawStep.par` with an
explicit reduction target. No rule fires "magically"; each is a
kernel ctor with a body. Adding a new feature is admissible iff its
eliminations can be expressed as constructor-driven dispatch.

## 3. The three classes of non-computability vectors

A theorem can fail to be computable through three distinct classes of
mechanism. The strict harness has gates for each.

### Class 1 — Explicit axioms

```
axiom propext           : ∀ {a b : Prop}, (a ↔ b) → a = b
axiom Quot.sound        : r a b → Quot.mk r a = Quot.mk r b
axiom Classical.choice  : Nonempty α → α
sorryAx                 : ∀ α, α    -- emitted by `sorry`
```

**Detection**: `#print axioms YourTheorem` walks the dependency graph
transitively. If empty, Class 1 is closed.

**Coverage**: STRICT-1 (`#assert_no_axioms`) build-time gate.

### Class 2 — Non-computability markers

```
noncomputable def foo : X := ...
@[extern "c_func"] def bar : X := ...
@[implemented_by realImpl] def baz : X := ...
@[opaque] def qux : X := body
unsafe def loop : X := ...
partial def stream : X := ...
```

**Detection**: `#print axioms` does NOT report these — they are
separate Lean mechanisms. Need syntactic attribute scan.

**Coverage**: STRICT-2 (`#audit_namespace_strict`) walks every user
declaration and rejects any with these markers.

### Class 3 — Implicit dependencies that propagate axioms

The most subtle class. A theorem may have no axioms or markers in its
body, yet `#print axioms` reports propext / Classical.choice /
Quot.sound because of how Lean elaborates certain patterns.

| Pattern | Vector |
|---------|--------|
| Wildcard `\| _ =>` in match | propext via auto-equation lemma |
| Indexed-inductive partial match | propext via impossible-case equation |
| Tactic-mode `by ... match` | propext via match-compiler lifting |
| `simp` with default simp-set | propext via Prop-rewriting lemmas |
| `decide` over Classical-derived `Decidable` | Classical.choice via instance |
| `Inhabited X` from `Classical.choice` | Classical.choice via `default : X` |
| `decreasing_by sorry` | sorryAx via termination proof |
| `cases` on dependent inductive without motive | propext via dependent elim |

**Detection**: STRICT-1's transitive `#print axioms` catches each
because the proof term Lean generates references the axiom even though
the source code does not.

**Coverage**: STRICT-1 + lean-fx-2's accumulated discipline
(memory-encoded match-compiler patterns) prevents the patterns from
appearing in source.

## 4. The strict harness coverage matrix

Every non-computability vector maps to at least one strict-harness
gate.

| Vector | Source | Detection gate |
|--------|--------|----------------|
| Explicit axiom | direct decl | STRICT-1 |
| Axiom in transitive dep | inherited | STRICT-1 (transitive walk) |
| `noncomputable` marker | source attribute | STRICT-2 |
| `@[extern]` / `@[implemented_by]` | source attribute | STRICT-2 |
| `opaque` non-reducible | source attribute | STRICT-2 |
| Direct `Classical.X` reference | identifier | STRICT-2 |
| `unsafe` / `partial` | source keyword | STRICT-2 + decl-form check |
| `sorry` in proof body | sorryAx propagation | STRICT-1 + source scan |
| Match-compiler propext leaks | match-compiler emission | STRICT-1 (per-decl) |
| Classical Decidable via decide | instance propagation | STRICT-1 |
| Hypothesis-as-postulate | extra parameter pretending to be theorem | STRICT-7 |
| Raw/typed Step.par divergence | new ctor without typed mirror | STRICT-3 |
| Typed/raw Step.par divergence | typed ctor without raw mirror | STRICT-9 |
| Naming discipline | non-ASCII / short identifiers | STRICT-6 |

**Theorem**: a declaration that passes STRICT-1 through STRICT-9
(every gate green) is computable in the sense of §1, modulo the
trusted computing base in §8.

## 5. The two-layer architecture

lean-fx-2's computability story is layered:

```
┌──────────────────────────────────────────────────┐
│ Layer 2 — FX intrinsic kernel                    │
│   Term : Ctx mode level scope → Ty level scope    │
│          → RawTerm scope → Type                  │
│   Step : Term → Term → Prop                      │
│   Reductions are kernel β-rules with explicit    │
│   computational realizations                     │
└──────────────────────────────────────────────────┘
                        ↑ (encoded in)
┌──────────────────────────────────────────────────┐
│ Layer 1 — Lean 4 host                             │
│   Lean 4 kernel + standard library                │
│   Strict harness (Tools/AuditAll/, StrictHarness) │
└──────────────────────────────────────────────────┘
```

Both layers must be computable for the system to be computable end to
end. The strict harness operates at Layer 1 and applies to Layer 2's
encoding.

## 6. Match-compiler patterns to avoid

Lean 4's match compiler generates equation lemmas that occasionally
introduce `propext` or `Quot.sound` without source-level visibility.
References: `feedback_lean_zero_axiom_match`,
`feedback_lean_match_propext_recipe`,
`feedback_lean_indexed_partial_match`.

### P1 — Wildcard always leaks

```
def f : RawTerm → RawTerm
  | .lam body => ...
  | _ => default     -- LEAKS propext via auto-equation lemma
```
**Fix**: full enumeration of constructors; every variant explicit.

### P2 — Indexed-inductive partial match

```
def headBinding : GradedCtx (n + 1) → Binding
  | .cons newBind _ => newBind   -- LEAKS via impossible-case equation
```
**Fix**: `casesOn` with motive that takes index-equality witness;
discharge impossible cases via `Nat.noConfusion`.

### P3 — Tactic-mode match

```
theorem foo : ... := by
  match x with | A => ... | B => ...
```
Tactic-mode match leaks propext where direct pattern-match on def body
does not. **Fix**: direct pattern-match on def body; or `casesOn` /
`recOn` with explicit motive in tactic mode.

### P4 — Wildcard over big enums (>100 ctors)

For inductives with hundreds of constructors, `<;> rfl` chains may
exceed kernel budget or trip propext heuristics.
**Fix**: helper sub-enum partitioning.

### P5 — Multi-cons-literal patterns

```
match str with
| "abc" => ...
| "def" => ...
| _ => ...     -- multiple String literals + wildcard leaks propext
```
**Fix**: enumerate via Char-level patterns or `match` over `Decidable`
predicates.

### P6 — Multi-Nat-indexed inductives

Inductives like `Foo : Nat → Nat → Type` trigger propext+Quot.sound
when N implicits sit inside the ∀.
**Fix**: hoist all but one Nat to the theorem header (before `:`).
Reference: `feedback_lean_match_arity_axioms`.

### P7 — Match with witness

For dependent matches where impossible cases must be discharged:
```
match someTerm, witness with
| A, hA => ...
| B, hB => ...
```
This pattern lets the matcher use raw-form constructor mismatch to
discharge non-matching cases at zero axioms.
Reference: `feedback_lean_match_witness_pattern`.

### P8 — `Char.X` namespace pitfall

`Char.X` namespace functions sometimes route through a String API that
includes `propext`-using lemmas. Audit individually.

## 7. Termination and decidable judgments

### 7.1 Termination — every recursion measures

Every `rec` definition in lean-fx-2 must satisfy one of:

1. **Structural**: argument is a strict subterm of the input
2. **Lexicographic**: tuple of arguments decreases lexicographically
3. **`decreases by` with constructive proof**: explicit measure with
   well-foundedness witness
4. **`with Div` declaration**: explicit opt-in to potentially
   non-terminating semantics, accompanied by handler context

`decreasing_by sorry` is **forbidden**: it depends on `sorryAx` and
fails STRICT-1.

### 7.2 Decidability of dimension judgments

FX's 21 dimensions all have decidable structure. If any future
dimension is not decidable, computability cracks at that dimension.
New dimensions require explicit decidability arguments.

| Dimension | Decidability |
|-----------|--------------|
| Type | bidirectional algorithm |
| Refinement | decidable predicates compute; SMT for the rest with proof witness |
| Usage | `{0, 1, w}` — finite |
| Effect | finite sets — decidable join |
| Security | 2-element lattice |
| Protocol | finite transducer |
| Lifetime | region stack — decidable preorder |
| Provenance | finite label lattice |
| Trust | discrete totally ordered enum |
| Representation | finite layout enum |
| Observability | boolean |
| Clock domain | finite domain set |
| Complexity | cost-semiring with decidable equality on closed forms |
| Precision / Space / Size | naturals |
| Overflow | 4-element enum |
| FP order | 2-element enum |
| Mutation | 4-element lattice |
| Reentrancy | boolean |
| Version | finite ordered labels |

## 8. The trusted computing base

lean-fx-2 trusts:

1. **Lean 4 kernel** (~6 KLoC C++): typechecker + reduction rules.
   Externally cross-checked by Lean4Lean (Mario Carneiro's
   re-implementation in Lean).
2. **Lean 4 match compiler**: this is where most subtle propext leaks
   originate. lean-fx-2's accumulated recipes (§6 patterns) close
   each known leak.
3. **Lean 4 elaborator**: tactic mode resolution, instance synthesis,
   universe inference. Standard trust assumption.
4. **Lean 4 universe arithmetic**: cumulative hierarchy with
   `imax`-based level rules. No `Type : Type`. Decidable.
5. **Lean stdlib on the audited dependency surface**: every stdlib
   lemma transitively used by FX must be audited via `#print axioms`
   to ensure no inherited axioms.

The TCB is the same as for any rigorous Lean 4 project. lean-fx-2 does
not eliminate it; it minimizes its surface and audits its boundary.

## 9. Practical workflow

### 9.1 Per-theorem checklist

When shipping a new theorem `T`:

- [ ] **Discipline**: write the proof following lean-fx-2 patterns —
      full enumerations, direct pattern-match on def body, audit-clean
      `Decidable` instances, no `simp` with default simp-set on
      axiom-sensitive goals.
- [ ] **Build**: `lake build LeanFX2` succeeds (kernel-only).
- [ ] **Per-decl gate**: `#print axioms T` reports "does not depend on
      any axioms".
- [ ] **Strict gate**: `#assert_no_axioms T` added to
      `Tools/AuditAll/AuditX.lean` (X = relevant subsystem).
- [ ] **Smoke audit**: `T` appears in `Smoke/AuditPhaseY.lean` with
      `#print axioms T`.
- [ ] **Full audit**: `lake build LeanFX2 LeanFX2Audit` succeeds.

If all six pass green, `T` is shipped per FX's commitment.

### 9.2 Pre-commit checklist

- [ ] **Inner-loop**: `lake build LeanFX2` green (kernel-only).
- [ ] **Audit pass**: `lake build LeanFX2 LeanFX2Audit` green
      (full strict harness). Non-negotiable.
- [ ] **Smoke logs**: every new theorem has `#print axioms` entry.
- [ ] **Memory updates**: new match-compiler recipe → append to
      relevant `feedback_lean_*` memory.
- [ ] **Naming discipline** (STRICT-6).

## 10. Code smells

These patterns are not strictly forbidden but require careful audit
when they appear.

**Heavy `simp` use** — `simp` may use `propext` internally. The final
proof term is what's audited. Best practice: `simp only
[explicit_lemma_list]` with audited lemmas.

**Tactic-mode `match`** (per P3 above): leaks propext where direct
pattern-match doesn't. Best practice: direct pattern-match on def
body when possible.

**Implicit `Decidable` inference**: `decide P` finds Decidable via
ambient context; if found via `Classical.decEq`, Classical leaks.
Best practice: explicit `instance : Decidable P := isTrue ...` with
constructive witness.

**`Inhabited` propagation**: `default : X` requires `Inhabited X`. If
that instance was built from `Classical.choice`, Classical leaks
transitively. Best practice: verify Inhabited instances are
constructive.

**`infer_instance` for axiom-sensitive instances**: may find a
non-constructive instance from ambient context. Best practice:
explicit instance providers when audit-sensitive.

**`rfl` on opaque definitions**: `opaque` blocks kernel reduction. If
you need computability, do not use `opaque`.

## 11. Future extensions and gates needed

The current strict harness covers the kernel as currently shipped.
Future extensions require additional gates.

**User-extensible β rules** (the "diabolical D1" extension):
- STRICT-10 (proposed): confluence verifier for user-supplied β
  rules. New rules must not create critical pairs that don't join.
- STRICT-11 (proposed): termination verifier. User rules must
  preserve SN.
- STRICT-12 (proposed): type preservation verifier. User rules must
  preserve subject reduction.

**Optimal reduction (Lévy-Lamping)** adds a fourth reduction relation
`OptStep`. Requires STRICT-13: sharing-graph well-foundedness gate.

**WMM-aware kernel β**: memory operations with type-level orderings.
Requires STRICT-14: DRF preservation check.

**∞-groupoid coherences**: higher-dimensional cell ctors require
STRICT-15: n-cell decidability check at each dimension.

**Synthetic Tait computability**: if M04 (Tait SN) ships internally
rather than as Lean metatheory, requires STRICT-16: self-reference
soundness check.

These are forward-looking and do not affect the current shipping
discipline.

## 12. What adherence guarantees

A theorem that passes the full strict harness has:

| Guarantee | Mechanism |
|-----------|-----------|
| Every reduction step in normalization terminates | M04 SN (when shipped) + Lean's existing SN for Layer 1 |
| Every term has a normal form in well-typed contexts | SN + confluence |
| Type-checking decides yes/no in finite time | bidirectional algorithm, decidable Conv |
| Proof term is a closed program in Lean 4 calculus | zero-axiom + no markers |
| `#eval` works on closed instances of mentioned types | computability of all dependencies |
| FX's intrinsic Term carrying the witness is well-typed | intrinsic typing by construction |
| Subject reduction holds across all Step rules used | per-rule SR proven in `Term/SubjectReduction*.lean` |

These seven together = computability in the sense of §1.

## 13. What adherence does NOT guarantee

Honest scope:

- **Efficiency**: computable does not mean fast. A theorem may
  normalize in finite steps but the constant may be enormous.
- **Practical decidability**: a Decidable instance may take
  astronomically long. Audit only checks existence, not complexity.
- **Halting of arbitrary user programs**: FX programs may not
  terminate; the kernel guarantees termination of reductions, not of
  user-defined functions without `decreases`.
- **External oracle freedom**: theorems may depend on SMT or external
  tactic frameworks for proof construction. The proof term is
  audited; the external machinery is trusted at construction time.
- **Compile-time bounds**: type-checking decides yes/no, but the
  decision procedure may exceed any practical time budget for
  pathological inputs.

These are not breaches of computability; they are well-known
limitations of constructive systems. FX inherits them.

## 14. The BHK interpretation at ∞-categorical level

The deep "why" behind the strict harness: lean-fx-2's computability
discipline is the ∞-categorical generalization of the
Brouwer-Heyting-Kolmogorov interpretation.

Classical BHK (set-level):
```
Proof of (P ∧ Q)   = pair of proofs (proof_P, proof_Q)
Proof of (P ∨ Q)   = tagged proof: left(proof_P) | right(proof_Q)
Proof of (P → Q)   = function: takes proof_P, returns proof_Q
Proof of (∀x, P x) = function: takes x, returns proof_(P x)
Proof of (∃x, P x) = pair: (witness x, proof_(P x))
Proof of ⊥         = no construction
```

HoTT lifts BHK to dependent types: equality is path = construction.
Cubical TT makes paths computational via interval-based primitives.
Cohesive HoTT adds modal operators with computational realizations.
(∞,n)-type theories add higher-coherence cells, each with explicit
computational realization.

The pattern at every level: **every connective, every modality, every
coherence has an explicit construction**.

lean-fx-2 inherits this discipline. Every Step ctor is a constructive
realization. Every Conv proof is a path with computational content.
Every modality has β-rules. Every cumul step is a witnessed
reduction.

## 15. Cross-references

- **AXIOMS.md** — zero-axiom commitment + per-axiom catastrophe
  analysis. Companion document focused on the negative.
- **WORKING_RULES.md** — 18 distilled kernel-discipline rules.
  Concrete operationalizations of principles in this document.
- **ARCHITECTURE.md** — 13-layer dependency DAG. Computability is
  preserved across layers iff each layer's audit passes.
- **ROADMAP.md** — phased plan; future extensions in §11 reference
  roadmap items.
- **MIGRATION.md** — lean-fx → lean-fx-2 cutover plan; computability
  audit was a hard cutover requirement.
- **CLAUDE.md** (lean-fx-2) — project-local instructions; the
  "Forbidden declaration forms" section enumerates Class 2 vectors
  in detail.
- **Tools/AuditAll/** — implementation of STRICT-1 through STRICT-9.
- **Tools/StrictHarness.lean** — `#assert_no_axioms`,
  `#audit_namespace`, `#audit_namespace_strict`,
  `#assert_raw_typed_parity`, `#audit_summary`.
- **Smoke/AuditPhase*.lean** — reviewer-facing per-phase audit logs.
- **`feedback_lean_*` memories** at
  `/root/.claude/projects/-root-iprit-FX/memory/` — accumulated
  recipes for Class 3 vector avoidance.

---

End of computability-rules.md.
