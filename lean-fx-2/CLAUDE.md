# CLAUDE.md — lean-fx-2 project-local instructions

When working in `lean-fx-2/` (this directory), apply the rules below
in addition to global `/root/iprit/FX/CLAUDE.md`.

## Required reading (in order, on every fresh context)

1. `AXIOMS.md` (this dir) — trust budget + per-axiom catastrophe analysis
2. `WORKING_RULES.md` (this dir) — 18 distilled kernel-discipline rules
3. `ARCHITECTURE.md` (this dir) — 13-layer dependency DAG
4. `ROADMAP.md` (this dir) — Layer-by-Layer phasing
5. `MIGRATION.md` (this dir) — lean-fx → lean-fx-2 cutover plan
6. `LeanFX2/Sketch/Wave9.lean` — raw-aware Term proof of concept

## Architectural commitments (DO NOT violate)

* **Term carries `RawTerm scope` as a type-level index.**
  `Term : Ctx mode level scope → Ty level scope → RawTerm scope → Type`.
  `Term.toRaw t = raw` is `rfl`.

* **Subst is unified.**  `Subst level src tgt = { forTy : Fin src → Ty level tgt, forRaw : RawTermSubst src tgt }`.
  ONE `Subst.singleton` operation; NO `dropNewest`, NO `termSingleton` variant.

* **Conv is `∃ commonReduct, StepStar t1 commonReduct ∧ StepStar t2 commonReduct`.**
  NOT inductive with 13 cong rules.  `Conv.trans` lives in Layer 3 (depends on Church-Rosser).

* **η is opt-in** (`Step.eta` namespace).  βι is the default.

* **Cumulativity is a Conv rule** (Layer 3+), not a Ty constructor.

* **Mode lives at Ctx level.**  `Ctx : Mode → Nat → Nat → Type`.  Term
  ctors carry `{mode : Mode}` as implicit (forward-compat with mode-
  changing modal ctors at Layer 6 — `modIntro`/`subsume` may produce
  a Term in a different mode than its input).  User code never
  explicitly names mode; Lean infers it from context's type.  Modal
  types proper introduced via `Ty.modal modality inner` constructor
  at Layer 6.

* **Identity-type endpoints are RawTerm**, not typed Term.
  Sidesteps Lean 4's mutual-index rule.

## Zero-axiom commitment — ABSOLUTE, NO EXCEPTIONS

**Every shipped declaration MUST be `theorem`, `lemma`, `def`, `inductive`,
`structure`, or `instance`.  No exceptions.  No "documented exceptions".
No "trust budget".  No layered policy.  This rule is non-negotiable and
overrides any older AXIOMS.md / WORKING_RULES.md text granting exceptions.**

### Forbidden declaration forms

The following declaration forms are BANNED across the entire project,
including HoTT/Univalence.lean, including HIT files, including modal
files, including bridges:

* `axiom` — no axioms.  Period.  Even one is too many.
* `postulate` — Lean 4 doesn't expose this keyword, but the equivalent
  via `axiom` is also banned.
* `opaque` declarations whose body is `sorry` or whose equation is not
  derivable from kernel reductions — opaque is permitted ONLY when used
  to hide a fully-defined function for typeclass-resolution reasons,
  and the body must reduce.
* `sorry` (durable in any committed file — no `sorry` slips through CI)
* `admit`
* `@[univalence_postulate]` attribute — DELETED.  The attribute itself
  was a deception scaffold; the attribute is forbidden.
* `noncomputable` — banned for kernel theorems.  If a theorem reaches
  for `Classical.choice` or `propDecidable`, the theorem is wrong.
* `@[implemented_by]` / `@[extern]` for kernel theorems — these hide
  Lean meta-level computation behind unverified C/native code.

### Forbidden reasoning patterns (axiom-equivalents)

These patterns SHIP a theorem conditionally on an unprovable assumption.
That is a deception — semantically identical to an axiom, just with
extra parameters.  ALL of these are banned:

* **Hypothesis-as-postulate**: `theorem foo (univ : Univalence) : ...` —
  if `Univalence` itself is unprovable in the kernel, then `foo` is
  vacuously "shipped" with its truth deferred to the unprovable input.
  Same lie as `axiom Univalence`.  BANNED.
* **`IsX : Prop` / `HasX : Sort N` placeholder predicates** that pretend
  to ship a result but only state what the result would say if it
  existed.  E.g. `def IsUnivalent : Sort 2 := ...` followed by
  `theorem ... (h : IsUnivalent) : ...`.  BANNED.
* **`Type → Type` parameter that secretly carries univalence**:
  passing equivalences/equalities you can't construct as data is the
  same lie at a different name.  BANNED.
* **`Inhabited X` instance for a type X you can't construct** — relying
  on classical inhabitation to ship a witness is the choice axiom in
  disguise.  BANNED for kernel theorems.
* **Conditional theorems whose hypothesis is `sorry`-blocked** — even if
  the hypothesis is "defined" elsewhere, if the only proof of it is
  `sorry`, the conditional is a deception.

### Mandatory verification gate

Every committed theorem/lemma/def MUST have an axiom gate.  The
preferred gate is `#assert_no_axioms YourTheorem` in
`LeanFX2/Tools/AuditAll.lean`, because it fails elaboration if any
dependency tree contains an axiom.  `#print axioms` gates in
`Smoke/AuditPhase*.lean` files remain useful reviewer-facing
regression logs, but they are supplementary because they only print.

`#assert_no_axioms` is implemented in
`LeanFX2/Tools/DependencyAudit.lean` and includes Lean core axioms:
`propext`, `Quot.sound`, and `Classical.choice` are build failures.
Until the whole-project generated audit is complete, new load-bearing
declarations MUST be added both to the curated fail-fast
`Tools/AuditAll.lean` list and to the relevant smoke audit file.

The smoke audit MUST report:

```
'Foo' does not depend on any axioms
```

A theorem that prints `propext`, `Quot.sound`, `Classical.choice`, or
ANY user-declared axiom name is NOT shipped.  Either prove it cleanly
or DELETE it.

### Univalence, funext, and HIT eliminators are PROVED, not postulated

Vanilla MLTT cannot prove Univalence — but lean-fx-2 is NOT vanilla
MLTT.  We define our own `Step` relation, and we MAKE univalence
definitional by adding the right reduction rule.  Univalence in this
project is a REAL THEOREM with a REAL BODY, gated by `#print axioms`.
Same for funext.  Same for HIT eliminators.

**Univalence (must ship as a theorem):**

```lean
-- in Reduction/Step.lean (D2.6)
inductive Step ... where
  | eqType : Step (Ty.id (Ty.universe lvl) leftTy rightTy)
                  (Ty.equiv leftTy rightTy)
  ...

-- in HoTT/Univalence.lean (D3.6)
theorem Univalence (lvl : Nat) (leftTy rightTy : Ty lvl scope) :
    Conv (Ty.id (Ty.universe lvl) leftTy rightTy) (Ty.equiv leftTy rightTy) :=
  Conv.fromStep Step.eqType
```

`#assert_no_axioms Univalence` MUST pass, and `#print axioms
Univalence` MUST report "does not depend on any axioms".  The theorem
has a body.  No hypothesis.  No `Inhabited`.  No `axiom`.  This is the
only acceptable form.

**Funext (must ship as a theorem):**

```lean
-- in Reduction/Step.lean (D2.6)
  | eqArrow : Step (Ty.id (Ty.arrow domainTy codomainTy) leftFn rightFn)
                   (Ty.piTy domainTy (Ty.id codomainTy ...))
```

Then `theorem funext := Conv.fromStep Step.eqArrow`.  Real theorem.

**HIT eliminators (must ship as theorems):**

Each HIT (Quot, propTrunc, setTrunc, S¹, suspension, pushout,
coequalizer) ships its eliminator's computation rule as a `Step`
constructor.  The eliminator itself is a `theorem` whose body invokes
those `Step` rules via `Conv.fromStep _`.  Body required.  No
postulate.  No hypothesis-as-postulate.

**There is no "if you cannot ship"** — this commitment is non-negotiable.
The dependency chain D1.2 → D2.6 → D3.6 is the LOAD-BEARING work that
makes Univalence-as-theorem possible, and shipping those reductions is
mandatory.  An empty file with a docstring describing the plan is
acceptable as a placeholder; an `axiom` or hypothesis-as-postulate
filling in for the missing theorem is NOT.

### Shipping discipline

When you ship a new theorem:

1. Write the proof.
2. Run `lake build LeanFX2`.  Build green.
3. Add `#assert_no_axioms YourTheorem` to
   `LeanFX2/Tools/AuditAll.lean` when the declaration is load-bearing
   or otherwise part of the curated kernel gate.
4. Add `#print axioms YourTheorem` to the matching
   `Smoke/AuditPhase*.lean` file.  Verify "does not depend on any
   axioms".
5. Commit only after both gates pass.

If the audit prints any axiom — including `propext`, `Quot.sound`,
`Classical.choice`, `funext`, `Univalence`, or any user axiom — the
theorem is NOT shipped.  Either rewrite cleanly or delete.

After every new theorem, verify:
```lean
#assert_no_axioms TheoremName  -- must elaborate successfully
#print axioms TheoremName  -- must report "does not depend on any axioms"
```

## Build verification

```bash
cd /root/iprit/FX/lean-fx-2 && lake build LeanFX2
```

Expected: green build.  AuditAll gates auto-fire during build.

## Naming + style discipline

Per `WORKING_RULES.md`:
* ASCII-only identifiers (no Greek, no Unicode in code)
* ≥4-character names (no `g`, `t`, `e`, `s`, `i`, `j`, `ty`, `fn`, etc.)
* Predicates use question verbs (`isLinear`, `hasRefinement`, `shouldInline`)
* Match-arity rule: hoist Nat indices before `:` for multi-indexed pattern theorems
* No wildcards in match (always full enumeration)
* `@[reducible]` on substitution-shape helpers
* Binder-form match for indexed inductives (verify with `#print axioms`)

## What to do when stuck

1. Re-read the relevant `WORKING_RULES.md` rule
2. Re-read the source memory in `/root/.claude/projects/-root-iprit-FX/memory/`
3. Check the lean-fx analog in `/root/iprit/FX/lean-fx/LeanFX/` for inspiration
4. Apply the paired-predicate pattern (Discipline #6) if tactic-mode opacity blocks you
5. Apply the toRaw-shape dispatch (Discipline #2 Rule 5) if dep-elim wall blocks you
6. Apply the mapStep abstraction (Discipline #7) if you're writing 4-line cong inductions

## What NOT to do

* Don't introduce `Subst.dropNewest` (the source of lean-fx's bridge sorries)
* Don't introduce `Subst.termSingleton` separate from `Subst.singleton` (the variant that motivated Wave 9)
* Don't introduce `Term.toRaw_subst0_term` or any "_term" suffix variant (collapse via raw-aware Term)
* Don't add `propext`, `Quot.sound`, `Classical.choice` to ANY kernel theorem
* Don't add `axiom` declarations.  ANYWHERE.  Including `HoTT/Univalence.lean`.
  Univalence enters via `Step.eqType` (definitional reduction), not via axiom.
* Don't take `Univalence` / `Funext` / any unprovable principle as a
  HYPOTHESIS to "ship" theorems conditionally — that is the same lie
  as adding an axiom, just with extra parameters.  See "Forbidden
  reasoning patterns" above.
* Don't ship `IsX : Prop` / `HasX : Sort N` predicates as placeholders
  for "the result we'd have if X were true".  The result is either
  proven (with a body) or deleted.
* Don't bolt Mode onto Term inhabitants — keep at Ctx level
* Don't skip reading specs / memories on fresh context — those are the recovery mechanism
* Don't claim a task is "completed" because a file exists.  A task is
  completed iff (1) every shipped declaration is a theorem/lemma/def
  with a body, (2) `lake build LeanFX2` is green, AND (3) every shipped
  declaration is gated by `#print axioms` reporting clean.  Anything
  else is a deception, even if a `Smoke/AuditPhase*.lean` file exists.
