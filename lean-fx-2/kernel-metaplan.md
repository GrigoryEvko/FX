# kernel-metaplan.md

## Purpose

This document defines the metatheory and trusted-computing-base plan for
lean-fx-2 after the kernel sprint.

The goal is not to rewrite lean-fx-2. The goal is to put a smaller trust
substrate under the existing kernel, prove that the current rich encoding
lowers into it, and use that path to reimplement the Lean kernel for
lean-fx purposes.

The existing lean-fx-2 kernel remains the rich feature layer. New minimal
cores are added below it.

## Core Claim

lean-fx-2 should have three layers with different trust roles:

```text
LeanFX2 rich layer
  Existing Ty / RawTerm / Term / Step / Conv / Graded / HoTT / Cubical code.
  Kept for expressivity and current roadmap work.

FX1
  Minimal Lean-like lambda-Pi kernel.
  Used for ergonomic self-hosting and Lean-kernel reimplementation.

FX0
  MM0-like first-order certificate checker.
  Used as the eventual skeptical root verifier.
```

The immediate work is FX1. FX0 is the escape hatch that prevents FX1 from
becoming the final large trusted base.

## Non-Goals

This plan does not require:

- rewriting existing `LeanFX2.Foundation.Ty`;
- rewriting existing `LeanFX2.Foundation.RawTerm`;
- rewriting existing `LeanFX2.Term`;
- deleting existing HoTT, cubical, modal, graded, refinement, session, or
  effect files;
- trusting the Lean parser, elaborator, tactics, Lake, compiler, or Std as
  part of the object-theory story;
- implementing full Lean surface syntax;
- implementing the full Lean elaborator;
- trusting an FX1 checker result without an eventual FX0 certificate path.

The plan is additive first. Refactoring existing files happens only after
the bridge into FX1 is load-bearing.

## Local Lean Reference Boundary

The local Lean source at `/root/Downloads/lean4` is the reference for the
Lean-kernel-compatible part of FX1.

Lean's kernel boundary is the source set under:

```text
/root/Downloads/lean4/src/kernel/
```

The minimal reference files are:

```text
level.cpp / level.h
expr.cpp / expr.h
abstract.cpp / instantiate.cpp
local_ctx.cpp / local_ctx.h
declaration.cpp / declaration.h
environment.cpp / environment.h
type_checker.cpp / type_checker.h
inductive.cpp / inductive.h
quot.cpp / quot.h
```

The following are not kernel roots for FX1:

```text
src/Lean/
src/Std/
src/library/
src/lake/
src/runtime/
src/bin/
parser, elaborator, macro system, tactic framework, server, compiler backend
```

They may be reference material, but they are not trusted semantics.

## Lean Host Policy For FX1

Lean 4 is the host metatheory while FX1 is being mechanized. FX1/Core must
use as little of Lean as practical.

Allowed in FX1/Core:

```lean
prelude
import Init.Prelude
```

Allowed host concepts:

- Lean's kernel checking;
- `inductive`, `structure`, and structurally recursive `def`;
- `Nat`, `Bool`, `Option`, `List`, `Prod`, `Sum`, `Unit`, `Empty` from
  `Init.Prelude`;
- `Eq`, `HEq` only when audit-clean and not used to smuggle extensional
  principles;
- explicit pattern matching;
- term-mode proofs;
- `rfl` and direct constructor proofs.

Forbidden in FX1/Core:

- `import Lean`;
- `import Std`;
- `import Init.Classical`;
- `Classical.*`;
- `propext`;
- `Quot`, `Quot.sound`, `Quot.lift`;
- `noncomputable`;
- `unsafe`;
- `partial`;
- `opaque` as a proof shortcut;
- `sorry`, `admit`, `sorryAx`;
- `@[extern]`;
- `@[implemented_by]`;
- `Init.Tactics`, `omega`, `grind`, or tactic-heavy automation;
- well-founded/extrinsic recursion machinery as a computational shortcut;
- deriving instances unless the generated declaration is audit-clean.

FX1/Core gets its own strict audit gate. Passing the general LeanFX2 audit is
necessary but not sufficient.

## FX1 Minimal Kernel

FX1 starts smaller than Lean's real kernel.

Initial FX1 syntax:

```lean
namespace LeanFX2.FX1

inductive Name where
  | anonymous
  | str (prefix : Name) (part : String)
  | num (prefix : Name) (index : Nat)

inductive Level where
  | zero
  | succ (base : Level)
  | max (left right : Level)
  | imax (left right : Level)
  | param (name : Name)

inductive Expr where
  | bvar (index : Nat)
  | sort (level : Level)
  | const (name : Name)
  | pi (domain body : Expr)
  | lam (domain body : Expr)
  | app (function argument : Expr)

end LeanFX2.FX1
```

The first FX1 core intentionally omits:

- free variables;
- metavariables;
- let expressions;
- literals;
- metadata;
- projections;
- inductives;
- quotient primitives;
- proof irrelevance;
- eta;
- unsafe/partial/opaque declarations.

Those are added only after the smaller core has preservation and checker
soundness.

## FX1 Environment

FX1 has a checked environment, not arbitrary constants.

Initial declarations:

```lean
inductive Declaration where
  | axiomDecl (name : Name) (type : Expr)
  | defDecl (name : Name) (type value : Expr)
  | theoremDecl (name : Name) (type proof : Expr)
```

Release policy:

- `axiomDecl` is allowed only for modeling object systems during staged
  development.
- `axiomDecl` is forbidden in the release root.
- Lean's built-in `propext`, `Quot.sound`, and `Classical.choice` are never
  used to justify FX1 declarations.

Definitions are transparent by default. Opaque definitions are not part of
FX1/Core.

## FX1 Metatheory Spine

FX1/Core is not trusted merely because it is small. It must prove its own
load-bearing metatheory.

Required results:

```text
scope checking
weakening
renaming
substitution
substitution identity
substitution composition
renaming/substitution interaction
beta substitution lemma
environment well-formedness
context well-formedness
typing preservation for beta
typing preservation for delta
conversion soundness
WHNF soundness
checker soundness
```

Primary theorem:

```lean
theorem FX1.check_sound :
    FX1.check environment context expression = some typeExpression ->
    FX1.HasType environment context expression typeExpression
```

No FX1 feature counts as trusted until it is covered by this theorem or by an
explicit theorem that reduces it to the covered fragment.

## FX1 Checker

The checker is the ergonomic root for the Lean-like layer.

Initial checker responsibilities:

- infer/check `sort`;
- infer/check constants by environment lookup;
- infer/check Pi;
- infer/check lambda against expected Pi;
- infer/check application;
- compare by beta/delta conversion;
- reject ill-scoped expressions;
- reject unknown constants;
- reject universe-level errors.

The checker does not perform elaboration. It checks already elaborated FX1
kernel expressions.

## Existing LeanFX2 Integration

Existing lean-fx-2 remains the rich layer. It is integrated by translation,
not by rewrite.

Bridge functions:

```lean
def encodeTy :
    LeanFX2.Ty level scope -> FX1.Expr

def encodeRawTerm :
    LeanFX2.RawTerm scope -> FX1.Expr

def encodeCtx :
    LeanFX2.Ctx mode level scope -> FX1.Context
```

Load-bearing theorem:

```lean
theorem encode_term_sound :
    LeanFX2.Term context typeExpression rawExpression ->
    FX1.HasType environment
      (encodeCtx context)
      (encodeRawTerm rawExpression)
      (encodeTy typeExpression)
```

This theorem is added incrementally:

1. variables;
2. unit;
3. Pi/lambda/app;
4. universe codes;
5. core identity fragment;
6. current rich constructors as declared object constants;
7. rich constructors with real definitions as they become available.

Rich features do not need to be removed. They are initially "fired in" as
FX1 declarations, then replaced by definitions/proofs when their metatheory is
ready.

## "Primitives Fired In" Policy

Some lean-fx-2 features are too large to be primitive in FX1/Core:

- HoTT equality reductions;
- cubical paths and transport;
- HITs;
- modalities;
- graded rules;
- refinements;
- effects;
- sessions;
- codata/productivity.

These should enter FX1 in staged form:

```text
Stage A: declared constants in FX1 environment
Stage B: typing rules encoded as FX1 predicates
Stage C: computation rules encoded as FX1 theorems
Stage D: current LeanFX2 constructor soundness proved via encode_*_sound
Stage E: optional replacement by smaller definitions if worth it
```

This preserves current lean-fx-2 semantics while shrinking the root.

No staged primitive is allowed to masquerade as done. Each primitive is
classified:

```text
declared
typed
computational
encoded-sound
checker-sound
FX0-certified
```

Only `checker-sound` and `FX0-certified` are root-trust statuses.

## Lean-In-Lean-FX Path

The Lean kernel reimplementation targets FX1, not the current rich kernel.

Staged LeanKernel namespace:

```text
LeanFX2/FX1/LeanKernel/Name.lean
LeanFX2/FX1/LeanKernel/Level.lean
LeanFX2/FX1/LeanKernel/Expr.lean
LeanFX2/FX1/LeanKernel/Declaration.lean
LeanFX2/FX1/LeanKernel/Environment.lean
LeanFX2/FX1/LeanKernel/Substitution.lean
LeanFX2/FX1/LeanKernel/Reduction.lean
LeanFX2/FX1/LeanKernel/HasType.lean
LeanFX2/FX1/LeanKernel/Check.lean
LeanFX2/FX1/LeanKernel/Soundness.lean
```

Faithful Lean stages:

1. Lean levels: zero, succ, max, imax, param, mvar.
2. Lean names: anonymous, string, number.
3. Lean expressions: the 12 kernel constructors.
4. Lean declarations: definitions, theorems, opaque, axioms, inductives,
   quotients, mutual definitions.
5. Lean substitution: instantiate, abstract, lifting.
6. Lean reduction: beta, delta, zeta.
7. Lean projections.
8. Lean inductives and recursor iota.
9. Lean quotient primitives as modeled object declarations, not as host
   `Quot.sound`.
10. Lean `isDefEq` soundness, not completeness first.
11. Lean checker soundness.

The primary theorem:

```lean
theorem LeanKernel.check_sound :
    LeanKernel.check environment localContext expression = some typeExpression ->
    LeanKernel.HasType environment localContext expression typeExpression
```

This reduces trust in Lean's implementation, but does not eliminate the Lean
host until FX0 or standalone extraction verifies the same result.

## FX0 Escape Hatch

FX0 is an MM0-like root certificate checker.

FX0 is not the ergonomic kernel. It is the final audit machine.

FX0 primitives:

- sorts;
- term constructors;
- theorem declarations;
- explicit theorem application;
- explicit substitution;
- explicit definition unfolding;
- stack-machine proof checking;
- no dependent conversion engine;
- no elaborator;
- no tactics;
- no hidden inference.

Target path:

```text
FX1 theorem/check trace
  -> FX1 certificate emitter
  -> FX0 certificate
  -> FX0 verifier accepts
```

First FX0 milestone:

```text
FX1 identity function typing proof
  -> emitted FX0 certificate
  -> FX0 verifier accepts
```

FX0 is not required before FX1 work starts. It is required before claiming
minimal final TCB.

## Sprint Integration

This metaplan adds a new trust-spine track to `kernel-sprint.md`.

```text
M0: FX1 host-minimal policy
  Add FX1/Core namespace.
  Add host-minimal audit gate.
  No existing rich-kernel rewrite.

M1: FX1 syntax and environments
  Name, Level, Expr, Declaration, Env, Context.
  Scope checking.

M2: FX1 renaming and substitution
  Shift, lift, instantiate.
  Substitution identity and composition.

M3: FX1 typing and reduction
  HasType.
  beta and delta Step.
  preservation.

M4: FX1 checker
  WHNF for beta/delta.
  conversion soundness.
  check.
  check_sound.

M5: Existing LeanFX2 bridge
  encodeTy.
  encodeRawTerm.
  encodeCtx.
  encode_term_sound for core constructors.

M6: LeanKernel over FX1
  Port existing Lean.Kernel skeleton to FX1 namespace.
  prove subset check_sound.

M7: FX0 prototype
  MM0-like certificate VM.
  verify one FX1 typing certificate.
```

Original sprint tasks are reclassified:

```text
Day 1-3 foundation/cubical/HoTT:
  FX-rich layer unless bridged into FX1.

Day 5 graded/refine/effects/sessions/codata:
  FX-rich typing disciplines unless bridged into FX1.

Day 8 Lean kernel:
  Move under FX1/LeanKernel.

Day 7 audit:
  Extend with root-status classification and FX1 host-minimal gate.
```

## Root Status Labels

Every module gets one of these labels:

```text
Root-FX1
  Part of the minimal lambda-Pi kernel and covered by FX1.check_sound.

LeanKernel-FX1
  Part of the Lean-kernel reimplementation over FX1.

FX-rich
  Existing expressive lean-fx-2 layer.

Bridge
  Translation/soundness connection between layers.

FX0-root
  First-order certificate checker layer.

Scaffold
  Syntax or docs without load-bearing theorem.

Deferred
  Explicitly not claimed.
```

No feature is counted as root-trusted unless it is `Root-FX1` or
`FX0-root`.

## Acceptance Criteria

FX1 M0 is done when:

- FX1/Core imports only host-minimal files;
- strict audit forbids `Lean`, `Std`, `Classical`, `Quot`, `unsafe`,
  `noncomputable`, `opaque`, `extern`, and `implemented_by`;
- `lake build LeanFX2` is green.

FX1 M4 is done when:

- `FX1.check_sound` typechecks;
- all FX1/Core declarations are axiom-clean;
- malformed terms have negative smoke tests;
- no current lean-fx-2 rich feature is counted as FX1-root.

LeanKernel M6 is done when:

- a Lean-kernel subset is represented over FX1;
- the subset checker has a soundness theorem;
- quotient and classical primitives are modeled, not used from Lean.

FX0 M7 is done when:

- FX0 has a tiny proof checker;
- one FX1 typing theorem is emitted as an FX0 certificate;
- FX0 verifies that certificate.

## Operational Rule

When adding new lean-fx-2 primitives:

1. Keep current rich encoding if it already exists.
2. Add an FX1 declaration for the primitive only if needed by translation.
3. Add typing and computation theorems as explicit FX1 facts.
4. Prove an `encode_*_sound` theorem before upgrading status.
5. Do not move the primitive into FX1/Core unless it is required for the
   minimal lambda-Pi checker itself.

This is the core discipline: preserve existing semantics, shrink the trusted
root, and make the escape path to Lean-in-lean-fx explicit.
