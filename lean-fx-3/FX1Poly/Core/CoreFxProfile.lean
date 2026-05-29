import FX1Poly.Core.GeneratorAdmission

/-! # Foundation/PolyCell/Core/CoreFxProfile — restricted-profile admission demonstration

V2-fix-4 (2026-05-27).  Ships a CONCRETE restricted-profile
admission predicate that exercises the per-profile admission
machinery and discharges Agent 3's H3.2 finding.

## Context: why this file exists

Agent 3 of the V2 falsification audit (2026-05-27) found that
`supportedGenerator?` is the constant `some _` for every
`Generator` under the default `fxProfile` — the `.none` branch
of `match supportedGenerator? generator with | none => ...
| some => ...` in the certifier is **unreachable**.  The
"per-profile admission" architecture is decoration today.

That finding is **architecturally accurate**: the admission
inductive `SupportedGenerator` (V2-L1.4) has a constructor for
every Generator, so the decision procedure `supportedGenerator?`
can never fail.  Restricted profiles requiring fewer Generators
would need a DIFFERENT admission predicate with FEWER admitting
arms.

But until this commit, no concrete restricted-profile predicate
existed — so the architectural claim "per-profile admission can
restrict" had no machine-witnessed example.  This commit ships
that example.

## What this file ships

A **restricted-profile predicate** `Generator.isInCoreFx` based on
list-membership against an explicit exclusion list:

```lean
def coreFxExcluded : List Generator :=
  [.gen_modIntro, .gen_modElim, .gen_subsume]

@[reducible] def Generator.isInCoreFx (g : Generator) : Bool :=
  !(coreFxExcluded.contains g)
```

Concretely: the core-FX restricted profile EXCLUDES three modal
generators (`gen_modIntro`, `gen_modElim`, `gen_subsume`).  Every
other generator remains admitted.  This is a small but real
restriction — useful for FX subtargets that don't require modal
type theory (embedded systems, real-time targets, certified
crypto stacks).

## Six witness theorems

The shipped theorems pin the predicate's behavior on concrete
Generators:

* **3 admission theorems**: `gen_var`, `gen_lam`, `gen_app` are
  admitted (the lambda-calculus backbone that EVERY profile
  needs).
* **3 rejection theorems**: `gen_modIntro`, `gen_modElim`,
  `gen_subsume` are rejected (the exclusion set's defining members).

Each closes by `rfl`: list-membership on a Generator decidable-
equality list reduces definitionally at compile time, and the
predicate's `!`-negation is a Bool reduction.

## Why list-based, not full enumeration

The clean alternative — a 194-arm match
`Generator → Bool | .gen_var => true | .gen_unit => true | ...
| .gen_modIntro => false | ...` — would honor the
`feedback_lean_zero_axiom_match` no-wildcard discipline but
require 194 explicit arms.  At V2-VORACIOUS scale this is ~200
lines per restricted profile, hostile to forward extensibility.

The list-based approach trades:
* Brevity for explicitness (3 lines per exclusion, not 194).
* `rfl`-cleanliness preserved (list membership against
  decidable-equality types reduces definitionally).
* Forward-compat for ProfileExtension's restriction interface:
  a future profile defines its own `Excluded : List Generator`
  and the rest of the infrastructure inherits.

## Integration trajectory (FUTURE work, not this commit)

This commit ships the PREDICATE and its witness theorems.  Full
integration with the certifier — i.e., a `certifyRawCellExact?`
variant parameterized by a restricted-profile admission filter —
is a separate architectural concern (would require either
modifying `supportedGenerator?` to accept a profile parameter,
or wrapping the certifier in a generator-allowlist filter).

The predicate stands alone as the FIRST concrete restricted-
profile admission decision in v2.  Subsequent work (V2-mig-x or
a future V2-fix-* extension) can integrate it with the certifier
when the engineering payoff is clear.

## Zero-axiom verification

All six witness theorems pass `#print axioms`.  Audit-gated in
`Tools/AuditAll/AuditPolyCell.lean`.

## Labor-value cascade payoff

Agent 3 H3.2 was the second of three Tier-B "architecture-honesty"
findings (after H3.3 unbounded universes / V2-fix-3, before H3.4
coverage sparsity / V2-fix-5).  This commit converts the
admission-decoration finding from "infrastructure with no example"
to "infrastructure with one concrete restricted-profile witness".

The trajectory: each Tier-B finding either becomes substantive
(V2-fix-3 design commitment witness, V2-fix-4 concrete restricted
predicate) or gets honestly framed (V2-fix-1 `_sound` docstring
rewrite).  Tier-A shipped-code violations (V2-fix-2 ResourceGraded
propext) are pure fixes.  V2-fix-* is incrementally closing the
labor-value gap that the Marxist critique correctly identified.
-/

namespace FX1Poly.Core

/-- Generators excluded from the core-FX restricted profile.

Three modal generators currently — minimal demonstration of the
restricted-profile machinery.  Future targets may extend (e.g.,
embedded profiles excluding voracious math generators, certified-
crypto profiles excluding HoTT-only generators). -/
def coreFxExcluded : List Generator :=
  [.gen_modIntro, .gen_modElim, .gen_subsume]

/-- Generator admission predicate for the core-FX restricted profile.

True iff the generator is NOT in `coreFxExcluded`.  The
`@[reducible]` attribute lets `rfl`-style witness theorems close
their per-generator equations definitionally.

For comparison: `supportedGenerator?` returns `some _` for ALL
194 Generators (constant-true under fxProfile).  `isInCoreFx`
returns `false` for the 3 excluded Generators.  This is the FIRST
shipped Bool predicate that genuinely rejects some Generator. -/
@[reducible] def Generator.isInCoreFx (someGenerator : Generator) : Bool :=
  !(coreFxExcluded.contains someGenerator)

/-! ## Section 1 — Admission witnesses (3 admitted Generators)

These theorems pin the predicate's `true` branch on Generators
that every profile must admit (lambda-calculus backbone). -/

/-- `gen_var` is admitted under core-FX (variables are
profile-universal). -/
theorem Generator.gen_var_isInCoreFx :
    Generator.gen_var.isInCoreFx = true := rfl

/-- `gen_lam` is admitted under core-FX (lambda abstraction is
profile-universal). -/
theorem Generator.gen_lam_isInCoreFx :
    Generator.gen_lam.isInCoreFx = true := rfl

/-- `gen_app` is admitted under core-FX (function application is
profile-universal). -/
theorem Generator.gen_app_isInCoreFx :
    Generator.gen_app.isInCoreFx = true := rfl

/-! ## Section 2 — Rejection witnesses (3 excluded Generators)

These theorems pin the predicate's `false` branch on the modal
generators that the core-FX restricted profile deliberately
excludes.  Each closes by `rfl` because list-membership on a
decidable-equality list reduces definitionally. -/

/-- `gen_modIntro` is REJECTED under core-FX (modal generators
require the modal-mode axis which embedded targets don't ship). -/
theorem Generator.gen_modIntro_notInCoreFx :
    Generator.gen_modIntro.isInCoreFx = false := rfl

/-- `gen_modElim` is REJECTED under core-FX. -/
theorem Generator.gen_modElim_notInCoreFx :
    Generator.gen_modElim.isInCoreFx = false := rfl

/-- `gen_subsume` is REJECTED under core-FX (mode-subsumption is
part of the modal axis). -/
theorem Generator.gen_subsume_notInCoreFx :
    Generator.gen_subsume.isInCoreFx = false := rfl

/-! ## Section 3 — Symmetry: under fxProfile every Generator admits

Contrast: under the default `fxProfile`, the three modal
Generators DO admit (since `supportedGenerator?` is constant
`some _`).  These three theorems exhibit the difference between
the two profiles' admission decisions on the same Generators. -/

/-- Under fxProfile, `gen_modIntro` ADMITS — contrast with
`gen_modIntro_notInCoreFx`.  The two profiles disagree on this
Generator: fxProfile says admit, core-FX says reject. -/
theorem fxProfile_admits_modIntro_but_coreFx_rejects :
    (supportedGenerator? Generator.gen_modIntro).isSome = true ∧
    Generator.gen_modIntro.isInCoreFx = false :=
  ⟨rfl, rfl⟩

/-- Symmetric pair theorem for `gen_modElim`. -/
theorem fxProfile_admits_modElim_but_coreFx_rejects :
    (supportedGenerator? Generator.gen_modElim).isSome = true ∧
    Generator.gen_modElim.isInCoreFx = false :=
  ⟨rfl, rfl⟩

/-- Symmetric pair theorem for `gen_subsume`. -/
theorem fxProfile_admits_subsume_but_coreFx_rejects :
    (supportedGenerator? Generator.gen_subsume).isSome = true ∧
    Generator.gen_subsume.isInCoreFx = false :=
  ⟨rfl, rfl⟩

end FX1Poly.Core
