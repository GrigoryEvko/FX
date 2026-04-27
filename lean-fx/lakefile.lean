import Lake
open Lake DSL

/-
lean-fx — ground-up Lean 4 formalisation of FX's type theory.

Hard rules:

  * No `axiom` beyond Lean core (propext, Quot.sound, Classical.choice).
  * No `sorry` anywhere.  Build script greps for it; CI fails on sight.
  * No external dependencies.  No Mathlib, no Std4, no `lean-smt`.
    Everything we need we prove ourselves on top of Lean's prelude.
  * No `decide` on type-theory facts that we can prove constructively.
    `decide` is reserved for finite enumerations (modes, levels<bound).
  * No coupling to elaboration, SMT, codegen, or CLI.  This package
    contains the kernel + its metatheory and nothing else.

Build:
  lake build       -- compile every layer in dependency order
-/

package leanfx where
  leanOptions := #[
    ⟨`linter.unusedVariables, true⟩,
    ⟨`autoImplicit,           false⟩,
    ⟨`relaxedAutoImplicit,    false⟩,
    ⟨`pp.unicode.fun,         true⟩,
    ⟨`maxHeartbeats,          400000⟩
  ]

@[default_target]
lean_lib LeanFX where
  srcDir := "."
  roots  := #[`LeanFX]
  globs  := #[.andSubmodules `LeanFX]
