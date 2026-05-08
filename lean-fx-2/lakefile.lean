import Lake
open Lake DSL

package «lean-fx-2» where
  version := v!"0.1.0-skeleton"
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`pp.unicode.fun, true⟩,
    ⟨`maxHeartbeats, (20000000 : Nat)⟩,
    ⟨`synthInstance.maxHeartbeats, 20000000⟩
  ]

/-! ## Build targets

Two libraries are declared:

* `LeanFX2` (default) — the kernel + algo + reduction + confluence + ... .
  The audit / smoke / sketch namespaces are deliberately excluded so the
  inner-loop `lake build LeanFX2` does NOT pay the per-decl
  `#assert_no_axioms` / `#print axioms` elaboration cost on every iteration.

* `LeanFX2Audit` — the audit engine: `LeanFX2.Tools.*`,
  `LeanFX2.Smoke.*`, and the experimental `LeanFX2.Sketch.*` modules.
  Run `lake build LeanFX2Audit` (or, equivalently,
  `lake build LeanFX2 LeanFX2Audit`) for a full strict-zero-axiom sweep.
  CI invokes the latter; pre-merge gating depends on it.

The two-target split keeps every audit gate, smoke log, and STRICT
harness invocation EXACTLY where they were — only the *triggering*
build target changed.  Inner-loop iteration drops from O(audit closure
× per-build) to O(kernel only); audit fires on demand only.

Glob semantics:

* `.one X` — single module file `X.lean` at the namespace root.
* `.submodules X` — modules under `X/` directory, NOT including a
  hypothetical `X.lean` head.
* `.andSubmodules X` — both the head module `X.lean` AND submodules
  under `X/`.  Requires the head file to exist.

Most kernel subdirs (Foundation, Algo, Reduction, ...) have NO head
file — use `.submodules`.  Subdirs with a head file (Bridge.lean,
FX1.lean, ...) use `.one` for the head plus `.submodules` for the
contents.
-/

@[default_target]
lean_lib LeanFX2 where
  globs := #[
    .one `LeanFX2,
    .submodules `LeanFX2.Foundation,
    .submodules `LeanFX2.Term,
    .submodules `LeanFX2.Reduction,
    .submodules `LeanFX2.Confluence,
    .submodules `LeanFX2.HoTT,
    .submodules `LeanFX2.Cubical,
    .submodules `LeanFX2.Modal,
    .submodules `LeanFX2.Sessions,
    .submodules `LeanFX2.Effects,
    .submodules `LeanFX2.Codata,
    .submodules `LeanFX2.Graded,
    .submodules `LeanFX2.Refine,
    .submodules `LeanFX2.Algo,
    .submodules `LeanFX2.Surface,
    .submodules `LeanFX2.Bridge,
    .submodules `LeanFX2.Conservativity,
    .submodules `LeanFX2.Translation,
    .submodules `LeanFX2.InternalLanguage,
    .submodules `LeanFX2.FX1,
    .submodules `LeanFX2.FX1Bridge,
    .one `LeanFX2.Bridge,
    .one `LeanFX2.FX1,
    .one `LeanFX2.FX1Bridge,
    .one `LeanFX2.Kernel,
    .one `LeanFX2.Pipeline,
    .one `LeanFX2.Rich,
    .one `LeanFX2.Term
  ]

lean_lib LeanFX2Audit where
  globs := #[
    .submodules `LeanFX2.Tools,
    .submodules `LeanFX2.Smoke,
    .submodules `LeanFX2.Sketch
  ]
