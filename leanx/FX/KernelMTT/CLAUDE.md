# FX.KernelMTT — module-local design notes

Multimodal Dependent Type Theory spine under construction per
`fx_reframing.md`.  **Scaffold status during Phase R0–R4**;
graduates to TRUSTED at the Phase R5 migration
(`fx_reframing.md` §8.7).

## Trust layer during scaffolding

`FX/KernelMTT/**` is currently UNTRUSTED scaffold.  The MTT
kernel runs PARALLEL to `FX/Kernel/**` (the current trusted
kernel) until the Phase R1 acceptance gate (R1.14) closes.
During parallel operation:

  * **No new axioms.**  Any new primitive must be derivable
    from MTT canonicity (Gratzer LICS 2022) or from the mode
    theory's 2-category structure.  An axiom requires an RFC
    per `fx_reframing.md` §9.1.
  * **Zero `sorry`.**  Same discipline as `FX/Kernel/**`.
  * **Not wired into the default fxi dispatch.**  R5.2 flips
    the default; until then, MTT is opt-in via a flag (R1.8).

After R5 migration: `FX/KernelMTT/**` graduates to TRUSTED and
`FX/Kernel/**` deprecates per `fx_reframing.md` §8.7 (legacy
kernel maintained for 12 months post-R5, then removed).

## File catalog

Files in this tree as of R1.1 landing.  A single aggregator
`FX/KernelMTT.lean` (at the parent directory) re-exports the
whole scaffold for downstream `import FX.KernelMTT` consumers;
individual submodules remain importable directly for
downstream files that need only one.

### Landed

  * `Mode.lean` (R0.2) — the four 0-cells (Ghost, Software,
    Hardware, Wire) plus `ModeConfig` and lookup helpers.
    Foundation for every downstream R0/R1 task.
  * `Modality.lean` (R0.3) — 20-constructor endo-modality
    enumeration + per-mode admissibility + 12 pinning
    theorems agreeing with `Mode.lean`'s per-mode modality
    name lists.
  * `Adjunction.lean` (R0.4 + R0.8) — four cross-mode
    adjunction records (ghost⊣erase, synth, serialize⊣parse,
    observe) with R0.8 unit/counit 2-cell fields,
    triangle-endpoint helpers, and 30+ pinning theorems.
  * `TwoCells.lean` (R0.5) — 27 subsumption 2-cells across 11
    modalities + `reachableFrom` fuel-bounded BFS + 21
    pinning theorems.
  * `Collisions.lean` (R0.6) — §6.8 primary rules (9) +
    reductions (3) + `byErrorCode?` / `byGapRef?` lookups
    + 14 pinning theorems.
  * `Coherence.lean` (R0.7 + R0.8) — aggregate mode-theory
    coherence witness (9-conjunct `mode_theory_coherent`)
    over every R0 scaffold artifact.

### Upcoming (forward-looking schedule)

  * `Term.lean` (R1.4) — mode-indexed kernel terms
  * `Typing.lean`, `Reduction.lean`, `Conversion.lean`,
    `Substitution.lean`, `Context.lean` (R1.5–R1.7) — the
    kernel checker parameterized at the FX mode theory
  * `Modality/Later.lean` (R2a), `Modality/Bridge.lean`
    (R2b), HIT / univalence / 2LTT / session corecursion
    modules (R2c–R2f) — the frontier modalities
  * `Port/*` — BiSikkel + smpst-sr-smer ports (R1.2–R1.3,
    R2h) land in a sibling directory tree

## Aggregator import

Use `import FX.KernelMTT` to pull in the entire scaffold at
once (Mode + Modality + Adjunction + TwoCells + Collisions +
Coherence).  The aggregator lives at `FX/KernelMTT.lean` and
also exposes `scaffoldVersion` and `closedRTasks` for agents
inspecting the scaffold's completion state.

## Fixed mode theory per reframe version

Per `fx_reframing.md` §2.4: "The spine's mode theory is fixed
per reframe version."  This means the 4-mode enum and the
18+4+2+0 modality enumeration in `Mode.lean` are STRUCTURAL —
they change only with an RFC and a reframe version bump.
User-defined grade dimensions (§6.6 peripheral) add modality
names at the user scope, OUTSIDE the spine.

The `Mode.*_modality_count` theorems in `Mode.lean` pin the
exact counts so any accidental edit to the modality lists
fails the build.  If you need to change a count, write an RFC
first (per `fx_reframing.md` §9.2).

## No wiring into FX/Core.lean yet

`FX/Core.lean` is NOT updated to re-export `FX.KernelMTT.*`.
Intentional — the R1.14 acceptance gate is the point at which
the MTT scaffold graduates from parallel-UNTRUSTED to the
default dispatch.  Until then, `FX.KernelMTT.*` is accessible
only via explicit `import FX.KernelMTT` (aggregator) or one
of the submodule imports.

The default `fxi check` dispatch stays on the trusted
`FX/Kernel/**` path.  R1.8 adds an opt-in `fxi check --mtt`
flag for parallel-dispatch testing once R1.4–R1.7 populate
enough of the MTT kernel for round-tripping.  R5.2 eventually
flips the default.

This preserves the parallel-kernel boundary: a run of the
conformance suite on default settings can never accidentally
exercise MTT paths, so any divergence between kernels shows
up in explicit `--mtt` comparison runs, not as a silent
regression.
