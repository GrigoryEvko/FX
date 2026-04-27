-- FX.KernelMTT — Phase R0-R4 scaffold for the MTT-spine reframe.
--
-- This file is the library aggregator for the MTT kernel tree.
-- Consumers that want the WHOLE mode-theory scaffold at once say
-- `import FX.KernelMTT`; consumers that want just one submodule
-- (Mode, Modality, Adjunction, ...) import it directly.
--
-- **Trust layer.** `FX/KernelMTT/**` is currently UNTRUSTED scaffold
-- per `FX/KernelMTT/CLAUDE.md`.  It runs in PARALLEL to `FX/Kernel/**`
-- (the trusted kernel) until the Phase R1 acceptance gate (R1.14)
-- closes.  The scaffold graduates to TRUSTED at the Phase R5 migration
-- (task R5.2, `fx_reframing.md §8.7`).
--
-- **No wiring into FX/Core.lean yet.**  Deliberate — FX/Core.lean is
-- the project-wide library entry point, and re-exporting KernelMTT
-- from Core would blur the parallel-kernel boundary.  The default
-- `fxi` dispatch stays on `FX/Kernel/**` until R5.2 flips the default;
-- until then, MTT is opt-in via the R1.8 `--mtt` flag.
--
-- **File catalog (as of W2 landing)**:
--
--   Mode.lean        R0.2  — four modes + ModeConfig + morphism lists
--   Modality.lean    R0.3  — 20 modalities + per-modality admissibility
--   Adjunction.lean  R0.4  — four cross-mode adjunction records
--                    R0.8  — + unit/counit 2-cell structure
--   TwoCells.lean    R0.5  — 27 subsumption 2-cells + reachability BFS
--   Collisions.lean  R0.6  — §6.8 primary rules (9) + reductions (3)
--   Coherence.lean   R0.7  — coherence laws + aggregate witness
--                    R0.8  — + triangle-endpoint shape invariants
--   Term.lean        R1.4  — mode-indexed Term inductive
--                    W2    — well-scoped (Term : Nat → Type) +
--                            mutual TermArgs n
--   ModalityOps.lean V1.4  — modality intro/elim smart constructors
--                            + 2-cell coerceCell + eraseCoercions
--   Substitution.lean W3   — typed shift / substAt / shift0 /
--                            β-subst over well-scoped Term
--   Reduction.lean    V1.15 — β / ι / ν / modElim-ι / idJ-ι /
--                            coerceCell-strip + whnf
--   Conversion.lean   V1.5  — definitional equality (convEq)
--                            via whnf + η on Lam (first
--                            installment of V1.5 checker work)
--   Subtyping.lean    V1.5  — T-sub: convEq fast path +
--                            U-cumul + Pi (contra/co/effect) +
--                            Sigma (covariant both) +
--                            forallLevel (covariant body)
--                            (second installment of V1.5)
--
-- V1.5 follow-on chunks (Context.lean, Subtyping.lean,
-- WellTyped relation, infer decidability), V1.6 2-cell
-- subsumption lookup, V1.7+ etc. land under this tree as their
-- tasks close.  See `FX/KernelMTT/CLAUDE.md` for the forward
-- roadmap.

import FX.KernelMTT.Mode
import FX.KernelMTT.Modality
import FX.KernelMTT.Adjunction
import FX.KernelMTT.TwoCells
import FX.KernelMTT.Collisions
import FX.KernelMTT.Coherence
import FX.KernelMTT.Term
import FX.KernelMTT.ModalityOps
import FX.KernelMTT.Substitution
import FX.KernelMTT.Reduction
import FX.KernelMTT.Conversion
import FX.KernelMTT.Subtyping

namespace FX.KernelMTT

/-- Scaffold version tag.  Bumped at every R-task close that changes
    the enumerated data (modes, modalities, adjunctions, 2-cells,
    collisions) or extends the AST with new constructors / scoping
    invariants.  Cross-referenced by `fx_modecat.md §10`'s decision
    ledger. -/
def scaffoldVersion : String := "V1.5-sub"

/-- The R-task ledger this scaffold version includes — one line per
    closed R-task contributing to the current version. -/
def closedRTasks : List String :=
  [ "R0.1 — fx_modecat.md skeleton"
  , "R0.2 — Mode datatype + per-mode configs"
  , "R0.3 — Modality enumeration + admissibility"
  , "R0.4 — four cross-mode adjunction records"
  , "R0.5 — 27 subsumption 2-cells"
  , "R0.6 — §6.8 collision catalog as missing 2-cells"
  , "R0.7 — 2-category coherence laws"
  , "R0.8 — unit/counit 2-cell structure"
  , "R1.1 — tree aggregator + lakefile wiring"
  , "R1.4 / V1.3 — mode-indexed Term inductive"
  , "V1.4 — modality intro/elim primitives"
  , "W2 — well-scoped (Term : Nat → Type) + mutual TermArgs"
  , "W3 — typed shift + substitution"
  , "V1.15 — Reduction.lean (β/ι/ν/modElim-ι/idJ-ι/coerce + whnf)"
  , "V1.5 (first installment) — Conversion.lean (convEq + η)"
  , "V1.5 (second installment) — Subtyping.lean (T-sub)"
  ]

/-- Pin the scaffold version count so a drift between `closedRTasks`
    and the version tag fails `lake build`.  Each task close is ONE
    entry; the count here matches the tag's progress.  Post-
    V1.5-sub has 16 closed tasks (R0.1–R0.8 + R1.1 + R1.4/V1.3 +
    V1.4 + W2 + W3 + V1.15 + V1.5-conv + V1.5-sub). -/
theorem closed_r_task_count : closedRTasks.length = 16 := by decide

end FX.KernelMTT
