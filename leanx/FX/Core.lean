-- leanx — Lean 4 reference interpreter for FX.
--
-- This file is the library entry point.  It re-exports the modules
-- that make up `leanx`; downstream consumers (tests, the `fxi`
-- binary) import `FX` (via `FX.lean`) rather than individual paths.
--
-- The layering mirrors the trust story in SPEC.md §3:
--
--   Util         leaf utilities (errors, pretty-printing)
--   Syntax       lexer, parser, surface AST   (Phase 1, untrusted)
--   Kernel       trusted type theory kernel   (Phase 2+, TRUSTED)
--   Metatheory   preservation / progress / …  (Phase 2+, PROVED)
--   Elab         surface → kernel             (Phase 3+, untrusted)
--   Eval         tree-walking interpreter     (Phase 3+, untrusted)
--   Derived      kernel translations of §3–§26 (Phase 5+, untrusted)
--   Io           print / read_file / …        (Phase 3+, trusted boundary)
--   Smt          Z3 oracle for refinements    (Phase 4+, trusted oracle)
--   Cli          fxi binary dispatch          (Phase 0+, untrusted)
--
-- Only the layers marked "Phase 1" are imported here.  As each phase
-- lands, lift the corresponding import out of the block comment.
--
-- See SPEC.md for the full design.

-- Phase 1 — utilities (leaf dependency).
import FX.Util.Basic
import FX.Util.Pretty

-- Phase 1 — surface syntax (untrusted).  Imported lazily by `fxi`
-- subcommands that need them; re-exported here so downstream code
-- just says `import FX`.
-- NOTE: FX.Syntax.* depend on FX.Util; keeping their import here
-- means a single `import FX` is sufficient for the common case.
-- They are intentionally commented out at the root aggregator until
-- every submodule in FX/Syntax/** compiles green under this phase;
-- the CLI pulls them in directly.

-- Phase 2+ — trusted kernel and its proved metatheory.  Everything
-- else routes through these.
-- import FX.Kernel.Level
-- import FX.Kernel.Grade
-- import FX.Kernel.Term
-- import FX.Kernel.Context
-- import FX.Kernel.Typing
-- import FX.Kernel.Reduction
-- import FX.Kernel.Conversion
-- import FX.Kernel.Subtyping
-- import FX.Kernel.Check
-- import FX.Kernel.Emit
-- import FX.Metatheory.Preservation
-- import FX.Metatheory.Progress

namespace FX

/-- leanx version string.  Bumped per phase milestone.

The format is SemVer with a `-phaseN` suffix while the project is
still pre-1.0.  `fxi version` and `fxi --version` read this; the
daemon protocol (fx_design.md §24) will surface it via `GET /`. -/
def version : String := "0.0.0-phase1"

/-- The current phase.  Informational; surfaced by `fxi self-test`
    so agents can reason about which subcommands to try. -/
def phase : Nat := 1

end FX
