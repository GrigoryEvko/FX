/-! # LeanFX2 — umbrella import.

Single-import gateway to the entire lean-fx-2 engine.  Importing
this pulls in all 13 layers from foundation through tools.

## Layered architecture (each depends only on layers below)

| Layer | Scope                                            |
| ----- | ------------------------------------------------ |
|  0    | Foundation: Mode, RawTerm, RawSubst, Ty, Subst, Context |
|  1    | Term: raw-aware typed Term inductive             |
|  2    | Reduction: Step, StepStar, Conv (∃-StepStar), ParRed, RawPar, Compat |
|  3    | Confluence: Tait-Martin-Löf chain (Cd, Diamond, Church-Rosser) |
|  4    | Bridge: typed↔raw correspondence (rfl-driven)    |
|  5    | HoTT: Identity, J, Path, Transport, Equivalence, NTypes, HIT |
|  6    | Modal: MTT (modal foundation, Later, Bridge, Cap, Ghost, 2LTT) |
|  7    | Graded: semiring framework + dimension instances |
|  8    | Refine: refinement types + decidable + SMT cert  |
|  9    | Algo: WHNF, decConv, infer, check, eval, soundness/completeness |
| 10    | Surface: lex, parse, print, elab, roundtrip      |
| 11    | Pipeline: end-to-end compile                     |
| 12    | Tools: AuditAll, AuditGen, tactic helpers        |

See `ARCHITECTURE.md` for the dependency DAG and per-layer file list.
See `ROADMAP.md` for the phasing from skeleton to full engine.
See `WORKING_RULES.md` for kernel-discipline rules.
See `AXIOMS.md` for trust-budget policy. -/

-- Layer 0 — Foundation
import LeanFX2.Foundation.Mode
import LeanFX2.Foundation.RawTerm
import LeanFX2.Foundation.RawSubst
import LeanFX2.Foundation.Ty
import LeanFX2.Foundation.Subst
import LeanFX2.Foundation.Context
import LeanFX2.Foundation.Universe
import LeanFX2.Foundation.RenameIdentity

-- Layer 1 — Term
import LeanFX2.Term
import LeanFX2.Term.Rename
import LeanFX2.Term.Subst
import LeanFX2.Term.ToRaw
import LeanFX2.Term.Pointwise
import LeanFX2.Term.HEqCongr
import LeanFX2.Term.Bridge
import LeanFX2.Term.ProofIrrel

-- Layer 2 — Reduction
import LeanFX2.Reduction.Step
import LeanFX2.Reduction.StepStar
import LeanFX2.Reduction.Conv
import LeanFX2.Reduction.ParRed
import LeanFX2.Reduction.RawPar
import LeanFX2.Reduction.RawParInversion
import LeanFX2.Reduction.RawParRename
import LeanFX2.Reduction.RawParCompatible
import LeanFX2.Reduction.Compat
import LeanFX2.Reduction.Cumul

-- Layer 3 — Confluence
import LeanFX2.Confluence.Cd
import LeanFX2.Confluence.CdLemma
import LeanFX2.Confluence.Diamond
import LeanFX2.Confluence.ChurchRosser
import LeanFX2.Confluence.CanonicalForm
import LeanFX2.Confluence.RawCd
import LeanFX2.Confluence.RawCdDominates
import LeanFX2.Confluence.RawCdLemma

-- Layer 4 — Bridge
import LeanFX2.Bridge

-- Layer 5 — HoTT
import LeanFX2.HoTT.Identity
import LeanFX2.HoTT.J
import LeanFX2.HoTT.Path.Composition
import LeanFX2.HoTT.Path.Inverse
import LeanFX2.HoTT.Path.Groupoid
import LeanFX2.HoTT.Transport
import LeanFX2.HoTT.Equivalence
import LeanFX2.HoTT.NTypes
import LeanFX2.HoTT.Univalence
import LeanFX2.HoTT.HIT.Spec
import LeanFX2.HoTT.HIT.Setoid
import LeanFX2.HoTT.HIT.Eliminator
import LeanFX2.HoTT.HIT.Examples

-- Layer 6 — Modal
import LeanFX2.Modal.Foundation
import LeanFX2.Modal.Later
import LeanFX2.Modal.Clock
import LeanFX2.Modal.Bridge
import LeanFX2.Modal.Cap
import LeanFX2.Modal.Ghost
import LeanFX2.Modal.«2LTT»

-- Layer 7 — Graded
import LeanFX2.Graded.Semiring
import LeanFX2.Graded.GradeVector
import LeanFX2.Graded.Ctx
import LeanFX2.Graded.Rules
import LeanFX2.Graded.Instances.Usage
import LeanFX2.Graded.Instances.Effect
import LeanFX2.Graded.Instances.Security

-- Layer 8 — Refine
import LeanFX2.Refine.Ty
import LeanFX2.Refine.Term
import LeanFX2.Refine.Decidable
import LeanFX2.Refine.SMTCert
import LeanFX2.Refine.SMTRecheck

-- Layer 9 — Algo
import LeanFX2.Algo.WHNF
import LeanFX2.Algo.DecConv
import LeanFX2.Algo.Infer
import LeanFX2.Algo.Check
import LeanFX2.Algo.Synth
import LeanFX2.Algo.Eval
import LeanFX2.Algo.Soundness
import LeanFX2.Algo.Completeness

-- Layer 10 — Surface
import LeanFX2.Surface.Token
import LeanFX2.Surface.Lex
import LeanFX2.Surface.AST
import LeanFX2.Surface.Parse
import LeanFX2.Surface.Print
import LeanFX2.Surface.Roundtrip
import LeanFX2.Surface.Elab
import LeanFX2.Surface.ElabSoundness
import LeanFX2.Surface.ElabCompleteness

-- Layer 11 — Pipeline
import LeanFX2.Pipeline

-- Layer 12 — Tools
import LeanFX2.Tools.DependencyAudit
import LeanFX2.Tools.AuditAll
import LeanFX2.Tools.AuditGen
import LeanFX2.Tools.Tactics.Cast
import LeanFX2.Tools.Tactics.HEq
import LeanFX2.Tools.Tactics.SimpStrip

-- Sketch (proof-of-concept)
import LeanFX2.Sketch.Wave9

-- Smoke (per-layer concrete examples)
import LeanFX2.Smoke.Foundation
import LeanFX2.Smoke.Term
import LeanFX2.Smoke.Reduction
import LeanFX2.Smoke.Confluence
import LeanFX2.Smoke.Bridge
import LeanFX2.Smoke.HoTT
import LeanFX2.Smoke.Modal
import LeanFX2.Smoke.Graded
import LeanFX2.Smoke.AuditPhase5Bridge
import LeanFX2.Smoke.AuditPhase6ARawCd
import LeanFX2.Smoke.AuditPhase6BInversion
import LeanFX2.Smoke.AuditPhase6BCdDominates
import LeanFX2.Smoke.AuditPhase6BCompatible
import LeanFX2.Smoke.AuditPhase6BCdLemma

namespace LeanFX2

end LeanFX2
