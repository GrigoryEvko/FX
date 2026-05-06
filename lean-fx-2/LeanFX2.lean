import LeanFX2.Rich

/-! # LeanFX2 - compatibility umbrella.

Single-import gateway to the rich production lean-fx-2 engine.  This module
now delegates to `LeanFX2.Rich`, so users can choose narrower public surfaces:

* `LeanFX2.Kernel` for foundation, terms, reduction, bridges, and confluence.
* `LeanFX2.Rich` for the full rich production engine.
* `LeanFX2.FX1` for the separate minimal trusted-root spine.

Importing this deliberately excludes smoke tests, audit tooling, sketches,
explicit host-boundary shims, and FX1.  Lake still builds those modules via
`.andSubmodules`; they are not part of this compatibility import surface.

## Layered architecture

| Layer | Scope                                            |
| ----- | ------------------------------------------------ |
|  0    | Foundation: Mode, RawTerm, RawSubst, Ty, Subst, Context |
|  1    | Term core: raw-aware typed Term inductive        |
|  2    | Reduction: Step, StepStar, Conv, ParRed, RawPar, Compat |
|  3    | Reduction-facing Term metatheory + typed/raw bridge |
|  4    | Confluence: Cd, Diamond, Church-Rosser           |
|  5    | HoTT and cubical                                 |
|  6    | Modal                                            |
|  7    | Effects, sessions, codata                        |
|  8    | Graded: semiring framework + dimension instances |
|  9    | Refine: refinement types + decidable + SMT cert  |
| 10    | Algo: WHNF, decConv, infer, check, eval          |
| 11    | Surface: lex, parse, print, elab, roundtrip      |
| 12    | Pipeline: end-to-end compile                     |
| 13    | Cross-theory bridges, conservativity, translation |
| 14    | Audit/tooling and FX1 modules: built by Lake, not imported by this umbrella |

See `ARCHITECTURE.md` for the dependency DAG and per-layer file list.
See `ROADMAP.md` for the phasing from skeleton to full engine.
See `WORKING_RULES.md` for kernel-discipline rules.
See `AXIOMS.md` for trust-budget policy.
-/

namespace LeanFX2

end LeanFX2
