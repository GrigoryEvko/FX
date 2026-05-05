-- Layer 0 — Foundation
import LeanFX2.Foundation.Mode
import LeanFX2.Foundation.RawTerm
import LeanFX2.Foundation.RawSubst
import LeanFX2.Foundation.RawPartialRename
import LeanFX2.Foundation.Ty
import LeanFX2.Foundation.Subst
import LeanFX2.Foundation.SubstActsOnTy
import LeanFX2.Foundation.TyAct
import LeanFX2.Foundation.TyActBridge
import LeanFX2.Foundation.Context
import LeanFX2.Foundation.Universe
import LeanFX2.Foundation.RenameIdentity

-- Layer 1 — Term
import LeanFX2.Term
import LeanFX2.Term.Rename
import LeanFX2.Term.Subst
import LeanFX2.Term.Act
import LeanFX2.Term.ToRaw
import LeanFX2.Term.Pointwise
import LeanFX2.Term.HEqCongr
import LeanFX2.Term.Bridge
import LeanFX2.Term.ProofIrrel
import LeanFX2.Term.Inversion

-- Layer 2 — Reduction
import LeanFX2.Reduction.Step
import LeanFX2.Reduction.StepStar
import LeanFX2.Reduction.Conv
import LeanFX2.Reduction.ConvBridge
import LeanFX2.Reduction.ConvCanonical
import LeanFX2.Reduction.ParRed
import LeanFX2.Reduction.RawPar
import LeanFX2.Reduction.RawParInversion
import LeanFX2.Reduction.RawParRename
import LeanFX2.Reduction.RawParCompatible
import LeanFX2.Reduction.ParStar
import LeanFX2.Reduction.StepStarToPar
import LeanFX2.Reduction.Compat
import LeanFX2.Reduction.Cumul
import LeanFX2.Reduction.ConvCumulHomo
import LeanFX2.Reduction.CumulCastElim
import LeanFX2.Reduction.CumulBenton
import LeanFX2.Reduction.CumulAllais
import LeanFX2.Reduction.CumulPairedEnv
import LeanFX2.Reduction.CumulSubstCompat
import LeanFX2.Reduction.CumulPattern23Bridge

-- Layer 3 — Reduction-facing metatheory and typed/raw bridge
import LeanFX2.Term.SubjectReduction
import LeanFX2.Term.SubjectReductionUniverse
import LeanFX2.Bridge

-- Layer 4 — Confluence
import LeanFX2.Confluence.Cd
import LeanFX2.Confluence.CdLemma
import LeanFX2.Confluence.Diamond
import LeanFX2.Confluence.ChurchRosser
import LeanFX2.Confluence.CanonicalForm
import LeanFX2.Confluence.RawCd
import LeanFX2.Confluence.RawCdDominates
import LeanFX2.Confluence.RawCdLemma
import LeanFX2.Confluence.RawDiamond
import LeanFX2.Confluence.RawParStarCong
import LeanFX2.Confluence.ParStarBridge
import LeanFX2.Confluence.ConvBridge

-- Layer 5 — HoTT
import LeanFX2.HoTT.OEq
import LeanFX2.HoTT.Identity
import LeanFX2.HoTT.J
import LeanFX2.HoTT.Path.Composition
import LeanFX2.HoTT.Path.Inverse
import LeanFX2.HoTT.Path.Groupoid
import LeanFX2.HoTT.Transport
import LeanFX2.HoTT.Equivalence
import LeanFX2.HoTT.NTypes
import LeanFX2.HoTT.Univalence
import LeanFX2.HoTT.Funext
import LeanFX2.HoTT.UnivalenceFull
import LeanFX2.HoTT.FunextFull
import LeanFX2.HoTT.UnivalenceTransport
import LeanFX2.HoTT.Observational
import LeanFX2.HoTT.HIT.Spec
import LeanFX2.HoTT.HIT.Setoid
import LeanFX2.HoTT.HIT.Eliminator
import LeanFX2.HoTT.HIT.Examples
import LeanFX2.HoTT.HIT.Quot
import LeanFX2.HoTT.HIT.PropTrunc
import LeanFX2.HoTT.HIT.SetTrunc
import LeanFX2.HoTT.HIT.S1
import LeanFX2.HoTT.HIT.Suspension
import LeanFX2.HoTT.HIT.Pushout
import LeanFX2.HoTT.HIT.Coequalizer

-- Cubical scaffold
import LeanFX2.Cubical.Path
import LeanFX2.Cubical.Composition
import LeanFX2.Cubical.Transport
import LeanFX2.Cubical.Glue
import LeanFX2.Cubical.Ua
import LeanFX2.Cubical.PathLemmas
import LeanFX2.Cubical.Bridge

-- Layer 6 — Modal
import LeanFX2.Modal.Foundation
import LeanFX2.Modal.Later
import LeanFX2.Modal.Clock
import LeanFX2.Modal.Bridge
import LeanFX2.Modal.Cap
import LeanFX2.Modal.Ghost
import LeanFX2.Modal.«2LTT»
import LeanFX2.Modal.TwoLevel
import LeanFX2.Modal.BoxPath
import LeanFX2.Modal.Cohesive
import LeanFX2.Modal.Adjunction

-- Layer 7 — Effects, sessions, codata
import LeanFX2.Effects.Foundation
import LeanFX2.Effects.Handlers
import LeanFX2.Effects.Step
import LeanFX2.Sessions.Foundation
import LeanFX2.Sessions.Duality
import LeanFX2.Sessions.Step
import LeanFX2.Codata.Foundation
import LeanFX2.Codata.Productivity
import LeanFX2.Codata.Step

-- Layer 8 — Graded
import LeanFX2.Graded.Semiring
import LeanFX2.Graded.GradeVector
import LeanFX2.Graded.Ctx
import LeanFX2.Graded.Rules
import LeanFX2.Graded.Term
import LeanFX2.Graded.Instances.Usage
import LeanFX2.Graded.AtkeyAttack
import LeanFX2.Graded.Instances.Effect
import LeanFX2.Graded.Instances.Security
import LeanFX2.Graded.Instances.Observability
import LeanFX2.Graded.Instances.Reentrancy
import LeanFX2.Graded.Instances.FPOrder
import LeanFX2.Graded.Instances.Mutation
import LeanFX2.Graded.Instances.NatResource
import LeanFX2.Graded.Instances.Lifetime
import LeanFX2.Graded.Instances.Provenance
import LeanFX2.Graded.Instances.Trust
import LeanFX2.Graded.Instances.Representation
import LeanFX2.Graded.Instances.ClockDomain
import LeanFX2.Graded.Instances.Complexity
import LeanFX2.Graded.Instances.Precision
import LeanFX2.Graded.Instances.Space
import LeanFX2.Graded.Instances.Overflow
import LeanFX2.Graded.Instances.Size
import LeanFX2.Graded.Instances.Version
import LeanFX2.Graded.Dimensions21

-- Layer 9 — Refine
import LeanFX2.Refine.Ty
import LeanFX2.Refine.Term
import LeanFX2.Refine.Decidable
import LeanFX2.Refine.SMTCert
import LeanFX2.Refine.SMTRecheck

-- Layer 10 — Algo
import LeanFX2.Algo.RawWHNF
import LeanFX2.Algo.RawWHNFCorrect
import LeanFX2.Algo.WHNF
import LeanFX2.Algo.DecConv
import LeanFX2.Algo.Infer
import LeanFX2.Algo.Check
import LeanFX2.Algo.Synth
import LeanFX2.Algo.Eval
import LeanFX2.Algo.Soundness
import LeanFX2.Algo.Completeness

-- Layer 11 — Surface
import LeanFX2.Surface.Token
import LeanFX2.Surface.Lex
import LeanFX2.Surface.AST
import LeanFX2.Surface.SchemaAudit
import LeanFX2.Surface.StdNames
import LeanFX2.Surface.KernelBridge
import LeanFX2.Surface.KernelBridgeReduction
import LeanFX2.Surface.KernelEnv
import LeanFX2.Surface.KernelEnvCorrespondence
import LeanFX2.Surface.Parse
import LeanFX2.Surface.Print
import LeanFX2.Surface.Roundtrip
import LeanFX2.Surface.Elab
import LeanFX2.Surface.ElabSoundness
import LeanFX2.Surface.ElabCompleteness

-- Layer 12 — Pipeline
import LeanFX2.Pipeline

-- Layer 13 — Cross-theory bridges, conservativity, translation
import LeanFX2.Bridge.PathToId
import LeanFX2.Bridge.IdToPath
import LeanFX2.Bridge.PathIdInverse
import LeanFX2.Bridge.PathIdMeta
import LeanFX2.Bridge.IdEqType
import LeanFX2.Bridge.PathEqType
import LeanFX2.Bridge.BoxObservational
import LeanFX2.Bridge.BoxCubical
import LeanFX2.Conservativity.HOTTOverMLTT
import LeanFX2.Conservativity.CubicalOverHOTT
import LeanFX2.Conservativity.ModalOverObservational
import LeanFX2.Translation.CubicalToObservational
import LeanFX2.Translation.ObservationalToCubical
import LeanFX2.Translation.Inverse
import LeanFX2.InternalLanguage.Coherence

-- FX1 minimal trust spine
import LeanFX2.FX1.Core

/-! # LeanFX2 — umbrella import.

Single-import gateway to the production lean-fx-2 engine.  Importing
this deliberately excludes smoke tests, audit tooling, sketches, and
the legacy `LeanFX2.Lean.Kernel` scaffold.  Lake still builds those
modules via `.andSubmodules`; they are not part of the public kernel
surface or trusted-root dependency story.

## Layered architecture (each depends only on layers below)

| Layer | Scope                                            |
| ----- | ------------------------------------------------ |
|  0    | Foundation: Mode, RawTerm, RawSubst, Ty, Subst, Context |
|  1    | Term core: raw-aware typed Term inductive        |
|  2    | Reduction: Step, StepStar, Conv (∃-StepStar), ParRed, RawPar, Compat |
|  3    | Reduction-facing Term metatheory + typed↔raw bridge |
|  4    | Confluence: Tait-Martin-Löf chain (Cd, Diamond, Church-Rosser) |
|  5    | HoTT: Identity, J, Path, Transport, Equivalence, NTypes, HIT |
|  6    | Modal: MTT (modal foundation, Later, Bridge, Cap, Ghost, 2LTT) |
|  7    | Effects, sessions, codata                        |
|  8    | Graded: semiring framework + dimension instances |
|  9    | Refine: refinement types + decidable + SMT cert  |
| 10    | Algo: WHNF, decConv, infer, check, eval, soundness/completeness |
| 11    | Surface: lex, parse, print, elab, roundtrip      |
| 12    | Pipeline: end-to-end compile                     |
| 13    | Cross-theory bridges, conservativity, translation |
| 14    | FX1: minimal lambda-Pi trust spine, dependency-isolated by harness |
| 15    | Audit/tooling modules: built by Lake, not imported by this umbrella |

See `ARCHITECTURE.md` for the dependency DAG and per-layer file list.
See `ROADMAP.md` for the phasing from skeleton to full engine.
See `WORKING_RULES.md` for kernel-discipline rules.
See `AXIOMS.md` for trust-budget policy. -/

namespace LeanFX2

end LeanFX2
