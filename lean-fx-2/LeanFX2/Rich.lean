import LeanFX2.Kernel

-- Layer 5 - HoTT and cubical
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
import LeanFX2.Cubical.Path
import LeanFX2.Cubical.Composition
import LeanFX2.Cubical.Transport
import LeanFX2.Cubical.Glue
import LeanFX2.Cubical.Ua
import LeanFX2.Cubical.PathLemmas
import LeanFX2.Cubical.Bridge

-- Layer 6 - Modal
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

-- Layer 7 - Effects, sessions, codata
import LeanFX2.Effects.Foundation
import LeanFX2.Effects.Handlers
import LeanFX2.Effects.Step
import LeanFX2.Sessions.Foundation
import LeanFX2.Sessions.Duality
import LeanFX2.Sessions.Step
import LeanFX2.Codata.Foundation
import LeanFX2.Codata.Productivity
import LeanFX2.Codata.Step

-- Layer 8 - Graded
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

-- Layer 9 - Refine
import LeanFX2.Refine.Ty
import LeanFX2.Refine.Term
import LeanFX2.Refine.Decidable
import LeanFX2.Refine.SMTCert
import LeanFX2.Refine.SMTRecheck

-- Layer 10 - Algo
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

-- Layer 11 - Surface
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

-- Layer 12 - Pipeline
import LeanFX2.Pipeline

-- Layer 13 - Cross-theory bridges, conservativity, translation
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

/-! # LeanFX2.Rich

Public umbrella for the rich production lean-fx-2 engine.  It imports
`LeanFX2.Kernel` plus the higher theory, graded, algorithmic, surface,
pipeline, and cross-theory layers.  It deliberately excludes smoke tests,
audit tooling, sketches, FX1, explicit host-boundary shims, and the legacy
Lean-kernel scaffold.
-/

namespace LeanFX2

end LeanFX2
