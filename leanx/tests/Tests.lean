-- Aggregator for the `Tests` library.  Importing this imports
-- every compile-time-verified test module; `lake build Tests`
-- runs every `example : P := by decide` in the tree.
-- Runtime test suites are aggregated in `Tests.Main` instead.
import Tests.Framework
import Tests.Runner
import Tests.ElabSupport  -- shared AST/test builders
import Tests.FrameworkTests
import Tests.Util.BasicTests
import Tests.Syntax.SpanTests
import Tests.Syntax.TokenTests
import Tests.Syntax.LexerTests
import Tests.Syntax.ParserTests
-- Session decl parsing (task S10):
import Tests.Syntax.SessionParserTests
-- `try EXPR` prefix form (task E-3 parser half):
import Tests.Syntax.TryParserTests
-- `effect NAME ... end effect;` declaration (task E-4 parser half):
import Tests.Syntax.EffectParserTests
-- `handle EXPR ... end handle` expression (task E-5 parser half):
import Tests.Syntax.HandleParserTests
-- TokenStream `manyWithProgress` combinator (task Q51):
import Tests.Syntax.TokenStreamTests
-- Parser accumulating-loop EOF-robustness regression (task Q52):
import Tests.Syntax.ParserRobustnessTests
-- Session decl elaborator coverage (S11 / G2):
import Tests.Elab.SessionElabTests
import Tests.Kernel.LevelTests
import Tests.Kernel.GradeTests
import Tests.Kernel.Grade.UsageTests
import Tests.Kernel.Grade.SecurityTests
import Tests.Kernel.Grade.TrustTests
import Tests.Kernel.Grade.ObservabilityTests
import Tests.Kernel.Grade.FpOrderTests
import Tests.Kernel.Grade.ReentrancyTests
import Tests.Kernel.Grade.MutationTests
import Tests.Kernel.Grade.OverflowTests
import Tests.Kernel.Grade.EffectTests
import Tests.Kernel.Grade.LifetimeTests
import Tests.Kernel.Grade.ProvenanceTests
import Tests.Kernel.Grade.RepresentationTests
import Tests.Kernel.Grade.ClockTests
import Tests.Kernel.Grade.ComplexityTests
import Tests.Kernel.Grade.PrecisionTests
import Tests.Kernel.Grade.SpaceTests
import Tests.Kernel.Grade.SizeTests
import Tests.Kernel.Grade.ProtocolTests
import Tests.Kernel.Grade.VersionTests
-- D2: fixed-width primitive types + char + string registration
import Tests.Kernel.Grade.PrimitiveTests
-- T7/T8: tier-class instance resolution + tier-generic theorems
import Tests.Kernel.Grade.TierTests
-- F5: axiom walker (for fxi show-axioms transitive closure)
import Tests.Kernel.AxiomWalkerTests
import Tests.Metatheory.UnsoundnessCorpusTests
-- Phase 2 kernel pipeline:
import Tests.Kernel.SubstitutionTests
import Tests.Kernel.ReductionTests
import Tests.Kernel.ConversionTests
import Tests.Kernel.ContextTests
import Tests.Kernel.TypingTests
-- Coind typing rules — Coind-form / Coind-intro / Coind-elim (task S6):
import Tests.Kernel.CoindTypingTests
import Tests.Kernel.IdTests
import Tests.Kernel.QuotTests
import Tests.Kernel.EtaTests
import Tests.Kernel.SubtypingTests
import Tests.Kernel.UniversePolyTests
import Tests.Kernel.LinearityTests
-- Phase 2.1 elaboration:
import Tests.Elab.ScopeTests
import Tests.Elab.ElaborateTests
-- Q53 surface→kernel grade mapping regression pin:
import Tests.Elab.ModeToGradeTests
-- Q53 end-to-end: ref vs linear parameter rejection pair:
import Tests.Elab.RefGradeEndToEndTests
-- Q54 end-to-end: @[copy] attribute rejection pair:
import Tests.Elab.CopyGradeEndToEndTests
-- Q55: @[copy] transitive soundness check:
import Tests.Elab.CopySoundnessTests
-- Q57: kernel-side Term.prettyCompact for T002 errors:
import Tests.Kernel.PrettyCompactTests
-- Phase 2.2 inductive families (task A1):
import Tests.Kernel.InductiveTests
-- Phase 2.2 coinductive families (task A2):
import Tests.Kernel.CoinductiveTests
-- Stream A cross-module integration coverage (task G1):
import Tests.Kernel.IntegrationTests
-- Phase 2.2 global environment (task A11):
import Tests.Kernel.EnvTests
import Tests.Elab.CrossDeclTests
-- Phase 2.2 prelude surface access (tasks D1 + D2):
import Tests.Elab.PreludeTests
-- Phase 2.2 if/else elaboration (task B6):
import Tests.Elab.IfExprTests
-- Phase 2.2 for/while loop desugaring (task B10):
import Tests.Elab.LoopTests
-- Phase 2.2 match elaboration (task B7):
import Tests.Elab.MatchExprTests
-- Per-construct surface-sugar coverage (Q64 carve-out of G2):
--   §4.2 pipe + dot-shorthand, §2.6 logical not/and/or.
import Tests.Elab.SurfaceSugarTests
-- Phase 2.2 named argument routing (task B12):
import Tests.Elab.NamedArgsTests
-- Multi-feature integration tests (conformance-style):
import Tests.Elab.ConformanceTests
-- Phase 2.2 user ADT declarations (task B9):
import Tests.Elab.AdtTests
-- Phase 2.2 type parameters (task B2):
import Tests.Elab.TypeParamsTests
-- Phase 2.2 self-recursion + forward refs via Term.const:
import Tests.Elab.RecursionTests
-- Phase 2.2 evaluator (Stream G3):
import Tests.Eval.InterpTests
-- Advanced eval coverage — isCanonical / globalEnv / applyValue (G3):
import Tests.Eval.InterpAdvancedTests
-- Phase 7+ CodeGen IR stubs (task H1):
import Tests.CodeGen.IRStubsTests
-- Phase 7+ CodeGen per-arch FXAsm stubs (task H2):
import Tests.CodeGen.FXAsmStubsTests
-- MTT reframe scaffold (task R0.2): four modes + per-mode config.
-- Scaffold status — graduates to TRUSTED at Phase R5 migration.
import Tests.KernelMTT.ModeTests
-- MTT reframe scaffold (task R0.3): 20 modalities with
-- per-mode admissibility (18 Software + 4 Hardware overlap + 2 Wire).
import Tests.KernelMTT.ModalityTests
-- MTT reframe scaffold (task R0.4): four cross-mode adjunction records
-- per fx_reframing.md §3.5 (ghost⊣erase, synth, serialize⊣parse, observe).
import Tests.KernelMTT.AdjunctionTests
-- MTT reframe scaffold (task R0.5): 27 subsumption 2-cells across
-- 11 modalities per fx_reframing.md §3.6.1 / fx_design.md §6.2-§6.3.
import Tests.KernelMTT.TwoCellsTests
-- MTT reframe scaffold (task R0.6): §6.8 collision catalog —
-- 9 primary rules + 3 reductions, encoded as "missing 2-cells".
import Tests.KernelMTT.CollisionsTests
-- MTT reframe scaffold (task R0.7): 2-category coherence laws —
-- reflexivity/transitivity of subsumption 2-cells, adjunction
-- cross-mode invariants, aggregate `mode_theory_coherent` witness.
import Tests.KernelMTT.CoherenceTests
-- MTT reframe scaffold (task R1.1): scaffold-version + closed-task
-- ledger + single-import aggregator reachability pin.
import Tests.KernelMTT.AggregatorTests
-- Session translation (task S9): SessionType → CoindSpec list with
-- loop/continue resolution + malformed-input error recording.
import Tests.Derived.SessionTranslateTests
-- Session dual-pair translation (task S12): primary + dual CoindSpecs
-- emitted together for `new_channel<S>()` to resolve both endpoints.
import Tests.Derived.SessionDualPairTests
-- Session ν reduction bridge (task S7): translated specs drive
-- kernel ν reduction correctly on concrete unfold terms.
import Tests.Derived.SessionReductionTests
-- SMT-LIB2 encoder runtime tests (task V8.1 / E1):
import Tests.Smt.EncodeTests
-- KernelMTT mode-indexed Term inductive (task V1.3 / R1.4).
import Tests.KernelMTT.TermTests
-- KernelMTT typed shift + substitution (task W3).
import Tests.KernelMTT.SubstitutionTests
-- KernelMTT reduction over well-scoped Term (task V1.15).
import Tests.KernelMTT.ReductionTests
-- KernelMTT convertibility / definitional equality (V1.5 first
-- installment).
import Tests.KernelMTT.ConversionTests
-- KernelMTT subtyping / T-sub (V1.5 second installment).
import Tests.KernelMTT.SubtypingTests
