import LeanFX2.Tools.DependencyAudit
import LeanFX2.Tools.AuditGen
import LeanFX2.Tools.StrictHarness
import LeanFX2
import LeanFX2.FX1.LeanKernel.Name
import LeanFX2.FX1.LeanKernel.Level
import LeanFX2.FX1.LeanKernel.Expr
import LeanFX2.FX1.LeanKernel.Substitution
import LeanFX2.FX1.LeanKernel.Reduction
import LeanFX2.FX1.LeanKernel.Inductive
import LeanFX2.FX1.LeanKernel.HasType
import LeanFX2.FX1.LeanKernel.Check
import LeanFX2.FX1.LeanKernel.Soundness
import LeanFX2.FX1.LeanKernel.Audit
import LeanFX2.FX1
import LeanFX2.FX1Bridge
-- Per-decl axiom audits — 40 sibling files, semantically grouped by namespace.
-- Each file imports the same prelude and is independent of the others, so
-- Lake compiles them in parallel.
import LeanFX2.Tools.AuditAll.AuditBridge
import LeanFX2.Tools.AuditAll.AuditCodata
import LeanFX2.Tools.AuditAll.AuditConfluence
import LeanFX2.Tools.AuditAll.AuditConvCumul
import LeanFX2.Tools.AuditAll.AuditCubical
import LeanFX2.Tools.AuditAll.AuditEffects
import LeanFX2.Tools.AuditAll.AuditFX1Bridge_Bool
import LeanFX2.Tools.AuditAll.AuditFX1Bridge_Encode
import LeanFX2.Tools.AuditAll.AuditFX1Bridge_Nat
import LeanFX2.Tools.AuditAll.AuditFX1Bridge_UnitEncode
import LeanFX2.Tools.AuditAll.AuditFX1Bridge_UnitEnv
import LeanFX2.Tools.AuditAll.AuditFX1Bridge_UnitEquiv
import LeanFX2.Tools.AuditAll.AuditFX1Bridge_UnitId
import LeanFX2.Tools.AuditAll.AuditFX1Bridge_UnitOther
import LeanFX2.Tools.AuditAll.AuditFX1Bridge_UnitType
import LeanFX2.Tools.AuditAll.AuditFX1Bridge_UnitTypeForm
import LeanFX2.Tools.AuditAll.AuditFX1Bridge_UnitValue
import LeanFX2.Tools.AuditAll.AuditFX1Bridge_UnitVar
import LeanFX2.Tools.AuditAll.AuditFX1Bridge_Universe
import LeanFX2.Tools.AuditAll.AuditFX1LeanKernel_Env
import LeanFX2.Tools.AuditAll.AuditFX1LeanKernel_Expr
import LeanFX2.Tools.AuditAll.AuditFX1LeanKernel_Other
import LeanFX2.Tools.AuditAll.AuditFX1_Environment
import LeanFX2.Tools.AuditAll.AuditFX1_Expr
import LeanFX2.Tools.AuditAll.AuditFX1_Other
import LeanFX2.Tools.AuditAll.AuditFX1_Reduction
import LeanFX2.Tools.AuditAll.AuditFX1_Types
import LeanFX2.Tools.AuditAll.AuditFoundation
import LeanFX2.Tools.AuditAll.AuditGraded
import LeanFX2.Tools.AuditAll.AuditHIT_Generic
import LeanFX2.Tools.AuditAll.AuditHIT_Pushout
import LeanFX2.Tools.AuditAll.AuditHIT_Quotient
import LeanFX2.Tools.AuditAll.AuditHIT_S1
import LeanFX2.Tools.AuditAll.AuditHIT_Suspension
import LeanFX2.Tools.AuditAll.AuditHIT_Trunc
import LeanFX2.Tools.AuditAll.AuditMisc_Option
import LeanFX2.Tools.AuditAll.AuditReduction
import LeanFX2.Tools.AuditAll.AuditSessions
import LeanFX2.Tools.AuditAll.AuditTerm
import LeanFX2.Tools.AuditAll.AuditTranslation
-- Heavy budget gates — 17 sibling files, each containing 1-19 commands.
-- Independent siblings; Lake parallelizes.
import LeanFX2.Tools.AuditAll.GatesAxiomAdj
import LeanFX2.Tools.AuditAll.GatesBroad
import LeanFX2.Tools.AuditAll.GatesCore
import LeanFX2.Tools.AuditAll.GatesEffect
import LeanFX2.Tools.AuditAll.GatesExtern
import LeanFX2.Tools.AuditAll.GatesFX1ImportSurface
import LeanFX2.Tools.AuditAll.GatesGenerous
import LeanFX2.Tools.AuditAll.GatesHostBoundary
import LeanFX2.Tools.AuditAll.GatesImportCensus
import LeanFX2.Tools.AuditAll.GatesIndCount
import LeanFX2.Tools.AuditAll.GatesNamespaceSweep
import LeanFX2.Tools.AuditAll.GatesNaming
import LeanFX2.Tools.AuditAll.GatesNumOps
import LeanFX2.Tools.AuditAll.GatesParity
import LeanFX2.Tools.AuditAll.GatesProductionImports
import LeanFX2.Tools.AuditAll.GatesPublicUmbrella
import LeanFX2.Tools.AuditAll.GatesShape
-- End-of-build summary commands — 3 sibling files.  Each does a full
-- LeanFX2 namespace walk; running them in parallel saves ~10-30s vs
-- sequential.  Strictly informational; the per-budget gates above
-- already failed the build if any ratchet rose.
import LeanFX2.Tools.AuditAll.SummarySubnamespace
import LeanFX2.Tools.AuditAll.SummaryAuditReport
import LeanFX2.Tools.AuditAll.SummaryDebtDashboard

/-! # Tools/AuditAll — pure-import umbrella, all work in sibling submodules.

`LeanFX2/Tools/AuditAll/` contains 60 sibling files:

* 40 `Audit*.lean` — `#assert_no_axioms` per-decl checks, semantically
  grouped by namespace (Foundation, Term, Reduction, Confluence,
  HoTT.HIT subdivisions, FX1.* subdivisions, FX1Bridge.* subdivisions).
* 17 `Gates*.lean` — heavy budget gates split by topic (extern, imports,
  parity, broad/cast, axiom-adjacent, universe/Quot/Acc, OfNat/Subtype,
  Mode/Bridge/Sigma, Classical/IO, generous, naming, etc.).
* 3 `Summary*.lean` — end-of-build summary commands (subnamespace counts,
  audit report, debt dashboard).

This umbrella is pure imports.  Lake compiles all 60 siblings in
parallel up to the worker count.  No file in this directory contains
inter-sibling dependencies. -/
