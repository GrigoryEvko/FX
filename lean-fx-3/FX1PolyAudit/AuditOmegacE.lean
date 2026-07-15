import FX1PolyAudit.Polygraph.Rewriting.WordSystems.AbsorptionConfluence
import FX1PolyAudit.Polygraph.Rewriting.WordSystems.AbsorptionLocalConfluence
import FX1PolyAudit.Polygraph.Rewriting.WordSystems.AbsorptionReducer
import FX1PolyAudit.Polygraph.Rewriting.WordSystems.AbsorptionSystem
import FX1PolyAudit.Polygraph.Rewriting.WordSystems.Confluence
import FX1PolyAudit.Polygraph.Rewriting.WordSystems.EmptySystem
import FX1PolyAudit.Polygraph.Rewriting.WordSystems.IdempotentConfluence
import FX1PolyAudit.Polygraph.Rewriting.WordSystems.IdempotentReducer
import FX1PolyAudit.Polygraph.Rewriting.WordSystems.IdempotentSystem
import FX1PolyAudit.Polygraph.Rewriting.WordSystems.OmegacEFiniteType
import FX1PolyAudit.Polygraph.Rewriting.WordSystems.ReducerNormalizer
import FX1PolyAudit.Polygraph.Rewriting.WordSystems.Rewrite
import FX1PolyAudit.Polygraph.Rewriting.WordSystems.SortingConfluence
import FX1PolyAudit.Polygraph.Rewriting.WordSystems.SortingReducer
import FX1PolyAudit.Polygraph.Rewriting.WordSystems.SortingSystem
import FX1PolyAudit.Polygraph.Rewriting.WordSystems.SortingTermination
import FX1PolyAudit.Polygraph.Rewriting.WordSystems.TranspositionConfluence
import FX1PolyAudit.Polygraph.Rewriting.WordSystems.TranspositionReducer
import FX1PolyAudit.Polygraph.Rewriting.WordSystems.TranspositionSystem
import FX1PolyAudit.Polygraph.Rewriting.WordSystems.WordFreeMonoid
import FX1PolyAudit.Polygraph.Rewriting.WordSystems.WordFreeMonoidUniversal
import FX1PolyAudit.Polygraph.Rewriting.WordSystems.WordProblem

/-! # FX1PolyAudit.AuditOmegacE — aggregator over the per-kernel-module audit shards

The omega-cE / Makkai word-problem leg, now mirrored one-file-per-kernel-module
under `FX1PolyAudit/Axis/OmegacE/...` (auto-discovered by the lakefile
`.submodules` glob, elaborating in parallel).  This aggregator re-imports them so
`lake build FX1PolyAudit.AuditOmegacE` still pulls the whole word-problem gate
set. -/
