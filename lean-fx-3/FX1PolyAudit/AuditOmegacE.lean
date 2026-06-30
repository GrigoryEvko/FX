import FX1PolyAudit.Polygraph.OmegacE.AbsorptionConfluence
import FX1PolyAudit.Polygraph.OmegacE.AbsorptionLocalConfluence
import FX1PolyAudit.Polygraph.OmegacE.AbsorptionReducer
import FX1PolyAudit.Polygraph.OmegacE.AbsorptionSystem
import FX1PolyAudit.Polygraph.OmegacE.Confluence
import FX1PolyAudit.Polygraph.OmegacE.EmptySystem
import FX1PolyAudit.Polygraph.OmegacE.IdempotentConfluence
import FX1PolyAudit.Polygraph.OmegacE.IdempotentReducer
import FX1PolyAudit.Polygraph.OmegacE.IdempotentSystem
import FX1PolyAudit.Polygraph.OmegacE.OmegacEFiniteType
import FX1PolyAudit.Polygraph.OmegacE.ReducerNormalizer
import FX1PolyAudit.Polygraph.OmegacE.Rewrite
import FX1PolyAudit.Polygraph.OmegacE.SortingConfluence
import FX1PolyAudit.Polygraph.OmegacE.SortingReducer
import FX1PolyAudit.Polygraph.OmegacE.SortingSystem
import FX1PolyAudit.Polygraph.OmegacE.SortingTermination
import FX1PolyAudit.Polygraph.OmegacE.TranspositionConfluence
import FX1PolyAudit.Polygraph.OmegacE.TranspositionReducer
import FX1PolyAudit.Polygraph.OmegacE.TranspositionSystem
import FX1PolyAudit.Polygraph.OmegacE.WordFreeMonoid
import FX1PolyAudit.Polygraph.OmegacE.WordFreeMonoidUniversal
import FX1PolyAudit.Polygraph.OmegacE.WordProblem

/-! # FX1PolyAudit.AuditOmegacE — aggregator over the per-kernel-module audit shards

The omega-cE / Makkai word-problem leg, now mirrored one-file-per-kernel-module
under `FX1PolyAudit/Tier0/OmegacE/...` (auto-discovered by the lakefile
`.submodules` glob, elaborating in parallel).  This aggregator re-imports them so
`lake build FX1PolyAudit.AuditOmegacE` still pulls the whole word-problem gate
set. -/
