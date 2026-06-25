import FX1PolyAudit.Tier0.OmegacE.AbsorptionConfluence
import FX1PolyAudit.Tier0.OmegacE.AbsorptionLocalConfluence
import FX1PolyAudit.Tier0.OmegacE.AbsorptionReducer
import FX1PolyAudit.Tier0.OmegacE.AbsorptionSystem
import FX1PolyAudit.Tier0.OmegacE.Confluence
import FX1PolyAudit.Tier0.OmegacE.EmptySystem
import FX1PolyAudit.Tier0.OmegacE.IdempotentConfluence
import FX1PolyAudit.Tier0.OmegacE.IdempotentReducer
import FX1PolyAudit.Tier0.OmegacE.IdempotentSystem
import FX1PolyAudit.Tier0.OmegacE.OmegacEFiniteType
import FX1PolyAudit.Tier0.OmegacE.ReducerNormalizer
import FX1PolyAudit.Tier0.OmegacE.Rewrite
import FX1PolyAudit.Tier0.OmegacE.SortingConfluence
import FX1PolyAudit.Tier0.OmegacE.SortingReducer
import FX1PolyAudit.Tier0.OmegacE.SortingSystem
import FX1PolyAudit.Tier0.OmegacE.SortingTermination
import FX1PolyAudit.Tier0.OmegacE.TranspositionConfluence
import FX1PolyAudit.Tier0.OmegacE.TranspositionReducer
import FX1PolyAudit.Tier0.OmegacE.TranspositionSystem
import FX1PolyAudit.Tier0.OmegacE.WordFreeMonoid
import FX1PolyAudit.Tier0.OmegacE.WordFreeMonoidUniversal
import FX1PolyAudit.Tier0.OmegacE.WordProblem

/-! # FX1PolyAudit.AuditOmegacE — aggregator over the per-kernel-module audit shards

The omega-cE / Makkai word-problem leg, now mirrored one-file-per-kernel-module
under `FX1PolyAudit/Tier0/OmegacE/...` (auto-discovered by the lakefile
`.submodules` glob, elaborating in parallel).  This aggregator re-imports them so
`lake build FX1PolyAudit.AuditOmegacE` still pulls the whole word-problem gate
set. -/
