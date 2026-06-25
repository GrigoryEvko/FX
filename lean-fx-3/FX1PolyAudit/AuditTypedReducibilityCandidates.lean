import FX1PolyAudit.Typed.Metatheory.Reducibility.Candidate.ReducibilityCandidates
import FX1PolyAudit.Typed.Metatheory.Reducibility.Candidate.ReducibilityCandidatesMore
import FX1PolyAudit.Typed.Metatheory.Reducibility.Candidate.ReducibilityCandidatesMore2
import FX1PolyAudit.Typed.Metatheory.Reducibility.Candidate.ReducibilityCandidatesMore3
import FX1PolyAudit.Typed.Metatheory.Reducibility.Candidate.ReducibilityCandidatesMore4
import FX1PolyAudit.Typed.Metatheory.Reducibility.Candidate.ReducibilityCandidatesMore5
import FX1PolyAudit.Typed.Metatheory.Reducibility.Candidate.ReducibilityCandidatesMore6
import FX1PolyAudit.Typed.Metatheory.Reducibility.Candidate.ReducibilityCandidatesMore7

/-! # FX1PolyAudit/AuditTypedReducibilityCandidates — re-export shim

The reducibility-candidate audit gates were sharded into the mirror-tree files under
`FX1PolyAudit.Typed.Metatheory.Reducibility.Candidate.ReducibilityCandidates*` (each under 50
`#assert_no_axioms` evals, elaborating in parallel).  This file re-imports those shards so existing
importers (the `AuditTyped` aggregator) keep resolving the original module name; all gate content and
counts are conserved exactly across the shards. -/
