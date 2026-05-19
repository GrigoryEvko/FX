import LeanFX2.Tools.AuditAll.AuditTerm.BaseAndPoly
import LeanFX2.Tools.AuditAll.AuditTerm.HEqAndWeakenInverse
import LeanFX2.Tools.AuditAll.AuditTerm.PartialStrengthenApi
import LeanFX2.Tools.AuditAll.AuditTerm.StrengtheningSoundness
import LeanFX2.Tools.AuditAll.AuditTerm.StrengtheningImage
import LeanFX2.Tools.AuditAll.AuditTerm.TotalOnWeaken
import LeanFX2.Tools.AuditAll.AuditTerm.AggregatorTotal
import LeanFX2.Tools.AuditAll.AuditTerm.RenameEquations

/-! # AuditTerm — umbrella for Term-family per-declaration axiom gates.

The audit leaves under `Tools/AuditAll/AuditTerm/` are split by theorem
family so Lake can cache and rebuild independent audit slices instead of
re-elaborating the full Term audit surface for every local change. -/
