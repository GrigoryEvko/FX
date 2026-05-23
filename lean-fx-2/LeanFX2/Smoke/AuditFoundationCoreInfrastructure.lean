import LeanFX2.Foundation.RawPartialRename
import LeanFX2.Foundation.RawPartialRename.UnweakenSubstCommute
import LeanFX2.Foundation.RawPartialRename.UnweakenSubstDispatch
import LeanFX2.Foundation.Polygraph.Wellfounded

/-! # Smoke/AuditFoundationCoreInfrastructure

Reviewer-facing `#print axioms` gate for the foundational core
infrastructure declarations under `LeanFX2.Foundation.*` that have
zero-axiom `#assert_no_axioms` gates in
`Tools/AuditAll/AuditFoundation.lean` but lacked any reviewer-
visible smoke parity until now.

Three sub-families:

* **PartialRawRenaming infrastructure** (7) — the partial-renaming
  primitives (`lift`, `dropNewest`, the weakening-lift-compose
  lemmas) consumed by every `partialRename?` / `partialStrengthen?`
  call site.
* **RawTerm strengthening surface** (22) — the raw-layer partial
  renaming + unweaken family, plus `constantPathBody?` pathLam
  recognizers used by the path-η detection machinery.
* **Polygraph cell-extraction helpers** (13) — the `PolyCell`
  source/target/index projections plus the
  `dimensionMeasure_lt` accessibility witnesses used by the
  polygraph well-foundedness story.

Each `#print axioms` entry mirrors a gate in
`Tools/AuditAll/AuditFoundation.lean` (lines 24-92 + 154-165) and
must report "does not depend on any axioms" — strict Layer K
gate per `lean-fx-2/CLAUDE.md`. -/

namespace LeanFX2.Smoke.AuditFoundationCoreInfrastructure

-- PartialRawRenaming primitives.
#print axioms LeanFX2.PartialRawRenaming
#print axioms LeanFX2.PartialRawRenaming.lift
#print axioms LeanFX2.PartialRawRenaming.dropNewest
#print axioms LeanFX2.PartialRawRenaming.dropNewest_weaken
#print axioms LeanFX2.PartialRawRenaming.lift_dropNewest_weaken_lift
#print axioms LeanFX2.PartialRawRenaming.lift_subst_compat
#print axioms LeanFX2.PartialRawRenaming.dropNewest_subst_lift_compat
#print axioms LeanFX2.PartialRawRenaming.lift_rename_some

-- RawTerm partial renaming + unweaken surface.
#print axioms LeanFX2.RawTerm.partialRename?
#print axioms LeanFX2.RawTerm.partialRename?_subst_compat
#print axioms LeanFX2.RawTerm.partialRename?_rename_some
#print axioms LeanFX2.RawTerm.partialRename?_lift_preserves_binder_var
#print axioms LeanFX2.RawTerm.unweaken?
#print axioms LeanFX2.RawTerm.unweaken?_newest_var_none
#print axioms LeanFX2.RawTerm.unweaken?_weaken_var
#print axioms LeanFX2.RawTerm.unweaken?_pathLam_binder_var
#print axioms LeanFX2.RawTerm.unweaken?_pathLam_dropped_outer_var_none
#print axioms LeanFX2.RawTerm.unweaken?_subst_lift_commute
#print axioms LeanFX2.RawTerm.unweaken?_subst_lift_dispatch_some
#print axioms LeanFX2.RawTerm.unweaken?_subst_lift_dispatch_none
#print axioms LeanFX2.RawTerm.partialStrengthen?_eq_partialRename?
#print axioms LeanFX2.RawTerm.strengthen?_weaken
#print axioms LeanFX2.RawTerm.strengthen?_imp_weaken
#print axioms LeanFX2.RawTerm.constantPathBody?
#print axioms LeanFX2.RawTerm.constantPathBody?_unit_none
#print axioms LeanFX2.RawTerm.constantPathBody?_pathLam_weaken
#print axioms LeanFX2.RawTerm.constantPathBody?_pathLam_weaken_var
#print axioms LeanFX2.RawTerm.constantPathBody?_pathLam_interval_var_none
#print axioms LeanFX2.RawTerm.constantPathBody?_pathLam_nested_binder_var
#print axioms LeanFX2.RawTerm.constantPathBody?_pathLam_nested_interval_escape_none

-- Polygraph cell-extraction + accessibility helpers.
#print axioms LeanFX2.Foundation.Polygraph.PolyCell
#print axioms LeanFX2.Foundation.Polygraph.ParallelPair
#print axioms LeanFX2.Foundation.Polygraph.atomVertex
#print axioms LeanFX2.Foundation.Polygraph.arrowSource
#print axioms LeanFX2.Foundation.Polygraph.arrowTarget
#print axioms LeanFX2.Foundation.Polygraph.cellSource
#print axioms LeanFX2.Foundation.Polygraph.cellTarget
#print axioms LeanFX2.Foundation.Polygraph.cellIdx
#print axioms LeanFX2.Foundation.Polygraph.dimensionMeasure
#print axioms LeanFX2.Foundation.Polygraph.cellSource_dimensionMeasure_lt
#print axioms LeanFX2.Foundation.Polygraph.cellTarget_dimensionMeasure_lt
#print axioms LeanFX2.Foundation.Polygraph.arrowSource_dimensionMeasure_lt
#print axioms LeanFX2.Foundation.Polygraph.arrowTarget_dimensionMeasure_lt

end LeanFX2.Smoke.AuditFoundationCoreInfrastructure
