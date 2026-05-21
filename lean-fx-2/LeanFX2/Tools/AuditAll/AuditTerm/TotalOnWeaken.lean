import LeanFX2.Tools.DependencyAudit
import LeanFX2.Term.StrengtheningImage

/-! # AuditTerm.TotalOnWeaken — weaken-image totality gates. -/

namespace LeanFX2.Tools

-- T1-backed weaken-image totality.  The old per-constructor
-- `isTotalOnWeaken_*` cascade was deleted once the universal
-- renaming-image theorem supplied this surface directly.

#assert_no_axioms LeanFX2.Term.IsTotalOnWeaken
#assert_no_axioms LeanFX2.Term.isTotalOnWeaken_universal
#assert_no_axioms LeanFX2.Term.weaken_image_totality

end LeanFX2.Tools
