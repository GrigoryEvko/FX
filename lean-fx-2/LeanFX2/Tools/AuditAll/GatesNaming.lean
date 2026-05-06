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

namespace LeanFX2.Tools


/-! ## Gates: naming+postulate+headline (extracted from AuditAll lines 471-492). -/

-- Naming discipline gate.  Bans non-ASCII identifiers and short
-- identifiers (< 4 chars) outside the documented whitelist.  Catches
-- regressions like `def f (x) := ...` or pasted Greek-letter names
-- that violate CLAUDE.md naming rules.
#assert_namespace_naming LeanFX2

-- Hypothesis-as-postulate detector.  No theorem signature in the
-- production namespace may take Univalence / funext / their het
-- variants as a hypothesis (CLAUDE.md "Forbidden reasoning patterns":
-- shipping a theorem conditionally on an unprovable hypothesis is
-- semantically identical to adding an axiom).
#assert_no_postulate_hypothesis LeanFX2

-- Headline refl-fragment budget.  The current `Univalence` / `funext`
-- headline family still depends on manufactured raw-alignment Step rules.
-- This pins that debt to four claims and rejects future growth.
#assert_headline_refl_fragment_budget LeanFX2 4

-- Staged FX1 axiom leak detector.  Object-level `axiomDecl` placeholders are
-- allowed inside FX1 itself and the explicit FX1Bridge staging boundary only;
-- regular rich/root production declarations must not depend on them.
#assert_no_root_staged_axiom_leak LeanFX2

end LeanFX2.Tools
