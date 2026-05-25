import LeanFX2.Tools.DependencyAudit
import LeanFX2.Reduction.Conv

namespace LeanFX2.Tools

/-! ## AuditConfluence — live Conv core audit

The old confluence/canonical-form cascade is TODO POLYCELL-disabled in
`LeanFX2.Confluence.*` after the cascade-fake bulldoze. This audit therefore
checks only the live conversion core in `Reduction/Conv.lean`.

Do not re-add stale `Conv.toRawJoin`, `Conv.canonicalRaw`, or per-constructor
reachability checks here. Their replacement must be audited through the future
PolyCell confluence / FXConv view once that machinery exists.
-/

#assert_no_axioms LeanFX2.Conv
#assert_no_axioms LeanFX2.Conv.refl
#assert_no_axioms LeanFX2.Conv.sym
#assert_no_axioms LeanFX2.Conv.fromStepStar
#assert_no_axioms LeanFX2.Conv.fromStep
#assert_no_axioms LeanFX2.Conv.transChains

end LeanFX2.Tools
