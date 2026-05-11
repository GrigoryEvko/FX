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


/-! ## Gates: OfNat+Subtype+Eq+Reducible (extracted from AuditAll lines 358-381). -/

-- OfNat / OfScientific dependent census.  OfNat instances let numeric
-- literals inject into types; custom instances on inappropriate types
-- are literal-injection vectors.  843 today reflects pervasive use of
-- Nat literals in proofs plus the stronger `equivIntroHet` constructor
-- shape, pointwise proof-function premise on `Term.oeqFunext`, the
-- dependent bool eliminator motive, and the FIFTEEN Algo/Completeness
-- M10 inferable theorems closing the full inferable subset (atomic +
-- single-recurse + multi-recurse) whose closure transitively pulls in
-- `Term.infer`, plus the FIFTEEN M10 check-mode theorems whose closure
-- transitively pulls in `Term.check` (which itself references OfNat
-- via the Nat-indexed Fin scope position dispatch).  D3.6-P1 added
-- one cong rule + ctor whose cascade arms thread one new OfNat path.
-- D3.6-P2 adds one more OfNat path via `equivApply` cascade arms.
-- D3.6-P3: typed `Term.uaToEquiv` cascade adds five more OfNat paths
-- (rename/subst/substHet/Allais helper/Step.par cong arms — each
-- threads UniverseLevel/innerLevel through Nat).
-- D3.6-P4: typed `Term.equivApply` binary cascade adds four more OfNat
-- paths (binary cong rules — equivApplyEquiv + equivApplyArgument +
-- Step.par cong + ConvCumul cong + Allais helper + dispatch arm).
-- D3.6-S3: raw `RawTerm.pathCompose` cascade adds one more OfNat path
-- through new shape-inversion helper rename_eq_pathCompose_imp.
-- D3.6-S4: raw `RawTerm.idToEquiv` cascade adds one more OfNat path
-- through new shape-inversion helper rename_eq_idToEquiv_imp.
-- D3.6-S5: raw `RawTerm.oeqTrans` + `RawTerm.equivCompose` cascade
-- adds two more OfNat paths through new shape-inversion helpers
-- rename_eq_oeqTrans_imp + rename_eq_equivCompose_imp.
-- K11.13 Phase A: RawPolyTerm.rename references Fin / Nat through
-- every position binder, threading OfNat through 73 equation lemmas
-- and the commute lemma. +75.
#assert_ofnat_dependent_budget LeanFX2 1310

-- Subtype.mk / Subtype.val dependent census.  Tight ratchet at zero —
-- the kernel doesn't use subtype-encoded reasoning.
#assert_subtype_dependent_budget LeanFX2 0

-- Function.Injective / Bijective / Surjective dependent census.  Tight
-- ratchet at zero — the kernel doesn't use cardinality-based reasoning.
#assert_function_property_dependent_budget LeanFX2 0

-- Eq.symm / Eq.trans / Eq.mp / Eq.recOn / Eq.subst dependent census.
-- 1079 today reflects pervasive equality-rewriting in proofs plus the
-- stronger `equivIntroHet` constructor shape and pointwise proof-function
-- premise on `Term.oeqFunext`, plus the dependent bool eliminator motive,
-- plus the FIFTEEN Algo/Completeness M10 inferable theorems closing
-- the full inferable subset (atomic + single-recurse + multi-recurse
-- including the dsimp-only/dif_pos-rfl recipe for app/listCons)
-- pulling in `Term.infer`, plus the FIFTEEN M10 check-mode counterpart
-- theorems whose closure threads `h ▸ t` (which expands through
-- Eq.rec) on every expected-type-equality arm of `Term.check`.
-- D3.6-P1's cascade arms (28-ctor matches in subst/rename/cd) add
-- one new Eq-rewriting path through the new ctor.  D3.6-P2 adds one
-- more Eq-rewriting path via the binary `equivApply` ctor cascade.
-- D3.6-P3: typed cascade adds six more Eq-rewriting paths.
-- D3.6-P4: typed `Term.equivApply` binary cascade adds five more
-- Eq-rewriting paths.
-- D3.6-S3: raw `RawTerm.pathCompose` cascade adds one more Eq-rewriting
-- path through the new cd cascade arm + inversion helper.
-- D3.6-S4: raw `RawTerm.idToEquiv` cascade adds one more Eq-rewriting
-- path through the new cdIdToEquivCase + inversion helper.
-- D3.6-S5: raw `RawTerm.oeqTrans` + `RawTerm.equivCompose` cascade
-- adds two more Eq-rewriting paths through cdIdToEquivCase oeqTrans
-- arm + idToEquiv_inv 5-disjunct extension + 2 new shape-inversion
-- helpers.
-- K11.13 Phase A: rename_toRawPoly_commute uses simp+congrArg over
-- 73 cases, each threading Eq.symm / Eq.trans / Eq.rec. +75.
#assert_eq_rewriting_dependent_budget LeanFX2 1493

-- Reducible / abbrev kernel decl census.  476 today reflects the
-- Action / Subst / Renaming infrastructure being abbrev-shaped for
-- unification, plus Ty.weaken being @[reducible] per
-- feedback_lean_reducible_weaken.md.  Tight ratchet at current count.
-- D3.6-P3: typed `Term.uaToEquiv` cascade adds two more reducible
-- decls (the typed ctor + raw-projection theorem are reducible by
-- Lean's auto-derivation).
-- D3.6-P4: typed `Term.equivApply` cascade adds two more reducible
-- decls (the binary typed ctor + raw-projection theorem) reflected
-- in the live count.
#assert_reducible_decl_budget LeanFX2 598

end LeanFX2.Tools
