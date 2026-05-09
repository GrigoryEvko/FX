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

/-! # AuditModalTwoCell — Modal/TwoCell + Modal/TwoCellLaws gates.

Per-decl `#assert_no_axioms` checks for the 2-cell inductive
(`Modal/TwoCell.lean`, D4.0a #1699) plus the four coherence-law
theorems and the supporting `TwoCellEq` equivalence-relation
inductive (`Modal/TwoCellLaws.lean`, D4.0b #1700).

Per `CLAUDE.md` zero-axiom commitment, every shipped declaration
must report "does not depend on any axioms".  This file is the
machine-enforced gate; `Smoke/AuditPhase12A4TwoCell.lean` is the
matching reviewer-facing log.

The four coherence laws (`vertAssoc`, `vertLeftId`, `vertRightId`,
`exchange`) ship up to the equivalence relation `TwoCellEq` rather
than as Lean propositional equalities — see
`Modal/TwoCellLaws.lean`'s top docstring for the rationale (free
inductive `TwoCell` does not admit these laws as `=`; the proper
mathematical setting is the equivalence relation that quotients
the free 2-cells by the strict-2-category coherence laws). -/

namespace LeanFX2.Tools

/-! ## D4.0a — TwoCell inductive + 3 core ctors -/

#assert_no_axioms LeanFX2.TwoCell
#assert_no_axioms LeanFX2.TwoCell.refl
#assert_no_axioms LeanFX2.TwoCell.vert
#assert_no_axioms LeanFX2.TwoCell.horiz

/-! ## D4.0b — TwoCellEq inductive + 9 ctors -/

#assert_no_axioms LeanFX2.TwoCellEq
#assert_no_axioms LeanFX2.TwoCellEq.reflEq
#assert_no_axioms LeanFX2.TwoCellEq.symmEq
#assert_no_axioms LeanFX2.TwoCellEq.transEq
#assert_no_axioms LeanFX2.TwoCellEq.vertCongEq
#assert_no_axioms LeanFX2.TwoCellEq.horizCongEq
#assert_no_axioms LeanFX2.TwoCellEq.vertAssocEq
#assert_no_axioms LeanFX2.TwoCellEq.vertLeftIdEq
#assert_no_axioms LeanFX2.TwoCellEq.vertRightIdEq
#assert_no_axioms LeanFX2.TwoCellEq.exchangeEq

/-! ## D4.0b — Four coherence-law theorems -/

#assert_no_axioms LeanFX2.TwoCell.vertAssoc
#assert_no_axioms LeanFX2.TwoCell.vertLeftId
#assert_no_axioms LeanFX2.TwoCell.vertRightId
#assert_no_axioms LeanFX2.TwoCell.exchange

/-! ## D4.0c — Modality.composeOpen (cross-mode compose, #1701) -/

#assert_no_axioms LeanFX2.Modality.composeOpen
#assert_no_axioms LeanFX2.Modality.composeOpen_left_identity
#assert_no_axioms LeanFX2.Modality.composeOpen_right_identity
#assert_no_axioms LeanFX2.Modality.composeOpen_boxK_idempotent
#assert_no_axioms LeanFX2.Modality.composeOpen_diamondK_idempotent
#assert_no_axioms LeanFX2.Modality.composeOpen_flat_sharp_cancel
#assert_no_axioms LeanFX2.Modality.composeOpen_sharp_flat_cancel
#assert_no_axioms LeanFX2.Modality.composeOpen_eq_compose_sameMode

end LeanFX2.Tools
