import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.TableBetaEtaRootReduce
import FX1Poly.Core.TableBetaEtaRootNormalize
import FX1Poly.Typed.TableBetaEtaRootConvDecidable

/-! # FX1PolyAudit/AuditTableBetaEtaRootConvDecidable — the TABLE-NATIVE
union beta-eta conversion decider shard

Per-declaration zero-axiom gate for the three computable bricks of the
TABLE-NATIVE union beta-eta decider (ZERO dependence on the bespoke
`Step.betaEta`/`reduceOnceBetaEta`/`normalizeBetaEta`):

* PIECE 1 — the union one-step reducer
  (`reduceOnceTableBetaEtaRoot?`): the per-row eta firer, the eta-table
  walk with its generic soundness/completeness, the canonical eta root
  firer with its blocking inversion, and the layered union reducer with
  its soundness + blocking completeness;
* PIECE 2 — the union normalizer (`normalizeTableBetaEtaRoot`): the
  `UnionSuccessor` bridge, the `Acc.rec` normalizer, its unfold, and the
  reaches-normal-form + is-normal-form correctness lemmas;
* PIECE 3 — the decider (`ConvTableBetaEtaRoot.decidableOfWfTyped`): the
  union conversion relation, the conversion ↔ normal-form-equality
  characterization, and the `Decidable` instance on the
  well-formed-typed fragment.

Every gate must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

/-! ## PIECE 1 — the union one-step reducer -/

#assert_no_axioms FX1Poly.Core.EtaRuleDesc.fireAtRootEta?
#assert_no_axioms FX1Poly.Core.EtaRuleDesc.fireAtRootEta?_sound
#assert_no_axioms FX1Poly.Core.fireEtaTableRedexOver
#assert_no_axioms FX1Poly.Core.fireEtaTableRedexOver_sound
#assert_no_axioms FX1Poly.Core.fireEtaTableRedexOver_complete
#assert_no_axioms FX1Poly.Core.RawTerm.fireRootEtaTableRedex?
#assert_no_axioms FX1Poly.Core.RawTerm.fireRootEtaTableRedex?_sound
#assert_no_axioms FX1Poly.Core.RawTerm.fireRootEtaTableRedex?_blocksStep
#assert_no_axioms FX1Poly.Core.StepTableBetaEtaRootUnion
#assert_no_axioms FX1Poly.Core.RawTerm.reduceOnceTableBetaEtaRoot?
#assert_no_axioms FX1Poly.Core.RawTerm.reduceOnceTableBetaEtaRoot?_sound
#assert_no_axioms FX1Poly.Core.RawTerm.reduceOnceTableBetaEtaRoot?_blocksStep

/-! ## PIECE 2 — the union normalizer -/

#assert_no_axioms FX1Poly.Core.unionStarPrependLeft
#assert_no_axioms FX1Poly.Core.unionStarPrependRight
#assert_no_axioms FX1Poly.Core.reduceOnceTableBetaEtaRoot?_unionSuccessor
#assert_no_axioms FX1Poly.Core.RawTerm.normalizeTableBetaEtaRoot
#assert_no_axioms FX1Poly.Core.RawTerm.normalizeTableBetaEtaRoot_unfold
#assert_no_axioms FX1Poly.Core.RawTerm.normalizeTableBetaEtaRoot_reachesNormalForm
#assert_no_axioms FX1Poly.Core.RawTerm.normalizeTableBetaEtaRoot_isNormalForm

/-! ## PIECE 3 — the decider -/

#assert_no_axioms FX1Poly.Typed.unionStarTrans
#assert_no_axioms FX1Poly.Typed.ConvTableBetaEtaRoot
#assert_no_axioms FX1Poly.Typed.ConvTableBetaEtaRoot.iff_normalForms_eq
#assert_no_axioms FX1Poly.Typed.ConvTableBetaEtaRoot.decidableOfWfTyped

end FX1PolyAudit
