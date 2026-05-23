import LeanFX2.Term.Pointwise.PointwiseAndCompositionInfrastructure.CastHEq

/-! # LeanFX2.Term.LiftPointwiseHEq  (strength-T8 infrastructure)

Cross-sigma heterogeneous analogue of `TermSubst.lift_pointwise`.  Where
`TermSubst.lift_pointwise` (`…/SubstPointwise.lean`) bridges two TermSubsts over
the *same* underlying `Subst`, this bridges two TermSubsts over *different but
pointwise-equal* Substs, producing a heterogeneous (HEq) per-position equality of
their lifts.

This is the binder-enabler for the eventual cross-sigma `Term.subst` HEq bridge
(`Term.subst_pointwise_HEq`), which in turn discharges the binder / scope+1 arms of
`Term.rename_subst_commute` (strength-T8, #1964 → the 34 subst0-family arms of #2027).

Crucially it uses NO `funext`: the type indices are aligned by the cross-sigma,
axiom-clean `Ty.subst_pointwise` (homogeneous `Eq`), the `▸` casts inside
`TermSubst.lift` are peeled by the HEq-innocent `Term.type_eq_symm_cast_heq`, and
the value content is var-0 / weaken HEq congruence.  The full-`Subst`-equality route
(via `funext`) was rejected last investigation because it drags in `Quot.sound`,
which the strict `#assert_no_axioms` gate forbids. -/

namespace LeanFX2

/-- `lift` preserves cross-sigma pointwise heterogeneous equality of TermSubsts.
If `firstTermSubst` (over `sigma1`) and `secondTermSubst` (over `sigma2`) agree
heterogeneously at every position, and the two Substs agree pointwise on `forTy`
and `forRaw`, then their lifts agree heterogeneously at every position. -/
theorem TermSubst.lift_pointwise_HEq
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma1 sigma2 : Subst level sourceScope targetScope}
    (forTyEq : ∀ position, sigma1.forTy position = sigma2.forTy position)
    (forRawEq : ∀ position, sigma1.forRaw position = sigma2.forRaw position)
    {firstTermSubst : TermSubst sourceCtx targetCtx sigma1}
    {secondTermSubst : TermSubst sourceCtx targetCtx sigma2}
    (entryHEq :
      ∀ position, HEq (firstTermSubst position) (secondTermSubst position))
    (newSourceType : Ty level sourceScope) :
    ∀ position,
      HEq (firstTermSubst.lift newSourceType position)
          (secondTermSubst.lift newSourceType position)
  | ⟨0, _⟩ =>
      -- Both lifts at position 0 are the cast fresh variable; peel the casts and
      -- align the two cons-head types via `Ty.subst_pointwise`.
      HEq.trans
        (Term.type_eq_symm_cast_heq
          (Ty.weaken_subst_commute sigma1 newSourceType))
        (HEq.trans
          (Term.var_zero_cons_type_eq_heq
            (Ty.subst_pointwise forTyEq forRawEq newSourceType))
          (Term.type_eq_symm_cast_heq
            (Ty.weaken_subst_commute sigma2 newSourceType)).symm)
  | ⟨k + 1, h⟩ =>
      -- Both lifts at position k+1 are the cast weakening of the underlying entry.
      -- Peel the casts, then bridge the differing head type and the differing entry.
      HEq.trans
        (Term.type_eq_symm_cast_heq
          (Ty.weaken_subst_commute sigma1
            (varType sourceCtx ⟨k, Nat.lt_of_succ_lt_succ h⟩)))
        (HEq.trans
          (HEq.trans
            (Term.weaken_head_type_eq_heq
              (Ty.subst_pointwise forTyEq forRawEq newSourceType)
              (firstTermSubst ⟨k, Nat.lt_of_succ_lt_succ h⟩))
            (Term.weaken_heq_of_eq
              (newSourceType.subst sigma2)
              (Ty.subst_pointwise forTyEq forRawEq
                (varType sourceCtx ⟨k, Nat.lt_of_succ_lt_succ h⟩))
              (forRawEq ⟨k, Nat.lt_of_succ_lt_succ h⟩)
              (entryHEq ⟨k, Nat.lt_of_succ_lt_succ h⟩)))
          (Term.type_eq_symm_cast_heq
            (Ty.weaken_subst_commute sigma2
              (varType sourceCtx ⟨k, Nat.lt_of_succ_lt_succ h⟩))).symm)

end LeanFX2
