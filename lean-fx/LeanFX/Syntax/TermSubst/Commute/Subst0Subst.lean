import LeanFX.Syntax.TermSubst.Compose

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ## `subst0` and downstream term substitution.

These lemmas are the substitution-side companion to
`Term.rename_subst0_HEq`: substituting one argument and then applying
an outer substitution agrees, up to HEq, with substituting the body
under the lifted outer substitution and substituting the argument.
-/

theorem TermSubst.precompose_weaken_singleton_pointwise
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {argumentType : Ty level scope}
    (argumentTerm : Term context argumentType) :
    ∀ position,
      HEq
        (TermSubst.precompose (TermRenaming.weaken context argumentType)
          (TermSubst.singleton argumentTerm) position)
        (TermSubst.identity context position) := by
  intro position
  match position with
  | ⟨index, isWithinScope⟩ =>
      unfold TermSubst.precompose TermSubst.singleton TermSubst.identity Renaming.weaken
      simp
      apply HEq.trans (eqRec_heq _ _)
      apply HEq.symm
      apply HEq.trans (eqRec_heq _ _)
      apply HEq.trans
        (heq_var_across_ctx_eq (rfl : context = context)
          ⟨index, isWithinScope⟩)
      exact Term.castRight_HEq _ _

theorem Term.subst_weaken_singleton_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {argumentType termType : Ty level scope}
    (term : Term context termType)
    (argumentTerm : Term context argumentType) :
    HEq
      (Term.subst (TermSubst.singleton argumentTerm)
        (Term.weaken argumentType term))
      term := by
  show HEq
    (Term.subst (TermSubst.singleton argumentTerm)
      (Term.rename (TermRenaming.weaken context argumentType) term))
    term
  apply HEq.trans
    (Term.rename_subst_commute_HEq
      (TermRenaming.weaken context argumentType)
      (TermSubst.singleton argumentTerm)
      term)
  apply HEq.trans
    (Term.subst_HEq_pointwise rfl
      (TermSubst.precompose (TermRenaming.weaken context argumentType)
        (TermSubst.singleton argumentTerm))
      (TermSubst.identity context)
      (Subst.precompose_weaken_singleton_equiv_identity argumentType)
      (TermSubst.precompose_weaken_singleton_pointwise argumentTerm)
      term)
  exact Term.subst_id_HEq term

theorem TermSubst.singleton_compose_pointwise
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceContext : Ctx mode level sourceScope}
    {targetContext : Ctx mode level targetScope}
    {typeSubstitution : Subst level sourceScope targetScope}
    (termSubstitution : TermSubst sourceContext targetContext typeSubstitution)
    {argumentType : Ty level sourceScope}
    (argumentTerm : Term sourceContext argumentType) :
    ∀ (position : Fin (sourceScope + 1)),
      HEq
        (TermSubst.compose (TermSubst.singleton argumentTerm) termSubstitution position)
        (TermSubst.compose
          (TermSubst.lift termSubstitution argumentType)
          (TermSubst.singleton (Term.subst termSubstitution argumentTerm)) position) := by
  intro position
  match position with
  | ⟨0, isWithinScope⟩ =>
      apply HEq.trans (eqRec_heq _ _)
      apply HEq.trans
        (Term.subst_HEq_cast_input termSubstitution
          (Ty.weaken_subst_singleton argumentType argumentType).symm
          argumentTerm)
      apply HEq.symm
      apply HEq.trans (eqRec_heq _ _)
      apply HEq.trans
        (Term.subst_HEq_cast_input
          (TermSubst.singleton (Term.subst termSubstitution argumentTerm))
          (Ty.subst_weaken_commute argumentType typeSubstitution).symm
          (Term.var ⟨0, Nat.zero_lt_succ targetScope⟩))
      apply HEq.trans (eqRec_heq _ _)
      exact HEq.refl _
  | ⟨index + 1, isWithinScope⟩ =>
      apply HEq.trans (eqRec_heq _ _)
      apply HEq.trans
        (Term.subst_HEq_cast_input termSubstitution
          (Ty.weaken_subst_singleton
            (varType sourceContext ⟨index, Nat.lt_of_succ_lt_succ isWithinScope⟩)
            argumentType).symm
          (Term.var ⟨index, Nat.lt_of_succ_lt_succ isWithinScope⟩))
      apply HEq.symm
      apply HEq.trans (eqRec_heq _ _)
      apply HEq.trans
        (Term.subst_HEq_cast_input
          (TermSubst.singleton (Term.subst termSubstitution argumentTerm))
          (Ty.subst_weaken_commute
            (varType sourceContext ⟨index, Nat.lt_of_succ_lt_succ isWithinScope⟩)
            typeSubstitution).symm
          (Term.weaken (argumentType.subst typeSubstitution)
            (termSubstitution ⟨index, Nat.lt_of_succ_lt_succ isWithinScope⟩)))
      exact Term.subst_weaken_singleton_HEq
        (termSubstitution ⟨index, Nat.lt_of_succ_lt_succ isWithinScope⟩)
        (Term.subst termSubstitution argumentTerm)

theorem Term.subst0_subst_HEq
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceContext : Ctx mode level sourceScope}
    {targetContext : Ctx mode level targetScope}
    {typeSubstitution : Subst level sourceScope targetScope}
    (termSubstitution : TermSubst sourceContext targetContext typeSubstitution)
    {argumentType : Ty level sourceScope}
    {bodyType : Ty level (sourceScope + 1)}
    (bodyTerm : Term (sourceContext.cons argumentType) bodyType)
    (argumentTerm : Term sourceContext argumentType) :
    HEq
      (Term.subst termSubstitution (Term.subst0 bodyTerm argumentTerm))
      (Term.subst0
        (Term.subst (TermSubst.lift termSubstitution argumentType) bodyTerm)
        (Term.subst termSubstitution argumentTerm)) := by
  show HEq
      (Term.subst termSubstitution (Term.subst (TermSubst.singleton argumentTerm) bodyTerm))
      (Term.subst (TermSubst.singleton (Term.subst termSubstitution argumentTerm))
        (Term.subst (TermSubst.lift termSubstitution argumentType) bodyTerm))
  apply HEq.trans
    (Term.subst_compose_HEq (TermSubst.singleton argumentTerm) termSubstitution bodyTerm)
  apply HEq.trans
    (Term.subst_HEq_pointwise rfl
      (TermSubst.compose (TermSubst.singleton argumentTerm) termSubstitution)
      (TermSubst.compose
        (TermSubst.lift termSubstitution argumentType)
        (TermSubst.singleton (Term.subst termSubstitution argumentTerm)))
      (Subst.singleton_compose_equiv_lift_compose_singleton argumentType typeSubstitution)
      (TermSubst.singleton_compose_pointwise termSubstitution argumentTerm)
      bodyTerm)
  exact HEq.symm
    (Term.subst_compose_HEq
      (TermSubst.lift termSubstitution argumentType)
      (TermSubst.singleton (Term.subst termSubstitution argumentTerm))
      bodyTerm)

/-! ### `subst0_term`-side counterparts.

These are the term-bearing analogs needed by the Phase C migration of
`Step.par.betaApp` from `Term.subst0` to `Term.subst0_term`.  Each one
tracks a `Term.toRaw` projection at position 0 instead of the
unit-shaped raw drop.

Most proofs are line-for-line copies of the `singleton` analogs, with
`Subst.singleton` replaced by `Subst.termSingleton` and an extra
`Term.toRaw arg` argument threaded through the supporting Ty lemmas
(`weaken_subst_termSingleton`, `precompose_weaken_termSingleton_equiv_identity`,
`termSingleton_compose_equiv_lift_compose_termSingleton`).

The headline `Term.subst0_term_subst_HEq` carries an extra
`TermSubst.RawConsistent termSubstitution` hypothesis: it's needed to
align `Term.toRaw (Term.subst termSubst arg)` with
`(Term.toRaw arg).subst typeSubst.forRaw`, which is the form produced
by `termSingleton_compose_equiv_lift_compose_termSingleton`'s RHS.  At
all Phase C call sites the substitution is raw-consistent. -/

theorem TermSubst.precompose_weaken_termSingleton_pointwise
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {argumentType : Ty level scope}
    (argumentTerm : Term context argumentType) :
    ∀ position,
      HEq
        (TermSubst.precompose (TermRenaming.weaken context argumentType)
          (TermSubst.termSingleton argumentTerm) position)
        (TermSubst.identity context position) := by
  intro position
  match position with
  | ⟨index, isWithinScope⟩ =>
      unfold TermSubst.precompose TermSubst.termSingleton TermSubst.identity
        Renaming.weaken
      simp
      apply HEq.trans (eqRec_heq _ _)
      apply HEq.symm
      apply HEq.trans (eqRec_heq _ _)
      apply HEq.trans
        (heq_var_across_ctx_eq (rfl : context = context)
          ⟨index, isWithinScope⟩)
      exact Term.castRight_HEq _ _

theorem Term.subst_weaken_termSingleton_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {argumentType termType : Ty level scope}
    (term : Term context termType)
    (argumentTerm : Term context argumentType) :
    HEq
      (Term.subst (TermSubst.termSingleton argumentTerm)
        (Term.weaken argumentType term))
      term := by
  show HEq
    (Term.subst (TermSubst.termSingleton argumentTerm)
      (Term.rename (TermRenaming.weaken context argumentType) term))
    term
  apply HEq.trans
    (Term.rename_subst_commute_HEq
      (TermRenaming.weaken context argumentType)
      (TermSubst.termSingleton argumentTerm)
      term)
  apply HEq.trans
    (Term.subst_HEq_pointwise rfl
      (TermSubst.precompose (TermRenaming.weaken context argumentType)
        (TermSubst.termSingleton argumentTerm))
      (TermSubst.identity context)
      (Subst.precompose_weaken_termSingleton_equiv_identity argumentType
        (Term.toRaw argumentTerm))
      (TermSubst.precompose_weaken_termSingleton_pointwise argumentTerm)
      term)
  exact Term.subst_id_HEq term

theorem TermSubst.termSingleton_compose_pointwise
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceContext : Ctx mode level sourceScope}
    {targetContext : Ctx mode level targetScope}
    {typeSubstitution : Subst level sourceScope targetScope}
    (termSubstitution : TermSubst sourceContext targetContext typeSubstitution)
    {argumentType : Ty level sourceScope}
    (argumentTerm : Term sourceContext argumentType) :
    ∀ (position : Fin (sourceScope + 1)),
      HEq
        (TermSubst.compose (TermSubst.termSingleton argumentTerm)
          termSubstitution position)
        (TermSubst.compose
          (TermSubst.lift termSubstitution argumentType)
          (TermSubst.termSingleton (Term.subst termSubstitution argumentTerm))
          position) := by
  intro position
  match position with
  | ⟨0, isWithinScope⟩ =>
      apply HEq.trans (eqRec_heq _ _)
      apply HEq.trans
        (Term.subst_HEq_cast_input termSubstitution
          (Ty.weaken_subst_termSingleton argumentType argumentType
            (Term.toRaw argumentTerm)).symm
          argumentTerm)
      apply HEq.symm
      apply HEq.trans (eqRec_heq _ _)
      apply HEq.trans
        (Term.subst_HEq_cast_input
          (TermSubst.termSingleton (Term.subst termSubstitution argumentTerm))
          (Ty.subst_weaken_commute argumentType typeSubstitution).symm
          (Term.var ⟨0, Nat.zero_lt_succ targetScope⟩))
      apply HEq.trans (eqRec_heq _ _)
      exact HEq.refl _
  | ⟨index + 1, isWithinScope⟩ =>
      apply HEq.trans (eqRec_heq _ _)
      apply HEq.trans
        (Term.subst_HEq_cast_input termSubstitution
          (Ty.weaken_subst_termSingleton
            (varType sourceContext ⟨index, Nat.lt_of_succ_lt_succ isWithinScope⟩)
            argumentType
            (Term.toRaw argumentTerm)).symm
          (Term.var ⟨index, Nat.lt_of_succ_lt_succ isWithinScope⟩))
      apply HEq.symm
      apply HEq.trans (eqRec_heq _ _)
      apply HEq.trans
        (Term.subst_HEq_cast_input
          (TermSubst.termSingleton (Term.subst termSubstitution argumentTerm))
          (Ty.subst_weaken_commute
            (varType sourceContext ⟨index, Nat.lt_of_succ_lt_succ isWithinScope⟩)
            typeSubstitution).symm
          (Term.weaken (argumentType.subst typeSubstitution)
            (termSubstitution ⟨index, Nat.lt_of_succ_lt_succ isWithinScope⟩)))
      exact Term.subst_weaken_termSingleton_HEq
        (termSubstitution ⟨index, Nat.lt_of_succ_lt_succ isWithinScope⟩)
        (Term.subst termSubstitution argumentTerm)

/- Note: the headline `Term.subst0_term_subst_HEq` and its
`RawConsistent`-aware helper `Subst.termSingleton_compose_equiv_lift_compose_termSingleton_subst`
live in `LeanFX/Syntax/ToRawCommute.lean`.  They depend on
`Term.toRaw_subst` (which lives there too), which sits above the
`TermSubst.Commute.*` layer in the dependency DAG. -/


end LeanFX.Syntax
