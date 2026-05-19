import LeanFX2.Term.Pointwise.PointwiseAndCompositionInfrastructure.SingletonPrecompose

/-! # LeanFX2.Term.Pointwise.PointwiseAndCompositionInfrastructure.LiftCompose

Semantic slice of typed pointwise substitution and composition infrastructure. -/

namespace LeanFX2

/-! ## Lift/compose alignment

These lemmas compare the two substitution shapes exposed by binder
composition:

* lifting the already-composed substitution; and
* composing the two individually lifted substitutions.

The fresh-variable case is the first cast-bearing obstruction in the
`Term.subst_compose` binder proof: both sides reduce to variable zero,
but their target contexts differ by `Ty.subst_compose`. -/

/-- Fresh-variable entry of lifted substitution composition.

This compares `(first.compose second).lift` with
`first.lift.compose second.lift` at position zero.  The proof strips the
type-index casts on both sides, then relates the two variable-zero terms
through the context-head equality supplied by `Ty.subst_compose`. -/
theorem TermSubst.lift_compose_zero_HEq
    {mode : Mode} {level sourceScope middleScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {middleCtx : Ctx mode level middleScope}
    {targetCtx : Ctx mode level targetScope}
    {firstSubst : Subst level sourceScope middleScope}
    {secondSubst : Subst level middleScope targetScope}
    (firstTermSubst : TermSubst sourceCtx middleCtx firstSubst)
    (secondTermSubst : TermSubst middleCtx targetCtx secondSubst)
    (newSourceType : Ty level sourceScope) :
    HEq
      ((TermSubst.compose firstTermSubst secondTermSubst).lift
        newSourceType ⟨0, Nat.zero_lt_succ sourceScope⟩)
      (TermSubst.compose (firstTermSubst.lift newSourceType)
        (secondTermSubst.lift (newSourceType.subst firstSubst))
        ⟨0, Nat.zero_lt_succ sourceScope⟩) := by
  simp only [TermSubst.lift, TermSubst.compose]
  apply HEq.trans
  · exact Term.type_eq_symm_cast_heq
      (Ty.weaken_subst_commute (Subst.compose firstSubst secondSubst)
        newSourceType)
  · apply HEq.symm
    apply HEq.trans
    · exact cast_heq _ _
    · apply HEq.trans
      · exact Term.subst_type_eq_cast_heq _ _ _
      · simp only [Term.subst, TermSubst.lift]
        apply HEq.trans
        · exact Term.type_eq_symm_cast_heq
            (Ty.weaken_subst_commute secondSubst
              (newSourceType.subst firstSubst))
        · exact Term.var_zero_cons_type_eq_heq
            (Ty.subst_compose firstSubst secondSubst newSourceType)

/-- Substitution law for the beta-specific environment extension:
weakening a source type, lifting an existing substitution, then
substituting the fresh argument is propositionally the original
substitution on that type. -/
theorem Ty.weaken_subst_lift_singleton
    {level scope targetScope : Nat}
    (sourceType domainType : Ty level scope)
    (sigma : Subst level scope targetScope)
    (argumentRaw : RawTerm targetScope) :
    sourceType.weaken.subst
        (Subst.compose sigma.lift
          (Subst.singleton (domainType.subst sigma) argumentRaw)) =
      sourceType.subst sigma := by
  rw [← Ty.subst_compose sigma.lift
        (Subst.singleton (domainType.subst sigma) argumentRaw)
        sourceType.weaken]
  rw [Ty.weaken_subst_commute sigma sourceType]
  exact Ty.weaken_subst_singleton (sourceType.subst sigma)
    (domainType.subst sigma) argumentRaw

/-- Raw beta-contractum alignment for the beta-specific substitution
extension. -/
theorem RawTerm.subst_lift_singleton_eq_subst0
    {level scope targetScope : Nat}
    (bodyRaw : RawTerm (scope + 1))
    (domainType : Ty level scope)
    (sigma : Subst level scope targetScope)
    (argumentRaw : RawTerm targetScope) :
    bodyRaw.subst
        (Subst.compose sigma.lift
          (Subst.singleton (domainType.subst sigma) argumentRaw)).forRaw =
      (bodyRaw.subst sigma.forRaw.lift).subst0 argumentRaw := by
  unfold RawTerm.subst0
  rw [RawTerm.subst_compose sigma.forRaw.lift
    (RawTermSubst.singleton argumentRaw) bodyRaw]

/-- Weakening under one existing binder, then substituting by the lifted
singleton, returns the original raw term. -/
theorem RawTerm.weaken_lift_subst_singleton_lift {scope : Nat}
    (term : RawTerm (scope + 1)) (rawArg : RawTerm scope) :
    (term.rename RawRenaming.weaken.lift).subst
        (RawTermSubst.singleton rawArg).lift =
      term := by
  rw [RawTerm.rename_subst_commute RawRenaming.weaken.lift
      (RawTermSubst.singleton rawArg).lift term,
    RawTerm.subst_pointwise ?_ term,
    RawTerm.subst_identity term]
  intro position
  rcases position with ⟨positionIndex, positionLt⟩
  cases positionIndex with
  | zero => rfl
  | succ _ => rfl

/-- Weakening under one existing binder, then substituting by the lifted
singleton, returns the original type. -/
theorem Ty.weaken_lift_subst_singleton_lift {level scope : Nat}
    (someType : Ty level (scope + 1))
    (substituent : Ty level scope)
    (rawArg : RawTerm scope) :
    (someType.rename RawRenaming.weaken.lift).subst
        (Subst.singleton substituent rawArg).lift =
      someType := by
  rw [Ty.rename_subst_commute RawRenaming.weaken.lift
      (Subst.singleton substituent rawArg).lift someType]
  rw [Ty.subst_pointwise ?_ ?_ someType, Ty.subst_identity someType]
  · intro position
    rcases position with ⟨positionIndex, positionLt⟩
    cases positionIndex with
    | zero => rfl
    | succ _ => rfl
  · intro position
    rcases position with ⟨positionIndex, positionLt⟩
    cases positionIndex with
    | zero => rfl
    | succ _ => rfl

/-- Beta-specific extension of a typed substitution by an argument.

Unlike `TermSubst.lift`, this substitution lands back in the original
target context: position zero maps to the supplied argument, while
successor positions map to the original substitution witnesses. -/
def TermSubst.consSingleton
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    {domainType : Ty level scope}
    {argumentRaw : RawTerm targetScope}
    (argumentTerm : Term targetCtx (domainType.subst sigma) argumentRaw) :
    TermSubst (sourceCtx.cons domainType) targetCtx
      (Subst.compose sigma.lift
        (Subst.singleton (domainType.subst sigma) argumentRaw))
  | ⟨0, _⟩ =>
      (Ty.weaken_subst_lift_singleton domainType domainType sigma
        argumentRaw).symm ▸
        argumentTerm
  | ⟨positionIndex + 1, positionIsWithinScope⟩ =>
      let previousPosition : Fin scope :=
        ⟨positionIndex, Nat.lt_of_succ_lt_succ positionIsWithinScope⟩
      have typeEq :
          ((varType (sourceCtx.cons domainType)
              ⟨positionIndex + 1, positionIsWithinScope⟩).subst
            (Subst.compose sigma.lift
              (Subst.singleton (domainType.subst sigma) argumentRaw))) =
            (varType sourceCtx previousPosition).subst sigma := by
        exact Ty.weaken_subst_lift_singleton
          (varType sourceCtx previousPosition) domainType sigma argumentRaw
      have rawEq :
          (Subst.compose sigma.lift
              (Subst.singleton (domainType.subst sigma) argumentRaw)).forRaw
              ⟨positionIndex + 1, positionIsWithinScope⟩ =
            sigma.forRaw previousPosition := by
        exact RawTerm.weaken_subst_singleton
          (sigma.forRaw previousPosition) argumentRaw
      rawEq.symm ▸ typeEq.symm ▸ termSubst previousPosition

/-- The fresh entry of `TermSubst.consSingleton` is the supplied
argument, modulo the definitional type-index cast used by the
substitution family. -/
theorem TermSubst.consSingleton_zero_HEq
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    {domainType : Ty level scope}
    {argumentRaw : RawTerm targetScope}
    (argumentTerm : Term targetCtx (domainType.subst sigma) argumentRaw) :
    HEq
      (TermSubst.consSingleton termSubst argumentTerm
        ⟨0, Nat.zero_lt_succ scope⟩)
      argumentTerm :=
  Term.type_eq_cast_heq
    (Ty.weaken_subst_lift_singleton domainType domainType sigma
      argumentRaw).symm
    argumentTerm

/-- A successor entry of `TermSubst.consSingleton` is the corresponding
old substitution entry, modulo the raw/type casts that collapse
weakening followed by singleton substitution. -/
theorem TermSubst.consSingleton_succ_HEq
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    {domainType : Ty level scope}
    {argumentRaw : RawTerm targetScope}
    (argumentTerm : Term targetCtx (domainType.subst sigma) argumentRaw)
    (previousIndex : Nat)
    (positionIsWithinScope : previousIndex + 1 < scope + 1) :
    HEq
      (TermSubst.consSingleton termSubst argumentTerm
        ⟨previousIndex + 1, positionIsWithinScope⟩)
      (termSubst
        ⟨previousIndex, Nat.lt_of_succ_lt_succ positionIsWithinScope⟩) := by
  simp only [TermSubst.consSingleton]
  exact Term.type_raw_eq_cast_heq
    (Ty.weaken_subst_lift_singleton
      (varType sourceCtx
        ⟨previousIndex, Nat.lt_of_succ_lt_succ positionIsWithinScope⟩)
      domainType sigma argumentRaw).symm
    (RawTerm.weaken_subst_singleton
      (sigma.forRaw
        ⟨previousIndex, Nat.lt_of_succ_lt_succ positionIsWithinScope⟩)
      argumentRaw).symm
    (termSubst
      ⟨previousIndex, Nat.lt_of_succ_lt_succ positionIsWithinScope⟩)

/-- The fresh variable of `termSubst.lift` collapses to the singleton
argument after substituting by `TermSubst.singleton`, up to HEq. -/
theorem TermSubst.lift_zero_subst_singleton_heq
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    {domainType : Ty level scope}
    {argumentRaw : RawTerm targetScope}
    (argumentTerm : Term targetCtx (domainType.subst sigma) argumentRaw) :
    HEq
      (Term.subst (TermSubst.singleton argumentTerm)
        (termSubst.lift domainType ⟨0, Nat.zero_lt_succ scope⟩))
      argumentTerm := by
  simp only [TermSubst.lift, varType]
  apply HEq.trans
    (Term.subst_type_eq_cast_heq (TermSubst.singleton argumentTerm)
      (Ty.weaken_subst_commute sigma domainType).symm
      (Term.var (context := targetCtx.cons (domainType.subst sigma))
        ⟨0, Nat.zero_lt_succ targetScope⟩))
  change HEq
    (TermSubst.singleton argumentTerm ⟨0, Nat.zero_lt_succ targetScope⟩)
    argumentTerm
  simp only [TermSubst.singleton, varType]
  exact Term.type_eq_cast_heq
    (Ty.weaken_subst_singleton (domainType.subst sigma)
      (domainType.subst sigma) argumentRaw).symm
    argumentTerm

/-- The fresh entry of the composed lift-then-singleton substitution
agrees with the beta-specific `consSingleton` substitution.

This is the zero-position half of the entrywise comparison needed by
the typed beta-contractum bridge.  The successor half requires the
general weaken-then-singleton collapse for arbitrary substituted terms
and is intentionally left to that structural theorem. -/
theorem TermSubst.compose_lift_singleton_consSingleton_zero_HEq
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    {domainType : Ty level scope}
    {argumentRaw : RawTerm targetScope}
    (argumentTerm : Term targetCtx (domainType.subst sigma) argumentRaw) :
    HEq
      (TermSubst.compose (termSubst.lift domainType)
        (TermSubst.singleton argumentTerm)
        ⟨0, Nat.zero_lt_succ scope⟩)
      (TermSubst.consSingleton termSubst argumentTerm
        ⟨0, Nat.zero_lt_succ scope⟩) := by
  exact HEq.trans
    (TermSubst.compose_position_HEq
      (termSubst.lift domainType)
      (TermSubst.singleton argumentTerm)
      ⟨0, Nat.zero_lt_succ scope⟩)
    (HEq.trans
      (TermSubst.lift_zero_subst_singleton_heq termSubst argumentTerm)
      (TermSubst.consSingleton_zero_HEq termSubst argumentTerm).symm)

/-- Successor comparison for composed lift-then-singleton substitutions,
assuming the old substitution entry itself collapses after weakening and
singleton substitution.

This theorem does not hide the hard structural obligation: `entryHEq`
is precisely the arbitrary-term weaken-then-singleton collapse needed
for the old substitution entry.  Once that structural theorem exists,
this lemma turns it into the successor half of the `compose` versus
`consSingleton` comparison. -/
theorem TermSubst.compose_lift_singleton_consSingleton_succ_of_entry_HEq
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    {domainType : Ty level scope}
    {argumentRaw : RawTerm targetScope}
    (argumentTerm : Term targetCtx (domainType.subst sigma) argumentRaw)
    (previousIndex : Nat)
    (positionIsWithinScope : previousIndex + 1 < scope + 1)
    (entryHEq :
      HEq
        (Term.subst (TermSubst.singleton argumentTerm)
          (Term.weaken (domainType.subst sigma)
            (termSubst
              ⟨previousIndex,
                Nat.lt_of_succ_lt_succ positionIsWithinScope⟩)))
        (termSubst
          ⟨previousIndex,
            Nat.lt_of_succ_lt_succ positionIsWithinScope⟩)) :
    HEq
      (TermSubst.compose (termSubst.lift domainType)
        (TermSubst.singleton argumentTerm)
        ⟨previousIndex + 1, positionIsWithinScope⟩)
      (TermSubst.consSingleton termSubst argumentTerm
        ⟨previousIndex + 1, positionIsWithinScope⟩) := by
  let previousPosition : Fin scope :=
    ⟨previousIndex, Nat.lt_of_succ_lt_succ positionIsWithinScope⟩
  exact HEq.trans
    (TermSubst.compose_position_HEq
      (termSubst.lift domainType)
      (TermSubst.singleton argumentTerm)
      ⟨previousIndex + 1, positionIsWithinScope⟩)
    (HEq.trans
      (Term.subst_type_eq_cast_heq
        (TermSubst.singleton argumentTerm)
        (Ty.weaken_subst_commute sigma
          (varType sourceCtx previousPosition)).symm
        (Term.weaken (domainType.subst sigma)
          (termSubst previousPosition)))
      (HEq.trans entryHEq
        (TermSubst.consSingleton_succ_HEq termSubst argumentTerm
          previousIndex positionIsWithinScope).symm))

/-- Pointwise equality between the composed lift-then-singleton
substitution and the beta-specific `consSingleton` substitution.

The theorem packages the already-audited zero and successor HEq entries
into the exact same-index equality needed by `Term.subst_pointwise`.
It still exposes the real remaining obligation: every old substitution
entry must collapse after weakening and singleton substitution. -/
theorem TermSubst.compose_lift_singleton_consSingleton_pointwise_of_entry
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    {domainType : Ty level scope}
    {argumentRaw : RawTerm targetScope}
    (argumentTerm : Term targetCtx (domainType.subst sigma) argumentRaw)
    (entryHEq :
      ∀ previousPosition : Fin scope,
        HEq
          (Term.subst (TermSubst.singleton argumentTerm)
            (Term.weaken (domainType.subst sigma)
              (termSubst previousPosition)))
          (termSubst previousPosition)) :
    ∀ position,
      TermSubst.compose (termSubst.lift domainType)
        (TermSubst.singleton argumentTerm) position =
      TermSubst.consSingleton termSubst argumentTerm position := by
  intro position
  rcases position with ⟨positionIndex, positionIsWithinScope⟩
  cases positionIndex with
  | zero =>
      exact eq_of_heq
        (TermSubst.compose_lift_singleton_consSingleton_zero_HEq
          termSubst argumentTerm)
  | succ previousIndex =>
      exact eq_of_heq
        (TermSubst.compose_lift_singleton_consSingleton_succ_of_entry_HEq
          termSubst argumentTerm previousIndex positionIsWithinScope
          (entryHEq
            ⟨previousIndex,
              Nat.lt_of_succ_lt_succ positionIsWithinScope⟩))

/-- Substituting a term with the composed lift-then-singleton
substitution is the same as substituting it with the beta-specific
`consSingleton` substitution, assuming the old substitution entries
collapse after weaken-then-singleton.

This is the body-level form needed by the lambda contractum route:
after the entry theorem is available, `Term.subst_pointwise` can
transport every body in one step instead of re-opening constructor
cases. -/
theorem Term.subst_compose_lift_singleton_eq_consSingleton_of_entry
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    {domainType : Ty level scope}
    {argumentRaw : RawTerm targetScope}
    (argumentTerm : Term targetCtx (domainType.subst sigma) argumentRaw)
    (entryHEq :
      ∀ previousPosition : Fin scope,
        HEq
          (Term.subst (TermSubst.singleton argumentTerm)
            (Term.weaken (domainType.subst sigma)
              (termSubst previousPosition)))
          (termSubst previousPosition))
    {bodyType : Ty level (scope + 1)}
    {bodyRaw : RawTerm (scope + 1)}
    (bodyTerm : Term (sourceCtx.cons domainType) bodyType bodyRaw) :
    Term.subst
        (TermSubst.compose (termSubst.lift domainType)
          (TermSubst.singleton argumentTerm))
        bodyTerm =
      Term.subst (TermSubst.consSingleton termSubst argumentTerm)
        bodyTerm := by
  exact Term.subst_pointwise
    (TermSubst.compose_lift_singleton_consSingleton_pointwise_of_entry
      termSubst argumentTerm entryHEq)
    bodyTerm


end LeanFX2
