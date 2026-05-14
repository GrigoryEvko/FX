import LeanFX2.Term.Pointwise.PointwiseAndCompositionInfrastructure

/-! # LeanFX2.Term.Pointwise.IdentitySubst

Typed identity-substitution erasure helpers for the M04 lambda route.

These lemmas are kept out of `PointwiseAndCompositionInfrastructure`
so the identity-erasure cascade can evolve without forcing every edit
through the large composition-infrastructure module. -/

namespace LeanFX2

/-! ## Lifted identity entries -/

/-- Fresh entry of lifted identity substitution. -/
theorem TermSubst.identity_lift_zero_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (newType : Ty level scope) :
    HEq
      ((TermSubst.identity context).lift newType
        ⟨0, Nat.zero_lt_succ scope⟩)
      (TermSubst.identity (context.cons newType)
        ⟨0, Nat.zero_lt_succ scope⟩) := by
  change HEq
    ((Ty.weaken_subst_commute (@Subst.identity level scope) newType).symm ▸
      (show
        Term
          (context.cons (newType.subst (@Subst.identity level scope)))
          ((newType.subst (@Subst.identity level scope)).weaken)
          (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩) from
        Term.var
          (context := context.cons
            (newType.subst (@Subst.identity level scope)))
          ⟨0, Nat.zero_lt_succ scope⟩))
    ((Ty.subst_identity (newType.weaken)).symm ▸
      (show
        Term (context.cons newType) newType.weaken
          (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩) from
        Term.var
          (context := context.cons newType)
          ⟨0, Nat.zero_lt_succ scope⟩))
  exact HEq.trans
    (Term.type_eq_symm_cast_heq
      (Ty.weaken_subst_commute (@Subst.identity level scope) newType))
    (HEq.trans
      (Term.var_zero_cons_type_eq_heq
        (Ty.subst_identity newType))
      (HEq.symm
        (Term.type_eq_symm_cast_heq
          (context := context.cons newType)
          (typeEq := Ty.subst_identity (newType.weaken))
          (targetTerm := Term.var
            (context := context.cons newType)
            ⟨0, Nat.zero_lt_succ scope⟩))))

/-- Old-variable entry of lifted identity substitution. -/
theorem TermSubst.identity_lift_succ_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (newType : Ty level scope)
    (position : Fin scope) :
    HEq
      ((TermSubst.identity context).lift newType (Fin.succ position))
      (TermSubst.identity (context.cons newType) (Fin.succ position)) := by
  rcases position with ⟨positionIndex, positionIsWithinScope⟩
  simp only [TermSubst.lift, TermSubst.identity]
  exact HEq.trans
    (Term.type_eq_symm_cast_heq
      (Ty.weaken_subst_commute (@Subst.identity level scope)
        (varType context ⟨positionIndex, positionIsWithinScope⟩)))
    (HEq.trans
      (Term.weaken_head_type_eq_heq
        (Ty.subst_identity newType)
        ((Ty.subst_identity
          (varType context ⟨positionIndex, positionIsWithinScope⟩)).symm ▸
          Term.var ⟨positionIndex, positionIsWithinScope⟩))
      (HEq.trans
        (Term.rename_type_eq_cast_heq
          (TermRenaming.weakenStep context newType)
          (Ty.subst_identity
            (varType context ⟨positionIndex, positionIsWithinScope⟩)).symm
          (Term.var ⟨positionIndex, positionIsWithinScope⟩))
        (HEq.trans
          (Term.type_eq_cast_heq
            (context := context.cons newType)
            (typeEq := congrArg
              (fun someType => Ty.rename someType RawRenaming.weaken)
              (Ty.subst_identity
                (varType context ⟨positionIndex, positionIsWithinScope⟩)).symm)
            (sourceTerm :=
              Term.rename (TermRenaming.weakenStep context newType)
                (Term.var ⟨positionIndex, positionIsWithinScope⟩)))
          (HEq.trans
            (Term.rename_var_HEq
              (TermRenaming.weakenStep context newType)
              ⟨positionIndex, positionIsWithinScope⟩)
            (HEq.symm
              (Term.type_eq_symm_cast_heq
                (context := context.cons newType)
                (typeEq := Ty.subst_identity
                  (varType (context.cons newType)
                    (Fin.succ ⟨positionIndex, positionIsWithinScope⟩)))
                (targetTerm := Term.var
                  (context := context.cons newType)
                  (Fin.succ
                    ⟨positionIndex, positionIsWithinScope⟩))))))))

/-- Lifting identity substitution is pointwise heterogeneously equal
to identity on the extended context. -/
theorem TermSubst.identity_lift_position_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (newType : Ty level scope)
    (position : Fin (scope + 1)) :
    HEq
      ((TermSubst.identity context).lift newType position)
      (TermSubst.identity (context.cons newType) position) := by
  rcases position with ⟨positionIndex, positionIsWithinScope⟩
  cases positionIndex with
  | zero =>
      exact TermSubst.identity_lift_zero_HEq
        (context := context) newType
  | succ previousIndex =>
      exact TermSubst.identity_lift_succ_HEq
        (context := context) newType
        ⟨previousIndex,
          Nat.lt_of_succ_lt_succ positionIsWithinScope⟩

/-! ## Lifted identity at the term surface -/

/-- Variable surface case for ordinary identity substitution. -/
theorem Term.subst_identity_var_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (position : Fin scope) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.var (context := context) position))
      (Term.var (context := context) position) := by
  simp only [Term.subst, TermSubst.identity]
  exact Term.type_eq_symm_cast_heq
    (context := context)
    (typeEq := Ty.subst_identity (varType context position))
    (targetTerm := Term.var (context := context) position)

/-- Variable surface case for lifted identity substitution. -/
theorem Term.subst_identity_lift_var_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (newType : Ty level scope)
    (position : Fin (scope + 1)) :
    HEq
      (Term.subst ((TermSubst.identity context).lift newType)
        (Term.var (context := context.cons newType) position))
      (Term.var (context := context.cons newType) position) := by
  simp only [Term.subst]
  exact HEq.trans
    (TermSubst.identity_lift_position_HEq
      (context := context) newType position)
    (Term.type_eq_symm_cast_heq
      (context := context.cons newType)
      (typeEq := Ty.subst_identity
        (varType (context.cons newType) position))
      (targetTerm := Term.var
        (context := context.cons newType) position))

/-! ## Nullary value cases -/

/-- Unit value case for ordinary identity substitution. -/
theorem Term.subst_identity_unit_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.unit (context := context)))
      (Term.unit (context := context)) := by
  rfl

/-- Boolean true case for ordinary identity substitution. -/
theorem Term.subst_identity_boolTrue_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.boolTrue (context := context)))
      (Term.boolTrue (context := context)) := by
  rfl

/-- Boolean false case for ordinary identity substitution. -/
theorem Term.subst_identity_boolFalse_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.boolFalse (context := context)))
      (Term.boolFalse (context := context)) := by
  rfl

/-- Natural zero case for ordinary identity substitution. -/
theorem Term.subst_identity_natZero_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.natZero (context := context)))
      (Term.natZero (context := context)) := by
  rfl

/-- Left interval endpoint case for ordinary identity substitution. -/
theorem Term.subst_identity_interval0_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.interval0 (context := context)))
      (Term.interval0 (context := context)) := by
  rfl

/-- Right interval endpoint case for ordinary identity substitution. -/
theorem Term.subst_identity_interval1_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.interval1 (context := context)))
      (Term.interval1 (context := context)) := by
  rfl

end LeanFX2
