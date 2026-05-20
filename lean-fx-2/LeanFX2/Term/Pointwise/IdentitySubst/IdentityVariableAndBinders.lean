import LeanFX2.Term.Pointwise.IdentitySubst.Foundation
import LeanFX2.Term.HEqCongr.Compound
import LeanFX2.Term.HEqCongr.Atomic.Base
import LeanFX2.Term.HEqCongr.Atomic.Cubical

/-! # LeanFX2.Term.Pointwise.IdentitySubst.IdentityVariableAndBinders

Semantic slice of typed identity-substitution erasure helpers. -/

namespace LeanFX2

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

/-! ## Binder cases -/

/-- Lambda case for ordinary identity substitution.

The recursive premise is intentionally stated for the lifted identity
substitution, matching the actual `Term.subst` binder arm. -/
theorem Term.subst_identity_lam_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {bodyRaw : RawTerm (scope + 1)}
    (body : Term (context.cons domainType) codomainType.weaken bodyRaw)
    (bodyHEq :
      HEq (Term.subst ((TermSubst.identity context).lift domainType) body)
        body) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.lam (codomainType := codomainType) body))
      (Term.lam (codomainType := codomainType) body) := by
  simp only [Term.subst]
  have bodyRawIdentity :
      bodyRaw.subst (@Subst.identity level scope).forRaw.lift = bodyRaw := by
    rw [RawTerm.subst_pointwise
      (@Subst.identity_lift_forRaw_pointwise level scope) bodyRaw]
    exact RawTerm.subst_identity bodyRaw
  have bodyCastHEq :
      HEq
        ((Ty.weaken_subst_commute Subst.identity codomainType) ▸
          Term.subst ((TermSubst.identity context).lift domainType) body)
        body :=
    HEq.trans
      (Term.type_eq_cast_heq
        (Ty.weaken_subst_commute Subst.identity codomainType)
        (Term.subst ((TermSubst.identity context).lift domainType) body))
      bodyHEq
  exact Term.lam_HEq_congr
    (Ty.subst_identity domainType)
    (Ty.subst_identity codomainType)
    bodyRawIdentity
    bodyCastHEq

/-- Dependent lambda case for ordinary identity substitution.

The recursive premise is intentionally stated for the lifted identity
substitution, matching the actual `Term.subst` binder arm. -/
theorem Term.subst_identity_lamPi_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType : Ty level scope}
    {codomainType : Ty level (scope + 1)}
    {bodyRaw : RawTerm (scope + 1)}
    (body : Term (context.cons domainType) codomainType bodyRaw)
    (bodyHEq :
      HEq (Term.subst ((TermSubst.identity context).lift domainType) body)
        body) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.lamPi (domainType := domainType) body))
      (Term.lamPi (domainType := domainType) body) := by
  simp only [Term.subst]
  have codomainIdentity :
      codomainType.subst (@Subst.identity level scope).lift = codomainType := by
    rw [Ty.subst_pointwise
      (@Subst.identity_lift_forTy_pointwise level scope)
      (@Subst.identity_lift_forRaw_pointwise level scope)
      codomainType]
    exact Ty.subst_identity codomainType
  have bodyRawIdentity :
      bodyRaw.subst (@Subst.identity level scope).forRaw.lift = bodyRaw := by
    rw [RawTerm.subst_pointwise
      (@Subst.identity_lift_forRaw_pointwise level scope) bodyRaw]
    exact RawTerm.subst_identity bodyRaw
  exact Term.lamPi_HEq_congr
    (Ty.subst_identity domainType)
    codomainIdentity
    bodyRawIdentity
    bodyHEq

/-- Path lambda case for ordinary identity substitution.

The recursive premise is intentionally stated for the lifted interval
identity substitution, matching the actual `Term.subst` binder arm. -/
theorem Term.subst_identity_pathLam_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {bodyRaw : RawTerm (scope + 1)}
    (body : Term (context.cons Ty.interval) carrierType.weaken bodyRaw)
    (bodyHEq :
      HEq (Term.subst ((TermSubst.identity context).lift Ty.interval) body)
        body) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.pathLam modeIsUnivalent carrierType leftEndpoint rightEndpoint
          body))
      (Term.pathLam modeIsUnivalent carrierType leftEndpoint rightEndpoint
        body) := by
  simp only [Term.subst]
  have bodyRawIdentity :
      bodyRaw.subst (@Subst.identity level scope).forRaw.lift = bodyRaw := by
    rw [RawTerm.subst_pointwise
      (@Subst.identity_lift_forRaw_pointwise level scope) bodyRaw]
    exact RawTerm.subst_identity bodyRaw
  have bodyCastHEq :
      HEq
        ((Ty.weaken_subst_commute Subst.identity carrierType) ▸
          Term.subst ((TermSubst.identity context).lift Ty.interval) body)
        body :=
    HEq.trans
      (Term.type_eq_cast_heq
        (Ty.weaken_subst_commute Subst.identity carrierType)
        (Term.subst ((TermSubst.identity context).lift Ty.interval) body))
      bodyHEq
  exact Term.pathLam_HEq_congr
    modeIsUnivalent
    (Ty.subst_identity carrierType)
    (RawTerm.subst_identity leftEndpoint)
    (RawTerm.subst_identity rightEndpoint)
    bodyRawIdentity
    bodyCastHEq

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

/-- Empty list case for ordinary identity substitution. -/
theorem Term.subst_identity_listNil_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType : Ty level scope} :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.listNil (context := context) (elementType := elementType)))
      (Term.listNil (context := context) (elementType := elementType)) := by
  simp only [Term.subst]
  exact Term.listNil_HEq_congr (Ty.subst_identity elementType)

/-- Empty option case for ordinary identity substitution. -/
theorem Term.subst_identity_optionNone_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType : Ty level scope} :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.optionNone (context := context) (elementType := elementType)))
      (Term.optionNone (context := context) (elementType := elementType)) := by
  simp only [Term.subst]
  exact Term.optionNone_HEq_congr (Ty.subst_identity elementType)

end LeanFX2
