import LeanFX2.Term.HEqCongr
import LeanFX2.Term.Subst
import LeanFX2.Term.Pointwise.PointwiseAndCompositionInfrastructure

/-! # LeanFX2.Term.Pointwise.VariableAndIntroArms

weaken-subst-singleton arms for variables, units, lambdas, and simple
introduction forms (booleans, naturals zero/succ, list nil/cons, option
none/some, eithers, intervals + ops, path lambda, modal intro/elim/subsume).

## Root status

Kernel — variable and introduction-form arms of the Pointwise
weaken-then-singleton cascade. -/

namespace LeanFX2

/-! ## Weakening followed by singleton substitution

These lemmas build the constructor-by-constructor collapse needed by
the lambda beta-contractum route: weaken a typed term through a fresh
binder, then substitute that fresh binder by a singleton argument.  The
full structural theorem is intentionally assembled in small audited
slices because cast-bearing binders and dependent eliminators require
their own alignment work. -/

/-- Variable case for weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_var_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (position : Fin scope)
    (newType : Ty level scope)
    {argumentRaw : RawTerm scope}
    (argumentTerm : Term context newType argumentRaw) :
    HEq
      (Term.subst (TermSubst.singleton argumentTerm)
        (Term.weaken newType (Term.var (context := context) position)))
      (Term.var (context := context) position) := by
  simp only [Term.weaken, Term.rename, Term.subst, TermSubst.singleton]
  exact Term.type_raw_eq_cast_heq
    (Ty.weaken_subst_singleton (varType context position) newType
      argumentRaw).symm
    (RawTerm.weaken_subst_singleton (RawTerm.var position) argumentRaw).symm
    (Term.var position)

/-- Unit value case for weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_unit_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (newType : Ty level scope)
    {argumentRaw : RawTerm scope}
    (argumentTerm : Term context newType argumentRaw) :
    HEq
      (Term.subst (TermSubst.singleton argumentTerm)
        (Term.weaken newType (Term.unit (context := context))))
      (Term.unit (context := context)) := by
  rfl

/-- Lambda introduction preserves weaken-then-singleton collapse.

The body premise is intentionally stated under the lifted singleton:
after weakening a lambda, its body lives under the original lambda binder
and the newly inserted outer binder.  Collapsing that body is the
substitution-parametric shape consumed by the typed-β cascade. -/
theorem Term.weaken_subst_singleton_lam_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {bodyRaw : RawTerm (scope + 1)}
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (body : Term (context.cons domainType) codomainType.weaken bodyRaw)
    (bodyHEq :
      HEq
        (Ty.weaken_subst_commute
          (Subst.singleton newType singletonRaw)
          (codomainType.rename RawRenaming.weaken) ▸
          Term.subst
            ((TermSubst.singleton singletonTerm).lift
              (domainType.rename RawRenaming.weaken))
            (Ty.weaken_rename_commute RawRenaming.weaken codomainType ▸
              Term.rename
                ((TermRenaming.weakenStep context newType).lift domainType)
                body))
        body) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType (Term.lam body)))
      (Term.lam body) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.lam_HEq_congr
    (Ty.weaken_subst_singleton domainType newType singletonRaw)
    (Ty.weaken_subst_singleton codomainType newType singletonRaw)
    (RawTerm.weaken_lift_subst_singleton_lift bodyRaw singletonRaw)
    bodyHEq

/-- Dependent lambda introduction preserves weaken-then-singleton
collapse under the lifted-singleton body premise. -/
theorem Term.weaken_subst_singleton_lamPi_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType : Ty level scope}
    {codomainType : Ty level (scope + 1)}
    {bodyRaw : RawTerm (scope + 1)}
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (body : Term (context.cons domainType) codomainType bodyRaw)
    (bodyHEq :
      HEq
        (Term.subst
          ((TermSubst.singleton singletonTerm).lift
            (domainType.rename RawRenaming.weaken))
          (Term.rename
            ((TermRenaming.weakenStep context newType).lift domainType)
            body))
        body) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType (Term.lamPi body)))
      (Term.lamPi body) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.lamPi_HEq_congr
    (Ty.weaken_subst_singleton domainType newType singletonRaw)
    (Ty.weaken_lift_subst_singleton_lift codomainType newType singletonRaw)
    (RawTerm.weaken_lift_subst_singleton_lift bodyRaw singletonRaw)
    bodyHEq

/-- Boolean true case for weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_boolTrue_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (newType : Ty level scope)
    {argumentRaw : RawTerm scope}
    (argumentTerm : Term context newType argumentRaw) :
    HEq
      (Term.subst (TermSubst.singleton argumentTerm)
        (Term.weaken newType (Term.boolTrue (context := context))))
      (Term.boolTrue (context := context)) := by
  rfl

/-- Boolean false case for weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_boolFalse_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (newType : Ty level scope)
    {argumentRaw : RawTerm scope}
    (argumentTerm : Term context newType argumentRaw) :
    HEq
      (Term.subst (TermSubst.singleton argumentTerm)
        (Term.weaken newType (Term.boolFalse (context := context))))
      (Term.boolFalse (context := context)) := by
  rfl

/-- Natural zero case for weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_natZero_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (newType : Ty level scope)
    {argumentRaw : RawTerm scope}
    (argumentTerm : Term context newType argumentRaw) :
    HEq
      (Term.subst (TermSubst.singleton argumentTerm)
        (Term.weaken newType (Term.natZero (context := context))))
      (Term.natZero (context := context)) := by
  rfl

/-- Empty list case for weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_listNil_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (elementType : Ty level scope)
    (newType : Ty level scope)
    {argumentRaw : RawTerm scope}
    (argumentTerm : Term context newType argumentRaw) :
    HEq
      (Term.subst (TermSubst.singleton argumentTerm)
        (Term.weaken newType
          (Term.listNil (context := context) (elementType := elementType))))
      (Term.listNil (context := context) (elementType := elementType)) := by
  simp only [Term.weaken, Term.rename]
  exact Term.listNil_HEq_congr
    (Ty.weaken_subst_singleton elementType newType argumentRaw)

/-- Empty option case for weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_optionNone_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (elementType : Ty level scope)
    (newType : Ty level scope)
    {argumentRaw : RawTerm scope}
    (argumentTerm : Term context newType argumentRaw) :
    HEq
      (Term.subst (TermSubst.singleton argumentTerm)
        (Term.weaken newType
          (Term.optionNone (context := context) (elementType := elementType))))
      (Term.optionNone (context := context) (elementType := elementType)) := by
  simp only [Term.weaken, Term.rename]
  exact Term.optionNone_HEq_congr
    (Ty.weaken_subst_singleton elementType newType argumentRaw)

/-- Interval zero case for weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_interval0_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (newType : Ty level scope)
    {argumentRaw : RawTerm scope}
    (argumentTerm : Term context newType argumentRaw) :
    HEq
      (Term.subst (TermSubst.singleton argumentTerm)
        (Term.weaken newType (Term.interval0 (context := context))))
      (Term.interval0 (context := context)) := by
  rfl

/-- Interval one case for weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_interval1_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (newType : Ty level scope)
    {argumentRaw : RawTerm scope}
    (argumentTerm : Term context newType argumentRaw) :
    HEq
      (Term.subst (TermSubst.singleton argumentTerm)
        (Term.weaken newType (Term.interval1 (context := context))))
      (Term.interval1 (context := context)) := by
  rfl

/-- Natural successor preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_natSucc_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {predecessorRaw : RawTerm scope}
    (newType : Ty level scope)
    {argumentRaw : RawTerm scope}
    (argumentTerm : Term context newType argumentRaw)
    (predecessorTerm : Term context Ty.nat predecessorRaw)
    (predecessorHEq :
      HEq
        (Term.subst (TermSubst.singleton argumentTerm)
          (Term.weaken newType predecessorTerm))
        predecessorTerm) :
    HEq
      (Term.subst (TermSubst.singleton argumentTerm)
        (Term.weaken newType (Term.natSucc predecessorTerm)))
      (Term.natSucc predecessorTerm) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.natSucc_HEq_congr
    (RawTerm.weaken_subst_singleton predecessorRaw argumentRaw)
    predecessorHEq

/-- List cons preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_listCons_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType : Ty level scope}
    {headRaw tailRaw : RawTerm scope}
    (newType : Ty level scope)
    {argumentRaw : RawTerm scope}
    (argumentTerm : Term context newType argumentRaw)
    (headTerm : Term context elementType headRaw)
    (tailTerm : Term context (Ty.listType elementType) tailRaw)
    (headHEq :
      HEq
        (Term.subst (TermSubst.singleton argumentTerm)
          (Term.weaken newType headTerm))
        headTerm)
    (tailHEq :
      HEq
        (Term.subst (TermSubst.singleton argumentTerm)
          (Term.weaken newType tailTerm))
        tailTerm) :
    HEq
      (Term.subst (TermSubst.singleton argumentTerm)
        (Term.weaken newType (Term.listCons headTerm tailTerm)))
      (Term.listCons headTerm tailTerm) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.listCons_HEq_congr
    (Ty.weaken_subst_singleton elementType newType argumentRaw)
    (RawTerm.weaken_subst_singleton headRaw argumentRaw)
    (RawTerm.weaken_subst_singleton tailRaw argumentRaw)
    headHEq tailHEq

/-- Option some preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_optionSome_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType : Ty level scope}
    {valueRaw : RawTerm scope}
    (newType : Ty level scope)
    {argumentRaw : RawTerm scope}
    (argumentTerm : Term context newType argumentRaw)
    (valueTerm : Term context elementType valueRaw)
    (valueHEq :
      HEq
        (Term.subst (TermSubst.singleton argumentTerm)
          (Term.weaken newType valueTerm))
        valueTerm) :
    HEq
      (Term.subst (TermSubst.singleton argumentTerm)
        (Term.weaken newType (Term.optionSome valueTerm)))
      (Term.optionSome valueTerm) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.optionSome_HEq_congr
    (Ty.weaken_subst_singleton elementType newType argumentRaw)
    (RawTerm.weaken_subst_singleton valueRaw argumentRaw)
    valueHEq

/-- Either-left injection preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_eitherInl_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {leftType rightType : Ty level scope}
    {valueRaw : RawTerm scope}
    (newType : Ty level scope)
    {argumentRaw : RawTerm scope}
    (argumentTerm : Term context newType argumentRaw)
    (valueTerm : Term context leftType valueRaw)
    (valueHEq :
      HEq
        (Term.subst (TermSubst.singleton argumentTerm)
          (Term.weaken newType valueTerm))
        valueTerm) :
    HEq
      (Term.subst (TermSubst.singleton argumentTerm)
        (Term.weaken newType
          (Term.eitherInl (rightType := rightType) valueTerm)))
      (Term.eitherInl (rightType := rightType) valueTerm) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.eitherInl_HEq_congr
    (Ty.weaken_subst_singleton leftType newType argumentRaw)
    (Ty.weaken_subst_singleton rightType newType argumentRaw)
    (RawTerm.weaken_subst_singleton valueRaw argumentRaw)
    valueHEq

/-- Either-right injection preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_eitherInr_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {leftType rightType : Ty level scope}
    {valueRaw : RawTerm scope}
    (newType : Ty level scope)
    {argumentRaw : RawTerm scope}
    (argumentTerm : Term context newType argumentRaw)
    (valueTerm : Term context rightType valueRaw)
    (valueHEq :
      HEq
        (Term.subst (TermSubst.singleton argumentTerm)
          (Term.weaken newType valueTerm))
        valueTerm) :
    HEq
      (Term.subst (TermSubst.singleton argumentTerm)
        (Term.weaken newType
          (Term.eitherInr (leftType := leftType) valueTerm)))
      (Term.eitherInr (leftType := leftType) valueTerm) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.eitherInr_HEq_congr
    (Ty.weaken_subst_singleton leftType newType argumentRaw)
    (Ty.weaken_subst_singleton rightType newType argumentRaw)
    (RawTerm.weaken_subst_singleton valueRaw argumentRaw)
    valueHEq

/-- Interval negation preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_intervalOpp_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {innerRaw : RawTerm scope}
    (newType : Ty level scope)
    {argumentRaw : RawTerm scope}
    (argumentTerm : Term context newType argumentRaw)
    (innerTerm : Term context Ty.interval innerRaw)
    (innerHEq :
      HEq
        (Term.subst (TermSubst.singleton argumentTerm)
          (Term.weaken newType innerTerm))
        innerTerm) :
    HEq
      (Term.subst (TermSubst.singleton argumentTerm)
        (Term.weaken newType (Term.intervalOpp innerTerm)))
      (Term.intervalOpp innerTerm) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.intervalOpp_HEq_congr
    (RawTerm.weaken_subst_singleton innerRaw argumentRaw)
    innerHEq

/-- Interval meet preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_intervalMeet_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {leftRaw rightRaw : RawTerm scope}
    (newType : Ty level scope)
    {argumentRaw : RawTerm scope}
    (argumentTerm : Term context newType argumentRaw)
    (leftTerm : Term context Ty.interval leftRaw)
    (rightTerm : Term context Ty.interval rightRaw)
    (leftHEq :
      HEq
        (Term.subst (TermSubst.singleton argumentTerm)
          (Term.weaken newType leftTerm))
        leftTerm)
    (rightHEq :
      HEq
        (Term.subst (TermSubst.singleton argumentTerm)
          (Term.weaken newType rightTerm))
        rightTerm) :
    HEq
      (Term.subst (TermSubst.singleton argumentTerm)
        (Term.weaken newType (Term.intervalMeet leftTerm rightTerm)))
      (Term.intervalMeet leftTerm rightTerm) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.intervalMeet_HEq_congr
    (RawTerm.weaken_subst_singleton leftRaw argumentRaw)
    (RawTerm.weaken_subst_singleton rightRaw argumentRaw)
    leftHEq rightHEq

/-- Interval join preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_intervalJoin_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {leftRaw rightRaw : RawTerm scope}
    (newType : Ty level scope)
    {argumentRaw : RawTerm scope}
    (argumentTerm : Term context newType argumentRaw)
    (leftTerm : Term context Ty.interval leftRaw)
    (rightTerm : Term context Ty.interval rightRaw)
    (leftHEq :
      HEq
        (Term.subst (TermSubst.singleton argumentTerm)
          (Term.weaken newType leftTerm))
        leftTerm)
    (rightHEq :
      HEq
        (Term.subst (TermSubst.singleton argumentTerm)
          (Term.weaken newType rightTerm))
        rightTerm) :
    HEq
      (Term.subst (TermSubst.singleton argumentTerm)
        (Term.weaken newType (Term.intervalJoin leftTerm rightTerm)))
      (Term.intervalJoin leftTerm rightTerm) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.intervalJoin_HEq_congr
    (RawTerm.weaken_subst_singleton leftRaw argumentRaw)
    (RawTerm.weaken_subst_singleton rightRaw argumentRaw)
    leftHEq rightHEq

/-- Path lambda introduction preserves weaken-then-singleton collapse
under the lifted-singleton body premise. -/
theorem Term.weaken_subst_singleton_pathLam_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    (carrierType : Ty level scope)
    (leftEndpoint rightEndpoint : RawTerm scope)
    {bodyRaw : RawTerm (scope + 1)}
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (body : Term (context.cons Ty.interval) carrierType.weaken bodyRaw)
    (bodyHEq :
      HEq
        (Ty.weaken_subst_commute
          (Subst.singleton newType singletonRaw)
          (carrierType.rename RawRenaming.weaken) ▸
          Term.subst
            ((TermSubst.singleton singletonTerm).lift Ty.interval)
            (Ty.weaken_rename_commute RawRenaming.weaken carrierType ▸
              Term.rename
                ((TermRenaming.weakenStep context newType).lift Ty.interval)
                body))
        body) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.pathLam modeIsUnivalent carrierType leftEndpoint
            rightEndpoint body)))
      (Term.pathLam modeIsUnivalent carrierType leftEndpoint
        rightEndpoint body) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.pathLam_HEq_congr modeIsUnivalent
    (Ty.weaken_subst_singleton carrierType newType singletonRaw)
    (RawTerm.weaken_subst_singleton leftEndpoint singletonRaw)
    (RawTerm.weaken_subst_singleton rightEndpoint singletonRaw)
    (RawTerm.weaken_lift_subst_singleton_lift bodyRaw singletonRaw)
    bodyHEq

/-- Modal introduction preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_modIntro_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    (newType : Ty level scope)
    {argumentRaw : RawTerm scope}
    (argumentTerm : Term context newType argumentRaw)
    (innerTerm : Term context innerType innerRaw)
    (innerHEq :
      HEq
        (Term.subst (TermSubst.singleton argumentTerm)
          (Term.weaken newType innerTerm))
        innerTerm) :
    HEq
      (Term.subst (TermSubst.singleton argumentTerm)
        (Term.weaken newType (Term.modIntro innerTerm)))
      (Term.modIntro innerTerm) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.modIntro_HEq_congr
    (Ty.weaken_subst_singleton innerType newType argumentRaw)
    (RawTerm.weaken_subst_singleton innerRaw argumentRaw)
    innerHEq

/-- Modal elimination preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_modElim_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    (newType : Ty level scope)
    {argumentRaw : RawTerm scope}
    (argumentTerm : Term context newType argumentRaw)
    (innerTerm : Term context innerType innerRaw)
    (innerHEq :
      HEq
        (Term.subst (TermSubst.singleton argumentTerm)
          (Term.weaken newType innerTerm))
        innerTerm) :
    HEq
      (Term.subst (TermSubst.singleton argumentTerm)
        (Term.weaken newType (Term.modElim innerTerm)))
      (Term.modElim innerTerm) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.modElim_HEq_congr
    (Ty.weaken_subst_singleton innerType newType argumentRaw)
    (RawTerm.weaken_subst_singleton innerRaw argumentRaw)
    innerHEq

/-- Cumulativity subsumption preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_subsume_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    (newType : Ty level scope)
    {argumentRaw : RawTerm scope}
    (argumentTerm : Term context newType argumentRaw)
    (innerTerm : Term context innerType innerRaw)
    (innerHEq :
      HEq
        (Term.subst (TermSubst.singleton argumentTerm)
          (Term.weaken newType innerTerm))
        innerTerm) :
    HEq
      (Term.subst (TermSubst.singleton argumentTerm)
        (Term.weaken newType (Term.subsume innerTerm)))
      (Term.subsume innerTerm) := by
  simp only [Term.weaken, Term.rename, Term.subst]
  exact Term.subsume_HEq_congr
    (Ty.weaken_subst_singleton innerType newType argumentRaw)
    (RawTerm.weaken_subst_singleton innerRaw argumentRaw)
    innerHEq

end LeanFX2
