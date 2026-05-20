import LeanFX2.Term.HEqCongr.Compound.ApplicationsAndBinders
import LeanFX2.Term.Subst
import LeanFX2.Term.Pointwise.PointwiseAndCompositionInfrastructure.LiftCompose

/-! # LeanFX2.Term.Pointwise.ApplicationAndSigmaArms

weaken-subst-singleton arms for the application family (app, appPi) and
sigma family (pair, fst, snd) — the cast-heaviest introduction/elimination
forms in the cascade.

## Root status

Kernel — application and sigma arms of the Pointwise weaken-then-singleton
cascade. -/

namespace LeanFX2

/-- Non-dependent application preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_app_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {functionRaw argumentValueRaw : RawTerm scope}
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (functionTerm :
      Term context (Ty.arrow domainType codomainType) functionRaw)
    (argumentValue : Term context domainType argumentValueRaw)
    (functionHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType functionTerm))
        functionTerm)
    (argumentHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType argumentValue))
        argumentValue) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType (Term.app functionTerm argumentValue)))
      (Term.app functionTerm argumentValue) := by
  -- `Term.weaken` is `@[reducible]`, so the weaken-then-subst chain over
  -- `Term.app` reduces by iota (the `.app` arms of `Term.rename` and
  -- `Term.subst`) to a `Term.app` of the renamed/substituted subterms.
  -- Presenting that reduct via `show` avoids generating the full 78-arm
  -- equational unfolders that `simp only [Term.rename, Term.subst]` builds.
  show
    HEq
      (Term.app
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.rename (TermRenaming.weakenStep context newType)
            functionTerm))
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.rename (TermRenaming.weakenStep context newType)
            argumentValue)))
      (Term.app functionTerm argumentValue)
  exact Term.app_HEq_congr
    (Ty.weaken_subst_singleton domainType newType singletonRaw)
    (Ty.weaken_subst_singleton codomainType newType singletonRaw)
    (RawTerm.weaken_subst_singleton functionRaw singletonRaw)
    (RawTerm.weaken_subst_singleton argumentValueRaw singletonRaw)
    functionHEq argumentHEq

/-- Dependent function application preserves weaken-then-singleton
collapse. -/
theorem Term.weaken_subst_singleton_appPi_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType : Ty level scope}
    {codomainType : Ty level (scope + 1)}
    {functionRaw argumentRaw : RawTerm scope}
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (functionTerm :
      Term context (Ty.piTy domainType codomainType) functionRaw)
    (argumentTerm : Term context domainType argumentRaw)
    (functionHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType functionTerm))
        functionTerm)
    (argumentHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType argumentTerm))
        argumentTerm) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.appPi functionTerm argumentTerm)))
      (Term.appPi functionTerm argumentTerm) := by
  -- `Term.weaken` is `@[reducible]`; the `.appPi` arm of `Term.rename`
  -- carries a `subst0_rename_commute` cast.  Iota reduces the
  -- weaken-then-rename chain to that cast over a `Term.appPi` of renamed
  -- subterms.  `show` presents the reduct so we avoid the 78-arm
  -- equational unfolder that `simp only [Term.rename]` would build.
  show
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        ((Ty.subst0_rename_commute codomainType domainType
          argumentRaw RawRenaming.weaken).symm ▸
          Term.appPi
            (Term.rename (TermRenaming.weakenStep context newType)
              functionTerm)
            (Term.rename (TermRenaming.weakenStep context newType)
              argumentTerm)))
      (Term.appPi functionTerm argumentTerm)
  -- `Term.weaken` is `@[reducible]`, so the hypotheses already have the
  -- renamed shape definitionally; no `simpa` rewrite is required.
  have functionWithoutCastsHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.rename (TermRenaming.weakenStep context newType)
            functionTerm))
        functionTerm := functionHEq
  have argumentWithoutCastsHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.rename (TermRenaming.weakenStep context newType)
            argumentTerm))
        argumentTerm := argumentHEq
  have innerCastHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          ((Ty.subst0_rename_commute codomainType domainType
            argumentRaw RawRenaming.weaken).symm ▸
            Term.appPi
              (Term.rename (TermRenaming.weakenStep context newType)
                functionTerm)
              (Term.rename (TermRenaming.weakenStep context newType)
                argumentTerm)))
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.appPi
            (Term.rename (TermRenaming.weakenStep context newType)
              functionTerm)
            (Term.rename (TermRenaming.weakenStep context newType)
              argumentTerm))) := by
    exact Term.subst_type_eq_cast_heq
      (TermSubst.singleton singletonTerm)
      (Ty.subst0_rename_commute codomainType domainType
        argumentRaw RawRenaming.weaken).symm
      (Term.appPi
        (Term.rename (TermRenaming.weakenStep context newType)
          functionTerm)
        (Term.rename (TermRenaming.weakenStep context newType)
          argumentTerm))
  have appPiWithoutCastsHEq :
      HEq
        (Term.appPi
          (Term.subst (TermSubst.singleton singletonTerm)
            (Term.rename (TermRenaming.weakenStep context newType)
              functionTerm))
          (Term.subst (TermSubst.singleton singletonTerm)
            (Term.rename (TermRenaming.weakenStep context newType)
              argumentTerm)))
        (Term.appPi functionTerm argumentTerm) :=
    Term.appPi_HEq_congr
      (Ty.weaken_subst_singleton domainType newType singletonRaw)
      (Ty.weaken_lift_subst_singleton_lift codomainType newType singletonRaw)
      (RawTerm.weaken_subst_singleton functionRaw singletonRaw)
      (RawTerm.weaken_subst_singleton argumentRaw singletonRaw)
      functionWithoutCastsHEq argumentWithoutCastsHEq
  have outerCastHEq :
      HEq
        ((Ty.subst0_subst_commute
            (codomainType.rename RawRenaming.weaken.lift)
            (domainType.rename RawRenaming.weaken)
            (argumentRaw.rename RawRenaming.weaken)
            (Subst.singleton newType singletonRaw)).symm ▸
          Term.appPi
            (Term.subst (TermSubst.singleton singletonTerm)
              (Term.rename (TermRenaming.weakenStep context newType)
                functionTerm))
            (Term.subst (TermSubst.singleton singletonTerm)
              (Term.rename (TermRenaming.weakenStep context newType)
                argumentTerm)))
        (Term.appPi
          (Term.subst (TermSubst.singleton singletonTerm)
            (Term.rename (TermRenaming.weakenStep context newType)
              functionTerm))
          (Term.subst (TermSubst.singleton singletonTerm)
            (Term.rename (TermRenaming.weakenStep context newType)
              argumentTerm))) := by
    exact Term.type_eq_cast_heq
      (Ty.subst0_subst_commute
        (codomainType.rename RawRenaming.weaken.lift)
        (domainType.rename RawRenaming.weaken)
        (argumentRaw.rename RawRenaming.weaken)
        (Subst.singleton newType singletonRaw)).symm
      (Term.appPi
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.rename (TermRenaming.weakenStep context newType)
            functionTerm))
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.rename (TermRenaming.weakenStep context newType)
            argumentTerm)))
  exact HEq.trans innerCastHEq
    (HEq.trans outerCastHEq appPiWithoutCastsHEq)

/-- Sigma pair introduction preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_pair_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    {firstRaw secondRaw : RawTerm scope}
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (firstValue : Term context firstType firstRaw)
    (secondValue :
      Term context (secondType.subst0 firstType firstRaw) secondRaw)
    (firstHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType firstValue))
        firstValue)
    (secondHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType secondValue))
        secondValue) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.pair (secondType := secondType) firstValue secondValue)))
      (Term.pair (secondType := secondType) firstValue secondValue) := by
  -- `Term.weaken` is `@[reducible]`; the `.pair` arms of `Term.rename`
  -- and `Term.subst` each cast the second component (via
  -- `subst0_rename_commute` then `subst0_subst_commute`).  Iota reduces
  -- the weaken-then-subst chain to a `Term.pair` of the substituted
  -- first component and the doubly-cast substituted second component.
  -- `show` presents that reduct so we avoid the 78-arm equational
  -- unfolders for `Term.rename` / `Term.subst`.
  show
    HEq
      (Term.pair
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.rename (TermRenaming.weakenStep context newType)
            firstValue))
        ((Ty.subst0_subst_commute
            (secondType.rename RawRenaming.weaken.lift)
            (firstType.rename RawRenaming.weaken)
            (firstRaw.rename RawRenaming.weaken)
            (Subst.singleton newType singletonRaw)) ▸
          Term.subst (TermSubst.singleton singletonTerm)
            ((Ty.subst0_rename_commute secondType firstType firstRaw
              RawRenaming.weaken) ▸
              Term.rename (TermRenaming.weakenStep context newType)
                secondValue)))
      (Term.pair (secondType := secondType) firstValue secondValue)
  -- `Term.weaken` is `@[reducible]`, so this hypothesis already has the
  -- renamed shape definitionally; no `simpa` rewrite is required.
  have secondWithoutCastsHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.rename (TermRenaming.weakenStep context newType)
            secondValue))
        secondValue := secondHEq
  have secondInnerCastHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          ((Ty.subst0_rename_commute secondType firstType firstRaw
            RawRenaming.weaken) ▸
            Term.rename (TermRenaming.weakenStep context newType)
              secondValue))
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.rename (TermRenaming.weakenStep context newType)
            secondValue)) := by
    exact Term.subst_type_eq_cast_heq
      (TermSubst.singleton singletonTerm)
      (Ty.subst0_rename_commute secondType firstType firstRaw
        RawRenaming.weaken)
      (Term.rename (TermRenaming.weakenStep context newType) secondValue)
  have secondOuterCastHEq :
      HEq
        ((Ty.subst0_subst_commute
            (secondType.rename RawRenaming.weaken.lift)
            (firstType.rename RawRenaming.weaken)
            (firstRaw.rename RawRenaming.weaken)
            (Subst.singleton newType singletonRaw)) ▸
          Term.subst (TermSubst.singleton singletonTerm)
            ((Ty.subst0_rename_commute secondType firstType firstRaw
              RawRenaming.weaken) ▸
              Term.rename (TermRenaming.weakenStep context newType)
                secondValue))
        (Term.subst (TermSubst.singleton singletonTerm)
          ((Ty.subst0_rename_commute secondType firstType firstRaw
            RawRenaming.weaken) ▸
            Term.rename (TermRenaming.weakenStep context newType)
              secondValue)) := by
    exact Term.type_eq_cast_heq
      (Ty.subst0_subst_commute
        (secondType.rename RawRenaming.weaken.lift)
        (firstType.rename RawRenaming.weaken)
        (firstRaw.rename RawRenaming.weaken)
        (Subst.singleton newType singletonRaw))
      (Term.subst (TermSubst.singleton singletonTerm)
        ((Ty.subst0_rename_commute secondType firstType firstRaw
          RawRenaming.weaken) ▸
          Term.rename (TermRenaming.weakenStep context newType)
            secondValue))
  have secondCastsHEq :
      HEq
        ((Ty.subst0_subst_commute
            (secondType.rename RawRenaming.weaken.lift)
            (firstType.rename RawRenaming.weaken)
            (firstRaw.rename RawRenaming.weaken)
            (Subst.singleton newType singletonRaw)) ▸
          Term.subst (TermSubst.singleton singletonTerm)
            ((Ty.subst0_rename_commute secondType firstType firstRaw
              RawRenaming.weaken) ▸
              Term.rename (TermRenaming.weakenStep context newType)
                secondValue))
        secondValue :=
    HEq.trans secondOuterCastHEq
      (HEq.trans secondInnerCastHEq secondWithoutCastsHEq)
  exact Term.pair_HEq_congr
    (Ty.weaken_subst_singleton firstType newType singletonRaw)
    (Ty.weaken_lift_subst_singleton_lift secondType newType singletonRaw)
    (RawTerm.weaken_subst_singleton firstRaw singletonRaw)
    (RawTerm.weaken_subst_singleton secondRaw singletonRaw)
    firstHEq secondCastsHEq

/-- Sigma first projection preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_fst_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    {pairRaw : RawTerm scope}
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (pairTerm : Term context (Ty.sigmaTy firstType secondType) pairRaw)
    (pairHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType pairTerm))
        pairTerm) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType (Term.fst pairTerm)))
      (Term.fst pairTerm) := by
  -- `Term.fst` carries no type cast in either `Term.rename` or
  -- `Term.subst`, so the weaken-then-subst chain reduces by iota to a
  -- bare `Term.fst` of the renamed/substituted pair.  `show` presents
  -- that reduct without building the 78-arm equational unfolders.
  show
    HEq
      (Term.fst
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.rename (TermRenaming.weakenStep context newType)
            pairTerm)))
      (Term.fst pairTerm)
  exact Term.fst_HEq_congr
    (Ty.weaken_subst_singleton firstType newType singletonRaw)
    (Ty.weaken_lift_subst_singleton_lift secondType newType singletonRaw)
    (RawTerm.weaken_subst_singleton pairRaw singletonRaw)
    pairHEq

/-- Sigma second projection preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_snd_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    {pairRaw : RawTerm scope}
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (pairTerm : Term context (Ty.sigmaTy firstType secondType) pairRaw)
    (pairHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType pairTerm))
        pairTerm) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.snd (secondType := secondType) pairTerm)))
      (Term.snd (secondType := secondType) pairTerm) := by
  -- `Term.weaken` is `@[reducible]`; the `.snd` arm of `Term.rename`
  -- casts the result via `subst0_rename_commute (RawTerm.fst pairRaw)`.
  -- Iota reduces the weaken-then-rename chain to that cast over a
  -- `Term.snd` of the renamed pair.  `show` presents the reduct so we
  -- avoid the 78-arm equational unfolder that `simp only [Term.rename]`
  -- would build.
  show
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        ((Ty.subst0_rename_commute secondType firstType
          (RawTerm.fst pairRaw) RawRenaming.weaken).symm ▸
          Term.snd
            (Term.rename (TermRenaming.weakenStep context newType)
              pairTerm)))
      (Term.snd (secondType := secondType) pairTerm)
  -- `Term.weaken` is `@[reducible]`, so this hypothesis already has the
  -- renamed shape definitionally; no `simpa` rewrite is required.
  have pairWithoutCastsHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.rename (TermRenaming.weakenStep context newType)
            pairTerm))
        pairTerm := pairHEq
  have innerCastHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          ((Ty.subst0_rename_commute secondType firstType
            (RawTerm.fst pairRaw) RawRenaming.weaken).symm ▸
            Term.snd
              (Term.rename (TermRenaming.weakenStep context newType)
                pairTerm)))
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.snd
            (Term.rename (TermRenaming.weakenStep context newType)
              pairTerm))) := by
    exact Term.subst_type_eq_cast_heq
      (TermSubst.singleton singletonTerm)
      (Ty.subst0_rename_commute secondType firstType
        (RawTerm.fst pairRaw) RawRenaming.weaken).symm
      (Term.snd
        (Term.rename (TermRenaming.weakenStep context newType)
          pairTerm))
  have sndWithoutCastsHEq :
      HEq
        (Term.snd
          (Term.subst (TermSubst.singleton singletonTerm)
            (Term.rename (TermRenaming.weakenStep context newType)
              pairTerm)))
        (Term.snd (secondType := secondType) pairTerm) :=
    Term.snd_HEq_congr
      (Ty.weaken_subst_singleton firstType newType singletonRaw)
      (Ty.weaken_lift_subst_singleton_lift secondType newType singletonRaw)
      (RawTerm.weaken_subst_singleton pairRaw singletonRaw)
      pairWithoutCastsHEq
  have outerCastHEq :
      HEq
        ((Ty.subst0_subst_commute
            (secondType.rename RawRenaming.weaken.lift)
            (firstType.rename RawRenaming.weaken)
            (RawTerm.fst (pairRaw.rename RawRenaming.weaken))
            (Subst.singleton newType singletonRaw)).symm ▸
          Term.snd
            (Term.subst (TermSubst.singleton singletonTerm)
              (Term.rename (TermRenaming.weakenStep context newType)
                pairTerm)))
        (Term.snd
          (Term.subst (TermSubst.singleton singletonTerm)
            (Term.rename (TermRenaming.weakenStep context newType)
              pairTerm))) := by
    exact Term.type_eq_cast_heq
      (Ty.subst0_subst_commute
        (secondType.rename RawRenaming.weaken.lift)
        (firstType.rename RawRenaming.weaken)
        (RawTerm.fst (pairRaw.rename RawRenaming.weaken))
        (Subst.singleton newType singletonRaw)).symm
      (Term.snd
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.rename (TermRenaming.weakenStep context newType)
            pairTerm)))
  exact HEq.trans innerCastHEq
    (HEq.trans outerCastHEq sndWithoutCastsHEq)


end LeanFX2
