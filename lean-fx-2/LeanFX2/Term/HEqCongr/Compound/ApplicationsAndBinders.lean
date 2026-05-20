import LeanFX2.Term

/-! # Term/HEqCongr/Compound/ApplicationsAndBinders

HEq congruence lemmas for application, binder, and sigma-shaped
compound `Term` constructors. -/

namespace LeanFX2

/-- HEq congruence for `Term.app`.  When the domain/codomain types
and the function/argument raw forms differ only via Eq, two `Term.app`
values constructed from HEq sub-values are themselves HEq. -/
theorem Term.app_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {domainType1 domainType2 codomainType1 codomainType2 : Ty level scope}
    {functionRaw1 functionRaw2 argumentRaw1 argumentRaw2 : RawTerm scope}
    (domainEq : domainType1 = domainType2)
    (codomainEq : codomainType1 = codomainType2)
    (functionRawEq : functionRaw1 = functionRaw2)
    (argumentRawEq : argumentRaw1 = argumentRaw2)
    {function1 : Term context (Ty.arrow domainType1 codomainType1) functionRaw1}
    {function2 : Term context (Ty.arrow domainType2 codomainType2) functionRaw2}
    (functionHEq : HEq function1 function2)
    {argument1 : Term context domainType1 argumentRaw1}
    {argument2 : Term context domainType2 argumentRaw2}
    (argumentHEq : HEq argument1 argument2) :
    HEq (Term.app function1 argument1) (Term.app function2 argument2) := by
  subst domainEq
  subst codomainEq
  subst functionRawEq
  subst argumentRawEq
  cases functionHEq
  cases argumentHEq
  rfl

/-- HEq congruence for `Term.lam`.  The body's expected type involves
`codomainType.weaken`, which automatically aligns when codomainType
is substituted via the codomainEq hypothesis. -/
theorem Term.lam_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {domainType1 domainType2 codomainType1 codomainType2 : Ty level scope}
    {bodyRaw1 bodyRaw2 : RawTerm (scope + 1)}
    (domainEq : domainType1 = domainType2)
    (codomainEq : codomainType1 = codomainType2)
    (bodyRawEq : bodyRaw1 = bodyRaw2)
    {body1 : Term (context.cons domainType1) codomainType1.weaken bodyRaw1}
    {body2 : Term (context.cons domainType2) codomainType2.weaken bodyRaw2}
    (bodyHEq : HEq body1 body2) :
    HEq (Term.lam (codomainType := codomainType1) body1)
        (Term.lam (codomainType := codomainType2) body2) := by
  subst domainEq
  subst codomainEq
  subst bodyRawEq
  cases bodyHEq
  rfl

/-- HEq congruence for `Term.appPi`.  Source/target of dependent
application differ in their result type (via subst0 over the
argument's raw form), so HEq is essential here. -/
theorem Term.appPi_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {domainType1 domainType2 : Ty level scope}
    {codomainType1 codomainType2 : Ty level (scope + 1)}
    {functionRaw1 functionRaw2 argumentRaw1 argumentRaw2 : RawTerm scope}
    (domainEq : domainType1 = domainType2)
    (codomainEq : codomainType1 = codomainType2)
    (functionRawEq : functionRaw1 = functionRaw2)
    (argumentRawEq : argumentRaw1 = argumentRaw2)
    {function1 : Term context (Ty.piTy domainType1 codomainType1) functionRaw1}
    {function2 : Term context (Ty.piTy domainType2 codomainType2) functionRaw2}
    (functionHEq : HEq function1 function2)
    {argument1 : Term context domainType1 argumentRaw1}
    {argument2 : Term context domainType2 argumentRaw2}
    (argumentHEq : HEq argument1 argument2) :
    HEq (Term.appPi function1 argument1) (Term.appPi function2 argument2) := by
  subst domainEq
  subst codomainEq
  subst functionRawEq
  subst argumentRawEq
  cases functionHEq
  cases argumentHEq
  rfl

/-- HEq congruence for `Term.lamPi`.  The body's type is just
`codomainType` (no weaken -- Pi is dependent in the codomain). -/
theorem Term.lamPi_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {domainType1 domainType2 : Ty level scope}
    {codomainType1 codomainType2 : Ty level (scope + 1)}
    {bodyRaw1 bodyRaw2 : RawTerm (scope + 1)}
    (domainEq : domainType1 = domainType2)
    (codomainEq : codomainType1 = codomainType2)
    (bodyRawEq : bodyRaw1 = bodyRaw2)
    {body1 : Term (context.cons domainType1) codomainType1 bodyRaw1}
    {body2 : Term (context.cons domainType2) codomainType2 bodyRaw2}
    (bodyHEq : HEq body1 body2) :
    HEq (Term.lamPi (domainType := domainType1) body1)
        (Term.lamPi (domainType := domainType2) body2) := by
  subst domainEq
  subst codomainEq
  subst bodyRawEq
  cases bodyHEq
  rfl

/-- HEq congruence for `Term.pair`.  Second value's type depends on
the first via `subst0`, so this needs careful Eq alignment. -/
theorem Term.pair_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {firstType1 firstType2 : Ty level scope}
    {secondType1 secondType2 : Ty level (scope + 1)}
    {firstRaw1 firstRaw2 secondRaw1 secondRaw2 : RawTerm scope}
    (firstTypeEq : firstType1 = firstType2)
    (secondTypeEq : secondType1 = secondType2)
    (firstRawEq : firstRaw1 = firstRaw2)
    (secondRawEq : secondRaw1 = secondRaw2)
    {firstValue1 : Term context firstType1 firstRaw1}
    {firstValue2 : Term context firstType2 firstRaw2}
    (firstHEq : HEq firstValue1 firstValue2)
    {secondValue1 : Term context (secondType1.subst0 firstType1 firstRaw1) secondRaw1}
    {secondValue2 : Term context (secondType2.subst0 firstType2 firstRaw2) secondRaw2}
    (secondHEq : HEq secondValue1 secondValue2) :
    HEq (Term.pair (secondType := secondType1) firstValue1 secondValue1)
        (Term.pair (secondType := secondType2) firstValue2 secondValue2) := by
  subst firstTypeEq
  subst secondTypeEq
  subst firstRawEq
  subst secondRawEq
  cases firstHEq
  cases secondHEq
  rfl

/-- HEq congruence for `Term.fst`. -/
theorem Term.fst_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {firstType1 firstType2 : Ty level scope}
    {secondType1 secondType2 : Ty level (scope + 1)}
    {pairRaw1 pairRaw2 : RawTerm scope}
    (firstTypeEq : firstType1 = firstType2)
    (secondTypeEq : secondType1 = secondType2)
    (pairRawEq : pairRaw1 = pairRaw2)
    {pair1 : Term context (Ty.sigmaTy firstType1 secondType1) pairRaw1}
    {pair2 : Term context (Ty.sigmaTy firstType2 secondType2) pairRaw2}
    (pairHEq : HEq pair1 pair2) :
    HEq (Term.fst (secondType := secondType1) pair1)
        (Term.fst (secondType := secondType2) pair2) := by
  subst firstTypeEq
  subst secondTypeEq
  subst pairRawEq
  cases pairHEq
  rfl

/-- HEq congruence for `Term.snd`.  The result type uses
`subst0 ... (RawTerm.fst pairRaw)`, so pairRaw differences propagate
to the output type -- HEq accommodates this. -/
theorem Term.snd_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {firstType1 firstType2 : Ty level scope}
    {secondType1 secondType2 : Ty level (scope + 1)}
    {pairRaw1 pairRaw2 : RawTerm scope}
    (firstTypeEq : firstType1 = firstType2)
    (secondTypeEq : secondType1 = secondType2)
    (pairRawEq : pairRaw1 = pairRaw2)
    {pair1 : Term context (Ty.sigmaTy firstType1 secondType1) pairRaw1}
    {pair2 : Term context (Ty.sigmaTy firstType2 secondType2) pairRaw2}
    (pairHEq : HEq pair1 pair2) :
    HEq (Term.snd (secondType := secondType1) pair1)
        (Term.snd (secondType := secondType2) pair2) := by
  subst firstTypeEq
  subst secondTypeEq
  subst pairRawEq
  cases pairHEq
  rfl

end LeanFX2
