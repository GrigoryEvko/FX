import LeanFX2.Term

/-! # Term/HEqCongr — HEq congruence lemmas for Term constructors

When two raw-aware Term values have indices that differ via Eq (Ty
indices, RawTerm indices), HEq lets us state "these are equal modulo
Type alignment".  These congruence lemmas are the building blocks
for the HEq cascades in Reduction/Compat (rename / subst preserve
β-redex shape) and for the typed-confluence cd_lemma bridge.

## Pattern

Each lemma:
1. Quantifies over two parallel sets of indices (LHS and RHS)
2. Takes Eq witnesses for each varying index
3. Takes HEq witnesses for sub-Term values (whose indices may
   differ before the Eqs are applied)
4. Produces HEq for the constructed Term

The proof technique is uniform:
* `subst` each Eq to align the indices
* After alignment, HEq sub-values become Eq via `eq_of_heq`
* `cases` the resulting Eqs to replace LHS by RHS
* Conclude with `rfl` (HEq.refl since both sides are now identical)

## Zero-axiom discipline

`subst`, `cases` on Eq, and `eq_of_heq` are all axiom-free in Lean 4
(they use the Eq.casesOn / HEq.casesOn structural eliminators).  Each
lemma is verified zero-axiom by an audit gate.
-/

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
`codomainType` (no weaken — Π is dependent in the codomain). -/
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
to the output type — HEq accommodates this. -/
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

/-- HEq congruence for `Term.boolElim`. -/
theorem Term.boolElim_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {motiveType1 motiveType2 : Ty level (scope + 1)}
    {scrutineeRaw1 scrutineeRaw2 thenRaw1 thenRaw2 elseRaw1 elseRaw2 : RawTerm scope}
    (motiveEq : motiveType1 = motiveType2)
    (scrutineeRawEq : scrutineeRaw1 = scrutineeRaw2)
    (thenRawEq : thenRaw1 = thenRaw2)
    (elseRawEq : elseRaw1 = elseRaw2)
    {scrutinee1 : Term context Ty.bool scrutineeRaw1}
    {scrutinee2 : Term context Ty.bool scrutineeRaw2}
    (scrutineeHEq : HEq scrutinee1 scrutinee2)
    {thenBranch1 :
      Term context (motiveType1.subst0 Ty.bool RawTerm.boolTrue) thenRaw1}
    {thenBranch2 :
      Term context (motiveType2.subst0 Ty.bool RawTerm.boolTrue) thenRaw2}
    (thenHEq : HEq thenBranch1 thenBranch2)
    {elseBranch1 :
      Term context (motiveType1.subst0 Ty.bool RawTerm.boolFalse) elseRaw1}
    {elseBranch2 :
      Term context (motiveType2.subst0 Ty.bool RawTerm.boolFalse) elseRaw2}
    (elseHEq : HEq elseBranch1 elseBranch2) :
    HEq (Term.boolElim scrutinee1 thenBranch1 elseBranch1)
        (Term.boolElim scrutinee2 thenBranch2 elseBranch2) := by
  subst motiveEq
  subst scrutineeRawEq
  subst thenRawEq
  subst elseRawEq
  cases scrutineeHEq
  cases thenHEq
  cases elseHEq
  rfl

/-- HEq congruence for `Term.natSucc`. -/
theorem Term.natSucc_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {predecessorRaw1 predecessorRaw2 : RawTerm scope}
    (rawEq : predecessorRaw1 = predecessorRaw2)
    {predecessor1 : Term context Ty.nat predecessorRaw1}
    {predecessor2 : Term context Ty.nat predecessorRaw2}
    (predecessorHEq : HEq predecessor1 predecessor2) :
    HEq (Term.natSucc predecessor1) (Term.natSucc predecessor2) := by
  subst rawEq
  cases predecessorHEq
  rfl

/-- HEq congruence for `Term.natElim`. -/
theorem Term.natElim_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {motiveType1 motiveType2 : Ty level scope}
    {scrutineeRaw1 scrutineeRaw2 zeroRaw1 zeroRaw2 succRaw1 succRaw2 : RawTerm scope}
    (motiveEq : motiveType1 = motiveType2)
    (scrutineeRawEq : scrutineeRaw1 = scrutineeRaw2)
    (zeroRawEq : zeroRaw1 = zeroRaw2)
    (succRawEq : succRaw1 = succRaw2)
    {scrutinee1 : Term context Ty.nat scrutineeRaw1}
    {scrutinee2 : Term context Ty.nat scrutineeRaw2}
    (scrutineeHEq : HEq scrutinee1 scrutinee2)
    {zeroBranch1 : Term context motiveType1 zeroRaw1}
    {zeroBranch2 : Term context motiveType2 zeroRaw2}
    (zeroHEq : HEq zeroBranch1 zeroBranch2)
    {succBranch1 : Term context (Ty.arrow Ty.nat motiveType1) succRaw1}
    {succBranch2 : Term context (Ty.arrow Ty.nat motiveType2) succRaw2}
    (succHEq : HEq succBranch1 succBranch2) :
    HEq (Term.natElim scrutinee1 zeroBranch1 succBranch1)
        (Term.natElim scrutinee2 zeroBranch2 succBranch2) := by
  subst motiveEq
  subst scrutineeRawEq
  subst zeroRawEq
  subst succRawEq
  cases scrutineeHEq
  cases zeroHEq
  cases succHEq
  rfl

/-- HEq congruence for `Term.natRec`. -/
theorem Term.natRec_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {motiveType1 motiveType2 : Ty level scope}
    {scrutineeRaw1 scrutineeRaw2 zeroRaw1 zeroRaw2 succRaw1 succRaw2 : RawTerm scope}
    (motiveEq : motiveType1 = motiveType2)
    (scrutineeRawEq : scrutineeRaw1 = scrutineeRaw2)
    (zeroRawEq : zeroRaw1 = zeroRaw2)
    (succRawEq : succRaw1 = succRaw2)
    {scrutinee1 : Term context Ty.nat scrutineeRaw1}
    {scrutinee2 : Term context Ty.nat scrutineeRaw2}
    (scrutineeHEq : HEq scrutinee1 scrutinee2)
    {zeroBranch1 : Term context motiveType1 zeroRaw1}
    {zeroBranch2 : Term context motiveType2 zeroRaw2}
    (zeroHEq : HEq zeroBranch1 zeroBranch2)
    {succBranch1 : Term context (Ty.arrow Ty.nat (Ty.arrow motiveType1 motiveType1)) succRaw1}
    {succBranch2 : Term context (Ty.arrow Ty.nat (Ty.arrow motiveType2 motiveType2)) succRaw2}
    (succHEq : HEq succBranch1 succBranch2) :
    HEq (Term.natRec scrutinee1 zeroBranch1 succBranch1)
        (Term.natRec scrutinee2 zeroBranch2 succBranch2) := by
  subst motiveEq
  subst scrutineeRawEq
  subst zeroRawEq
  subst succRawEq
  cases scrutineeHEq
  cases zeroHEq
  cases succHEq
  rfl

/-- HEq congruence for `Term.listCons`. -/
theorem Term.listCons_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {elementType1 elementType2 : Ty level scope}
    {headRaw1 headRaw2 tailRaw1 tailRaw2 : RawTerm scope}
    (elementEq : elementType1 = elementType2)
    (headRawEq : headRaw1 = headRaw2)
    (tailRawEq : tailRaw1 = tailRaw2)
    {head1 : Term context elementType1 headRaw1}
    {head2 : Term context elementType2 headRaw2}
    (headHEq : HEq head1 head2)
    {tail1 : Term context (Ty.listType elementType1) tailRaw1}
    {tail2 : Term context (Ty.listType elementType2) tailRaw2}
    (tailHEq : HEq tail1 tail2) :
    HEq (Term.listCons head1 tail1) (Term.listCons head2 tail2) := by
  subst elementEq
  subst headRawEq
  subst tailRawEq
  cases headHEq
  cases tailHEq
  rfl

/-- HEq congruence for `Term.listElim`. -/
theorem Term.listElim_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {elementType1 elementType2 motiveType1 motiveType2 : Ty level scope}
    {scrutineeRaw1 scrutineeRaw2 nilRaw1 nilRaw2 consRaw1 consRaw2 : RawTerm scope}
    (elementEq : elementType1 = elementType2)
    (motiveEq : motiveType1 = motiveType2)
    (scrutineeRawEq : scrutineeRaw1 = scrutineeRaw2)
    (nilRawEq : nilRaw1 = nilRaw2)
    (consRawEq : consRaw1 = consRaw2)
    {scrutinee1 : Term context (Ty.listType elementType1) scrutineeRaw1}
    {scrutinee2 : Term context (Ty.listType elementType2) scrutineeRaw2}
    (scrutineeHEq : HEq scrutinee1 scrutinee2)
    {nilBranch1 : Term context motiveType1 nilRaw1}
    {nilBranch2 : Term context motiveType2 nilRaw2}
    (nilHEq : HEq nilBranch1 nilBranch2)
    {consBranch1 : Term context (Ty.arrow elementType1 (Ty.arrow (Ty.listType elementType1) motiveType1)) consRaw1}
    {consBranch2 : Term context (Ty.arrow elementType2 (Ty.arrow (Ty.listType elementType2) motiveType2)) consRaw2}
    (consHEq : HEq consBranch1 consBranch2) :
    HEq (Term.listElim scrutinee1 nilBranch1 consBranch1)
        (Term.listElim scrutinee2 nilBranch2 consBranch2) := by
  subst elementEq
  subst motiveEq
  subst scrutineeRawEq
  subst nilRawEq
  subst consRawEq
  cases scrutineeHEq
  cases nilHEq
  cases consHEq
  rfl

/-- HEq congruence for `Term.optionSome`. -/
theorem Term.optionSome_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {elementType1 elementType2 : Ty level scope}
    {valueRaw1 valueRaw2 : RawTerm scope}
    (elementEq : elementType1 = elementType2)
    (valueRawEq : valueRaw1 = valueRaw2)
    {value1 : Term context elementType1 valueRaw1}
    {value2 : Term context elementType2 valueRaw2}
    (valueHEq : HEq value1 value2) :
    HEq (Term.optionSome value1) (Term.optionSome value2) := by
  subst elementEq
  subst valueRawEq
  cases valueHEq
  rfl

/-- HEq congruence for `Term.optionMatch`. -/
theorem Term.optionMatch_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {elementType1 elementType2 motiveType1 motiveType2 : Ty level scope}
    {scrutineeRaw1 scrutineeRaw2 noneRaw1 noneRaw2 someRaw1 someRaw2 : RawTerm scope}
    (elementEq : elementType1 = elementType2)
    (motiveEq : motiveType1 = motiveType2)
    (scrutineeRawEq : scrutineeRaw1 = scrutineeRaw2)
    (noneRawEq : noneRaw1 = noneRaw2)
    (someRawEq : someRaw1 = someRaw2)
    {scrutinee1 : Term context (Ty.optionType elementType1) scrutineeRaw1}
    {scrutinee2 : Term context (Ty.optionType elementType2) scrutineeRaw2}
    (scrutineeHEq : HEq scrutinee1 scrutinee2)
    {noneBranch1 : Term context motiveType1 noneRaw1}
    {noneBranch2 : Term context motiveType2 noneRaw2}
    (noneHEq : HEq noneBranch1 noneBranch2)
    {someBranch1 : Term context (Ty.arrow elementType1 motiveType1) someRaw1}
    {someBranch2 : Term context (Ty.arrow elementType2 motiveType2) someRaw2}
    (someHEq : HEq someBranch1 someBranch2) :
    HEq (Term.optionMatch scrutinee1 noneBranch1 someBranch1)
        (Term.optionMatch scrutinee2 noneBranch2 someBranch2) := by
  subst elementEq
  subst motiveEq
  subst scrutineeRawEq
  subst noneRawEq
  subst someRawEq
  cases scrutineeHEq
  cases noneHEq
  cases someHEq
  rfl

/-- HEq congruence for `Term.eitherInl`. -/
theorem Term.eitherInl_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {leftType1 leftType2 rightType1 rightType2 : Ty level scope}
    {valueRaw1 valueRaw2 : RawTerm scope}
    (leftEq : leftType1 = leftType2)
    (rightEq : rightType1 = rightType2)
    (valueRawEq : valueRaw1 = valueRaw2)
    {value1 : Term context leftType1 valueRaw1}
    {value2 : Term context leftType2 valueRaw2}
    (valueHEq : HEq value1 value2) :
    HEq (Term.eitherInl (rightType := rightType1) value1)
        (Term.eitherInl (rightType := rightType2) value2) := by
  subst leftEq
  subst rightEq
  subst valueRawEq
  cases valueHEq
  rfl

/-- HEq congruence for `Term.eitherInr`. -/
theorem Term.eitherInr_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {leftType1 leftType2 rightType1 rightType2 : Ty level scope}
    {valueRaw1 valueRaw2 : RawTerm scope}
    (leftEq : leftType1 = leftType2)
    (rightEq : rightType1 = rightType2)
    (valueRawEq : valueRaw1 = valueRaw2)
    {value1 : Term context rightType1 valueRaw1}
    {value2 : Term context rightType2 valueRaw2}
    (valueHEq : HEq value1 value2) :
    HEq (Term.eitherInr (leftType := leftType1) value1)
        (Term.eitherInr (leftType := leftType2) value2) := by
  subst leftEq
  subst rightEq
  subst valueRawEq
  cases valueHEq
  rfl

/-- HEq congruence for `Term.eitherMatch`. -/
theorem Term.eitherMatch_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {leftType1 leftType2 rightType1 rightType2 motiveType1 motiveType2 : Ty level scope}
    {scrutineeRaw1 scrutineeRaw2 leftRaw1 leftRaw2 rightRaw1 rightRaw2 : RawTerm scope}
    (leftEq : leftType1 = leftType2)
    (rightEq : rightType1 = rightType2)
    (motiveEq : motiveType1 = motiveType2)
    (scrutineeRawEq : scrutineeRaw1 = scrutineeRaw2)
    (leftRawEq : leftRaw1 = leftRaw2)
    (rightRawEq : rightRaw1 = rightRaw2)
    {scrutinee1 : Term context (Ty.eitherType leftType1 rightType1) scrutineeRaw1}
    {scrutinee2 : Term context (Ty.eitherType leftType2 rightType2) scrutineeRaw2}
    (scrutineeHEq : HEq scrutinee1 scrutinee2)
    {leftBranch1 : Term context (Ty.arrow leftType1 motiveType1) leftRaw1}
    {leftBranch2 : Term context (Ty.arrow leftType2 motiveType2) leftRaw2}
    (leftBranchHEq : HEq leftBranch1 leftBranch2)
    {rightBranch1 : Term context (Ty.arrow rightType1 motiveType1) rightRaw1}
    {rightBranch2 : Term context (Ty.arrow rightType2 motiveType2) rightRaw2}
    (rightBranchHEq : HEq rightBranch1 rightBranch2) :
    HEq (Term.eitherMatch scrutinee1 leftBranch1 rightBranch1)
        (Term.eitherMatch scrutinee2 leftBranch2 rightBranch2) := by
  subst leftEq
  subst rightEq
  subst motiveEq
  subst scrutineeRawEq
  subst leftRawEq
  subst rightRawEq
  cases scrutineeHEq
  cases leftBranchHEq
  cases rightBranchHEq
  rfl

/-- HEq congruence for `Term.refl`.  Both arguments (carrier type and
raw witness) are explicit.  This is unique among Term ctors because
the type Ty.id depends on the rawWitness in two positions
(left and right endpoint). -/
theorem Term.refl_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {carrier1 carrier2 : Ty level scope}
    {rawWitness1 rawWitness2 : RawTerm scope}
    (carrierEq : carrier1 = carrier2)
    (rawWitnessEq : rawWitness1 = rawWitness2) :
    HEq (Term.refl (context := context) carrier1 rawWitness1)
        (Term.refl (context := context) carrier2 rawWitness2) := by
  subst carrierEq
  subst rawWitnessEq
  rfl

/-- HEq congruence for `Term.idJ`. -/
theorem Term.idJ_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {carrier1 carrier2 : Ty level scope}
    {leftEndpoint1 leftEndpoint2 rightEndpoint1 rightEndpoint2 : RawTerm scope}
    {motiveType1 motiveType2 : Ty level scope}
    {baseRaw1 baseRaw2 witnessRaw1 witnessRaw2 : RawTerm scope}
    (carrierEq : carrier1 = carrier2)
    (leftEq : leftEndpoint1 = leftEndpoint2)
    (rightEq : rightEndpoint1 = rightEndpoint2)
    (motiveEq : motiveType1 = motiveType2)
    (baseRawEq : baseRaw1 = baseRaw2)
    (witnessRawEq : witnessRaw1 = witnessRaw2)
    {baseCase1 : Term context motiveType1 baseRaw1}
    {baseCase2 : Term context motiveType2 baseRaw2}
    (baseCaseHEq : HEq baseCase1 baseCase2)
    {witness1 : Term context (Ty.id carrier1 leftEndpoint1 rightEndpoint1) witnessRaw1}
    {witness2 : Term context (Ty.id carrier2 leftEndpoint2 rightEndpoint2) witnessRaw2}
    (witnessHEq : HEq witness1 witness2) :
    HEq (Term.idJ baseCase1 witness1) (Term.idJ baseCase2 witness2) := by
  subst carrierEq
  subst leftEq
  subst rightEq
  subst motiveEq
  subst baseRawEq
  subst witnessRawEq
  cases baseCaseHEq
  cases witnessHEq
  rfl

/-- HEq congruence for `Term.modIntro`. -/
theorem Term.modIntro_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {innerType1 innerType2 : Ty level scope}
    {innerRaw1 innerRaw2 : RawTerm scope}
    (innerTypeEq : innerType1 = innerType2)
    (innerRawEq : innerRaw1 = innerRaw2)
    {inner1 : Term context innerType1 innerRaw1}
    {inner2 : Term context innerType2 innerRaw2}
    (innerHEq : HEq inner1 inner2) :
    HEq (Term.modIntro inner1) (Term.modIntro inner2) := by
  subst innerTypeEq
  subst innerRawEq
  cases innerHEq
  rfl

/-- HEq congruence for `Term.modElim`. -/
theorem Term.modElim_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {innerType1 innerType2 : Ty level scope}
    {innerRaw1 innerRaw2 : RawTerm scope}
    (innerTypeEq : innerType1 = innerType2)
    (innerRawEq : innerRaw1 = innerRaw2)
    {inner1 : Term context innerType1 innerRaw1}
    {inner2 : Term context innerType2 innerRaw2}
    (innerHEq : HEq inner1 inner2) :
    HEq (Term.modElim inner1) (Term.modElim inner2) := by
  subst innerTypeEq
  subst innerRawEq
  cases innerHEq
  rfl

/-- HEq congruence for `Term.subsume`. -/
theorem Term.subsume_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {innerType1 innerType2 : Ty level scope}
    {innerRaw1 innerRaw2 : RawTerm scope}
    (innerTypeEq : innerType1 = innerType2)
    (innerRawEq : innerRaw1 = innerRaw2)
    {inner1 : Term context innerType1 innerRaw1}
    {inner2 : Term context innerType2 innerRaw2}
    (innerHEq : HEq inner1 inner2) :
    HEq (Term.subsume inner1) (Term.subsume inner2) := by
  subst innerTypeEq
  subst innerRawEq
  cases innerHEq
  rfl

/-- HEq congruence for `Term.cumulUp`. -/
theorem Term.cumulUp_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {lowerLevel higherLevel : UniverseLevel}
    {cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat}
    {levelLeLow : lowerLevel.toNat + 1 ≤ level}
    {levelLeHigh : higherLevel.toNat + 1 ≤ level}
    {codeRaw1 codeRaw2 : RawTerm scope}
    (codeRawEq : codeRaw1 = codeRaw2)
    {typeCode1 : Term context (Ty.universe lowerLevel levelLeLow) codeRaw1}
    {typeCode2 : Term context (Ty.universe lowerLevel levelLeLow) codeRaw2}
    (typeCodeHEq : HEq typeCode1 typeCode2) :
    HEq
      (Term.cumulUp lowerLevel higherLevel cumulMonotone levelLeLow
        levelLeHigh typeCode1)
      (Term.cumulUp lowerLevel higherLevel cumulMonotone levelLeLow
        levelLeHigh typeCode2) := by
  subst codeRawEq
  cases typeCodeHEq
  rfl

/-- HEq congruence for the canonical identity equivalence. -/
theorem Term.equivReflId_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {carrier1 carrier2 : Ty level scope}
    (carrierEq : carrier1 = carrier2) :
    HEq (Term.equivReflId (context := context) carrier1)
      (Term.equivReflId (context := context) carrier2) := by
  subst carrierEq
  rfl

/-- HEq congruence for canonical funext reflexivity. -/
theorem Term.funextRefl_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {domainType1 domainType2 codomainType1 codomainType2 : Ty level scope}
    {applyRaw1 applyRaw2 : RawTerm (scope + 1)}
    (domainEq : domainType1 = domainType2)
    (codomainEq : codomainType1 = codomainType2)
    (applyRawEq : applyRaw1 = applyRaw2) :
    HEq
      (Term.funextRefl (context := context) domainType1 codomainType1
        applyRaw1)
      (Term.funextRefl (context := context) domainType2 codomainType2
        applyRaw2) := by
  subst domainEq
  subst codomainEq
  subst applyRawEq
  rfl

/-- HEq congruence for the Id-typed identity-equivalence witness. -/
theorem Term.equivReflIdAtId_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {innerLevel : UniverseLevel}
    {innerLevelLt : innerLevel.toNat + 1 ≤ level}
    {carrier1 carrier2 : Ty level scope}
    {carrierRaw1 carrierRaw2 : RawTerm scope}
    (carrierEq : carrier1 = carrier2)
    (carrierRawEq : carrierRaw1 = carrierRaw2) :
    HEq
      (Term.equivReflIdAtId (context := context) innerLevel innerLevelLt
        carrier1 carrierRaw1)
      (Term.equivReflIdAtId (context := context) innerLevel innerLevelLt
        carrier2 carrierRaw2) := by
  subst carrierEq
  subst carrierRawEq
  rfl

/-- HEq congruence for the Id-typed funext witness. -/
theorem Term.funextReflAtId_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {domainType1 domainType2 codomainType1 codomainType2 : Ty level scope}
    {applyRaw1 applyRaw2 : RawTerm (scope + 1)}
    (domainEq : domainType1 = domainType2)
    (codomainEq : codomainType1 = codomainType2)
    (applyRawEq : applyRaw1 = applyRaw2) :
    HEq
      (Term.funextReflAtId (context := context) domainType1 codomainType1
        applyRaw1)
      (Term.funextReflAtId (context := context) domainType2 codomainType2
        applyRaw2) := by
  subst domainEq
  subst codomainEq
  subst applyRawEq
  rfl

/-- HEq congruence for univalence β extraction. -/
theorem Term.uaToEquiv_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {innerLevel : UniverseLevel}
    {innerLevelLt : innerLevel.toNat + 1 ≤ level}
    {leftTy1 leftTy2 rightTy1 rightTy2 : Ty level scope}
    {leftTyRaw1 leftTyRaw2 rightTyRaw1 rightTyRaw2 proofRaw1 proofRaw2 :
      RawTerm scope}
    (leftTyEq : leftTy1 = leftTy2)
    (rightTyEq : rightTy1 = rightTy2)
    (leftTyRawEq : leftTyRaw1 = leftTyRaw2)
    (rightTyRawEq : rightTyRaw1 = rightTyRaw2)
    (proofRawEq : proofRaw1 = proofRaw2)
    {proof1 :
      Term context
        (Ty.id (Ty.universe innerLevel innerLevelLt) leftTyRaw1 rightTyRaw1)
        proofRaw1}
    {proof2 :
      Term context
        (Ty.id (Ty.universe innerLevel innerLevelLt) leftTyRaw2 rightTyRaw2)
        proofRaw2}
    (proofHEq : HEq proof1 proof2) :
    HEq
      (Term.uaToEquiv innerLevel innerLevelLt leftTy1 rightTy1
        leftTyRaw1 rightTyRaw1 proof1)
      (Term.uaToEquiv innerLevel innerLevelLt leftTy2 rightTy2
        leftTyRaw2 rightTyRaw2 proof2) := by
  subst leftTyEq
  subst rightTyEq
  subst leftTyRawEq
  subst rightTyRawEq
  subst proofRawEq
  cases proofHEq
  rfl

/-- HEq congruence for univalence β application. -/
theorem Term.equivApply_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {carrierA1 carrierA2 carrierB1 carrierB2 : Ty level scope}
    {equivRaw1 equivRaw2 argumentRaw1 argumentRaw2 : RawTerm scope}
    (carrierAEq : carrierA1 = carrierA2)
    (carrierBEq : carrierB1 = carrierB2)
    (equivRawEq : equivRaw1 = equivRaw2)
    (argumentRawEq : argumentRaw1 = argumentRaw2)
    {equivTerm1 : Term context (Ty.equiv carrierA1 carrierB1) equivRaw1}
    {equivTerm2 : Term context (Ty.equiv carrierA2 carrierB2) equivRaw2}
    (equivHEq : HEq equivTerm1 equivTerm2)
    {argumentTerm1 : Term context carrierA1 argumentRaw1}
    {argumentTerm2 : Term context carrierA2 argumentRaw2}
    (argumentHEq : HEq argumentTerm1 argumentTerm2) :
    HEq (Term.equivApply equivTerm1 argumentTerm1)
      (Term.equivApply equivTerm2 argumentTerm2) := by
  subst carrierAEq
  subst carrierBEq
  subst equivRawEq
  subst argumentRawEq
  cases equivHEq
  cases argumentHEq
  rfl

/-- HEq congruence for variables at equal positions. -/
theorem Term.var_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {position1 position2 : Fin scope}
    (positionEq : position1 = position2) :
    HEq (Term.var (context := context) position1)
      (Term.var (context := context) position2) := by
  subst positionEq
  rfl

/-- HEq congruence for `Term.unit`. -/
theorem Term.unit_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope} :
    HEq (Term.unit (context := context)) (Term.unit (context := context)) := by
  rfl

/-- HEq congruence for `Term.boolTrue`. -/
theorem Term.boolTrue_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope} :
    HEq (Term.boolTrue (context := context))
      (Term.boolTrue (context := context)) := by
  rfl

/-- HEq congruence for `Term.boolFalse`. -/
theorem Term.boolFalse_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope} :
    HEq (Term.boolFalse (context := context))
      (Term.boolFalse (context := context)) := by
  rfl

/-- HEq congruence for `Term.natZero`. -/
theorem Term.natZero_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope} :
    HEq (Term.natZero (context := context))
      (Term.natZero (context := context)) := by
  rfl

/-- HEq congruence for `Term.listNil`. -/
theorem Term.listNil_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {elementType1 elementType2 : Ty level scope}
    (elementTypeEq : elementType1 = elementType2) :
    HEq (Term.listNil (context := context) (elementType := elementType1))
      (Term.listNil (context := context) (elementType := elementType2)) := by
  subst elementTypeEq
  rfl

/-- HEq congruence for `Term.optionNone`. -/
theorem Term.optionNone_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {elementType1 elementType2 : Ty level scope}
    (elementTypeEq : elementType1 = elementType2) :
    HEq (Term.optionNone (context := context) (elementType := elementType1))
      (Term.optionNone (context := context) (elementType := elementType2)) := by
  subst elementTypeEq
  rfl

/-- HEq congruence for `Term.interval0`. -/
theorem Term.interval0_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope} :
    HEq (Term.interval0 (context := context))
      (Term.interval0 (context := context)) := by
  rfl

/-- HEq congruence for `Term.interval1`. -/
theorem Term.interval1_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope} :
    HEq (Term.interval1 (context := context))
      (Term.interval1 (context := context)) := by
  rfl

/-- HEq congruence for interval negation. -/
theorem Term.intervalOpp_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {innerRaw1 innerRaw2 : RawTerm scope}
    (innerRawEq : innerRaw1 = innerRaw2)
    {innerValue1 : Term context Ty.interval innerRaw1}
    {innerValue2 : Term context Ty.interval innerRaw2}
    (innerValueHEq : HEq innerValue1 innerValue2) :
    HEq (Term.intervalOpp innerValue1) (Term.intervalOpp innerValue2) := by
  subst innerRawEq
  cases innerValueHEq
  rfl

/-- HEq congruence for interval meet. -/
theorem Term.intervalMeet_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {leftRaw1 leftRaw2 rightRaw1 rightRaw2 : RawTerm scope}
    (leftRawEq : leftRaw1 = leftRaw2)
    (rightRawEq : rightRaw1 = rightRaw2)
    {leftValue1 : Term context Ty.interval leftRaw1}
    {leftValue2 : Term context Ty.interval leftRaw2}
    (leftValueHEq : HEq leftValue1 leftValue2)
    {rightValue1 : Term context Ty.interval rightRaw1}
    {rightValue2 : Term context Ty.interval rightRaw2}
    (rightValueHEq : HEq rightValue1 rightValue2) :
    HEq (Term.intervalMeet leftValue1 rightValue1)
      (Term.intervalMeet leftValue2 rightValue2) := by
  subst leftRawEq
  subst rightRawEq
  cases leftValueHEq
  cases rightValueHEq
  rfl

/-- HEq congruence for interval join. -/
theorem Term.intervalJoin_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {leftRaw1 leftRaw2 rightRaw1 rightRaw2 : RawTerm scope}
    (leftRawEq : leftRaw1 = leftRaw2)
    (rightRawEq : rightRaw1 = rightRaw2)
    {leftValue1 : Term context Ty.interval leftRaw1}
    {leftValue2 : Term context Ty.interval leftRaw2}
    (leftValueHEq : HEq leftValue1 leftValue2)
    {rightValue1 : Term context Ty.interval rightRaw1}
    {rightValue2 : Term context Ty.interval rightRaw2}
    (rightValueHEq : HEq rightValue1 rightValue2) :
    HEq (Term.intervalJoin leftValue1 rightValue1)
      (Term.intervalJoin leftValue2 rightValue2) := by
  subst leftRawEq
  subst rightRawEq
  cases leftValueHEq
  cases rightValueHEq
  rfl

/-- HEq congruence for path introduction with shared univalence evidence. -/
theorem Term.pathLam_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType1 carrierType2 : Ty level scope}
    {leftEndpoint1 leftEndpoint2 rightEndpoint1 rightEndpoint2 : RawTerm scope}
    {bodyRaw1 bodyRaw2 : RawTerm (scope + 1)}
    (carrierTypeEq : carrierType1 = carrierType2)
    (leftEndpointEq : leftEndpoint1 = leftEndpoint2)
    (rightEndpointEq : rightEndpoint1 = rightEndpoint2)
    (bodyRawEq : bodyRaw1 = bodyRaw2)
    {body1 : Term (context.cons Ty.interval) carrierType1.weaken bodyRaw1}
    {body2 : Term (context.cons Ty.interval) carrierType2.weaken bodyRaw2}
    (bodyHEq : HEq body1 body2) :
    HEq
      (Term.pathLam modeIsUnivalent carrierType1 leftEndpoint1
        rightEndpoint1 body1)
      (Term.pathLam modeIsUnivalent carrierType2 leftEndpoint2
        rightEndpoint2 body2) := by
  subst carrierTypeEq
  subst leftEndpointEq
  subst rightEndpointEq
  subst bodyRawEq
  cases bodyHEq
  rfl

/-- HEq congruence for path application with shared univalence evidence. -/
theorem Term.pathApp_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType1 carrierType2 : Ty level scope}
    {leftEndpoint1 leftEndpoint2 rightEndpoint1 rightEndpoint2 : RawTerm scope}
    {pathRaw1 pathRaw2 intervalRaw1 intervalRaw2 : RawTerm scope}
    (carrierTypeEq : carrierType1 = carrierType2)
    (leftEndpointEq : leftEndpoint1 = leftEndpoint2)
    (rightEndpointEq : rightEndpoint1 = rightEndpoint2)
    (pathRawEq : pathRaw1 = pathRaw2)
    (intervalRawEq : intervalRaw1 = intervalRaw2)
    {pathTerm1 :
      Term context (Ty.path carrierType1 leftEndpoint1 rightEndpoint1)
        pathRaw1}
    {pathTerm2 :
      Term context (Ty.path carrierType2 leftEndpoint2 rightEndpoint2)
        pathRaw2}
    (pathTermHEq : HEq pathTerm1 pathTerm2)
    {intervalTerm1 : Term context Ty.interval intervalRaw1}
    {intervalTerm2 : Term context Ty.interval intervalRaw2}
    (intervalTermHEq : HEq intervalTerm1 intervalTerm2) :
    HEq (Term.pathApp modeIsUnivalent pathTerm1 intervalTerm1)
      (Term.pathApp modeIsUnivalent pathTerm2 intervalTerm2) := by
  subst carrierTypeEq
  subst leftEndpointEq
  subst rightEndpointEq
  subst pathRawEq
  subst intervalRawEq
  cases pathTermHEq
  cases intervalTermHEq
  rfl

/-- HEq congruence for Glue introduction with shared univalence evidence. -/
theorem Term.glueIntro_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {baseType1 baseType2 : Ty level scope}
    {boundaryWitness1 boundaryWitness2 baseRaw1 baseRaw2 partialRaw1 partialRaw2 :
      RawTerm scope}
    (baseTypeEq : baseType1 = baseType2)
    (boundaryWitnessEq : boundaryWitness1 = boundaryWitness2)
    (baseRawEq : baseRaw1 = baseRaw2)
    (partialRawEq : partialRaw1 = partialRaw2)
    {baseValue1 : Term context baseType1 baseRaw1}
    {baseValue2 : Term context baseType2 baseRaw2}
    (baseValueHEq : HEq baseValue1 baseValue2)
    {partialValue1 : Term context baseType1 partialRaw1}
    {partialValue2 : Term context baseType2 partialRaw2}
    (partialValueHEq : HEq partialValue1 partialValue2) :
    HEq
      (Term.glueIntro modeIsUnivalent baseType1 boundaryWitness1
        baseValue1 partialValue1)
      (Term.glueIntro modeIsUnivalent baseType2 boundaryWitness2
        baseValue2 partialValue2) := by
  subst baseTypeEq
  subst boundaryWitnessEq
  subst baseRawEq
  subst partialRawEq
  cases baseValueHEq
  cases partialValueHEq
  rfl

/-- HEq congruence for Glue elimination with shared univalence evidence. -/
theorem Term.glueElim_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {baseType1 baseType2 : Ty level scope}
    {boundaryWitness1 boundaryWitness2 gluedRaw1 gluedRaw2 : RawTerm scope}
    (baseTypeEq : baseType1 = baseType2)
    (boundaryWitnessEq : boundaryWitness1 = boundaryWitness2)
    (gluedRawEq : gluedRaw1 = gluedRaw2)
    {gluedValue1 : Term context (Ty.glue baseType1 boundaryWitness1) gluedRaw1}
    {gluedValue2 : Term context (Ty.glue baseType2 boundaryWitness2) gluedRaw2}
    (gluedValueHEq : HEq gluedValue1 gluedValue2) :
    HEq (Term.glueElim modeIsUnivalent gluedValue1)
      (Term.glueElim modeIsUnivalent gluedValue2) := by
  subst baseTypeEq
  subst boundaryWitnessEq
  subst gluedRawEq
  cases gluedValueHEq
  rfl

/-- HEq congruence for homogeneous composition. -/
theorem Term.hcomp_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType1 carrierType2 : Ty level scope}
    {sidesRaw1 sidesRaw2 capRaw1 capRaw2 : RawTerm scope}
    (carrierTypeEq : carrierType1 = carrierType2)
    (sidesRawEq : sidesRaw1 = sidesRaw2)
    (capRawEq : capRaw1 = capRaw2)
    {sidesValue1 : Term context carrierType1 sidesRaw1}
    {sidesValue2 : Term context carrierType2 sidesRaw2}
    (sidesValueHEq : HEq sidesValue1 sidesValue2)
    {capValue1 : Term context carrierType1 capRaw1}
    {capValue2 : Term context carrierType2 capRaw2}
    (capValueHEq : HEq capValue1 capValue2) :
    HEq (Term.hcomp modeIsUnivalent sidesValue1 capValue1)
      (Term.hcomp modeIsUnivalent sidesValue2 capValue2) := by
  subst carrierTypeEq
  subst sidesRawEq
  subst capRawEq
  cases sidesValueHEq
  cases capValueHEq
  rfl

/-- HEq congruence for single-field record introduction. -/
theorem Term.recordIntro_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {singleFieldType1 singleFieldType2 : Ty level scope}
    {firstRaw1 firstRaw2 : RawTerm scope}
    (singleFieldTypeEq : singleFieldType1 = singleFieldType2)
    (firstRawEq : firstRaw1 = firstRaw2)
    {firstField1 : Term context singleFieldType1 firstRaw1}
    {firstField2 : Term context singleFieldType2 firstRaw2}
    (firstFieldHEq : HEq firstField1 firstField2) :
    HEq (Term.recordIntro firstField1) (Term.recordIntro firstField2) := by
  subst singleFieldTypeEq
  subst firstRawEq
  cases firstFieldHEq
  rfl

/-- HEq congruence for single-field record projection. -/
theorem Term.recordProj_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {singleFieldType1 singleFieldType2 : Ty level scope}
    {recordRaw1 recordRaw2 : RawTerm scope}
    (singleFieldTypeEq : singleFieldType1 = singleFieldType2)
    (recordRawEq : recordRaw1 = recordRaw2)
    {recordValue1 : Term context (Ty.record singleFieldType1) recordRaw1}
    {recordValue2 : Term context (Ty.record singleFieldType2) recordRaw2}
    (recordValueHEq : HEq recordValue1 recordValue2) :
    HEq (Term.recordProj recordValue1) (Term.recordProj recordValue2) := by
  subst singleFieldTypeEq
  subst recordRawEq
  cases recordValueHEq
  rfl

/-- HEq congruence for refinement elimination. -/
theorem Term.refineElim_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {baseType1 baseType2 : Ty level scope}
    {predicate1 predicate2 : RawTerm (scope + 1)}
    {refinedRaw1 refinedRaw2 : RawTerm scope}
    (baseTypeEq : baseType1 = baseType2)
    (predicateEq : predicate1 = predicate2)
    (refinedRawEq : refinedRaw1 = refinedRaw2)
    {refinedValue1 : Term context (Ty.refine baseType1 predicate1) refinedRaw1}
    {refinedValue2 : Term context (Ty.refine baseType2 predicate2) refinedRaw2}
    (refinedValueHEq : HEq refinedValue1 refinedValue2) :
    HEq (Term.refineElim refinedValue1) (Term.refineElim refinedValue2) := by
  subst baseTypeEq
  subst predicateEq
  subst refinedRawEq
  cases refinedValueHEq
  rfl

/-- HEq congruence for codata destruction. -/
theorem Term.codataDest_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {stateType1 stateType2 outputType1 outputType2 : Ty level scope}
    {codataRaw1 codataRaw2 : RawTerm scope}
    (stateTypeEq : stateType1 = stateType2)
    (outputTypeEq : outputType1 = outputType2)
    (codataRawEq : codataRaw1 = codataRaw2)
    {codataValue1 : Term context (Ty.codata stateType1 outputType1) codataRaw1}
    {codataValue2 : Term context (Ty.codata stateType2 outputType2) codataRaw2}
    (codataValueHEq : HEq codataValue1 codataValue2) :
    HEq (Term.codataDest codataValue1) (Term.codataDest codataValue2) := by
  subst stateTypeEq
  subst outputTypeEq
  subst codataRawEq
  cases codataValueHEq
  rfl

/-- HEq congruence for session receive. -/
theorem Term.sessionRecv_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {protocolStep1 protocolStep2 channelRaw1 channelRaw2 : RawTerm scope}
    (protocolStepEq : protocolStep1 = protocolStep2)
    (channelRawEq : channelRaw1 = channelRaw2)
    {channel1 : Term context (Ty.session protocolStep1) channelRaw1}
    {channel2 : Term context (Ty.session protocolStep2) channelRaw2}
    (channelHEq : HEq channel1 channel2) :
    HEq (Term.sessionRecv channel1) (Term.sessionRecv channel2) := by
  subst protocolStepEq
  subst channelRawEq
  cases channelHEq
  rfl

/-- HEq congruence for equivalence application. -/
theorem Term.equivApp_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {carrierA1 carrierA2 carrierB1 carrierB2 : Ty level scope}
    {equivRaw1 equivRaw2 argumentRaw1 argumentRaw2 : RawTerm scope}
    (carrierAEq : carrierA1 = carrierA2)
    (carrierBEq : carrierB1 = carrierB2)
    (equivRawEq : equivRaw1 = equivRaw2)
    (argumentRawEq : argumentRaw1 = argumentRaw2)
    {equivTerm1 : Term context (Ty.equiv carrierA1 carrierB1) equivRaw1}
    {equivTerm2 : Term context (Ty.equiv carrierA2 carrierB2) equivRaw2}
    (equivHEq : HEq equivTerm1 equivTerm2)
    {argumentTerm1 : Term context carrierA1 argumentRaw1}
    {argumentTerm2 : Term context carrierA2 argumentRaw2}
    (argumentHEq : HEq argumentTerm1 argumentTerm2) :
    HEq (Term.equivApp equivTerm1 argumentTerm1)
      (Term.equivApp equivTerm2 argumentTerm2) := by
  subst carrierAEq
  subst carrierBEq
  subst equivRawEq
  subst argumentRawEq
  cases equivHEq
  cases argumentHEq
  rfl

end LeanFX2
