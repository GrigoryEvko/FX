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

end LeanFX2
