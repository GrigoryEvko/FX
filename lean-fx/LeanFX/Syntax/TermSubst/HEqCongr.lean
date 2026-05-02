import LeanFX.Syntax.TermSubst.Core

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ## HEq bridge helpers for term-substitution functoriality.

`Term.subst_id` and `Term.subst_compose` need to bridge terms whose
types differ propositionally (e.g. `Term Γ (T.subst Subst.identity)`
vs `Term Γ T`).  HEq is the right notion of equality; the lemmas
below collapse outer casts and align cons-extended contexts. -/

/-- Constructor-level HEq congruence closer.

All `Term.<ctor>_HEq_congr` lemmas have the same proof shape:
substitute propositional equalities and heterogeneous equalities until
both constructor applications are definitionally identical, then close
with `rfl`.  Keeping this as a local tactic makes future constructors
add one proof line instead of another hand-written `cases` cascade. -/
macro "term_heq_congr" : tactic =>
  `(tactic| (subst_vars; rfl))

/-- Close a context-equality leaf case where both sides are the same
constructor after substituting the context equality. -/
macro "term_context_refl" : tactic =>
  `(tactic| (subst_vars; exact HEq.refl _))

/-- **HEq across context-shape change for `Term.var`**: if two
contexts at the same scope are propositionally equal, then the
`Term.var` constructor at the same Fin position produces HEq
values across them.  Proven by `cases` on the context equality —
both sides become identical, and HEq reduces to Eq.refl. -/
theorem heq_var_across_ctx_eq {mode : Mode} {level scope : Nat}
    {sourceContext targetContext : Ctx mode level scope}
    (contextEq : sourceContext = targetContext) (position : Fin scope) :
    HEq (Term.var (context := sourceContext) position)
        (Term.var (context := targetContext) position) := by
  cases contextEq
  rfl

/-- **Strip an inner type-cast through `Term.weaken`.**  The
generic helper: weakening a term commutes with a propositional
type cast on the input.  Proven by `cases` on the equation —
both sourceTy and targetTy are local variables, so the substitution
succeeds and the cast vanishes. -/
theorem Term.heq_weaken_strip_cast
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (newType : Ty level scope)
    {sourceTy targetTy : Ty level scope} (typeEq : sourceTy = targetTy)
    (term : Term context sourceTy) :
    HEq (Term.weaken newType (typeEq ▸ term))
        (Term.weaken newType term) := by
  cases typeEq
  rfl

/-- **HEq across context-shape change for `Term.weaken (... ▸
Term.var)`**: at position k+1 of the lifted-identity, the LHS
shape is `Term.weaken X ((Ty.subst_id _).symm ▸ Term.var ⟨k, _⟩)`,
which equals `Term.var ⟨k+1, _⟩` in the extended context modulo
context-shape and the inner cast.  Uses
`Term.heq_weaken_strip_cast` to discharge the inner cast, then
`Term.weaken X (Term.var ⟨k, _⟩) = Term.var ⟨k+1, _⟩` by `rfl`
(through `Term.rename`'s var arm + `TermRenaming.weaken`'s
rfl-pointwise + `Renaming.weaken = Fin.succ`). -/
theorem heq_weaken_var_across_ctx_eq {mode : Mode} {level scope : Nat}
    {sourceContext targetContext : Ctx mode level scope}
    (contextEq : sourceContext = targetContext)
    (sourceNewType : Ty level scope) (targetNewType : Ty level scope)
    (newTypeEq : sourceNewType = targetNewType)
    (predecessor : Nat) (succBound : predecessor + 1 < scope + 1) :
    HEq
      (Term.weaken sourceNewType
        ((Ty.subst_id (varType sourceContext
            ⟨predecessor, Nat.lt_of_succ_lt_succ succBound⟩)).symm ▸
          Term.var (context := sourceContext)
            ⟨predecessor, Nat.lt_of_succ_lt_succ succBound⟩))
      (Term.var (context := targetContext.cons targetNewType)
        ⟨predecessor + 1, succBound⟩) := by
  -- Reduce both sides simultaneously by `cases`-ing the context
  -- and newType equalities — this aligns sourceContext = targetContext
  -- and sourceNewType = targetNewType pointwise.
  cases contextEq
  cases newTypeEq
  -- Strip the inner cast via the helper.
  apply HEq.trans (Term.heq_weaken_strip_cast sourceNewType
    (Ty.subst_id (varType sourceContext
      ⟨predecessor, Nat.lt_of_succ_lt_succ succBound⟩)).symm
    (Term.var ⟨predecessor, Nat.lt_of_succ_lt_succ succBound⟩))
  -- Goal: HEq (Term.weaken sourceNewType (Term.var ⟨k, _⟩))
  --           (Term.var (context := sourceContext.cons sourceNewType) ⟨k+1, hk⟩)
  -- Term.weaken X (Term.var ⟨k, _⟩) reduces (rfl) to
  --   Term.var (Renaming.weaken ⟨k, _⟩) = Term.var ⟨k+1, _⟩
  rfl

/-- **The HEq stepping stone for `Term.subst_id`'s recursive cases.**
Lifting `TermSubst.identity Γ` under a binder produces a TermSubst
that, pointwise, agrees with `TermSubst.identity (Γ.cons newType)`
modulo HEq.  The contexts and underlying substitutions differ
propositionally (via `Ty.subst_id newType` and
`Subst.lift_identity_equiv`); HEq is the right notion of equality
because both differences manifest at the type level of the
substituent terms. -/
theorem TermSubst.lift_identity_pointwise
    {mode : Mode} {level scope : Nat}
    (context : Ctx mode level scope) (newType : Ty level scope) :
    ∀ (position : Fin (scope + 1)),
      HEq
        (TermSubst.lift (TermSubst.identity context) newType position)
        (TermSubst.identity (context.cons newType) position) := by
  intro position
  -- The bridging Ty-level fact, used in both Fin cases.
  have substIdEq : newType.subst Subst.identity = newType :=
    Ty.subst_id newType
  -- Lift to context-level equality.
  have contextEq :
      context.cons (newType.subst Subst.identity) = context.cons newType := by
    rw [substIdEq]
  match position with
  | ⟨0, zeroBound⟩ =>
    -- LHS = (Ty.subst_weaken_commute newType Subst.identity).symm ▸
    --        Term.var (context := Γ.cons (newType.subst Subst.identity)) ⟨0, _⟩
    -- RHS = (Ty.subst_id newType.weaken).symm ▸
    --        Term.var (context := Γ.cons newType) ⟨0, _⟩
    --
    -- Strip both outer casts via eqRec_heq, then bridge the two
    -- naked Term.var values via heq_var_across_ctx_eq + contextEq.
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans (heq_var_across_ctx_eq contextEq ⟨0, zeroBound⟩)
    exact (eqRec_heq _ _).symm
  | ⟨predecessor + 1, succBound⟩ =>
    -- LHS = (Ty.subst_weaken_commute (varType Γ ⟨k,_⟩) Subst.identity).symm ▸
    --        Term.weaken (newType.subst Subst.identity)
    --          (TermSubst.identity Γ ⟨k, _⟩)
    --      = ... ▸ Term.weaken (newType.subst Subst.identity)
    --                ((Ty.subst_id (varType Γ ⟨k,_⟩)).symm ▸
    --                  Term.var ⟨k, _⟩)
    -- RHS = (Ty.subst_id (varType Γ ⟨k,_⟩).weaken).symm ▸
    --        Term.var (context := Γ.cons newType) ⟨k + 1, hk⟩
    --
    -- Strip outer cast on each side, then bridge via
    -- heq_weaken_var_across_ctx_eq applied at the identity ctx
    -- equality (Γ = Γ) plus the newType equality.
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans
      (heq_weaken_var_across_ctx_eq (rfl : context = context)
        (newType.subst Subst.identity) newType
        substIdEq predecessor succBound)
    exact (eqRec_heq _ _).symm

/-! ## HEq congruence helpers per `Term` constructor.

Each `Term.C_HEq_congr` says: two `C`-applications are HEq when their
type-level implicits are propositionally equal and their value
arguments are HEq.  Building blocks for any inductive proof that
descends through `Term.subst` / `Term.rename` and needs to bridge
`Term` values across different type indices. -/

/-- HEq congruence for `Term.app`. -/
theorem Term.app_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {firstArgType firstResultType
     secondArgType secondResultType : Ty level scope}
    (argTypeEq : firstArgType = secondArgType)
    (resultTypeEq : firstResultType = secondResultType)
    (firstFunction : Term context (firstArgType.arrow firstResultType))
    (secondFunction : Term context (secondArgType.arrow secondResultType))
    (functionHEq : HEq firstFunction secondFunction)
    (firstArgument : Term context firstArgType)
    (secondArgument : Term context secondArgType)
    (argumentHEq : HEq firstArgument secondArgument) :
    HEq (Term.app firstFunction firstArgument)
        (Term.app secondFunction secondArgument) := by
  term_heq_congr

/-- HEq congruence for `Term.lam`. -/
theorem Term.lam_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {firstDomain secondDomain : Ty level scope}
    (domainEq : firstDomain = secondDomain)
    {firstCodomain secondCodomain : Ty level scope}
    (codomainEq : firstCodomain = secondCodomain)
    (firstBody : Term (context.cons firstDomain) firstCodomain.weaken)
    (secondBody : Term (context.cons secondDomain) secondCodomain.weaken)
    (bodyHEq : HEq firstBody secondBody) :
    HEq (Term.lam firstBody) (Term.lam secondBody) := by
  term_heq_congr

/-- HEq congruence for `Term.lamPi`. -/
theorem Term.lamPi_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {firstDomain secondDomain : Ty level scope}
    (domainEq : firstDomain = secondDomain)
    {firstCodomain secondCodomain : Ty level (scope + 1)}
    (codomainEq : firstCodomain = secondCodomain)
    (firstBody : Term (context.cons firstDomain) firstCodomain)
    (secondBody : Term (context.cons secondDomain) secondCodomain)
    (bodyHEq : HEq firstBody secondBody) :
    HEq (Term.lamPi firstBody) (Term.lamPi secondBody) := by
  term_heq_congr

/-- HEq congruence for `Term.appPi`.  Both sides use `rfl` for
the resultEq parameter (canonical β-result form), under W9.B1.1
the equation-bearing constructor.  Callers needing other
resultEq's go through `Term.appPi_HEq_eqIrrel`. -/
theorem Term.appPi_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {firstDomain secondDomain : Ty level scope}
    (domainEq : firstDomain = secondDomain)
    {firstCodomain secondCodomain : Ty level (scope + 1)}
    (codomainEq : firstCodomain = secondCodomain)
    (firstFunction : Term context (Ty.piTy firstDomain firstCodomain))
    (secondFunction : Term context (Ty.piTy secondDomain secondCodomain))
    (functionHEq : HEq firstFunction secondFunction)
    (firstArgument : Term context firstDomain)
    (secondArgument : Term context secondDomain)
    (argumentHEq : HEq firstArgument secondArgument) :
    HEq (Term.appPi rfl firstFunction firstArgument)
        (Term.appPi rfl secondFunction secondArgument) := by
  term_heq_congr

/-- HEq congruence for `Term.pair`. -/
theorem Term.pair_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {firstSigmaFirst secondSigmaFirst : Ty level scope}
    (sigmaFirstEq : firstSigmaFirst = secondSigmaFirst)
    {firstSigmaSecond secondSigmaSecond : Ty level (scope + 1)}
    (sigmaSecondEq : firstSigmaSecond = secondSigmaSecond)
    (firstFirstVal : Term context firstSigmaFirst)
    (secondFirstVal : Term context secondSigmaFirst)
    (firstValHEq : HEq firstFirstVal secondFirstVal)
    (firstSecondVal : Term context (firstSigmaSecond.subst0 firstSigmaFirst))
    (secondSecondVal : Term context (secondSigmaSecond.subst0 secondSigmaFirst))
    (secondValHEq : HEq firstSecondVal secondSecondVal) :
    HEq (Term.pair firstFirstVal firstSecondVal)
        (Term.pair secondFirstVal secondSecondVal) := by
  term_heq_congr

/-- HEq congruence for `Term.fst`. -/
theorem Term.fst_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {firstSigmaFirst secondSigmaFirst : Ty level scope}
    (sigmaFirstEq : firstSigmaFirst = secondSigmaFirst)
    {firstSigmaSecond secondSigmaSecond : Ty level (scope + 1)}
    (sigmaSecondEq : firstSigmaSecond = secondSigmaSecond)
    (firstPair : Term context (Ty.sigmaTy firstSigmaFirst firstSigmaSecond))
    (secondPair : Term context (Ty.sigmaTy secondSigmaFirst secondSigmaSecond))
    (pairHEq : HEq firstPair secondPair) :
    HEq (Term.fst firstPair) (Term.fst secondPair) := by
  term_heq_congr

/-- HEq congruence for `Term.snd`. -/
theorem Term.snd_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {firstSigmaFirst secondSigmaFirst : Ty level scope}
    (sigmaFirstEq : firstSigmaFirst = secondSigmaFirst)
    {firstSigmaSecond secondSigmaSecond : Ty level (scope + 1)}
    (sigmaSecondEq : firstSigmaSecond = secondSigmaSecond)
    (firstPair : Term context (Ty.sigmaTy firstSigmaFirst firstSigmaSecond))
    (secondPair : Term context (Ty.sigmaTy secondSigmaFirst secondSigmaSecond))
    (pairHEq : HEq firstPair secondPair) :
    HEq (Term.snd firstPair) (Term.snd secondPair) := by
  term_heq_congr

/-- **General HEq congruence for `Term.weaken`.**  Stronger than
`Term.heq_weaken_strip_cast` (which only handled an inner cast):
this allows the newType parameter AND the input term to differ
across the HEq.  Three `cases` discharge the three propositional
equalities; once unified, `rfl`. -/
theorem Term.weaken_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {firstNewType secondNewType : Ty level scope}
    (newTypeEq : firstNewType = secondNewType)
    {firstTy secondTy : Ty level scope} (typeEq : firstTy = secondTy)
    (firstTerm : Term context firstTy) (secondTerm : Term context secondTy)
    (termHEq : HEq firstTerm secondTerm) :
    HEq (Term.weaken firstNewType firstTerm)
        (Term.weaken secondNewType secondTerm) := by
  term_heq_congr

/-- Apply the same type cast to both sides of a same-source HEq. -/
theorem Term.castSame_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    (typeEquality : sourceType = targetType)
    {firstTerm secondTerm : Term context sourceType}
    (termEquality : HEq firstTerm secondTerm) :
    HEq (typeEquality ▸ firstTerm) (typeEquality ▸ secondTerm) := by
  cases typeEquality
  exact termEquality

/-- Relate a term to the same term cast along a type equality. -/
theorem Term.castRight_HEq
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    (typeEquality : sourceType = targetType)
    (sourceTerm : Term context sourceType) :
    HEq sourceTerm (typeEquality ▸ sourceTerm) := by
  cases typeEquality
  rfl

/-- HEq congruence for `Term.boolElim`. -/
theorem Term.boolElim_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {firstResultType secondResultType : Ty level scope}
    (resultTypeEq : firstResultType = secondResultType)
    (firstScrutinee secondScrutinee : Term context Ty.bool)
    (scrutineeEq : firstScrutinee = secondScrutinee)
    (firstThenBranch : Term context firstResultType)
    (secondThenBranch : Term context secondResultType)
    (thenBranchHEq : HEq firstThenBranch secondThenBranch)
    (firstElseBranch : Term context firstResultType)
    (secondElseBranch : Term context secondResultType)
    (elseBranchHEq : HEq firstElseBranch secondElseBranch) :
    HEq (Term.boolElim firstScrutinee firstThenBranch firstElseBranch)
        (Term.boolElim secondScrutinee secondThenBranch secondElseBranch) := by
  term_heq_congr

/-- HEq congruence for `Term.natSucc`.  natSucc has no type-level
indices that vary, so this collapses to plain equality of the
predecessor-term — we accept HEq for symmetry with the other
constructor congruences. -/
theorem Term.natSucc_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (firstPredecessor secondPredecessor : Term context Ty.nat)
    (predecessorHEq : HEq firstPredecessor secondPredecessor) :
    HEq (Term.natSucc firstPredecessor) (Term.natSucc secondPredecessor) := by
  term_heq_congr

/-- HEq congruence for `Term.natElim`. -/
theorem Term.natElim_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {firstResultType secondResultType : Ty level scope}
    (resultTypeEq : firstResultType = secondResultType)
    (firstScrutinee secondScrutinee : Term context Ty.nat)
    (scrutineeEq : firstScrutinee = secondScrutinee)
    (firstZeroBranch : Term context firstResultType)
    (secondZeroBranch : Term context secondResultType)
    (zeroBranchHEq : HEq firstZeroBranch secondZeroBranch)
    (firstSuccBranch : Term context (Ty.arrow Ty.nat firstResultType))
    (secondSuccBranch : Term context (Ty.arrow Ty.nat secondResultType))
    (succBranchHEq : HEq firstSuccBranch secondSuccBranch) :
    HEq (Term.natElim firstScrutinee firstZeroBranch firstSuccBranch)
        (Term.natElim secondScrutinee secondZeroBranch secondSuccBranch) := by
  term_heq_congr

/-- HEq congruence for `Term.natRec`.  Same shape as `natElim_HEq_congr`
but with succBranch typed `Ty.arrow Ty.nat (Ty.arrow result result)` —
the predecessor + IH curried form for primitive recursion. -/
theorem Term.natRec_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {firstResultType secondResultType : Ty level scope}
    (resultTypeEq : firstResultType = secondResultType)
    (firstScrutinee secondScrutinee : Term context Ty.nat)
    (scrutineeEq : firstScrutinee = secondScrutinee)
    (firstZeroBranch : Term context firstResultType)
    (secondZeroBranch : Term context secondResultType)
    (zeroBranchHEq : HEq firstZeroBranch secondZeroBranch)
    (firstSuccBranch : Term context
      (Ty.arrow Ty.nat (Ty.arrow firstResultType firstResultType)))
    (secondSuccBranch : Term context
      (Ty.arrow Ty.nat (Ty.arrow secondResultType secondResultType)))
    (succBranchHEq : HEq firstSuccBranch secondSuccBranch) :
    HEq (Term.natRec firstScrutinee firstZeroBranch firstSuccBranch)
        (Term.natRec secondScrutinee secondZeroBranch secondSuccBranch) := by
  term_heq_congr

/-- HEq congruence for `Term.listNil`.  Only the elementType varies
between sides; no value arguments. -/
theorem Term.listNil_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {firstElemType secondElemType : Ty level scope}
    (elemTypeEq : firstElemType = secondElemType) :
    HEq (Term.listNil (context := context) (elementType := firstElemType))
        (Term.listNil (context := context) (elementType := secondElemType)) := by
  term_heq_congr

/-- HEq congruence for `Term.listCons`. -/
theorem Term.listCons_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {firstElemType secondElemType : Ty level scope}
    (elemTypeEq : firstElemType = secondElemType)
    (firstHead : Term context firstElemType)
    (secondHead : Term context secondElemType)
    (headHEq : HEq firstHead secondHead)
    (firstTail : Term context (Ty.list firstElemType))
    (secondTail : Term context (Ty.list secondElemType))
    (tailHEq : HEq firstTail secondTail) :
    HEq (Term.listCons firstHead firstTail)
        (Term.listCons secondHead secondTail) := by
  term_heq_congr

/-- HEq congruence for `Term.listElim`.  Both `elementType` and
`resultType` may vary; the consBranch type
`elem → list elem → result` mentions `elementType` twice. -/
theorem Term.listElim_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {firstElemType secondElemType : Ty level scope}
    (elemTypeEq : firstElemType = secondElemType)
    {firstResultType secondResultType : Ty level scope}
    (resultTypeEq : firstResultType = secondResultType)
    (firstScrutinee : Term context (Ty.list firstElemType))
    (secondScrutinee : Term context (Ty.list secondElemType))
    (scrutineeHEq : HEq firstScrutinee secondScrutinee)
    (firstNilBranch : Term context firstResultType)
    (secondNilBranch : Term context secondResultType)
    (nilBranchHEq : HEq firstNilBranch secondNilBranch)
    (firstConsBranch : Term context
      (Ty.arrow firstElemType (Ty.arrow (Ty.list firstElemType) firstResultType)))
    (secondConsBranch : Term context
      (Ty.arrow secondElemType (Ty.arrow (Ty.list secondElemType) secondResultType)))
    (consBranchHEq : HEq firstConsBranch secondConsBranch) :
    HEq (Term.listElim firstScrutinee firstNilBranch firstConsBranch)
        (Term.listElim secondScrutinee secondNilBranch secondConsBranch) := by
  term_heq_congr

/-- HEq congruence for `Term.optionNone` — only elementType varies. -/
theorem Term.optionNone_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {firstElemType secondElemType : Ty level scope}
    (elemTypeEq : firstElemType = secondElemType) :
    HEq (Term.optionNone (context := context) (elementType := firstElemType))
        (Term.optionNone (context := context) (elementType := secondElemType)) := by
  term_heq_congr

/-- HEq congruence for `Term.optionSome`. -/
theorem Term.optionSome_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {firstElemType secondElemType : Ty level scope}
    (elemTypeEq : firstElemType = secondElemType)
    (firstValue : Term context firstElemType)
    (secondValue : Term context secondElemType)
    (valueHEq : HEq firstValue secondValue) :
    HEq (Term.optionSome firstValue) (Term.optionSome secondValue) := by
  term_heq_congr

/-- HEq congruence for `Term.optionMatch`. -/
theorem Term.optionMatch_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {firstElemType secondElemType : Ty level scope}
    (elemTypeEq : firstElemType = secondElemType)
    {firstResultType secondResultType : Ty level scope}
    (resultTypeEq : firstResultType = secondResultType)
    (firstScrutinee : Term context (Ty.option firstElemType))
    (secondScrutinee : Term context (Ty.option secondElemType))
    (scrutineeHEq : HEq firstScrutinee secondScrutinee)
    (firstNoneBranch : Term context firstResultType)
    (secondNoneBranch : Term context secondResultType)
    (noneBranchHEq : HEq firstNoneBranch secondNoneBranch)
    (firstSomeBranch : Term context (Ty.arrow firstElemType firstResultType))
    (secondSomeBranch : Term context (Ty.arrow secondElemType secondResultType))
    (someBranchHEq : HEq firstSomeBranch secondSomeBranch) :
    HEq (Term.optionMatch firstScrutinee firstNoneBranch firstSomeBranch)
        (Term.optionMatch secondScrutinee secondNoneBranch secondSomeBranch) := by
  term_heq_congr

/-- HEq congruence for `Term.eitherInl`.  Both `leftType` and
`rightType` may vary; only the `leftType` value is supplied. -/
theorem Term.eitherInl_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {firstLeftType secondLeftType : Ty level scope}
    (leftTypeEq : firstLeftType = secondLeftType)
    {firstRightType secondRightType : Ty level scope}
    (rightTypeEq : firstRightType = secondRightType)
    (firstValue : Term context firstLeftType)
    (secondValue : Term context secondLeftType)
    (valueHEq : HEq firstValue secondValue) :
    HEq (Term.eitherInl (rightType := firstRightType) firstValue)
        (Term.eitherInl (rightType := secondRightType) secondValue) := by
  term_heq_congr

/-- HEq congruence for `Term.eitherInr`.  Symmetric to `eitherInl_HEq_congr`. -/
theorem Term.eitherInr_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {firstLeftType secondLeftType : Ty level scope}
    (leftTypeEq : firstLeftType = secondLeftType)
    {firstRightType secondRightType : Ty level scope}
    (rightTypeEq : firstRightType = secondRightType)
    (firstValue : Term context firstRightType)
    (secondValue : Term context secondRightType)
    (valueHEq : HEq firstValue secondValue) :
    HEq (Term.eitherInr (leftType := firstLeftType) firstValue)
        (Term.eitherInr (leftType := secondLeftType) secondValue) := by
  term_heq_congr

/-- HEq congruence for `Term.eitherMatch`.  Three Ty-index equalities
(left, right, result) and three sub-term HEqs (scrutinee, leftBranch,
rightBranch). -/
theorem Term.eitherMatch_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {firstLeftType secondLeftType : Ty level scope}
    (leftTypeEq : firstLeftType = secondLeftType)
    {firstRightType secondRightType : Ty level scope}
    (rightTypeEq : firstRightType = secondRightType)
    {firstResultType secondResultType : Ty level scope}
    (resultTypeEq : firstResultType = secondResultType)
    (firstScrutinee : Term context (Ty.either firstLeftType firstRightType))
    (secondScrutinee : Term context (Ty.either secondLeftType secondRightType))
    (scrutineeHEq : HEq firstScrutinee secondScrutinee)
    (firstLeftBranch : Term context (Ty.arrow firstLeftType firstResultType))
    (secondLeftBranch : Term context (Ty.arrow secondLeftType secondResultType))
    (leftBranchHEq : HEq firstLeftBranch secondLeftBranch)
    (firstRightBranch : Term context (Ty.arrow firstRightType firstResultType))
    (secondRightBranch : Term context (Ty.arrow secondRightType secondResultType))
    (rightBranchHEq : HEq firstRightBranch secondRightBranch) :
    HEq (Term.eitherMatch firstScrutinee firstLeftBranch firstRightBranch)
        (Term.eitherMatch secondScrutinee secondLeftBranch secondRightBranch) := by
  term_heq_congr

/-- HEq congruence for `Term.refl`.  Only the `carrier` Ty varies
between sides; the open endpoint `rawTerm : RawTerm scope` is shared
verbatim, so it does not need an HEq parameter.  Two
propositionally-distinct carriers produce `Term`s at
propositionally-distinct types `Ty.id carrier₁ rawTerm rawTerm` vs
`Ty.id carrier₂ rawTerm rawTerm`; HEq collapses them via `cases
carrierEq`. -/
theorem Term.refl_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {firstCarrier secondCarrier : Ty level scope}
    (carrierEq : firstCarrier = secondCarrier)
    {firstRawTerm secondRawTerm : RawTerm scope}
    (rawTermEq : firstRawTerm = secondRawTerm) :
    HEq (Term.refl (context := context) (carrier := firstCarrier) firstRawTerm)
        (Term.refl (context := context) (carrier := secondCarrier) secondRawTerm) := by
  term_heq_congr

/-- HEq congruence for `Term.idJ`.  Four Ty-level equations (carrier,
leftEnd, rightEnd, resultType) and two HEq sub-term arguments
(baseCase and witness).  The witness's type depends on `carrier`,
`leftEnd`, `rightEnd`, so its HEq must travel via `cases` on those
three equations before HEq collapses to plain equality. -/
theorem Term.idJ_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {firstCarrier secondCarrier : Ty level scope}
    (carrierEq : firstCarrier = secondCarrier)
    {firstLeftEnd secondLeftEnd : RawTerm scope}
    (leftEndEq : firstLeftEnd = secondLeftEnd)
    {firstRightEnd secondRightEnd : RawTerm scope}
    (rightEndEq : firstRightEnd = secondRightEnd)
    {firstResultType secondResultType : Ty level scope}
    (resultTypeEq : firstResultType = secondResultType)
    (firstBaseCase : Term context firstResultType)
    (secondBaseCase : Term context secondResultType)
    (baseCaseHEq : HEq firstBaseCase secondBaseCase)
    (firstWitness : Term context (Ty.id firstCarrier firstLeftEnd firstRightEnd))
    (secondWitness : Term context (Ty.id secondCarrier secondLeftEnd secondRightEnd))
    (witnessHEq : HEq firstWitness secondWitness) :
    HEq (Term.idJ firstBaseCase firstWitness)
        (Term.idJ secondBaseCase secondWitness) := by
  term_heq_congr

/-! ## `Term.subst_id_HEq` leaf cases.

Four leaf constructors: `var` strips the inner `(Ty.subst_id _).symm
▸ Term.var i` cast via `eqRec_heq`; `unit`/`boolTrue`/`boolFalse`
have substitution-independent types so reduce to `HEq.refl`. -/

/-- Leaf HEq case of `Term.subst_id` for `var`. -/
theorem Term.subst_id_HEq_var
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (position : Fin scope) :
    HEq (Term.subst (TermSubst.identity context) (Term.var position))
        (Term.var (context := context) position) := by
  show HEq ((Ty.subst_id (varType context position)).symm ▸ Term.var position)
           (Term.var position)
  exact eqRec_heq _ _

/-- Leaf HEq case of `Term.subst_id` for `unit`. -/
theorem Term.subst_id_HEq_unit
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope} :
    HEq (Term.subst (TermSubst.identity context) (Term.unit (context := context)))
        (Term.unit (context := context)) :=
  HEq.refl _

/-- Leaf HEq case of `Term.subst_id` for `boolTrue`. -/
theorem Term.subst_id_HEq_boolTrue
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope} :
    HEq (Term.subst (TermSubst.identity context) (Term.boolTrue (context := context)))
        (Term.boolTrue (context := context)) :=
  HEq.refl _

/-- Leaf HEq case of `Term.subst_id` for `boolFalse`. -/
theorem Term.subst_id_HEq_boolFalse
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope} :
    HEq (Term.subst (TermSubst.identity context) (Term.boolFalse (context := context)))
        (Term.boolFalse (context := context)) :=
  HEq.refl _

/-! ## `Term.subst_id_HEq` closed-context cases.

Constructors whose subterms live in the same context as the parent
(no `TermSubst.lift`).  Each takes per-subterm HEq IHs and combines
via the constructor-HEq congruences with `Ty.subst_id` bridges.
The cast-bearing cases (`appPi`, `pair`, `snd`) strip the outer
`Ty.subst0_subst_commute` cast via `eqRec_heq` first. -/

/-- Recursive HEq case of `Term.subst_id` for `app`. -/
theorem Term.subst_id_HEq_app
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {argType resultType : Ty level scope}
    (functionTerm : Term context (argType.arrow resultType))
    (argumentTerm : Term context argType)
    (functionRecursiveHEq :
      HEq (Term.subst (TermSubst.identity context) functionTerm) functionTerm)
    (argumentRecursiveHEq :
      HEq (Term.subst (TermSubst.identity context) argumentTerm) argumentTerm) :
    HEq (Term.subst (TermSubst.identity context) (Term.app functionTerm argumentTerm))
        (Term.app (context := context) functionTerm argumentTerm) := by
  show HEq (Term.app (Term.subst (TermSubst.identity context) functionTerm)
                     (Term.subst (TermSubst.identity context) argumentTerm))
           (Term.app functionTerm argumentTerm)
  exact Term.app_HEq_congr (Ty.subst_id argType) (Ty.subst_id resultType)
    _ _ functionRecursiveHEq _ _ argumentRecursiveHEq

/-- Recursive HEq case of `Term.subst_id` for `fst`. -/
theorem Term.subst_id_HEq_fst
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sigmaFirst : Ty level scope} {sigmaSecond : Ty level (scope + 1)}
    (pairTerm : Term context (Ty.sigmaTy sigmaFirst sigmaSecond))
    (pairRecursiveHEq :
      HEq (Term.subst (TermSubst.identity context) pairTerm) pairTerm) :
    HEq (Term.subst (TermSubst.identity context) (Term.fst pairTerm))
        (Term.fst (context := context) pairTerm) := by
  show HEq (Term.fst (Term.subst (TermSubst.identity context) pairTerm))
           (Term.fst pairTerm)
  apply Term.fst_HEq_congr (Ty.subst_id sigmaFirst)
    ((Ty.subst_congr Subst.lift_identity_equiv sigmaSecond).trans
     (Ty.subst_id sigmaSecond))
  exact pairRecursiveHEq

/-- Recursive HEq case of `Term.subst_id` for `boolElim`. -/
theorem Term.subst_id_HEq_boolElim
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {resultType : Ty level scope}
    (scrutinee : Term context Ty.bool)
    (thenBranch : Term context resultType)
    (elseBranch : Term context resultType)
    (scrutineeRecursiveHEq :
      HEq (Term.subst (TermSubst.identity context) scrutinee) scrutinee)
    (thenBranchRecursiveHEq :
      HEq (Term.subst (TermSubst.identity context) thenBranch) thenBranch)
    (elseBranchRecursiveHEq :
      HEq (Term.subst (TermSubst.identity context) elseBranch) elseBranch) :
    HEq (Term.subst (TermSubst.identity context)
          (Term.boolElim scrutinee thenBranch elseBranch))
        (Term.boolElim (context := context) scrutinee thenBranch elseBranch) := by
  show HEq (Term.boolElim
            (Term.subst (TermSubst.identity context) scrutinee)
            (Term.subst (TermSubst.identity context) thenBranch)
            (Term.subst (TermSubst.identity context) elseBranch))
           (Term.boolElim scrutinee thenBranch elseBranch)
  apply Term.boolElim_HEq_congr (Ty.subst_id resultType)
    _ _ (eq_of_heq scrutineeRecursiveHEq)
    _ _ thenBranchRecursiveHEq
    _ _ elseBranchRecursiveHEq

/-- HEq irrelevance of the `resultEq` proof field of `Term.appPi`
(W9.B1.1).  Two `appPi`'s with the same indices but different
`resultEq` proofs are heterogeneously equal — the equation field
is propositional. -/
theorem Term.appPi_HEq_eqIrrel
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {domain : Ty level scope} {codomain : Ty level (scope + 1)}
    {resultType : Ty level scope}
    (firstEq secondEq : resultType = codomain.subst0 domain)
    (functionTerm : Term context (Ty.piTy domain codomain))
    (argumentTerm : Term context domain) :
    HEq (Term.appPi (context := context) firstEq functionTerm argumentTerm)
        (Term.appPi (context := context) secondEq functionTerm argumentTerm) := by
  -- Eq fields are propositional; cases on first eliminates one,
  -- subsumption on the other gives rfl.
  cases firstEq
  cases secondEq
  rfl

/-- Recursive HEq case of `Term.subst_id` for `appPi`.  The
substituted result carries `Ty.subst0_subst_commute` and the
equation-bearing cast on the outside; `eqRec_heq` strips them
before constructor congruence.  Polymorphic over `resultEq`
under W9.B1.1 (equation-bearing appPi). -/
theorem Term.subst_id_HEq_appPi
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {domain : Ty level scope} {codomain : Ty level (scope + 1)}
    {resultType : Ty level scope}
    (resultEq : resultType = codomain.subst0 domain)
    (functionTerm : Term context (Ty.piTy domain codomain))
    (argumentTerm : Term context domain)
    (functionRecursiveHEq :
      HEq (Term.subst (TermSubst.identity context) functionTerm) functionTerm)
    (argumentRecursiveHEq :
      HEq (Term.subst (TermSubst.identity context) argumentTerm) argumentTerm) :
    HEq (Term.subst (TermSubst.identity context)
          (Term.appPi resultEq functionTerm argumentTerm))
        (Term.appPi (context := context) resultEq functionTerm argumentTerm) := by
  show HEq
    ((congrArg (Ty.subst · Subst.identity) resultEq).symm ▸
      ((Ty.subst0_subst_commute codomain domain Subst.identity).symm ▸
        Term.appPi rfl (Term.subst (TermSubst.identity context) functionTerm)
                       (Term.subst (TermSubst.identity context) argumentTerm)))
    (Term.appPi resultEq functionTerm argumentTerm)
  apply HEq.trans (eqRec_heq _ _)
  apply HEq.trans (eqRec_heq _ _)
  -- Inner appPi HEq congruence; resultEq is irrelevant to constructor congruence.
  -- Need: appPi rfl substed substed ≍ appPi resultEq function argument.
  -- The first cases-rfl reduces resultType := codomain.subst0 domain so we can
  -- reuse plain appPi_HEq_congr.
  cases resultEq
  exact Term.appPi_HEq_congr (Ty.subst_id domain)
    ((Ty.subst_congr Subst.lift_identity_equiv codomain).trans
     (Ty.subst_id codomain))
    _ _ functionRecursiveHEq _ _ argumentRecursiveHEq

/-- Recursive HEq case of `Term.subst_id` for `pair`. -/
theorem Term.subst_id_HEq_pair
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sigmaFirst : Ty level scope} {sigmaSecond : Ty level (scope + 1)}
    (firstVal : Term context sigmaFirst)
    (secondVal : Term context (sigmaSecond.subst0 sigmaFirst))
    (firstValRecursiveHEq :
      HEq (Term.subst (TermSubst.identity context) firstVal) firstVal)
    (secondValRecursiveHEq :
      HEq (Term.subst (TermSubst.identity context) secondVal) secondVal) :
    HEq (Term.subst (TermSubst.identity context) (Term.pair firstVal secondVal))
        (Term.pair (context := context) firstVal secondVal) := by
  show HEq
    (Term.pair (Term.subst (TermSubst.identity context) firstVal)
      ((Ty.subst0_subst_commute sigmaSecond sigmaFirst Subst.identity) ▸
        (Term.subst (TermSubst.identity context) secondVal)))
    (Term.pair firstVal secondVal)
  apply Term.pair_HEq_congr (Ty.subst_id sigmaFirst)
    ((Ty.subst_congr Subst.lift_identity_equiv sigmaSecond).trans
     (Ty.subst_id sigmaSecond))
    _ _ firstValRecursiveHEq
  apply HEq.trans (eqRec_heq _ _)
  exact secondValRecursiveHEq

/-- Recursive HEq case of `Term.subst_id` for `snd`. -/
theorem Term.subst_id_HEq_snd
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sigmaFirst : Ty level scope} {sigmaSecond : Ty level (scope + 1)}
    (pairTerm : Term context (Ty.sigmaTy sigmaFirst sigmaSecond))
    (pairRecursiveHEq :
      HEq (Term.subst (TermSubst.identity context) pairTerm) pairTerm) :
    HEq (Term.subst (TermSubst.identity context) (Term.snd pairTerm))
        (Term.snd (context := context) pairTerm) := by
  show HEq
    ((Ty.subst0_subst_commute sigmaSecond sigmaFirst Subst.identity).symm ▸
      Term.snd (Term.subst (TermSubst.identity context) pairTerm))
    (Term.snd pairTerm)
  apply HEq.trans (eqRec_heq _ _)
  apply Term.snd_HEq_congr (Ty.subst_id sigmaFirst)
    ((Ty.subst_congr Subst.lift_identity_equiv sigmaSecond).trans
     (Ty.subst_id sigmaSecond))
  exact pairRecursiveHEq


end LeanFX.Syntax
