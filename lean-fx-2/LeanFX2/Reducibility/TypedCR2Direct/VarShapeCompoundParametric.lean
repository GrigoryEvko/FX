import LeanFX2.Reducibility.NeutralSNClosure
import LeanFX2.Reducibility.TypedCR2Direct.VarShapeDirect

/-! # LeanFX2.Reducibility.TypedCR2Direct.VarShapeCompoundParametric

K12.20.AZ compound varShape — second half of the compound-Ty arms.
Covers the equiv / refine / record / codata arms (Stage 1 advanced
type formers) and the parametric inductive arms listType /
optionType / eitherType plus the HoTT family piTy / id / oeq /
idStrict.

Each arm takes a sub-Ty CR3 hypothesis (codomain / refinement
underlying / payload / field) to bypass the structural-recursion
wall in `Reducible`'s def-by-recursion definition.

## Root status

Layer 3 metatheory leaf.  Fourth slice of `TypedCR2Direct`.  Consumed
by `TypedCR2Compound` (per-ctor cases) and the unified
`Reducible.step_preserves` dispatcher in `TypedCR2Wrapup`. -/

namespace LeanFX2

/-- **K12.20.U2 listType CR3 arm**: a neutral list is reducible at
`Ty.listType elementType` when every raw progress reduct is SN.

The K12.8 list candidate asks for SN of each eliminator result under
SN branches and the cons-application closure.  With a neutral scrutinee
the cons/nil ι arms cannot fire, so `RawTerm.listElim_neutral...`
closes from scrutinee SN plus branch SN; the cons-application premise is
reserved for canonical-cons fundamentals, not this neutral CR3 arm. -/
theorem Reducible.listType_of_neutral_progress_closure
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType : Ty level scope}
    {sourceRaw : RawTerm scope}
    (sourceTerm : Term context (Ty.listType elementType) sourceRaw)
    (sourceIsNeutral : RawTerm.IsNeutral sourceRaw)
    (closure :
      ∀ targetRaw : RawTerm scope,
        RawStep.parProgress sourceRaw targetRaw →
        RawTerm.isStronglyNormalizing targetRaw) :
    Reducible (Ty.listType elementType) sourceTerm := by
  have sourceIsSN : Term.isStronglyNormalizing sourceTerm :=
    Term.isStronglyNormalizing_of_neutral_progress_closure
      sourceTerm sourceIsNeutral closure
  refine ⟨sourceIsSN, ?_⟩
  intro _motiveType _nilRaw _consRaw _nilBranch _consBranch
    nilIsSN consIsSN _consApplied
  exact RawTerm.listElim_neutral_isStronglyNormalizing
    sourceIsNeutral sourceIsSN nilIsSN consIsSN

/-- **K12.20.U2 listType varShape arm**: variables are reducible at
list type.

The strengthened K12.8 list closure includes SN for both eliminator
branches.  That is exactly what the raw neutral-list eliminator helper
needs for `listElim (var position) nilBranch consBranch`; the branch
application hypothesis remains available for canonical cons ι-cases but
is not needed for the stuck-variable case. -/
theorem Reducible.listType_of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType : Ty level scope}
    {position : Fin scope}
    (term :
        Term context (Ty.listType elementType)
          (RawTerm.var position)) :
    Reducible (Ty.listType elementType) term :=
  ⟨Term.isStronglyNormalizing_of_varShape term,
   fun {_motiveType} {_nilRaw} {_consRaw}
       _nilBranch _consBranch nilIsSN consIsSN _consApplied =>
     RawTerm.listElim_var_isStronglyNormalizing position nilIsSN consIsSN⟩

/-- **K12.20.U2 optionType CR3 arm**: a neutral option value is reducible
at `Ty.optionType elementType` when every raw progress reduct is SN.

The K12.8 option candidate asks for SN of each match result under SN
branches and the some-application closure.  With a neutral scrutinee the
none/some ι arms cannot fire, so the raw neutral option-match helper
closes from scrutinee SN plus branch SN. -/
theorem Reducible.optionType_of_neutral_progress_closure
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType : Ty level scope}
    {sourceRaw : RawTerm scope}
    (sourceTerm : Term context (Ty.optionType elementType) sourceRaw)
    (sourceIsNeutral : RawTerm.IsNeutral sourceRaw)
    (closure :
      ∀ targetRaw : RawTerm scope,
        RawStep.parProgress sourceRaw targetRaw →
        RawTerm.isStronglyNormalizing targetRaw) :
    Reducible (Ty.optionType elementType) sourceTerm := by
  have sourceIsSN : Term.isStronglyNormalizing sourceTerm :=
    Term.isStronglyNormalizing_of_neutral_progress_closure
      sourceTerm sourceIsNeutral closure
  refine ⟨sourceIsSN, ?_⟩
  intro _motiveType _noneRaw _someRaw _noneBranch _someBranch
    noneIsSN someIsSN _someApplied
  exact RawTerm.optionMatch_neutral_isStronglyNormalizing
    sourceIsNeutral sourceIsSN noneIsSN someIsSN

/-- **K12.20.U2 optionType varShape arm**: variables are reducible at
option type.

The some-branch SN premise is load-bearing for neutral scrutinees:
`optionMatch` can reduce the some branch by congruence even when the
scrutinee is stuck at a variable. -/
theorem Reducible.optionType_of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType : Ty level scope}
    {position : Fin scope}
    (term :
        Term context (Ty.optionType elementType)
          (RawTerm.var position)) :
    Reducible (Ty.optionType elementType) term :=
  ⟨Term.isStronglyNormalizing_of_varShape term,
   fun {_motiveType} {_noneRaw} {_someRaw}
       _noneBranch _someBranch noneIsSN someIsSN _someApplied =>
     RawTerm.optionMatch_var_isStronglyNormalizing position noneIsSN someIsSN⟩

/-- **K12.20.U2 eitherType CR3 arm**: a neutral either value is
reducible at `Ty.eitherType leftType rightType` when every raw progress
reduct is SN.

The K12.8 either candidate asks for SN of each match result under SN
branches and both branch-application closures.  With a neutral scrutinee
the left/right ι arms cannot fire, so the raw neutral either-match
helper closes from scrutinee SN plus branch SN. -/
theorem Reducible.eitherType_of_neutral_progress_closure
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {leftType rightType : Ty level scope}
    {sourceRaw : RawTerm scope}
    (sourceTerm :
      Term context (Ty.eitherType leftType rightType) sourceRaw)
    (sourceIsNeutral : RawTerm.IsNeutral sourceRaw)
    (closure :
      ∀ targetRaw : RawTerm scope,
        RawStep.parProgress sourceRaw targetRaw →
        RawTerm.isStronglyNormalizing targetRaw) :
    Reducible (Ty.eitherType leftType rightType) sourceTerm := by
  have sourceIsSN : Term.isStronglyNormalizing sourceTerm :=
    Term.isStronglyNormalizing_of_neutral_progress_closure
      sourceTerm sourceIsNeutral closure
  refine ⟨sourceIsSN, ?_⟩
  intro _motiveType _leftRaw _rightRaw _leftBranch _rightBranch
    leftIsSN rightIsSN _leftApplied _rightApplied
  exact RawTerm.eitherMatch_neutral_isStronglyNormalizing
    sourceIsNeutral sourceIsSN leftIsSN rightIsSN

/-- **K12.20.U2 eitherType varShape arm**: variables are reducible at
either type.

Both branches must be SN because `eitherMatch` reduces both branch
positions by congruence under a stuck variable scrutinee. -/
theorem Reducible.eitherType_of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {leftType rightType : Ty level scope}
    {position : Fin scope}
    (term :
        Term context (Ty.eitherType leftType rightType)
          (RawTerm.var position)) :
    Reducible (Ty.eitherType leftType rightType) term :=
  ⟨Term.isStronglyNormalizing_of_varShape term,
   fun {_motiveType} {_leftRaw} {_rightRaw}
       _leftBranch _rightBranch leftIsSN rightIsSN
       _leftApplied _rightApplied =>
     RawTerm.eitherMatch_var_isStronglyNormalizing position
       leftIsSN rightIsSN⟩

/-- **K12.20.AZ.1 piTy arm**: variables are reducible at the
dependent-Π type.  Closure: SN(var) + ∀ argTerm, Reducible
domainType argTerm → SN(Term.appPi (var) argTerm).  The second
clause reduces (via Reducible.isStronglyNormalizing CR1) to
SN(argRaw), then Stage 1's `RawTerm.app_var_isStronglyNormalizing`
closes — Term.appPi's raw form is `RawTerm.app functionRaw
argumentRaw`, matching app_var's signature. -/
theorem Reducible.piTy_of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType : Ty level scope}
    {codomainType : Ty level (scope + 1)}
    {position : Fin scope}
    (term :
        Term context (Ty.piTy domainType codomainType)
          (RawTerm.var position)) :
    Reducible (Ty.piTy domainType codomainType) term :=
  ⟨Term.isStronglyNormalizing_of_varShape term,
   fun {_argRaw} _argTerm argIsReducible =>
     RawTerm.app_var_isStronglyNormalizing position
       (Reducible.isStronglyNormalizing argIsReducible)⟩

/-- **K12.20.U2 piTy CR3 arm**: a neutral dependent function is
reducible at `Ty.piTy domainType codomainType` when every raw
progress reduct is SN.

K12.6's current dependent-Π candidate is SN-output: it stores SN of
the function plus SN of every `Term.appPi` result under a reducible
domain argument.  Since `Term.appPi` erases to `RawTerm.app`, the raw
neutral-app SN helper closes the eliminator result directly. -/
theorem Reducible.piTy_of_neutral_progress_closure
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType : Ty level scope}
    {codomainType : Ty level (scope + 1)}
    {sourceRaw : RawTerm scope}
    (functionTerm :
      Term context (Ty.piTy domainType codomainType) sourceRaw)
    (sourceIsNeutral : RawTerm.IsNeutral sourceRaw)
    (closure :
      ∀ targetRaw : RawTerm scope,
        RawStep.parProgress sourceRaw targetRaw →
        RawTerm.isStronglyNormalizing targetRaw) :
    Reducible (Ty.piTy domainType codomainType) functionTerm := by
  have sourceIsSN : Term.isStronglyNormalizing functionTerm :=
    Term.isStronglyNormalizing_of_neutral_progress_closure
      functionTerm sourceIsNeutral closure
  refine ⟨sourceIsSN, ?_⟩
  intro _argumentRaw argumentTerm argumentIsReducible
  exact RawTerm.app_neutral_isStronglyNormalizing
    sourceIsNeutral
    sourceIsSN
    (Reducible.isStronglyNormalizing argumentIsReducible)

/-- **K12.20.U2 id CR3 arm**: a neutral identity witness is reducible
at `Ty.id carrier leftEndpoint rightEndpoint` when every raw progress
reduct is SN.

The current K12.9 identity candidate is SN-output: it stores SN of the
witness and SN preservation through `idJ` for any SN base case.  With a
neutral witness, the refl-ι arm cannot fire, so the raw neutral J helper
closes from witness SN plus base-case SN. -/
theorem Reducible.id_of_neutral_progress_closure
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint sourceRaw : RawTerm scope}
    (witness :
      Term context (Ty.id carrier leftEndpoint rightEndpoint) sourceRaw)
    (sourceIsNeutral : RawTerm.IsNeutral sourceRaw)
    (closure :
      ∀ targetRaw : RawTerm scope,
        RawStep.parProgress sourceRaw targetRaw →
        RawTerm.isStronglyNormalizing targetRaw) :
    Reducible (Ty.id carrier leftEndpoint rightEndpoint) witness := by
  have sourceIsSN : Term.isStronglyNormalizing witness :=
    Term.isStronglyNormalizing_of_neutral_progress_closure
      witness sourceIsNeutral closure
  refine ⟨sourceIsSN, ?_⟩
  intro _motiveType _baseRaw _baseCase baseIsSN
  exact RawTerm.idJ_neutral_isStronglyNormalizing
    sourceIsNeutral sourceIsSN baseIsSN

/-- **K12.20.AZ.2 id arm**: variables are reducible at the HoTT
propositional identity type.  Closure: SN(var) + ∀ baseCase,
SN(baseCase) → SN(Term.idJ baseCase var).  Stage 1's
`RawTerm.idJ_var_isStronglyNormalizing` discharges directly —
Term.idJ's raw form is `RawTerm.idJ baseRaw witnessRaw` with var
in the witness slot. -/
theorem Reducible.id_of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {position : Fin scope}
    (witness :
        Term context (Ty.id carrier leftEndpoint rightEndpoint)
          (RawTerm.var position)) :
    Reducible (Ty.id carrier leftEndpoint rightEndpoint) witness :=
  ⟨Term.isStronglyNormalizing_of_varShape witness,
   fun {_motiveType} {_baseRaw} _baseCase baseIsSN =>
     RawTerm.idJ_var_isStronglyNormalizing position baseIsSN⟩

/-- **K12.20.U2 oeq CR3 arm**: a neutral observational-equality
witness is reducible at `Ty.oeq carrier leftEndpoint rightEndpoint`
when every raw progress reduct is SN.

The current K12.10 observational-equality candidate is SN-output and
the raw `oeqJ` fragment is congruence-only, so the raw neutral helper
closes from witness SN plus base-case SN. -/
theorem Reducible.oeq_of_neutral_progress_closure
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint sourceRaw : RawTerm scope}
    (witness :
      Term context (Ty.oeq carrier leftEndpoint rightEndpoint) sourceRaw)
    (sourceIsNeutral : RawTerm.IsNeutral sourceRaw)
    (closure :
      ∀ targetRaw : RawTerm scope,
        RawStep.parProgress sourceRaw targetRaw →
        RawTerm.isStronglyNormalizing targetRaw) :
    Reducible (Ty.oeq carrier leftEndpoint rightEndpoint) witness := by
  have sourceIsSN : Term.isStronglyNormalizing witness :=
    Term.isStronglyNormalizing_of_neutral_progress_closure
      witness sourceIsNeutral closure
  refine ⟨sourceIsSN, ?_⟩
  intro _motiveType _baseRaw _baseCase baseIsSN
  exact RawTerm.oeqJ_neutral_isStronglyNormalizing
    sourceIsNeutral sourceIsSN baseIsSN

/-- **K12.20.AZ.3 oeq arm**: variables are reducible at the
observational equality type.  Closure: SN(var) + ∀ baseCase,
SN(baseCase) → SN(Term.oeqJ baseCase var).  Discharged by Stage 1's
`RawTerm.oeqJ_var_isStronglyNormalizing` (cong-only inversion;
oeq-ι deferred at raw layer).  Same shape as `id_of_varShape`. -/
theorem Reducible.oeq_of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {position : Fin scope}
    (witness :
        Term context (Ty.oeq carrier leftEndpoint rightEndpoint)
          (RawTerm.var position)) :
    Reducible (Ty.oeq carrier leftEndpoint rightEndpoint) witness :=
  ⟨Term.isStronglyNormalizing_of_varShape witness,
   fun {_motiveType} {_baseRaw} _baseCase baseIsSN =>
     RawTerm.oeqJ_var_isStronglyNormalizing position baseIsSN⟩

/-- **K12.20.U2 idStrict CR3 arm**: a neutral strict-identity
witness is reducible at `Ty.idStrict carrier leftEndpoint
rightEndpoint` when every raw progress reduct is SN.

The current K12.10 strict-identity candidate is SN-output.  Its
recursor carries a typed proof that the ambient mode is strict, but
the raw computation only sees `idStrictRec baseCase witness`.  With a
neutral witness, the strict-refl ι arm cannot fire, so the raw neutral
helper closes from witness SN plus base-case SN. -/
theorem Reducible.idStrict_of_neutral_progress_closure
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint sourceRaw : RawTerm scope}
    (witness :
      Term context (Ty.idStrict carrier leftEndpoint rightEndpoint)
        sourceRaw)
    (sourceIsNeutral : RawTerm.IsNeutral sourceRaw)
    (closure :
      ∀ targetRaw : RawTerm scope,
        RawStep.parProgress sourceRaw targetRaw →
        RawTerm.isStronglyNormalizing targetRaw) :
    Reducible (Ty.idStrict carrier leftEndpoint rightEndpoint)
      witness := by
  have sourceIsSN : Term.isStronglyNormalizing witness :=
    Term.isStronglyNormalizing_of_neutral_progress_closure
      witness sourceIsNeutral closure
  refine ⟨sourceIsSN, ?_⟩
  intro _modeIsStrict _motiveType _baseRaw _baseCase baseIsSN
  exact RawTerm.idStrictRec_neutral_isStronglyNormalizing
    sourceIsNeutral sourceIsSN baseIsSN

/-- **K12.20.AZ.4 idStrict arm**: variables are reducible at the
strict identity type.  Closure: SN(var) + ∀ (modeIsStrict : mode =
Mode.strict) baseCase, SN(baseCase) → SN(Term.idStrictRec
modeIsStrict baseCase var).  Discharged by Stage 1's
`RawTerm.idStrictRec_var_isStronglyNormalizing`; the typed mode
witness is universally quantified and consumed silently — the raw
form drops it. -/
theorem Reducible.idStrict_of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {position : Fin scope}
    (witness :
        Term context (Ty.idStrict carrier leftEndpoint rightEndpoint)
          (RawTerm.var position)) :
    Reducible (Ty.idStrict carrier leftEndpoint rightEndpoint) witness :=
  ⟨Term.isStronglyNormalizing_of_varShape witness,
   fun (_modeIsStrict : mode = Mode.strict)
       {_motiveType} {_baseRaw} _baseCase baseIsSN =>
     RawTerm.idStrictRec_var_isStronglyNormalizing position baseIsSN⟩



end LeanFX2
