import LeanFX2.Reducibility.Kripke.Basic
import LeanFX2.Foundation.RenameIdentity

/-! # ReducibleK closed-leaf SN projection.

Every reducible closed-leaf term is strongly normalizing.  Directly
extracts the SN from the predicate's closed-leaf definition. -/

namespace LeanFX2

theorem ReducibleK.sn_of_unit
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat} {raw : RawTerm scope}
    {term : Term context Ty.unit raw}
    (termIsR :
      @ReducibleK mode level scope context (stepCount + 1) Ty.unit raw term) :
    Term.isStronglyNormalizing term := termIsR

theorem ReducibleK.sn_of_bool
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat} {raw : RawTerm scope}
    {term : Term context Ty.bool raw}
    (termIsR :
      @ReducibleK mode level scope context (stepCount + 1) Ty.bool raw term) :
    Term.isStronglyNormalizing term := termIsR

theorem ReducibleK.sn_of_nat
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat} {raw : RawTerm scope}
    {term : Term context Ty.nat raw}
    (termIsR :
      @ReducibleK mode level scope context (stepCount + 1) Ty.nat raw term) :
    Term.isStronglyNormalizing term := termIsR

theorem ReducibleK.sn_of_empty
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat} {raw : RawTerm scope}
    {term : Term context Ty.empty raw}
    (termIsR :
      @ReducibleK mode level scope context (stepCount + 1) Ty.empty raw term) :
    Term.isStronglyNormalizing term := termIsR

theorem ReducibleK.sn_of_interval
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat} {raw : RawTerm scope}
    {term : Term context Ty.interval raw}
    (termIsR :
      @ReducibleK mode level scope context (stepCount + 1) Ty.interval raw term) :
    Term.isStronglyNormalizing term := termIsR

/-- Effect Kripke closure: in any future world, the renamed
effect-typed value is reducible at the renamed `Ty.effect` head.
There is no typed eliminator over `Ty.effect` whose source accepts
an arbitrary effectful value at the carrier type (the Effects-layer
`effectPerform` is schematic in its `OperationSignature` and
`CanPerform` witnesses), so the closure is renaming-stability of
reducibility at the same Ty.effect head. -/
theorem ReducibleK.effect_rename
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat}
    {carrierType : Ty level scope} {effectTag : RawTerm scope}
    {raw : RawTerm scope}
    {effectValue : Term context (Ty.effect carrierType effectTag) raw}
    (effectIsR :
      @ReducibleK mode level scope context (stepCount + 1)
        (Ty.effect carrierType effectTag) raw effectValue)
    {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming scope targetScope}
    (termRenaming : TermRenaming context targetCtx rho) :
    @ReducibleK mode level targetScope targetCtx stepCount
      (Ty.effect (carrierType.rename rho) (effectTag.rename rho)) _
      (Term.rename termRenaming effectValue) :=
  effectIsR.2 termRenaming

/-- Refinement Kripke SN projection. -/
theorem ReducibleK.sn_of_refine
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat}
    {baseType : Ty level scope} {predicate : RawTerm (scope + 1)}
    {raw : RawTerm scope}
    {term : Term context (Ty.refine baseType predicate) raw}
    (termIsR :
      @ReducibleK mode level scope context (stepCount + 1)
        (Ty.refine baseType predicate) raw term) :
    Term.isStronglyNormalizing term := termIsR.1

/-- Refinement Kripke closure: in any future world, `refineElim` of
the renamed refined value is reducible at `baseType.rename rho` at
the inner step count. -/
theorem ReducibleK.refine_elim
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat}
    {baseType : Ty level scope} {predicate : RawTerm (scope + 1)}
    {raw : RawTerm scope}
    {refinedValue : Term context (Ty.refine baseType predicate) raw}
    (refinedIsR :
      @ReducibleK mode level scope context (stepCount + 1)
        (Ty.refine baseType predicate) raw refinedValue)
    {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming scope targetScope}
    (termRenaming : TermRenaming context targetCtx rho) :
    @ReducibleK mode level targetScope targetCtx stepCount
      (baseType.rename rho) _
      (Term.refineElim (Term.rename termRenaming refinedValue)) :=
  refinedIsR.2 termRenaming

/-- Record Kripke SN projection. -/
theorem ReducibleK.sn_of_record
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat}
    {singleFieldType : Ty level scope}
    {raw : RawTerm scope}
    {term : Term context (Ty.record singleFieldType) raw}
    (termIsR :
      @ReducibleK mode level scope context (stepCount + 1)
        (Ty.record singleFieldType) raw term) :
    Term.isStronglyNormalizing term := termIsR.1

/-- Record Kripke closure: in any future world, `recordProj` of the
renamed record value is reducible at `singleFieldType.rename rho`. -/
theorem ReducibleK.record_proj
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat}
    {singleFieldType : Ty level scope}
    {raw : RawTerm scope}
    {recordValue : Term context (Ty.record singleFieldType) raw}
    (recordIsR :
      @ReducibleK mode level scope context (stepCount + 1)
        (Ty.record singleFieldType) raw recordValue)
    {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming scope targetScope}
    (termRenaming : TermRenaming context targetCtx rho) :
    @ReducibleK mode level targetScope targetCtx stepCount
      (singleFieldType.rename rho) _
      (Term.recordProj (Term.rename termRenaming recordValue)) :=
  recordIsR.2 termRenaming

/-- Codata Kripke SN projection. -/
theorem ReducibleK.sn_of_codata
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat}
    {stateType outputType : Ty level scope}
    {raw : RawTerm scope}
    {term : Term context (Ty.codata stateType outputType) raw}
    (termIsR :
      @ReducibleK mode level scope context (stepCount + 1)
        (Ty.codata stateType outputType) raw term) :
    Term.isStronglyNormalizing term := termIsR.1

/-- Codata Kripke closure: in any future world, `codataDest` of the
renamed codata value is reducible at `outputType.rename rho`. -/
theorem ReducibleK.codata_dest
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat}
    {stateType outputType : Ty level scope}
    {raw : RawTerm scope}
    {codataValue : Term context (Ty.codata stateType outputType) raw}
    (codataIsR :
      @ReducibleK mode level scope context (stepCount + 1)
        (Ty.codata stateType outputType) raw codataValue)
    {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming scope targetScope}
    (termRenaming : TermRenaming context targetCtx rho) :
    @ReducibleK mode level targetScope targetCtx stepCount
      (outputType.rename rho) _
      (Term.codataDest (Term.rename termRenaming codataValue)) :=
  codataIsR.2 termRenaming

/-- Session Kripke SN projection. -/
theorem ReducibleK.sn_of_session
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat}
    {protocolStep : RawTerm scope} {raw : RawTerm scope}
    {term : Term context (Ty.session protocolStep) raw}
    (termIsR :
      @ReducibleK mode level scope context (stepCount + 1)
        (Ty.session protocolStep) raw term) :
    Term.isStronglyNormalizing term := termIsR.1

/-- Session Kripke closure: in any future world, `sessionRecv` of the
renamed channel value is reducible at `Ty.session (protocolStep.rename
rho)`.  The current typed kernel preserves the session carrier under
`sessionRecv`; advanced protocol-state transitions live at the
Sessions layer. -/
theorem ReducibleK.session_recv
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat}
    {protocolStep : RawTerm scope} {raw : RawTerm scope}
    {channelValue : Term context (Ty.session protocolStep) raw}
    (channelIsR :
      @ReducibleK mode level scope context (stepCount + 1)
        (Ty.session protocolStep) raw channelValue)
    {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming scope targetScope}
    (termRenaming : TermRenaming context targetCtx rho) :
    @ReducibleK mode level targetScope targetCtx stepCount
      (Ty.session (protocolStep.rename rho)) _
      (Term.sessionRecv (Term.rename termRenaming channelValue)) :=
  channelIsR.2 termRenaming

/-- Modal Kripke SN projection. -/
theorem ReducibleK.sn_of_modal
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat}
    {modalityTag : Nat} {innerType : Ty level scope}
    {raw : RawTerm scope}
    {term : Term context (Ty.modal modalityTag innerType) raw}
    (termIsR :
      @ReducibleK mode level scope context (stepCount + 1)
        (Ty.modal modalityTag innerType) raw term) :
    Term.isStronglyNormalizing term := termIsR.1

/-- Modal Kripke closure: in any future world, `modElim` of the
renamed modal value is reducible at `Ty.modal modalityTag
(innerType.rename rho)`.  Layer 1's modal scaffolding preserves the
carrying type under `modElim`; Layer 6 will specialize per-modality. -/
theorem ReducibleK.mod_elim
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat}
    {modalityTag : Nat} {innerType : Ty level scope}
    {raw : RawTerm scope}
    {modalValue : Term context (Ty.modal modalityTag innerType) raw}
    (modalIsR :
      @ReducibleK mode level scope context (stepCount + 1)
        (Ty.modal modalityTag innerType) raw modalValue)
    {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming scope targetScope}
    (termRenaming : TermRenaming context targetCtx rho) :
    @ReducibleK mode level targetScope targetCtx stepCount
      (Ty.modal modalityTag (innerType.rename rho)) _
      (Term.modElim (Term.rename termRenaming modalValue)) :=
  modalIsR.2 termRenaming

/-! ## Dependent Π / Σ / List / Option / Either SN projections. -/

/-- Dependent Π Kripke SN projection: the SN component of the closure
pair. -/
theorem ReducibleK.sn_of_piTy
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {raw : RawTerm scope}
    {term : Term context (Ty.piTy domainType codomainType) raw}
    (termIsR :
      @ReducibleK mode level scope context (stepCount + 1)
        (Ty.piTy domainType codomainType) raw term) :
    Term.isStronglyNormalizing term := termIsR.1

/-- Dependent Π Kripke closure: in any future world, applying the
renamed function to a reducible argument at the renamed domain gives
a reducible result at the substituted renamed codomain. -/
theorem ReducibleK.piTy_apply
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {raw : RawTerm scope}
    {functionTerm : Term context (Ty.piTy domainType codomainType) raw}
    (functionIsR :
      @ReducibleK mode level scope context (stepCount + 1)
        (Ty.piTy domainType codomainType) raw functionTerm)
    {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming scope targetScope}
    (termRenaming : TermRenaming context targetCtx rho)
    {argumentRaw : RawTerm targetScope}
    (argumentTerm : Term targetCtx (domainType.rename rho) argumentRaw)
    (argumentIsR :
      @ReducibleK mode level targetScope targetCtx stepCount
        (domainType.rename rho) argumentRaw argumentTerm) :
    @ReducibleK mode level targetScope targetCtx stepCount
      ((codomainType.rename rho.lift).subst0
        (domainType.rename rho) argumentRaw) _
      (Term.appPi (Term.rename termRenaming functionTerm) argumentTerm) :=
  functionIsR.2 termRenaming argumentTerm argumentIsR

/-- Dependent Σ Kripke SN projection. -/
theorem ReducibleK.sn_of_sigmaTy
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {raw : RawTerm scope}
    {term : Term context (Ty.sigmaTy firstType secondType) raw}
    (termIsR :
      @ReducibleK mode level scope context (stepCount + 1)
        (Ty.sigmaTy firstType secondType) raw term) :
    Term.isStronglyNormalizing term := termIsR.1

/-- Dependent Σ Kripke `fst` projection: the renamed pair's first
projection is reducible at the renamed first type. -/
theorem ReducibleK.sigmaTy_fst
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {raw : RawTerm scope}
    {pairTerm : Term context (Ty.sigmaTy firstType secondType) raw}
    (pairIsR :
      @ReducibleK mode level scope context (stepCount + 1)
        (Ty.sigmaTy firstType secondType) raw pairTerm)
    {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming scope targetScope}
    (termRenaming : TermRenaming context targetCtx rho) :
    @ReducibleK mode level targetScope targetCtx stepCount
      (firstType.rename rho) _
      (Term.fst (Term.rename termRenaming pairTerm)) :=
  (pairIsR.2 termRenaming).1

/-- Dependent Σ Kripke `snd` projection: the renamed pair's second
projection is reducible at the substituted renamed second type. -/
theorem ReducibleK.sigmaTy_snd
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {raw : RawTerm scope}
    {pairTerm : Term context (Ty.sigmaTy firstType secondType) raw}
    (pairIsR :
      @ReducibleK mode level scope context (stepCount + 1)
        (Ty.sigmaTy firstType secondType) raw pairTerm)
    {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming scope targetScope}
    (termRenaming : TermRenaming context targetCtx rho) :
    @ReducibleK mode level targetScope targetCtx stepCount
      ((secondType.rename rho.lift).subst0
        (firstType.rename rho)
        (RawTerm.fst (pairTerm.toRaw.rename rho))) _
      (Term.snd (Term.rename termRenaming pairTerm)) :=
  (pairIsR.2 termRenaming).2

/-- List Kripke SN projection. -/
theorem ReducibleK.sn_of_listType
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat}
    {elementType : Ty level scope}
    {raw : RawTerm scope}
    {term : Term context (Ty.listType elementType) raw}
    (termIsR :
      @ReducibleK mode level scope context (stepCount + 1)
        (Ty.listType elementType) raw term) :
    Term.isStronglyNormalizing term := termIsR.1

/-- List Kripke ι-closure: in any future world, eliminating the
renamed list with reducible nil and cons branches produces a
reducible result at the chosen motive. -/
theorem ReducibleK.listType_elim
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat}
    {elementType : Ty level scope}
    {raw : RawTerm scope}
    {scrutinee : Term context (Ty.listType elementType) raw}
    (scrutineeIsR :
      @ReducibleK mode level scope context (stepCount + 1)
        (Ty.listType elementType) raw scrutinee)
    {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming scope targetScope}
    (termRenaming : TermRenaming context targetCtx rho)
    (motiveType : Ty level targetScope)
    {nilRaw consRaw : RawTerm targetScope}
    (nilBranch : Term targetCtx motiveType nilRaw)
    (consBranch :
      Term targetCtx
        (Ty.arrow (elementType.rename rho)
          (Ty.arrow (Ty.listType (elementType.rename rho)) motiveType))
        consRaw)
    (nilIsR :
      @ReducibleK mode level targetScope targetCtx stepCount
        motiveType nilRaw nilBranch)
    (consIsR :
      @ReducibleK mode level targetScope targetCtx stepCount
        (Ty.arrow (elementType.rename rho)
          (Ty.arrow (Ty.listType (elementType.rename rho)) motiveType))
        consRaw consBranch) :
    @ReducibleK mode level targetScope targetCtx stepCount
      motiveType _
      (Term.listElim (Term.rename termRenaming scrutinee)
        nilBranch consBranch) :=
  scrutineeIsR.2 termRenaming motiveType nilBranch consBranch nilIsR consIsR

/-- Option Kripke SN projection. -/
theorem ReducibleK.sn_of_optionType
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat}
    {elementType : Ty level scope}
    {raw : RawTerm scope}
    {term : Term context (Ty.optionType elementType) raw}
    (termIsR :
      @ReducibleK mode level scope context (stepCount + 1)
        (Ty.optionType elementType) raw term) :
    Term.isStronglyNormalizing term := termIsR.1

/-- Option Kripke ι-closure. -/
theorem ReducibleK.optionType_match
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat}
    {elementType : Ty level scope}
    {raw : RawTerm scope}
    {scrutinee : Term context (Ty.optionType elementType) raw}
    (scrutineeIsR :
      @ReducibleK mode level scope context (stepCount + 1)
        (Ty.optionType elementType) raw scrutinee)
    {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming scope targetScope}
    (termRenaming : TermRenaming context targetCtx rho)
    (motiveType : Ty level targetScope)
    {noneRaw someRaw : RawTerm targetScope}
    (noneBranch : Term targetCtx motiveType noneRaw)
    (someBranch :
      Term targetCtx (Ty.arrow (elementType.rename rho) motiveType) someRaw)
    (noneIsR :
      @ReducibleK mode level targetScope targetCtx stepCount
        motiveType noneRaw noneBranch)
    (someIsR :
      @ReducibleK mode level targetScope targetCtx stepCount
        (Ty.arrow (elementType.rename rho) motiveType) someRaw someBranch) :
    @ReducibleK mode level targetScope targetCtx stepCount
      motiveType _
      (Term.optionMatch (Term.rename termRenaming scrutinee)
        noneBranch someBranch) :=
  scrutineeIsR.2 termRenaming motiveType noneBranch someBranch
    noneIsR someIsR

/-- Either Kripke SN projection. -/
theorem ReducibleK.sn_of_eitherType
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat}
    {leftType rightType : Ty level scope}
    {raw : RawTerm scope}
    {term : Term context (Ty.eitherType leftType rightType) raw}
    (termIsR :
      @ReducibleK mode level scope context (stepCount + 1)
        (Ty.eitherType leftType rightType) raw term) :
    Term.isStronglyNormalizing term := termIsR.1

/-- Either Kripke ι-closure. -/
theorem ReducibleK.eitherType_match
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat}
    {leftType rightType : Ty level scope}
    {raw : RawTerm scope}
    {scrutinee : Term context (Ty.eitherType leftType rightType) raw}
    (scrutineeIsR :
      @ReducibleK mode level scope context (stepCount + 1)
        (Ty.eitherType leftType rightType) raw scrutinee)
    {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming scope targetScope}
    (termRenaming : TermRenaming context targetCtx rho)
    (motiveType : Ty level targetScope)
    {leftRaw rightRaw : RawTerm targetScope}
    (leftBranch :
      Term targetCtx (Ty.arrow (leftType.rename rho) motiveType) leftRaw)
    (rightBranch :
      Term targetCtx (Ty.arrow (rightType.rename rho) motiveType) rightRaw)
    (leftIsR :
      @ReducibleK mode level targetScope targetCtx stepCount
        (Ty.arrow (leftType.rename rho) motiveType) leftRaw leftBranch)
    (rightIsR :
      @ReducibleK mode level targetScope targetCtx stepCount
        (Ty.arrow (rightType.rename rho) motiveType) rightRaw rightBranch) :
    @ReducibleK mode level targetScope targetCtx stepCount
      motiveType _
      (Term.eitherMatch (Term.rename termRenaming scrutinee)
        leftBranch rightBranch) :=
  scrutineeIsR.2 termRenaming motiveType leftBranch rightBranch
    leftIsR rightIsR

/-- Universe Kripke SN projection.  Closed-leaf direct unfolding. -/
theorem ReducibleK.sn_of_universe
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat}
    {universeLevel : UniverseLevel}
    {levelLe : universeLevel.toNat + 1 ≤ level}
    {raw : RawTerm scope}
    {term : Term context (Ty.universe universeLevel levelLe) raw}
    (termIsR :
      @ReducibleK mode level scope context (stepCount + 1)
        (Ty.universe universeLevel levelLe) raw term) :
    Term.isStronglyNormalizing term := termIsR

/-- Type-variable Kripke SN projection.  Closed-leaf direct unfolding. -/
theorem ReducibleK.sn_of_tyVar
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat}
    {position : Fin scope}
    {raw : RawTerm scope}
    {term : Term context (Ty.tyVar position) raw}
    (termIsR :
      @ReducibleK mode level scope context (stepCount + 1)
        (Ty.tyVar position) raw term) :
    Term.isStronglyNormalizing term := termIsR

/-- Arrow Kripke SN projection.  Projects the first conjunct of the
arrow closure (SN of the function value). -/
theorem ReducibleK.sn_of_arrow
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat}
    {domainType codomainType : Ty level scope}
    {raw : RawTerm scope}
    {term : Term context (Ty.arrow domainType codomainType) raw}
    (termIsR :
      @ReducibleK mode level scope context (stepCount + 1)
        (Ty.arrow domainType codomainType) raw term) :
    Term.isStronglyNormalizing term := termIsR.1

/-- Identity-type Kripke SN projection. -/
theorem ReducibleK.sn_of_id
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat}
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {raw : RawTerm scope}
    {term : Term context (Ty.id carrier leftEndpoint rightEndpoint) raw}
    (termIsR :
      @ReducibleK mode level scope context (stepCount + 1)
        (Ty.id carrier leftEndpoint rightEndpoint) raw term) :
    Term.isStronglyNormalizing term := termIsR.1

/-- Observational-equality Kripke SN projection. -/
theorem ReducibleK.sn_of_oeq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat}
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {raw : RawTerm scope}
    {term : Term context (Ty.oeq carrier leftEndpoint rightEndpoint) raw}
    (termIsR :
      @ReducibleK mode level scope context (stepCount + 1)
        (Ty.oeq carrier leftEndpoint rightEndpoint) raw term) :
    Term.isStronglyNormalizing term := termIsR.1

/-- Strict-identity Kripke SN projection. -/
theorem ReducibleK.sn_of_idStrict
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat}
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {raw : RawTerm scope}
    {term : Term context (Ty.idStrict carrier leftEndpoint rightEndpoint) raw}
    (termIsR :
      @ReducibleK mode level scope context (stepCount + 1)
        (Ty.idStrict carrier leftEndpoint rightEndpoint) raw term) :
    Term.isStronglyNormalizing term := termIsR.1

/-- Equivalence-type Kripke SN projection. -/
theorem ReducibleK.sn_of_equiv
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat}
    {leftTy rightTy : Ty level scope}
    {raw : RawTerm scope}
    {term : Term context (Ty.equiv leftTy rightTy) raw}
    (termIsR :
      @ReducibleK mode level scope context (stepCount + 1)
        (Ty.equiv leftTy rightTy) raw term) :
    Term.isStronglyNormalizing term := termIsR.1

/-- Cubical path Kripke SN projection. -/
theorem ReducibleK.sn_of_path
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat}
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {raw : RawTerm scope}
    {term : Term context (Ty.path carrierType leftEndpoint rightEndpoint) raw}
    (termIsR :
      @ReducibleK mode level scope context (stepCount + 1)
        (Ty.path carrierType leftEndpoint rightEndpoint) raw term) :
    Term.isStronglyNormalizing term := termIsR.1

/-- Cubical glue Kripke SN projection. -/
theorem ReducibleK.sn_of_glue
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat}
    {baseType : Ty level scope}
    {boundaryWitness : RawTerm scope}
    {raw : RawTerm scope}
    {term : Term context (Ty.glue baseType boundaryWitness) raw}
    (termIsR :
      @ReducibleK mode level scope context (stepCount + 1)
        (Ty.glue baseType boundaryWitness) raw term) :
    Term.isStronglyNormalizing term := termIsR.1

/-! ## ===== AGENT STRIP HELPERS =====

Identity-renaming-based SN projection helpers used by `Headline.lean`
to ship eliminator SN headlines without the BANNED universally-
quantified `contractumIsSN` hypothesis-as-postulate.  Each helper
takes ReducibleK premises at the relevant Ty arms, applies the
corresponding Kripke closure clause at identity renaming, projects to
SN of the eliminator-applied raw form, and rewrites via
`RawTerm.rename_identity` to remove the residual renaming on the
function/scrutinee subterm. -/

/-- The canonical identity TermRenaming on any context.  Since
`RawRenaming.identity i = i` definitionally, the typing equation
reduces to `varType context i = (varType context i).rename
RawRenaming.identity`, discharged by `Ty.rename_identity`. -/
theorem TermRenaming.identity
    {mode : Mode} {level scope : Nat}
    (context : Ctx mode level scope) :
    TermRenaming context context (RawRenaming.identity (scope := scope)) :=
  fun position => (Ty.rename_identity (varType context position)).symm

/-- Transport a `ReducibleK` witness along an equation between Ty
indices.  Given `sourceType = targetType` and a reducibility witness
at `sourceType`, build the corresponding witness at `targetType` with
the term cast through the equation.

The proof is by induction on the equation (`cases eqTy`) which
reduces `targetType` to `sourceType` and the `▸ term` to `term`. -/
theorem ReducibleK.transport
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat}
    {sourceType targetType : Ty level scope}
    (eqTy : sourceType = targetType)
    {raw : RawTerm scope}
    {term : Term context sourceType raw}
    (termIsR :
      @ReducibleK mode level scope context stepCount sourceType raw term) :
    @ReducibleK mode level scope context stepCount targetType raw (eqTy ▸ term) := by
  cases eqTy
  exact termIsR

end LeanFX2
