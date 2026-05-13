import LeanFX2.Reducibility.NeutralSNClosure
import LeanFX2.Reducibility.TypedCR2Direct.VarShapeDirect

/-! # LeanFX2.Reducibility.TypedCR2Direct.VarShapeCompoundCubical

K12.20.AZ compound varShape — first half of the compound-Ty arms.
Covers the arrow / sigmaTy / path / glue arms, each shipping the
varShape (variables-as-reducible) and the matching
`_of_neutral_progress_closure` CR3 entry.

Each arm takes a CR3 hypothesis on a sub-Ty (codomain / projection /
base / equiv-fst) to sidestep the structural-recursion wall in the
def-by-recursion `Reducible` predicate.

## Root status

Layer 3 metatheory leaf.  Third slice of `TypedCR2Direct`.  Consumed
by `TypedCR2Compound`'s arrow / sigmaTy / path / glue cases. -/

namespace LeanFX2

/-! ### K12.20.AZ compound varShape — SN-only-closure compound types

Four compound-Ty `_of_varShape` lemmas where Reducible's closure
clause demands only SN of the eliminator result (not full
Reducible).  These extend K12.20.E's SN-direct batch with the
SN-only-closure compound arms — dependent Π, HoTT identity,
observational equality, strict identity — each discharged by ONE
Stage 1 neutral-head SN helper.  Compound arms with
Reducible-on-sub-Ty closures (arrow / sigmaTy / listType /
optionType / eitherType / path / glue / equiv / refine / record)
require induction-on-Ty and ship later in K12.20.BA+. -/

/-- **K12.20.U2 arrow varShape arm**: variables are reducible at
function type once the codomain CR3 step is available.

This is the binder-lift entry point for the arrow candidate.  The
function variable itself is SN by `Term.isStronglyNormalizing_of_varShape`.
For the application closure, `app (var position) argumentRaw` is neutral;
the raw Stage-1 lemma `RawTerm.app_var_isStronglyNormalizing` supplies the
progress-closure needed by the codomain CR3 hook. -/
theorem Reducible.arrow_of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {position : Fin scope}
    (term :
        Term context (Ty.arrow domainType codomainType)
          (RawTerm.var position))
    (codomainCR3 :
      ∀ {sourceRaw : RawTerm scope}
        (sourceTerm : Term context codomainType sourceRaw),
        RawTerm.IsNeutral sourceRaw →
        (∀ targetRaw : RawTerm scope,
          RawStep.parProgress sourceRaw targetRaw →
          RawTerm.isStronglyNormalizing targetRaw) →
        Reducible codomainType sourceTerm) :
    Reducible (Ty.arrow domainType codomainType) term :=
  ⟨Term.isStronglyNormalizing_of_varShape term,
   fun {_argumentRaw} argumentTerm argumentIsReducible =>
     codomainCR3 (Term.app term argumentTerm)
       (RawTerm.IsNeutral.app (RawTerm.IsNeutral.var position))
       (fun _targetRaw progressStep =>
         RawTerm.isStronglyNormalizing.step_preserves
           (RawTerm.app_var_isStronglyNormalizing position
             (Reducible.isStronglyNormalizing argumentIsReducible))
           progressStep)⟩

/-- **K12.20.U2 arrow CR3 arm**: a neutral function is reducible at
`Ty.arrow domain codomain` when every raw progress reduct is SN and
the codomain CR3 hook is available.

The function itself is SN by the neutral progress-closure wrapper.
For an argument, `app neutral argument` is neutral and strongly
normalizing by `RawTerm.app_neutral_isStronglyNormalizing`; that SN
witness supplies the codomain CR3 hook's progress-closure premise. -/
theorem Reducible.arrow_of_neutral_progress_closure
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {sourceRaw : RawTerm scope}
    (sourceTerm :
      Term context (Ty.arrow domainType codomainType) sourceRaw)
    (sourceIsNeutral : RawTerm.IsNeutral sourceRaw)
    (closure :
      ∀ targetRaw : RawTerm scope,
        RawStep.parProgress sourceRaw targetRaw →
        RawTerm.isStronglyNormalizing targetRaw)
    (codomainCR3 :
      ∀ {codomainRaw : RawTerm scope}
        (codomainTerm : Term context codomainType codomainRaw),
        RawTerm.IsNeutral codomainRaw →
        (∀ targetRaw : RawTerm scope,
          RawStep.parProgress codomainRaw targetRaw →
          RawTerm.isStronglyNormalizing targetRaw) →
        Reducible codomainType codomainTerm) :
    Reducible (Ty.arrow domainType codomainType) sourceTerm := by
  have sourceIsSN : Term.isStronglyNormalizing sourceTerm :=
    Term.isStronglyNormalizing_of_neutral_progress_closure
      sourceTerm sourceIsNeutral closure
  refine ⟨sourceIsSN, ?_⟩
  intro argumentRaw argumentTerm argumentIsReducible
  have appIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.app sourceRaw argumentRaw) :=
    RawTerm.app_neutral_isStronglyNormalizing
      sourceIsNeutral
      sourceIsSN
      (Reducible.isStronglyNormalizing argumentIsReducible)
  exact codomainCR3 (Term.app sourceTerm argumentTerm)
    (RawTerm.IsNeutral.app sourceIsNeutral)
    (fun _targetRaw progressStep =>
      RawTerm.isStronglyNormalizing.step_preserves appIsSN progressStep)

/-- **K12.20.U2 sigmaTy varShape arm**: variables are reducible at
dependent-pair type once the first-projection CR3 step is available.

The sigma candidate demands SN of the pair-shaped term, full Reducible
for `fst`, and SN for `snd`.  The raw `fst_var` / `snd_var` lemmas
provide the neutral projection SN closures; the full first projection
is delegated to the recursive CR3 hook for `firstType`. -/
theorem Reducible.sigmaTy_of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    {position : Fin scope}
    (term :
        Term context (Ty.sigmaTy firstType secondType)
          (RawTerm.var position))
    (firstTypeCR3 :
      ∀ {sourceRaw : RawTerm scope}
        (sourceTerm : Term context firstType sourceRaw),
        RawTerm.IsNeutral sourceRaw →
        (∀ targetRaw : RawTerm scope,
          RawStep.parProgress sourceRaw targetRaw →
          RawTerm.isStronglyNormalizing targetRaw) →
        Reducible firstType sourceTerm) :
    Reducible (Ty.sigmaTy firstType secondType) term :=
  ⟨Term.isStronglyNormalizing_of_varShape term,
   firstTypeCR3 (Term.fst term)
     (RawTerm.IsNeutral.fst (RawTerm.IsNeutral.var position))
     (fun _targetRaw progressStep =>
       RawTerm.isStronglyNormalizing.step_preserves
         (RawTerm.fst_var_isStronglyNormalizing position) progressStep),
   RawTerm.snd_var_isStronglyNormalizing position⟩

/-- **K12.20.U2 sigmaTy CR3 arm**: a neutral dependent pair is
reducible at `Ty.sigmaTy firstType secondType` when every raw
progress reduct is SN and the first-projection CR3 hook is available.

This matches the asymmetric sigma candidate: SN for the pair itself,
full Reducible for `fst`, and SN for `snd`.  The second projection
remains SN-only by the current K12.7 closure shape. -/
theorem Reducible.sigmaTy_of_neutral_progress_closure
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    {sourceRaw : RawTerm scope}
    (sourceTerm :
      Term context (Ty.sigmaTy firstType secondType) sourceRaw)
    (sourceIsNeutral : RawTerm.IsNeutral sourceRaw)
    (closure :
      ∀ targetRaw : RawTerm scope,
        RawStep.parProgress sourceRaw targetRaw →
        RawTerm.isStronglyNormalizing targetRaw)
    (firstTypeCR3 :
      ∀ {firstRaw : RawTerm scope}
        (firstTerm : Term context firstType firstRaw),
        RawTerm.IsNeutral firstRaw →
        (∀ targetRaw : RawTerm scope,
          RawStep.parProgress firstRaw targetRaw →
          RawTerm.isStronglyNormalizing targetRaw) →
        Reducible firstType firstTerm) :
    Reducible (Ty.sigmaTy firstType secondType) sourceTerm := by
  have sourceIsSN : Term.isStronglyNormalizing sourceTerm :=
    Term.isStronglyNormalizing_of_neutral_progress_closure
      sourceTerm sourceIsNeutral closure
  refine ⟨sourceIsSN, ?_, ?_⟩
  · have fstIsSN :
        RawTerm.isStronglyNormalizing (RawTerm.fst sourceRaw) :=
      RawTerm.fst_neutral_isStronglyNormalizing
        sourceIsNeutral sourceIsSN
    exact firstTypeCR3 (Term.fst sourceTerm)
      (RawTerm.IsNeutral.fst sourceIsNeutral)
      (fun _targetRaw progressStep =>
        RawTerm.isStronglyNormalizing.step_preserves fstIsSN progressStep)
  · exact RawTerm.snd_neutral_isStronglyNormalizing
      sourceIsNeutral sourceIsSN

/-- **K12.20.U2 path varShape arm**: variables are reducible at cubical
path type once carrier CR3 is available.

The path candidate's eliminator closure returns full Reducible at the
carrier type.  `pathApp (var position) interval` is neutral, and the
existing raw helper supplies the progress-closure SN needed by the
carrier CR3 hook. -/
theorem Reducible.path_of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {position : Fin scope}
    (term :
        Term context (Ty.path carrierType leftEndpoint rightEndpoint)
          (RawTerm.var position))
    (carrierCR3 :
      ∀ {sourceRaw : RawTerm scope}
        (sourceTerm : Term context carrierType sourceRaw),
        RawTerm.IsNeutral sourceRaw →
        (∀ targetRaw : RawTerm scope,
          RawStep.parProgress sourceRaw targetRaw →
          RawTerm.isStronglyNormalizing targetRaw) →
        Reducible carrierType sourceTerm) :
    Reducible (Ty.path carrierType leftEndpoint rightEndpoint) term :=
  ⟨Term.isStronglyNormalizing_of_varShape term,
   fun modeIsUnivalent {_intervalRaw} intervalTerm intervalIsSN =>
     carrierCR3 (Term.pathApp modeIsUnivalent term intervalTerm)
       (RawTerm.IsNeutral.pathApp (RawTerm.IsNeutral.var position))
       (fun _targetRaw progressStep =>
         RawTerm.isStronglyNormalizing.step_preserves
           (RawTerm.pathApp_var_isStronglyNormalizing position intervalIsSN)
           progressStep)⟩

/-- **K12.20.U2 path CR3 arm**: a neutral path is reducible at
`Ty.path carrierType leftEndpoint rightEndpoint` when every raw
progress reduct is SN and the carrier CR3 hook is available.

The path candidate's output closure is full Reducible at the carrier
type.  The interval argument remains SN-only, matching the current
K12.12 closure where `Ty.interval` is a closed leaf rather than a
structural sub-Ty of the path type. -/
theorem Reducible.path_of_neutral_progress_closure
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {sourceRaw : RawTerm scope}
    (sourceTerm :
      Term context (Ty.path carrierType leftEndpoint rightEndpoint) sourceRaw)
    (sourceIsNeutral : RawTerm.IsNeutral sourceRaw)
    (closure :
      ∀ targetRaw : RawTerm scope,
        RawStep.parProgress sourceRaw targetRaw →
        RawTerm.isStronglyNormalizing targetRaw)
    (carrierCR3 :
      ∀ {carrierRaw : RawTerm scope}
        (carrierTerm : Term context carrierType carrierRaw),
        RawTerm.IsNeutral carrierRaw →
        (∀ targetRaw : RawTerm scope,
          RawStep.parProgress carrierRaw targetRaw →
          RawTerm.isStronglyNormalizing targetRaw) →
        Reducible carrierType carrierTerm) :
    Reducible
      (Ty.path carrierType leftEndpoint rightEndpoint) sourceTerm := by
  have sourceIsSN : Term.isStronglyNormalizing sourceTerm :=
    Term.isStronglyNormalizing_of_neutral_progress_closure
      sourceTerm sourceIsNeutral closure
  refine ⟨sourceIsSN, ?_⟩
  intro modeIsUnivalent intervalRaw intervalTerm intervalIsSN
  have pathAppIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.pathApp sourceRaw intervalRaw) :=
    RawTerm.pathApp_neutral_isStronglyNormalizing
      sourceIsNeutral sourceIsSN intervalIsSN
  exact carrierCR3
    (Term.pathApp modeIsUnivalent sourceTerm intervalTerm)
    (RawTerm.IsNeutral.pathApp sourceIsNeutral)
    (fun _targetRaw progressStep =>
      RawTerm.isStronglyNormalizing.step_preserves pathAppIsSN progressStep)

/-- **K12.20.U2 glue CR3 arm**: a neutral glued value is reducible at
`Ty.glue baseType boundaryWitness` when every raw progress reduct is
SN and the base-type CR3 hook is available.

The Glue candidate demands full Reducible at the base type for
`glueElim`.  Since `baseType` is a strict sub-Ty of the Glue type,
the proof delegates that projection result to the recursive CR3 hook;
`RawTerm.glueElim_neutral_isStronglyNormalizing` supplies the raw
progress-closure SN premise for the neutral projection. -/
theorem Reducible.glue_of_neutral_progress_closure
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {baseType : Ty level scope}
    {boundaryWitness : RawTerm scope}
    {sourceRaw : RawTerm scope}
    (sourceTerm :
      Term context (Ty.glue baseType boundaryWitness) sourceRaw)
    (sourceIsNeutral : RawTerm.IsNeutral sourceRaw)
    (closure :
      ∀ targetRaw : RawTerm scope,
        RawStep.parProgress sourceRaw targetRaw →
        RawTerm.isStronglyNormalizing targetRaw)
    (baseTypeCR3 :
      ∀ {baseRaw : RawTerm scope}
        (baseTerm : Term context baseType baseRaw),
        RawTerm.IsNeutral baseRaw →
        (∀ targetRaw : RawTerm scope,
          RawStep.parProgress baseRaw targetRaw →
          RawTerm.isStronglyNormalizing targetRaw) →
        Reducible baseType baseTerm) :
    Reducible (Ty.glue baseType boundaryWitness) sourceTerm := by
  have sourceIsSN : Term.isStronglyNormalizing sourceTerm :=
    Term.isStronglyNormalizing_of_neutral_progress_closure
      sourceTerm sourceIsNeutral closure
  refine ⟨sourceIsSN, ?_⟩
  intro modeIsUnivalent
  have glueElimIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.glueElim sourceRaw) :=
    RawTerm.glueElim_neutral_isStronglyNormalizing
      sourceIsNeutral sourceIsSN
  exact baseTypeCR3
    (Term.glueElim modeIsUnivalent sourceTerm)
    (RawTerm.IsNeutral.glueElim sourceIsNeutral)
    (fun _targetRaw progressStep =>
      RawTerm.isStronglyNormalizing.step_preserves glueElimIsSN progressStep)

/-- **K12.20.U2 glue varShape arm**: variables are reducible at Glue
type once base-type CR3 is available. -/
theorem Reducible.glue_of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {baseType : Ty level scope}
    {boundaryWitness : RawTerm scope}
    {position : Fin scope}
    (term :
        Term context (Ty.glue baseType boundaryWitness)
          (RawTerm.var position))
    (baseTypeCR3 :
      ∀ {sourceRaw : RawTerm scope}
        (sourceTerm : Term context baseType sourceRaw),
        RawTerm.IsNeutral sourceRaw →
        (∀ targetRaw : RawTerm scope,
          RawStep.parProgress sourceRaw targetRaw →
          RawTerm.isStronglyNormalizing targetRaw) →
        Reducible baseType sourceTerm) :
    Reducible (Ty.glue baseType boundaryWitness) term :=
  ⟨Term.isStronglyNormalizing_of_varShape term,
   fun modeIsUnivalent =>
     baseTypeCR3 (Term.glueElim modeIsUnivalent term)
       (RawTerm.IsNeutral.glueElim (RawTerm.IsNeutral.var position))
       (fun _targetRaw progressStep =>
         RawTerm.isStronglyNormalizing.step_preserves
           (RawTerm.glueElim_var_isStronglyNormalizing position)
           progressStep)⟩

/-- **K12.20.U2 equiv varShape arm**: variables are reducible at
equivalence type once codomain CR3 is available. -/
theorem Reducible.equiv_of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierA carrierB : Ty level scope}
    {position : Fin scope}
    (term :
        Term context (Ty.equiv carrierA carrierB)
          (RawTerm.var position))
    (carrierBCR3 :
      ∀ {sourceRaw : RawTerm scope}
        (sourceTerm : Term context carrierB sourceRaw),
        RawTerm.IsNeutral sourceRaw →
        (∀ targetRaw : RawTerm scope,
          RawStep.parProgress sourceRaw targetRaw →
          RawTerm.isStronglyNormalizing targetRaw) →
        Reducible carrierB sourceTerm) :
    Reducible (Ty.equiv carrierA carrierB) term :=
  ⟨Term.isStronglyNormalizing_of_varShape term,
   fun {_argumentRaw} argumentTerm argumentIsReducible =>
     carrierBCR3 (Term.equivApp term argumentTerm)
       (RawTerm.IsNeutral.equivApp (RawTerm.IsNeutral.var position))
       (fun _targetRaw progressStep =>
         RawTerm.isStronglyNormalizing.step_preserves
           (RawTerm.equivApp_var_isStronglyNormalizing position
             (Reducible.isStronglyNormalizing argumentIsReducible))
           progressStep)⟩

/-- **K12.20.U2 equiv CR3 arm**: a neutral equivalence is reducible at
`Ty.equiv carrierA carrierB` when every raw progress reduct is SN and
the codomain CR3 hook is available.

The equivalence candidate mirrors the arrow candidate: for every
reducible argument at `carrierA`, `equivApp neutral argument` is a
neutral term at `carrierB`.  The raw neutral application helper gives
the progress-closure SN premise, and the recursive `carrierB` CR3 hook
upgrades that neutral result to full Reducible. -/
theorem Reducible.equiv_of_neutral_progress_closure
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierA carrierB : Ty level scope}
    {sourceRaw : RawTerm scope}
    (sourceTerm : Term context (Ty.equiv carrierA carrierB) sourceRaw)
    (sourceIsNeutral : RawTerm.IsNeutral sourceRaw)
    (closure :
      ∀ targetRaw : RawTerm scope,
        RawStep.parProgress sourceRaw targetRaw →
        RawTerm.isStronglyNormalizing targetRaw)
    (carrierBCR3 :
      ∀ {carrierBRaw : RawTerm scope}
        (carrierBTerm : Term context carrierB carrierBRaw),
        RawTerm.IsNeutral carrierBRaw →
        (∀ targetRaw : RawTerm scope,
          RawStep.parProgress carrierBRaw targetRaw →
          RawTerm.isStronglyNormalizing targetRaw) →
        Reducible carrierB carrierBTerm) :
    Reducible (Ty.equiv carrierA carrierB) sourceTerm := by
  have sourceIsSN : Term.isStronglyNormalizing sourceTerm :=
    Term.isStronglyNormalizing_of_neutral_progress_closure
      sourceTerm sourceIsNeutral closure
  refine ⟨sourceIsSN, ?_⟩
  intro argumentRaw argumentTerm argumentIsReducible
  have equivAppIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.equivApp sourceRaw argumentRaw) :=
    RawTerm.equivApp_neutral_isStronglyNormalizing
      sourceIsNeutral
      sourceIsSN
      (Reducible.isStronglyNormalizing argumentIsReducible)
  exact carrierBCR3
    (Term.equivApp sourceTerm argumentTerm)
    (RawTerm.IsNeutral.equivApp sourceIsNeutral)
    (fun _targetRaw progressStep =>
      RawTerm.isStronglyNormalizing.step_preserves
        equivAppIsSN progressStep)

/-- **K12.20.U2 refine CR3 arm**: a neutral refined value is reducible
at `Ty.refine baseType predicate` when every raw progress reduct is SN
and the base-type CR3 hook is available.

The refinement candidate demands full Reducible at the base type for
`refineElim`.  The raw neutral helper supplies SN for the neutral
projection, and the recursive base-type CR3 hook upgrades that neutral
projection to the required Reducible witness. -/
theorem Reducible.refine_of_neutral_progress_closure
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {baseType : Ty level scope}
    {predicate : RawTerm (scope + 1)}
    {sourceRaw : RawTerm scope}
    (sourceTerm :
      Term context (Ty.refine baseType predicate) sourceRaw)
    (sourceIsNeutral : RawTerm.IsNeutral sourceRaw)
    (closure :
      ∀ targetRaw : RawTerm scope,
        RawStep.parProgress sourceRaw targetRaw →
        RawTerm.isStronglyNormalizing targetRaw)
    (baseTypeCR3 :
      ∀ {baseRaw : RawTerm scope}
        (baseTerm : Term context baseType baseRaw),
        RawTerm.IsNeutral baseRaw →
        (∀ targetRaw : RawTerm scope,
          RawStep.parProgress baseRaw targetRaw →
          RawTerm.isStronglyNormalizing targetRaw) →
        Reducible baseType baseTerm) :
    Reducible (Ty.refine baseType predicate) sourceTerm := by
  have sourceIsSN : Term.isStronglyNormalizing sourceTerm :=
    Term.isStronglyNormalizing_of_neutral_progress_closure
      sourceTerm sourceIsNeutral closure
  refine ⟨sourceIsSN, ?_⟩
  have refineElimIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.refineElim sourceRaw) :=
    RawTerm.refineElim_neutral_isStronglyNormalizing
      sourceIsNeutral sourceIsSN
  exact baseTypeCR3
    (Term.refineElim sourceTerm)
    (RawTerm.IsNeutral.refineElim sourceIsNeutral)
    (fun _targetRaw progressStep =>
      RawTerm.isStronglyNormalizing.step_preserves
        refineElimIsSN progressStep)

/-- **K12.20.U2 refine varShape arm**: variables are reducible at
refinement type once base-type CR3 is available. -/
theorem Reducible.refine_of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {baseType : Ty level scope}
    {predicate : RawTerm (scope + 1)}
    {position : Fin scope}
    (term :
        Term context (Ty.refine baseType predicate)
          (RawTerm.var position))
    (baseTypeCR3 :
      ∀ {sourceRaw : RawTerm scope}
        (sourceTerm : Term context baseType sourceRaw),
        RawTerm.IsNeutral sourceRaw →
        (∀ targetRaw : RawTerm scope,
          RawStep.parProgress sourceRaw targetRaw →
          RawTerm.isStronglyNormalizing targetRaw) →
        Reducible baseType sourceTerm) :
    Reducible (Ty.refine baseType predicate) term :=
  ⟨Term.isStronglyNormalizing_of_varShape term,
   baseTypeCR3 (Term.refineElim term)
     (RawTerm.IsNeutral.refineElim (RawTerm.IsNeutral.var position))
     (fun _targetRaw progressStep =>
       RawTerm.isStronglyNormalizing.step_preserves
         (RawTerm.refineElim_var_isStronglyNormalizing position)
         progressStep)⟩

/-- **K12.20.U2 record CR3 arm**: a neutral single-field record is
reducible at `Ty.record singleFieldType` when every raw progress reduct
is SN and the field-type CR3 hook is available.

The record candidate demands full Reducible for the projected field.
The raw neutral projection helper supplies SN for `recordProj`, and the
recursive field-type CR3 hook upgrades that neutral projection to the
required Reducible witness. -/
theorem Reducible.record_of_neutral_progress_closure
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {singleFieldType : Ty level scope}
    {sourceRaw : RawTerm scope}
    (sourceTerm :
      Term context (Ty.record singleFieldType) sourceRaw)
    (sourceIsNeutral : RawTerm.IsNeutral sourceRaw)
    (closure :
      ∀ targetRaw : RawTerm scope,
        RawStep.parProgress sourceRaw targetRaw →
        RawTerm.isStronglyNormalizing targetRaw)
    (singleFieldTypeCR3 :
      ∀ {fieldRaw : RawTerm scope}
        (fieldTerm : Term context singleFieldType fieldRaw),
        RawTerm.IsNeutral fieldRaw →
        (∀ targetRaw : RawTerm scope,
          RawStep.parProgress fieldRaw targetRaw →
          RawTerm.isStronglyNormalizing targetRaw) →
        Reducible singleFieldType fieldTerm) :
    Reducible (Ty.record singleFieldType) sourceTerm := by
  have sourceIsSN : Term.isStronglyNormalizing sourceTerm :=
    Term.isStronglyNormalizing_of_neutral_progress_closure
      sourceTerm sourceIsNeutral closure
  refine ⟨sourceIsSN, ?_⟩
  have recordProjIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.recordProj sourceRaw) :=
    RawTerm.recordProj_neutral_isStronglyNormalizing
      sourceIsNeutral sourceIsSN
  exact singleFieldTypeCR3
    (Term.recordProj sourceTerm)
    (RawTerm.IsNeutral.recordProj sourceIsNeutral)
    (fun _targetRaw progressStep =>
      RawTerm.isStronglyNormalizing.step_preserves
        recordProjIsSN progressStep)

/-- **K12.20.U2 record varShape arm**: variables are reducible at
single-field record type once field-type CR3 is available. -/
theorem Reducible.record_of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {singleFieldType : Ty level scope}
    {position : Fin scope}
    (term :
        Term context (Ty.record singleFieldType)
          (RawTerm.var position))
    (singleFieldTypeCR3 :
      ∀ {sourceRaw : RawTerm scope}
        (sourceTerm : Term context singleFieldType sourceRaw),
        RawTerm.IsNeutral sourceRaw →
        (∀ targetRaw : RawTerm scope,
          RawStep.parProgress sourceRaw targetRaw →
          RawTerm.isStronglyNormalizing targetRaw) →
        Reducible singleFieldType sourceTerm) :
    Reducible (Ty.record singleFieldType) term :=
  ⟨Term.isStronglyNormalizing_of_varShape term,
   singleFieldTypeCR3 (Term.recordProj term)
     (RawTerm.IsNeutral.recordProj (RawTerm.IsNeutral.var position))
     (fun _targetRaw progressStep =>
       RawTerm.isStronglyNormalizing.step_preserves
         (RawTerm.recordProj_var_isStronglyNormalizing position)
         progressStep)⟩

/-- **K12.20.U2 codata CR3 arm**: a neutral codata value is reducible
at `Ty.codata stateType outputType` when every raw progress reduct is
SN and the output-type CR3 hook is available.

The codata candidate demands full Reducible for the observed output.
The raw neutral observation helper supplies SN for `codataDest`, and
the recursive output-type CR3 hook upgrades that neutral observation to
the required Reducible witness. -/
theorem Reducible.codata_of_neutral_progress_closure
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stateType outputType : Ty level scope}
    {sourceRaw : RawTerm scope}
    (sourceTerm :
      Term context (Ty.codata stateType outputType) sourceRaw)
    (sourceIsNeutral : RawTerm.IsNeutral sourceRaw)
    (closure :
      ∀ targetRaw : RawTerm scope,
        RawStep.parProgress sourceRaw targetRaw →
        RawTerm.isStronglyNormalizing targetRaw)
    (outputTypeCR3 :
      ∀ {outputRaw : RawTerm scope}
        (outputTerm : Term context outputType outputRaw),
        RawTerm.IsNeutral outputRaw →
        (∀ targetRaw : RawTerm scope,
          RawStep.parProgress outputRaw targetRaw →
          RawTerm.isStronglyNormalizing targetRaw) →
        Reducible outputType outputTerm) :
    Reducible (Ty.codata stateType outputType) sourceTerm := by
  have sourceIsSN : Term.isStronglyNormalizing sourceTerm :=
    Term.isStronglyNormalizing_of_neutral_progress_closure
      sourceTerm sourceIsNeutral closure
  refine ⟨sourceIsSN, ?_⟩
  have codataDestIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.codataDest sourceRaw) :=
    RawTerm.codataDest_neutral_isStronglyNormalizing
      sourceIsNeutral sourceIsSN
  exact outputTypeCR3
    (Term.codataDest sourceTerm)
    (RawTerm.IsNeutral.codataDest sourceIsNeutral)
    (fun _targetRaw progressStep =>
      RawTerm.isStronglyNormalizing.step_preserves
        codataDestIsSN progressStep)

/-- **K12.20.U2 codata varShape arm**: variables are reducible at
codata type once output-type CR3 is available. -/
theorem Reducible.codata_of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stateType outputType : Ty level scope}
    {position : Fin scope}
    (term :
        Term context (Ty.codata stateType outputType)
          (RawTerm.var position))
    (outputTypeCR3 :
      ∀ {sourceRaw : RawTerm scope}
        (sourceTerm : Term context outputType sourceRaw),
        RawTerm.IsNeutral sourceRaw →
        (∀ targetRaw : RawTerm scope,
          RawStep.parProgress sourceRaw targetRaw →
          RawTerm.isStronglyNormalizing targetRaw) →
        Reducible outputType sourceTerm) :
    Reducible (Ty.codata stateType outputType) term :=
  ⟨Term.isStronglyNormalizing_of_varShape term,
   outputTypeCR3 (Term.codataDest term)
     (RawTerm.IsNeutral.codataDest (RawTerm.IsNeutral.var position))
     (fun _targetRaw progressStep =>
       RawTerm.isStronglyNormalizing.step_preserves
         (RawTerm.codataDest_var_isStronglyNormalizing position)
         progressStep)⟩



end LeanFX2
