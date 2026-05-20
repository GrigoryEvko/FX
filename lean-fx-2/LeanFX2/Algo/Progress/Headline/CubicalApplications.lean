import LeanFX2.Algo.Progress.Headline.Prelude


namespace LeanFX2

variable {mode : Mode} {level scope : Nat}

/-- Algo-layer destructor for `Term.pathLam` (cubical path
abstraction).  Given a term whose `headCtor` is `.pathLam` and
whose raw form is `RawTerm.pathLam bodyRaw` at a path type
`Ty.path carrierType leftEndpoint rightEndpoint`, extracts the
mode-univalent witness, the typed body under one interval
binder, and an HEq witness that the original term equals the
reconstructed `Term.pathLam` application.

`Term.pathLam` is the unique Term ctor producing `RawTerm.pathLam`,
so the destructor's `cases` only sees the pathLam case.  The
extra wrinkle vs `Term.modIntroDestructAlgo` is the
`modeIsUnivalent : mode = Mode.univalent` proof carried by
`Term.pathLam`'s signature — we recover that proof from the
cases pattern and thread it back into the HEq witness. -/
def Term.pathLamDestructAlgo {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {bodyRaw : RawTerm (scope + 1)}
    (someTerm :
      Term context (Ty.path carrierType leftEndpoint rightEndpoint)
        (RawTerm.pathLam bodyRaw))
    (headEq : someTerm.headCtor = Term.HeadCtor.pathLam) :
    Σ' (modeIsUnivalent : mode = Mode.univalent)
       (body : Term (context.cons Ty.interval) carrierType.weaken bodyRaw),
       HEq someTerm
         (Term.pathLam modeIsUnivalent carrierType
            leftEndpoint rightEndpoint body) := by
  suffices key :
      ∀ {someType : Ty level scope}
        (genericTerm : Term context someType (RawTerm.pathLam bodyRaw))
        (sTyEq : someType = Ty.path carrierType leftEndpoint rightEndpoint)
        (hcEq : genericTerm.headCtor = Term.HeadCtor.pathLam),
        Σ' (modeIsUnivalent : mode = Mode.univalent)
           (body : Term (context.cons Ty.interval) carrierType.weaken bodyRaw),
           HEq genericTerm
             (Term.pathLam modeIsUnivalent carrierType
                leftEndpoint rightEndpoint body) by
    exact key someTerm rfl headEq
  intro someType genericTerm sTyEq _hcEq
  cases genericTerm
  case pathLam modeIsUnivalent innerCarrier innerLeft innerRight body =>
    have pathEq := Ty.path.inj sTyEq
    cases pathEq.1
    cases pathEq.2.1
    cases pathEq.2.2
    exact ⟨modeIsUnivalent, body, HEq.rfl⟩

/-- Focused progress theorem for the `Term.pathApp` head (cubical
path application).  Every well-typed `pathApp`-headed term is
either in WHNF (when the path position is not a `pathLam`) or
takes a cubical β-step (when the path position IS a `pathLam`).

M05.D.2 conditional eliminator #10 of 17.  Same template as
`Term.app_progress_or_step` but with `Ty.path` source type for
the path position, `Term.pathLamDestructAlgo` for the typed
body + modeIsUnivalent witness extraction, and `Step.betaPathApp`
as the firing contraction.  Threads the `modeIsUnivalent` proof
recovered from the destructor through both the rewrite and the
firing step. -/
theorem Term.pathApp_progress_or_step
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {pathRaw intervalRaw : RawTerm scope}
    (pathTerm :
      Term context (Ty.path carrierType leftEndpoint rightEndpoint) pathRaw)
    (intervalTerm : Term context Ty.interval intervalRaw) :
    Term.isWHNF (Term.pathApp modeIsUnivalent pathTerm intervalTerm) = true ∨
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.pathApp modeIsUnivalent pathTerm intervalTerm) target := by
  cases h : pathTerm.headCtor with
  | pathLam =>
      obtain ⟨bodyRaw, rawEq⟩ := Term.headCtor_pathLam_raw pathTerm h
      cases rawEq
      obtain ⟨univWitness, body, bodyHeq⟩ :=
        Term.pathLamDestructAlgo pathTerm h
      have bodyEq := eq_of_heq bodyHeq
      rw [bodyEq]
      exact Or.inr ⟨_, _, _, Step.betaPathApp univWitness body intervalTerm⟩
  | var =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | unit =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | lam =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | app =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | lamPi =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | appPi =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | pair =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | fst =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | snd =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | boolTrue =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | boolFalse =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | boolElim =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | natZero =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | natSucc =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | natElim =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | natRec =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | listNil =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | listCons =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | listElim =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | optionNone =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | optionSome =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | optionMatch =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | eitherInl =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | eitherInr =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | eitherMatch =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | refl =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | idJ =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | oeqRefl =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | oeqJ =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | oeqFunext =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | idStrictRefl =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | idStrictRec =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | modIntro =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | modElim =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | subsume =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | interval0 =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | interval1 =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | intervalOpp =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | intervalMeet =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | intervalJoin =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | pathApp =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | glueIntro =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | glueElim =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | transp =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | hcomp =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | recordIntro =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | recordProj =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | refineIntro =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | refineElim =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | codataUnfold =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | codataDest =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | sessionSend =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | sessionRecv =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | effectPerform =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | universeCode =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | cumulUp =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | equivReflId =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | funextRefl =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | equivReflIdAtId =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | funextReflAtId =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | equivIntroHet =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | equivApp =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | uaIntroHet =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | funextIntroHet =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | uaToEquiv =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | equivApply =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | arrowCode =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | piTyCode =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | sigmaTyCode =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | productCode =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | sumCode =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | listCode =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | optionCode =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | eitherCode =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | idCode =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | equivCode =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide

/-- Algo-layer destructor for `Term.glueIntro` (cubical Glue
introduction).  Given a term whose `headCtor` is `.glueIntro`
and whose raw form is `RawTerm.glueIntro baseRaw partialRaw` at
a glue type `Ty.glue baseType boundaryWitness`, extracts the
mode-univalent witness, base and partial typed terms, and an
HEq witness.

`Term.glueIntro` is the unique Term ctor producing
`RawTerm.glueIntro`, so the destructor's `cases` only sees the
glueIntro case.  The signature carries `modeIsUnivalent` and
two payload terms; we recover all three via the cases pattern
and thread them back into the HEq witness. -/
def Term.glueIntroDestructAlgo {context : Ctx mode level scope}
    {baseType : Ty level scope}
    {boundaryWitness : RawTerm scope}
    {baseRaw partialRaw : RawTerm scope}
    (someTerm :
      Term context (Ty.glue baseType boundaryWitness)
        (RawTerm.glueIntro baseRaw partialRaw))
    (headEq : someTerm.headCtor = Term.HeadCtor.glueIntro) :
    Σ' (modeIsUnivalent : mode = Mode.univalent)
       (baseValue : Term context baseType baseRaw)
       (partialValue : Term context baseType partialRaw),
       HEq someTerm
         (Term.glueIntro modeIsUnivalent baseType boundaryWitness
            baseValue partialValue) := by
  suffices key :
      ∀ {someType : Ty level scope}
        (genericTerm :
          Term context someType (RawTerm.glueIntro baseRaw partialRaw))
        (sTyEq : someType = Ty.glue baseType boundaryWitness)
        (hcEq : genericTerm.headCtor = Term.HeadCtor.glueIntro),
        Σ' (modeIsUnivalent : mode = Mode.univalent)
           (baseValue : Term context baseType baseRaw)
           (partialValue : Term context baseType partialRaw),
           HEq genericTerm
             (Term.glueIntro modeIsUnivalent baseType boundaryWitness
                baseValue partialValue) by
    exact key someTerm rfl headEq
  intro someType genericTerm sTyEq _hcEq
  cases genericTerm
  case glueIntro modeIsUnivalent innerBase innerBoundary
                 baseValueVal partialValueVal =>
    have glueEq := Ty.glue.inj sTyEq
    cases glueEq.1
    cases glueEq.2
    exact ⟨modeIsUnivalent, baseValueVal, partialValueVal, HEq.rfl⟩

/-- Focused progress theorem for the `Term.glueElim` head
(cubical Glue elimination).  Every well-typed `glueElim`-headed
term is either in WHNF (when the glued position is not a
`glueIntro`) or takes a cubical β-step (when the glued IS a
`glueIntro`).

M05.D.2 conditional eliminator #11 of 17.  Same template as
`Term.modElim_progress_or_step` (single-case destructor by raw
uniqueness) plus the `modeIsUnivalent` proof threaded through
both the outer `glueElim` and the firing
`Step.betaGlueElimIntro`. -/
theorem Term.glueElim_progress_or_step
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {baseType : Ty level scope}
    {boundaryWitness gluedRaw : RawTerm scope}
    (gluedValue :
      Term context (Ty.glue baseType boundaryWitness) gluedRaw) :
    Term.isWHNF (Term.glueElim modeIsUnivalent gluedValue) = true ∨
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.glueElim modeIsUnivalent gluedValue) target := by
  cases h : gluedValue.headCtor with
  | glueIntro =>
      obtain ⟨baseRaw, partialRaw, rawEq⟩ :=
        Term.headCtor_glueIntro_raw gluedValue h
      cases rawEq
      obtain ⟨univWitness, baseValue, partialValue, gluedHeq⟩ :=
        Term.glueIntroDestructAlgo gluedValue h
      have gluedEq := eq_of_heq gluedHeq
      rw [gluedEq]
      exact Or.inr
        ⟨_, _, _,
          Step.betaGlueElimIntro univWitness baseValue partialValue⟩
  | var =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | unit =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | lam =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | app =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | lamPi =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | appPi =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | pair =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | fst =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | snd =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | boolTrue =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | boolFalse =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | boolElim =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | natZero =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | natSucc =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | natElim =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | natRec =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | listNil =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | listCons =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | listElim =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | optionNone =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | optionSome =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | optionMatch =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | eitherInl =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | eitherInr =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | eitherMatch =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | refl =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | idJ =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | oeqRefl =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | oeqJ =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | oeqFunext =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | idStrictRefl =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | idStrictRec =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | modIntro =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | modElim =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | subsume =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | interval0 =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | interval1 =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | intervalOpp =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | intervalMeet =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | intervalJoin =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | pathLam =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | pathApp =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | glueElim =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | transp =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | hcomp =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | recordIntro =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | recordProj =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | refineIntro =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | refineElim =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | codataUnfold =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | codataDest =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | sessionSend =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | sessionRecv =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | effectPerform =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | universeCode =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | cumulUp =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | equivReflId =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | funextRefl =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | equivReflIdAtId =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | funextReflAtId =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | equivIntroHet =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | equivApp =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | uaIntroHet =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | funextIntroHet =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | uaToEquiv =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | equivApply =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | arrowCode =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | piTyCode =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | sigmaTyCode =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | productCode =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | sumCode =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | listCode =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | optionCode =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | eitherCode =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | idCode =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | equivCode =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide

end LeanFX2
