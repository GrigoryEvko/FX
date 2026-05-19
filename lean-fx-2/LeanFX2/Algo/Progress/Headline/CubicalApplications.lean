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
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | unit =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | lam =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | app =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | lamPi =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | appPi =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | pair =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | fst =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | snd =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | boolTrue =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | boolFalse =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | boolElim =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | natZero =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | natSucc =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | natElim =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | natRec =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | listNil =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | listCons =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | listElim =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | optionNone =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | optionSome =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | optionMatch =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | eitherInl =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | eitherInr =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | eitherMatch =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | refl =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | idJ =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | oeqRefl =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | oeqJ =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | oeqFunext =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | idStrictRefl =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | idStrictRec =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | modIntro =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | modElim =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | subsume =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | interval0 =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | interval1 =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | intervalOpp =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | intervalMeet =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | intervalJoin =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | pathApp =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | glueIntro =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | glueElim =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | transp =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | hcomp =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | recordIntro =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | recordProj =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | refineIntro =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | refineElim =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | codataUnfold =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | codataDest =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | sessionSend =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | sessionRecv =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | effectPerform =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | universeCode =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | cumulUp =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | equivReflId =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | funextRefl =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | equivReflIdAtId =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | funextReflAtId =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | equivIntroHet =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | equivApp =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | uaIntroHet =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | funextIntroHet =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | uaToEquiv =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | equivApply =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | arrowCode =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | piTyCode =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | sigmaTyCode =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | productCode =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | sumCode =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | listCode =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | optionCode =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | eitherCode =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | idCode =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | equivCode =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl

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
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | unit =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | lam =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | app =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | lamPi =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | appPi =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | pair =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | fst =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | snd =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | boolTrue =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | boolFalse =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | boolElim =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | natZero =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | natSucc =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | natElim =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | natRec =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | listNil =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | listCons =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | listElim =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | optionNone =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | optionSome =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | optionMatch =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | eitherInl =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | eitherInr =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | eitherMatch =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | refl =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | idJ =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | oeqRefl =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | oeqJ =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | oeqFunext =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | idStrictRefl =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | idStrictRec =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | modIntro =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | modElim =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | subsume =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | interval0 =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | interval1 =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | intervalOpp =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | intervalMeet =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | intervalJoin =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | pathLam =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | pathApp =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | glueElim =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | transp =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | hcomp =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | recordIntro =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | recordProj =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | refineIntro =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | refineElim =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | codataUnfold =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | codataDest =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | sessionSend =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | sessionRecv =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | effectPerform =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | universeCode =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | cumulUp =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | equivReflId =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | funextRefl =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | equivReflIdAtId =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | funextReflAtId =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | equivIntroHet =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | equivApp =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | uaIntroHet =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | funextIntroHet =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | uaToEquiv =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | equivApply =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | arrowCode =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | piTyCode =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | sigmaTyCode =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | productCode =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | sumCode =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | listCode =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | optionCode =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | eitherCode =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | idCode =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | equivCode =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl

end LeanFX2
