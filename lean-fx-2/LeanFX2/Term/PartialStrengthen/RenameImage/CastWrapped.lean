import LeanFX2.Term.PartialStrengthen.RenameImage.Core

/-! # Term/PartialStrengthen/RenameImage/CastWrapped

Rename-image T1 HEq bridges for cast-wrapped rename cases.
-/

namespace LeanFX2

namespace Term

/-- Common `.isSome` interface for type-index cast wrappers.

The 11 cast-wrapped rename-image constructors have two proof surfaces:
an HEq bridge for the full dispatcher result, and an `.isSome` bridge
for recursive totality.  The `.isSome` side should not repeat the
cast-peeling idiom by hand.  This lemma says that if the uncast
dispatcher succeeds, then the same dispatcher succeeds after an
Eq-recursive type-index cast. -/
theorem partialStrengthenTyped?_isSome_of_typeCast
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {someTypeA someTypeB : Ty level sourceScope}
    {someRaw : RawTerm sourceScope}
    (sourceTerm : Term sourceCtx someTypeA someRaw)
    (typeEq : someTypeA = someTypeB)
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (sourceIsSome :
      (partialStrengthenTyped? sourceTerm strengthening).isSome = true) :
    (partialStrengthenTyped? (typeEq ▸ sourceTerm) strengthening).isSome =
      true := by
  rw [partialStrengthenTyped?_isSome_castInvariant]
  exact sourceIsSome

/-- Cast-wrapped strength-T1 case (HEq form): `Term.var`.

The variable rename arm casts the target variable across the
`TermRenaming` evidence for this position.  The dispatcher itself is
cast-invariant at HEq, so the cast-wrapped renamed variable and the
uncast target variable have HEq-related strengthening results.
-/
theorem strengthenTyped?_rename_heq_var
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    (sourcePosition : Fin sourceScope) :
    HEq
      (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.var (context := sourceCtx) sourcePosition))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects))
      (partialStrengthenTyped?
        (Term.var (context := targetCtx) (forwardRename sourcePosition))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)) := by
  dsimp only [Term.rename]
  exact
    partialStrengthenTyped?_castInvariantHEq
      (Term.var (context := targetCtx) (forwardRename sourcePosition))
      (typedRenaming sourcePosition)
      (ContextStrengthening.ofRenaming forwardRename typedRenaming
        renameInverse renameInverseLeft renameInverseInjects)

/-- Cast-wrapped strength-T1 case (HEq form): `Term.appPi`.

The dependent application rename arm wraps the whole result in the
non-rfl `Ty.subst0_rename_commute ...` cast.  The HEq statement peels
that top-level cast and compares against the uncast renamed
application. -/
theorem strengthenTyped?_rename_heq_appPi
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    {domainType : Ty level sourceScope}
    {codomainType : Ty level (sourceScope + 1)}
    {functionRaw argumentRaw : RawTerm sourceScope}
    (functionTerm : Term sourceCtx (Ty.piTy domainType codomainType)
      functionRaw)
    (argumentTerm : Term sourceCtx domainType argumentRaw) :
    HEq
      (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.appPi functionTerm argumentTerm))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects))
      (partialStrengthenTyped?
        (Term.appPi
          (Term.rename typedRenaming functionTerm)
          (Term.rename typedRenaming argumentTerm))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)) := by
  dsimp only [Term.rename]
  exact
    partialStrengthenTyped?_castInvariantHEq
      (Term.appPi
        (Term.rename typedRenaming functionTerm)
        (Term.rename typedRenaming argumentTerm))
      (Ty.subst0_rename_commute codomainType domainType argumentRaw
        forwardRename).symm
      (ContextStrengthening.ofRenaming forwardRename typedRenaming
        renameInverse renameInverseLeft renameInverseInjects)

/-- Cast-wrapped strength-T1 case (HEq form): `Term.snd`.

The second projection rename arm wraps the whole result in the non-rfl
`Ty.subst0_rename_commute` cast for the projected second component
type.  The HEq form exposes that the cast-wrapped dispatcher result is
the same computation as the uncast renamed `snd`.
-/
theorem strengthenTyped?_rename_heq_snd
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    {firstType : Ty level sourceScope}
    {secondType : Ty level (sourceScope + 1)}
    {pairRaw : RawTerm sourceScope}
    (pairTerm : Term sourceCtx (Ty.sigmaTy firstType secondType) pairRaw) :
    HEq
      (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.snd pairTerm))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects))
      (partialStrengthenTyped?
        (Term.snd (Term.rename typedRenaming pairTerm))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)) := by
  dsimp only [Term.rename]
  exact
    partialStrengthenTyped?_castInvariantHEq
      (Term.snd (Term.rename typedRenaming pairTerm))
      (Ty.subst0_rename_commute secondType firstType
        (RawTerm.fst pairRaw) forwardRename).symm
      (ContextStrengthening.ofRenaming forwardRename typedRenaming
        renameInverse renameInverseLeft renameInverseInjects)

/-- Cast-wrapped strength-T1 case (HEq form): `Term.pair`.

The pair rename arm does not wrap the outer pair in a cast; instead the
second component is cast across `Ty.subst0_rename_commute` so its
dependent Σ component type matches the first component's renamed raw.
The HEq form records the dispatcher computation on that exact renamed
pair shape. -/
theorem strengthenTyped?_rename_heq_pair
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    {firstType : Ty level sourceScope}
    {secondType : Ty level (sourceScope + 1)}
    {firstRaw secondRaw : RawTerm sourceScope}
    (firstValue : Term sourceCtx firstType firstRaw)
    (secondValue :
      Term sourceCtx (secondType.subst0 firstType firstRaw) secondRaw) :
    HEq
      (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.pair firstValue secondValue))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects))
      (partialStrengthenTyped?
        (Term.pair
          (Term.rename typedRenaming firstValue)
          (Ty.subst0_rename_commute secondType firstType firstRaw
            forwardRename ▸
            Term.rename typedRenaming secondValue))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)) := by
  dsimp only [Term.rename]
  exact HEq.rfl

/-- Cast-wrapped strength-T1 case (HEq form): `Term.lam`.

The lambda rename arm casts the renamed body across
`Ty.weaken_rename_commute` before rebuilding the lambda.  The HEq form
records the dispatcher result for that exact renamed lambda shape. -/
theorem strengthenTyped?_rename_heq_lam
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    {domainType codomainType : Ty level sourceScope}
    {bodyRaw : RawTerm (sourceScope + 1)}
    (body :
      Term (sourceCtx.cons domainType) codomainType.weaken bodyRaw) :
    HEq
      (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.lam body))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects))
      (partialStrengthenTyped?
        (Term.lam
          (Ty.weaken_rename_commute forwardRename codomainType ▸
            Term.rename (typedRenaming.lift domainType) body))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)) := by
  dsimp only [Term.rename]
  exact HEq.rfl

/-- Cast-wrapped strength-T1 case (HEq form): `Term.lamPi`.

Dependent lambda rename is structurally direct once the renaming is lifted
under the domain binder.  The HEq form keeps it in the same cast-wall
family as the other binder constructors so T1 can account for every
renamed binder uniformly. -/
theorem strengthenTyped?_rename_heq_lamPi
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    {domainType : Ty level sourceScope}
    {codomainType : Ty level (sourceScope + 1)}
    {bodyRaw : RawTerm (sourceScope + 1)}
    (body : Term (sourceCtx.cons domainType) codomainType bodyRaw) :
    HEq
      (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.lamPi body))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects))
      (partialStrengthenTyped?
        (Term.lamPi
          (Term.rename (typedRenaming.lift domainType) body))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)) := by
  dsimp only [Term.rename]
  exact HEq.rfl

/-- Cast-wrapped strength-T1 case (HEq form): `Term.pathLam`.

Path lambda rename mirrors ordinary lambda rename: the lifted body is
transported across `Ty.weaken_rename_commute` for the path carrier. -/
theorem strengthenTyped?_rename_heq_pathLam
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    (leftEndpoint rightEndpoint : RawTerm sourceScope)
    {bodyRaw : RawTerm (sourceScope + 1)}
    (body :
      Term (sourceCtx.cons Ty.interval) carrierType.weaken bodyRaw) :
    HEq
      (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.pathLam modeIsUnivalent carrierType leftEndpoint
            rightEndpoint body))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects))
      (partialStrengthenTyped?
        (Term.pathLam modeIsUnivalent (carrierType.rename forwardRename)
          (leftEndpoint.rename forwardRename)
          (rightEndpoint.rename forwardRename)
          (Ty.weaken_rename_commute forwardRename carrierType ▸
            Term.rename (typedRenaming.lift Ty.interval) body))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)) := by
  dsimp only [Term.rename]
  exact HEq.rfl

/-- Cast-wrapped strength-T1 case (HEq form): `Term.oeqFunext`.

The observational funext rename arm casts the pointwise proof through
`oeqFunextPointwiseType_rename` before rebuilding the constructor. -/
theorem strengthenTyped?_rename_heq_oeqFunext
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    (domainType codomainType : Ty level sourceScope)
    (leftFunctionRaw rightFunctionRaw : RawTerm sourceScope)
    {pointwiseRaw : RawTerm sourceScope}
    (pointwiseProof :
      Term sourceCtx
        (oeqFunextPointwiseType domainType codomainType
          leftFunctionRaw rightFunctionRaw)
        pointwiseRaw) :
    HEq
      (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.oeqFunext domainType codomainType
            leftFunctionRaw rightFunctionRaw pointwiseProof))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects))
      (partialStrengthenTyped?
        (Term.oeqFunext
          (domainType.rename forwardRename)
          (codomainType.rename forwardRename)
          (leftFunctionRaw.rename forwardRename)
          (rightFunctionRaw.rename forwardRename)
          (oeqFunextPointwiseType_rename forwardRename domainType
            codomainType leftFunctionRaw rightFunctionRaw ▸
            Term.rename typedRenaming pointwiseProof))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)) := by
  dsimp only [Term.rename]
  exact HEq.rfl

/-- Cast-wrapped strength-T1 case (HEq form): `Term.equivIntroHet`.

The heterogeneous equivalence introduction rename arm structurally
renames the forward and backward maps, and casts both inverse proofs
through their dedicated inverse-type rename lemmas. -/
theorem strengthenTyped?_rename_heq_equivIntroHet
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    {carrierA carrierB : Ty level sourceScope}
    {forwardRaw backwardRaw leftInvRaw rightInvRaw : RawTerm sourceScope}
    (forward :
      Term sourceCtx (Ty.arrow carrierA carrierB) forwardRaw)
    (backward :
      Term sourceCtx (Ty.arrow carrierB carrierA) backwardRaw)
    (leftInv :
      Term sourceCtx
        (equivIntroHetLeftInverseType carrierA forwardRaw backwardRaw)
        leftInvRaw)
    (rightInv :
      Term sourceCtx
        (equivIntroHetRightInverseType carrierB forwardRaw backwardRaw)
        rightInvRaw) :
    HEq
      (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.equivIntroHet forward backward leftInv rightInv))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects))
      (partialStrengthenTyped?
        (Term.equivIntroHet
          (Term.rename typedRenaming forward)
          (Term.rename typedRenaming backward)
          (equivIntroHetLeftInverseType_rename forwardRename carrierA
            forwardRaw backwardRaw ▸
            Term.rename typedRenaming leftInv)
          (equivIntroHetRightInverseType_rename forwardRename carrierB
            forwardRaw backwardRaw ▸
            Term.rename typedRenaming rightInv))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)) := by
  dsimp only [Term.rename]
  exact HEq.rfl

/-- Cast-wrapped strength-T1 case (HEq form): `Term.boolElim`.

The Boolean eliminator rename arm has a top-level non-rfl
`Ty.subst0_rename_commute` cast for the motive instantiated at the
scrutinee.  The branch casts remain inside the uncast eliminator; this
lemma only removes the outer cast wrapper so later per-branch soundness
can be handled at the subterm level.
-/
theorem strengthenTyped?_rename_heq_boolElim
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    {motiveType : Ty level (sourceScope + 1)}
    {scrutineeRaw thenRaw elseRaw : RawTerm sourceScope}
    (scrutinee : Term sourceCtx Ty.bool scrutineeRaw)
    (thenBranch :
      Term sourceCtx (motiveType.subst0 Ty.bool RawTerm.boolTrue) thenRaw)
    (elseBranch :
      Term sourceCtx (motiveType.subst0 Ty.bool RawTerm.boolFalse) elseRaw) :
    HEq
      (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.boolElim scrutinee thenBranch elseBranch))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects))
      (partialStrengthenTyped?
        (Term.boolElim
          (motiveType := motiveType.rename forwardRename.lift)
          (Term.rename typedRenaming scrutinee)
          (Ty.subst0_rename_commute motiveType Ty.bool
            RawTerm.boolTrue forwardRename ▸
            Term.rename typedRenaming thenBranch)
          (Ty.subst0_rename_commute motiveType Ty.bool
            RawTerm.boolFalse forwardRename ▸
            Term.rename typedRenaming elseBranch))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)) := by
  dsimp only [Term.rename]
  exact
    partialStrengthenTyped?_castInvariantHEq
      (Term.boolElim
        (motiveType := motiveType.rename forwardRename.lift)
        (Term.rename typedRenaming scrutinee)
        (Ty.subst0_rename_commute motiveType Ty.bool
          RawTerm.boolTrue forwardRename ▸
          Term.rename typedRenaming thenBranch)
        (Ty.subst0_rename_commute motiveType Ty.bool
          RawTerm.boolFalse forwardRename ▸
          Term.rename typedRenaming elseBranch))
      (Ty.subst0_rename_commute motiveType Ty.bool scrutineeRaw
        forwardRename).symm
      (ContextStrengthening.ofRenaming forwardRename typedRenaming
        renameInverse renameInverseLeft renameInverseInjects)

/-- Cast-wrapped strength-T1 case (HEq form): `Term.funextRefl`.

Closed value-shape ctor (no Term subterms).  Three Ty/raw payloads:
`domainType`, `codomainType`, `applyRaw` at `scope+1`.  Rename arm
wraps the result in `(funextReflType_rename rho ...).symm ▸ Term.funextRefl
(renamed args)`.

The HEq form abstracts over the cast: the dispatcher on the cast-
wrapped input is HEq to the dispatcher on the un-cast `Term.funextRefl`
applied to the renamed payloads.  Proof: cast-invariance of the
dispatcher (`partialStrengthenTyped?_castInvariantHEq`) gives the HEq;
the un-cast dispatcher equation closes via the standard `split` chain.
-/
theorem strengthenTyped?_rename_heq_funextRefl
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    {domainType codomainType : Ty level sourceScope}
    (applyRaw : RawTerm (sourceScope + 1)) :
    HEq
      (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.funextRefl (context := sourceCtx) domainType codomainType
            applyRaw))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects))
      (partialStrengthenTyped?
        (Term.funextRefl (context := targetCtx)
          (domainType.rename forwardRename)
          (codomainType.rename forwardRename)
          (applyRaw.rename forwardRename.lift))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)) := by
  dsimp only [Term.rename]
  -- After dsimp, LHS becomes:
  --   partialStrengthenTyped?
  --     ((funextReflType_rename ...).symm ▸ Term.funextRefl (renamed args))
  --     σ
  -- Apply cast-invariance HEq to peel the cast wrapper.
  exact
    partialStrengthenTyped?_castInvariantHEq
      (Term.funextRefl (context := targetCtx)
        (domainType.rename forwardRename)
        (codomainType.rename forwardRename)
        (applyRaw.rename forwardRename.lift))
      (funextReflType_rename forwardRename domainType codomainType applyRaw).symm
      (ContextStrengthening.ofRenaming forwardRename typedRenaming
        renameInverse renameInverseLeft renameInverseInjects)

end Term

end LeanFX2
