import FX1Poly.Typed.KernelBinaryGenericFormer
import FX1Poly.Typed.BoundedGrownFundamental
import FX1Poly.Typed.BoundedDomainInhabitant
import FX1Poly.Typed.BoundedCodomainOpenSN
import FX1Poly.Typed.BoundExceedsPiDischarge

/-! # FX1Poly/Typed/KernelBinaryFundamental
    — ★ the binary fundamental theorem (kernel binary parametricity, OP1-K2 master assembly)

The budget-recursor assembly of the binary FT over BOTH typing engines, with the CONJOINED
motive: the conclusion quantifies over a closing-substitution PAIR carrying its two UNARY
bound-reducible environments alongside the binary-related environment.  The unary env premises
are what make the wall-premise discharge possible — at every recursor arm the per-substitution
wall facts (output gates, open codomain/body SN, domain unary reducibilities, argument unary
memberships) are read off the SHIPPED UNARY fundamental theorems applied to the arm's named
sub-derivation/sub-budget fields at the unary halves of the environment triple.

  * `BinaryFundamentalConclusionConjoinedAtBounded` — the conjoined `+1`-closing motive.
  * `IsBinaryTelescopeConjoinedAtBounded` — the conjoined binary telescope (motive_2's binary
    half; the unary half is the engine's shipped telescope predicate, re-derived in the cons
    arm from the closed unary FT on the head's named fields).
  * `formationLevelsArityBoundNonPiSigma` — non-Π/Σ formation rows have arity ≤ 1 (the binary
    fold supplier's gate, mirroring `formationLevelsArityBound`'s row-mirror discipline).
  * `HasTypeDesc.binaryFundamentalConjoinedAtBounded` — the FORMATION engine binary FT
    (`BoundExceeds.rec`): var / conv / universeFormation / genFormation (by_cases Π / Σ /
    generic-arity-≤1) + the conjoined telescopes.
  * ★ `HasTypeDescPi.binaryFundamentalConjoinedAtBounded` — the GROWN engine binary FT
    (`BoundExceedsPi.rec`): ofFormation feeds the formation binary FT; piIntro is the
    design-(f) payoff arm — the guards of the unary-guarded Π candidate convert to unary
    memberships (`⟨candidate, derivation, guard⟩`) that extend BOTH unary environments at the
    body IH, with the binary argument pair extending the binary environment; piElim reads the
    argument's unary memberships off the unary FT; genFormationPi mirrors the formation arm.
  * ★ `HasTypeDescPi.binaryParametricityClosed` — the closed corollary (the OP1-K3 doorway):
    every CLOSED well-typed term is binary-self-related under every closing-substitution pair
    at a budget-derived bound, with all three environment premises vacuous at scope 0.

Zero-axiom; gated in `FX1PolyAudit/AuditTypedSubstVecCwR.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation
open StepStar

/-! ## The conjoined motives -/

/-- ★ **The CONJOINED binary fundamental-theorem motive**: every `+1`-closing
substitution pair that is unary-bound-reducible ON EACH SIDE and binary-related takes the
subject's two closures to a binary-reducible member pair at the classifier's two closures.
The two unary premises are the honest price of binary parametricity — they are what the
recursor arms feed the shipped unary fundamental theorems to discharge the INHABITATION-WALL
premises, and they erase at the closed corollary (vacuous over the empty context). -/
def BinaryFundamentalConclusionConjoinedAtBounded {profile : PolyProfile} {scope : Nat}
    (env : Nat → Nat) (bound : Nat) (context : TypingContext profile scope)
    (subject classifier : RawTerm scope) : Prop :=
  ∀ {targetScope : Nat}
    (leftSubstitution rightSubstitution : RawTermSubst scope (targetScope + 1)),
    ReducibleEnvAtBounded env bound context leftSubstitution →
    ReducibleEnvAtBounded env bound context rightSubstitution →
    BinaryReducibleEnvAtBounded env bound context leftSubstitution rightSubstitution →
    IsBinaryReducibleMemberPairAtBounded env bound
      (RawTerm.subst leftSubstitution classifier) (RawTerm.subst rightSubstitution classifier)
      (RawTerm.subst leftSubstitution subject) (RawTerm.subst rightSubstitution subject)

/-- **The conjoined binary telescope motive (binary half of motive_2)**: under every
`+1`-closing triple-related substitution pair and every argument level at or below the bound,
the children form a binary telescope. -/
def IsBinaryTelescopeConjoinedAtBounded {profile : PolyProfile} {baseScope currentDepth : Nat}
    {binderShifts : List Nat}
    (env : Nat → Nat) (bound : Nat)
    (context : TypingContext profile (baseScope + currentDepth)) (levelsList : List LevelExpr)
    (flag : UniverseFlag) (children : RawTermChildren binderShifts baseScope) : Prop :=
  ∀ {targetScope : Nat}
    (leftSubstitution rightSubstitution :
      RawTermSubst (baseScope + currentDepth) (targetScope + 1))
    (argLevel : Nat) (_argLevelLeBound : argLevel ≤ bound),
    ReducibleEnvAtBounded env bound context leftSubstitution →
    ReducibleEnvAtBounded env bound context rightSubstitution →
    BinaryReducibleEnvAtBounded env bound context leftSubstitution rightSubstitution →
    (shapeEq : binderShifts = consecutiveShifts currentDepth levelsList.length) →
    BinaryTelescopeReducibleAtBounded env bound argLevel flag currentDepth levelsList.length
      leftSubstitution rightSubstitution levelsList (shapeEq ▸ children)

/-! ## The non-Π/Σ arity gate -/

/-- **Every non-Π non-Σ formation row has arity ≤ 1** — the gate the binary fold supplier
(`foldChildrenNormalizingAndOutputBelow`) consumes after the Π and Σ rows split off to their
premise-isolated arms.  Same row-mirror discipline as `formationLevelsArityBound`. -/
theorem formationLevelsArityBoundNonPiSigma {generator : Generator} {rule : TypingRuleDesc}
    {levels : List LevelExpr}
    (isFormation : typingRuleDescOf generator = some rule)
    (isNotPiFormer : generator ≠ .gen_piTyCode)
    (isNotSigmaFormer : generator ≠ .gen_sigmaTyCode)
    (shapeEq : generator.binderShifts = consecutiveShifts 0 levels.length) :
    levels.length ≤ 1 := by
  have lengthEq : generator.binderShifts.length = levels.length :=
    (congrArg List.length shapeEq).trans (consecutiveShifts_length 0 levels.length)
  by_cases isListFormer : generator = .gen_listCode
  · subst isListFormer; exact lengthEq ▸ Nat.le_refl 1
  by_cases isOptionFormer : generator = .gen_optionCode
  · subst isOptionFormer; exact lengthEq ▸ Nat.le_refl 1
  by_cases isUnitFormer : generator = .gen_unitCode
  · subst isUnitFormer; exact lengthEq ▸ Nat.zero_le 1
  exfalso
  dsimp only [typingRuleDescOf] at isFormation
  rw [if_neg isNotPiFormer, if_neg isNotSigmaFormer, if_neg isListFormer,
    if_neg isOptionFormer, if_neg isUnitFormer] at isFormation
  exact nomatch isFormation

/-! ## ★ The formation-engine binary fundamental theorem -/

/-- ★ **The bounded FORMATION-engine binary fundamental theorem** — `BoundExceeds.rec` with
the conjoined motive.  The wall facts at the `genFormation` arm (output gates, open codomain
SN, domain unary reducibilities at the output level) are read per-substitution off the UNARY
telescope half of motive_2 at each unary environment, mirroring the unary BFT-11 arm; the
binary halves close through the per-pair Π/Σ composition cores and the table-generic fold. -/
theorem HasTypeDesc.binaryFundamentalConjoinedAtBounded {profile : PolyProfile}
    (env : Nat → Nat) (bound : Nat) :
    ∀ {scope : Nat} {context : TypingContext profile scope} {subject classifier : RawTerm scope}
      (d : HasTypeDesc profile context subject classifier),
      BoundExceeds env bound d →
        BinaryFundamentalConclusionConjoinedAtBounded env bound context subject classifier := by
  intro scope context subject classifier d budget
  refine BoundExceeds.rec
    (motive_1 := fun {_scope} {_context} {_subject} {_classifier} _d _budget =>
      BinaryFundamentalConclusionConjoinedAtBounded env bound _context _subject _classifier)
    (motive_2 := fun {_baseScope _currentDepth _binderShifts} {_context} {_levels} {_flag}
        {_children} telescope _telescopeBudget =>
      IsFormationTelescopeReducibleAtBoundedSucc env bound _context _levels _flag _children
          telescope ∧
        IsBinaryTelescopeConjoinedAtBounded env bound _context _levels _flag _children)
    ?var ?conv ?universeFormation ?genFormation ?nilTelescope ?consTelescope budget
  · -- var: the binary env lookup IS the arm
    intro _scope context index
    intro _targetScope leftSubstitution rightSubstitution _leftEnv _rightEnv envRelated
    exact binaryFundamentalVarArm env bound context index leftSubstitution rightSubstitution
      envRelated
  · -- conv: gate from the reclassifier's binary IH, brick-3 transport
    intro _scope _context _subject _classifier _reclassifier levelExpr flag _typed converts
      _reclassifierTyped _subjectBudget _reclassifierBudget subjectFundamental
      reclassifierFundamental
    intro _targetScope leftSubstitution rightSubstitution leftEnv rightEnv envRelated
    have reclassifierMemberPair := reclassifierFundamental leftSubstitution rightSubstitution
      leftEnv rightEnv envRelated
    have belowBound : LevelExpr.denote levelExpr env < bound := by
      obtain ⟨_relation, universePairRelated, _membersIn⟩ := reclassifierMemberPair
      exact binaryUniverseCodeReducibleAtBounded_belowBound universePairRelated
    exact convMemberPairUnderClosingSubstitutionBounded env bound
      (subjectFundamental leftSubstitution rightSubstitution leftEnv rightEnv envRelated)
      (binaryReducibleTypePairFromUniverseMemberBounded reclassifierMemberPair belowBound)
      converts
  · -- universeFormation: the budget-consuming arm (closed payload — substitution-invariant)
    intro _scope context levelExpr flag belowBound
    intro _targetScope _leftSubstitution _rightSubstitution _leftEnv _rightEnv _envRelated
    exact binaryUniverseFormationMemberPairAtBounded env levelExpr flag bound belowBound
  · -- genFormation: by_cases Π / Σ / generic-arity-≤1
    intro _scope _context generator _payload children levelsList flag rule isFormation
      nullaryBelowBound premises _premisesBudget premisesFundamental
    intro _targetScope leftSubstitution rightSubstitution leftEnv rightEnv envRelated
    by_cases isPiFormer : generator = .gen_piTyCode
    · subst isPiFormer
      obtain rfl : rule = { outputType := universeFormerOutput } :=
        Option.some.inj isFormation.symm
      match children with
      | .childCons domain (.childCons codomain .childNil) =>
          obtain ⟨domainLevel, codomainLevel, levelsShape⟩ :=
            DescTelescope.twoChildLevels premises
          subst levelsShape
          dsimp only [universeFormerOutput]
          have leftUnaryTelescope := premisesFundamental.1 leftSubstitution bound
            (Nat.le_refl bound) leftEnv Generator.gen_piTyCode_binderShifts_eq
          obtain ⟨leftDomainMember, leftCodomainMemberFn⟩ := leftUnaryTelescope.twoChildMembers
          have domainBelowBound : LevelExpr.denote domainLevel env < bound := by
            obtain ⟨_, domainCandidateReducible, _⟩ := leftDomainMember
            exact universeCodeReducibleAtBounded_belowBound domainCandidateReducible
          have leftVariableZero := variableZeroMemberOfBoundedUniverseMember leftDomainMember
            domainBelowBound (Nat.le_of_lt domainBelowBound)
          have leftCodomainMember := leftCodomainMemberFn _ leftVariableZero
          have codomainBelowBound : LevelExpr.denote codomainLevel env < bound := by
            obtain ⟨_, codomainCandidateReducible, _⟩ := leftCodomainMember
            exact universeCodeReducibleAtBounded_belowBound codomainCandidateReducible
          have outputBelowBound :
              LevelExpr.denote (lmaxAll [domainLevel, codomainLevel]) env < bound :=
            levelMax_lt domainBelowBound codomainBelowBound
          have leftCodomainOpenSN :=
            codomainOpenStronglyNormalizing_ofBoundedFilledMember leftCodomainMember
          have rightUnaryTelescope := premisesFundamental.1 rightSubstitution bound
            (Nat.le_refl bound) rightEnv Generator.gen_piTyCode_binderShifts_eq
          obtain ⟨rightDomainMember, rightCodomainMemberFn⟩ :=
            rightUnaryTelescope.twoChildMembers
          have rightVariableZero := variableZeroMemberOfBoundedUniverseMember rightDomainMember
            domainBelowBound (Nat.le_of_lt domainBelowBound)
          have rightCodomainOpenSN := codomainOpenStronglyNormalizing_ofBoundedFilledMember
            (rightCodomainMemberFn _ rightVariableZero)
          have domainBelowOutput :=
            denote_domainLevel_le_lmaxAll_pair domainLevel codomainLevel env
          have leftDomainUnary : IsReducibleTypeAtBounded env
              (LevelExpr.denote (lmaxAll [domainLevel, codomainLevel]) env)
              (RawTerm.subst leftSubstitution domain) :=
            isReducibleBounded_cumulative
              (universeMemberReducibleAsTypeAtDecodedLevelBounded leftDomainMember
                domainBelowBound)
              domainBelowOutput
          have rightDomainUnary : IsReducibleTypeAtBounded env
              (LevelExpr.denote (lmaxAll [domainLevel, codomainLevel]) env)
              (RawTerm.subst rightSubstitution domain) :=
            isReducibleBounded_cumulative
              (universeMemberReducibleAsTypeAtDecodedLevelBounded rightDomainMember
                domainBelowBound)
              domainBelowOutput
          exact binaryPiFormerMemberPairUnderSubstAtBounded env bound
            domainLevel codomainLevel flag leftSubstitution rightSubstitution
            outputBelowBound leftCodomainOpenSN rightCodomainOpenSN
            leftDomainUnary rightDomainUnary
            (premisesFundamental.2 leftSubstitution rightSubstitution
              (LevelExpr.denote (lmaxAll [domainLevel, codomainLevel]) env)
              (Nat.le_of_lt outputBelowBound) leftEnv rightEnv envRelated
              Generator.gen_piTyCode_binderShifts_eq)
    · by_cases isSigmaFormer : generator = .gen_sigmaTyCode
      · subst isSigmaFormer
        obtain rfl : rule = { outputType := universeFormerOutput } :=
          Option.some.inj isFormation.symm
        match children with
        | .childCons domain (.childCons codomain .childNil) =>
            obtain ⟨domainLevel, codomainLevel, levelsShape⟩ :=
              DescTelescope.twoChildLevels premises
            subst levelsShape
            dsimp only [universeFormerOutput]
            have leftUnaryTelescope := premisesFundamental.1 leftSubstitution bound
              (Nat.le_refl bound) leftEnv Generator.gen_sigmaTyCode_binderShifts_eq
            obtain ⟨leftDomainMember, leftCodomainMemberFn⟩ :=
              leftUnaryTelescope.twoChildMembers
            have domainBelowBound : LevelExpr.denote domainLevel env < bound := by
              obtain ⟨_, domainCandidateReducible, _⟩ := leftDomainMember
              exact universeCodeReducibleAtBounded_belowBound domainCandidateReducible
            have leftVariableZero := variableZeroMemberOfBoundedUniverseMember leftDomainMember
              domainBelowBound (Nat.le_of_lt domainBelowBound)
            have leftCodomainMember := leftCodomainMemberFn _ leftVariableZero
            have codomainBelowBound : LevelExpr.denote codomainLevel env < bound := by
              obtain ⟨_, codomainCandidateReducible, _⟩ := leftCodomainMember
              exact universeCodeReducibleAtBounded_belowBound codomainCandidateReducible
            have outputBelowBound :
                LevelExpr.denote (lmaxAll [domainLevel, codomainLevel]) env < bound :=
              levelMax_lt domainBelowBound codomainBelowBound
            have leftCodomainOpenSN :=
              codomainOpenStronglyNormalizing_ofBoundedFilledMember leftCodomainMember
            have rightUnaryTelescope := premisesFundamental.1 rightSubstitution bound
              (Nat.le_refl bound) rightEnv Generator.gen_sigmaTyCode_binderShifts_eq
            obtain ⟨rightDomainMember, rightCodomainMemberFn⟩ :=
              rightUnaryTelescope.twoChildMembers
            have rightVariableZero := variableZeroMemberOfBoundedUniverseMember
              rightDomainMember domainBelowBound (Nat.le_of_lt domainBelowBound)
            have rightCodomainOpenSN := codomainOpenStronglyNormalizing_ofBoundedFilledMember
              (rightCodomainMemberFn _ rightVariableZero)
            exact binarySigmaFormerMemberPairUnderSubstAtBounded env bound
              domainLevel codomainLevel flag leftSubstitution rightSubstitution
              outputBelowBound leftCodomainOpenSN rightCodomainOpenSN
              (premisesFundamental.2 leftSubstitution rightSubstitution
                (LevelExpr.denote (lmaxAll [domainLevel, codomainLevel]) env)
                (Nat.le_of_lt outputBelowBound) leftEnv rightEnv envRelated
                Generator.gen_sigmaTyCode_binderShifts_eq)
      · -- the GENERIC arity-≤1 arm (table-generic, wall-free)
        have shapeEq := premises.shiftsShape
        obtain ⟨outputFlag, outputEq⟩ := formationRowOutputLevel isFormation shapeEq _ flag
        rw [outputEq]
        obtain ⟨leftChildrenNormalizing, rightChildrenNormalizing, outputBelowBound⟩ :=
          BinaryTelescopeReducibleAtBounded.foldChildrenNormalizingAndOutputBelow shapeEq
            (formationLevelsArityBoundNonPiSigma isFormation isPiFormer isSigmaFormer shapeEq)
            (fun levelsEmpty =>
              nullaryBelowBound (formationRowNullaryIsUnit isFormation
                (by rw [levelsEmpty] at shapeEq; exact shapeEq)))
            (premisesFundamental.2 leftSubstitution rightSubstitution bound
              (Nat.le_refl bound) leftEnv rightEnv envRelated shapeEq)
        exact binaryDataFormationUnderSubstAtBounded (lmaxAll levelsList) outputFlag
          leftSubstitution rightSubstitution isFormation isPiFormer outputBelowBound
          leftChildrenNormalizing rightChildrenNormalizing
  · -- nilTelescope
    intro _baseScope _currentDepth _context _flag
    refine ⟨?_, ?_⟩
    · intro _targetScope _substitution _argLevel _argLevelLeBound _env _shapeEq
      exact True.intro
    · intro _targetScope _leftSubstitution _rightSubstitution _argLevel _argLevelLeBound
        _leftEnv _rightEnv _envRelated _shapeEq
      exact True.intro
  · -- consTelescope: the unary half re-derives BFT-11's cons body from the CLOSED unary FT
    -- on the head's named fields; the binary half extends ALL THREE environments — the unary
    -- heads come from the telescope rest-clause's design-(f) unary-membership premises
    intro _baseScope _currentDepth _restShifts _context _head _headLevel _restLevels _flag
      _rest headTyped _restTyped headBudget _restBudget headFundamental restFundamental
    refine ⟨?_, ?_⟩
    · intro _targetScope substitution argLevel argLevelLeBound envReducible shapeEq
      dsimp only [List.length_cons, consecutiveShifts] at shapeEq
      obtain ⟨_headShiftEq, restShapeEq⟩ := List.cons.inj shapeEq
      subst restShapeEq
      exact fundamentalTelescopeConsAtBoundedSucc env bound argLevel envReducible
        (HasTypeDesc.fundamentalAtBoundedSucc env bound headTyped headBudget)
        (fun argument argumentMember =>
          restFundamental.1 (RawTermSubst.cons argument substitution) argLevel argLevelLeBound
            (ReducibleEnvAtBounded.cons envReducible (argumentMember.cumulative argLevelLeBound))
            rfl)
    · intro _targetScope leftSubstitution rightSubstitution argLevel argLevelLeBound
        leftEnv rightEnv envRelated shapeEq
      dsimp only [List.length_cons, consecutiveShifts] at shapeEq
      obtain ⟨_headShiftEq, restShapeEq⟩ := List.cons.inj shapeEq
      subst restShapeEq
      refine ⟨?_, ?_⟩
      · have headPair := headFundamental leftSubstitution rightSubstitution
          leftEnv rightEnv envRelated
        rw [subst_universeCodeCell] at headPair
        rwa [subst_universeCodeCell] at headPair
      · intro leftArgument rightArgument leftUnaryMember rightUnaryMember argumentsMember
        exact restFundamental.2 (RawTermSubst.cons leftArgument leftSubstitution)
          (RawTermSubst.cons rightArgument rightSubstitution) argLevel argLevelLeBound
          (ReducibleEnvAtBounded.cons leftEnv (leftUnaryMember.cumulative argLevelLeBound))
          (ReducibleEnvAtBounded.cons rightEnv (rightUnaryMember.cumulative argLevelLeBound))
          (BinaryReducibleEnvAtBounded.cons envRelated
            (isBinaryReducibleMemberPair_cumulative argumentsMember argLevelLeBound))
          rfl

/-! ## ★ The grown-engine binary fundamental theorem -/

/-- ★★ **THE bounded GROWN-engine binary fundamental theorem** — `BoundExceedsPi.rec` with the
conjoined motive: every well-typed term is binary-self-related under every triple-related
closing-substitution pair.  The `piIntro` arm is the design-(f) payoff: the guards of the
unary-guarded Π candidate convert to unary memberships that extend BOTH unary environments at
the body IH; the open-body SN comes from the unary FT at the variable-0-extended environment
through the `subst0` SN reflection. -/
theorem HasTypeDescPi.binaryFundamentalConjoinedAtBounded {profile : PolyProfile}
    (env : Nat → Nat) (bound : Nat) :
    ∀ {scope : Nat} {context : TypingContext profile scope} {subject classifier : RawTerm scope}
      (d : HasTypeDescPi profile context subject classifier),
      BoundExceedsPi env bound d →
        BinaryFundamentalConclusionConjoinedAtBounded env bound context subject classifier := by
  intro scope context subject classifier d budget
  refine BoundExceedsPi.rec
    (motive_1 := fun {_scope} {_context} {_subject} {_classifier} _d _budget =>
      BinaryFundamentalConclusionConjoinedAtBounded env bound _context _subject _classifier)
    (motive_2 := fun {_baseScope _currentDepth _binderShifts} {_context} {_levels} {_flag}
        {_children} telescope _telescopeBudget =>
      IsTelescopeReducibleAtBoundedSucc env bound _context _levels _flag _children telescope ∧
        IsBinaryTelescopeConjoinedAtBounded env bound _context _levels _flag _children)
    ?ofFormation ?conv ?piIntro ?piElim ?genFormationPi ?nilTelescope ?consTelescope budget
  · -- ofFormation: feed the carried embedded budget to the FORMATION binary FT
    intro _scope _context _subject _classifier formationTyped formationBudget
    exact HasTypeDesc.binaryFundamentalConjoinedAtBounded env bound formationTyped
      formationBudget
  · -- conv (identical body to the formation conv arm)
    intro _scope _context _subject _classifier _reclassifier levelExpr flag _typed converts
      _reclassifierTyped _subjectBudget _reclassifierBudget subjectFundamental
      reclassifierFundamental
    intro _targetScope leftSubstitution rightSubstitution leftEnv rightEnv envRelated
    have reclassifierMemberPair := reclassifierFundamental leftSubstitution rightSubstitution
      leftEnv rightEnv envRelated
    have belowBound : LevelExpr.denote levelExpr env < bound := by
      obtain ⟨_relation, universePairRelated, _membersIn⟩ := reclassifierMemberPair
      exact binaryUniverseCodeReducibleAtBounded_belowBound universePairRelated
    exact convMemberPairUnderClosingSubstitutionBounded env bound
      (subjectFundamental leftSubstitution rightSubstitution leftEnv rightEnv envRelated)
      (binaryReducibleTypePairFromUniverseMemberBounded reclassifierMemberPair belowBound)
      converts
  · -- ★ piIntro: the design-(f) payoff arm
    intro _scope _context _domainCode _codomainCode _body _domainLevel _codomainLevel _flag
      domainTyped codomainTyped bodyTyped domainBudget codomainBudget bodyBudget
      domainFundamental codomainFundamental bodyFundamental
    intro _targetScope leftSubstitution rightSubstitution leftEnv rightEnv envRelated
    -- unary domain facts per side, off the unary FT on the named (domainTyped, domainBudget)
    have leftDomainUniverseMember := HasTypeDescPi.fundamentalAtBoundedSucc env bound
      domainTyped domainBudget leftSubstitution leftEnv
    rw [subst_universeCodeCell] at leftDomainUniverseMember
    have domainBelowBound : LevelExpr.denote _domainLevel env < bound := by
      obtain ⟨_, domainCandidateReducible, _⟩ := leftDomainUniverseMember
      exact universeCodeReducibleAtBounded_belowBound domainCandidateReducible
    obtain ⟨leftDomainCandidate, leftDomainUnary⟩ :=
      reducibleTypeAtBoundFromUniverseMemberBounded env bound leftDomainUniverseMember
        domainBelowBound
    have rightDomainUniverseMember := HasTypeDescPi.fundamentalAtBoundedSucc env bound
      domainTyped domainBudget rightSubstitution rightEnv
    rw [subst_universeCodeCell] at rightDomainUniverseMember
    obtain ⟨rightDomainCandidate, rightDomainUnary⟩ :=
      reducibleTypeAtBoundFromUniverseMemberBounded env bound rightDomainUniverseMember
        domainBelowBound
    -- the binary domain facts off the binary domain IH
    have domainMemberPair := domainFundamental leftSubstitution rightSubstitution
      leftEnv rightEnv envRelated
    rw [subst_universeCodeCell] at domainMemberPair
    rw [subst_universeCodeCell] at domainMemberPair
    obtain ⟨leftDomainAnnSN, rightDomainAnnSN⟩ :=
      binaryStronglyNormalizingPairOfUniverseMemberAtBounded domainMemberPair
    -- open-body SN per side: unary body FT at the variable-0-extended environment,
    -- reflected through subst0 (the same trick as the open-codomain SN)
    have leftVariableZero := variableZeroMemberOfBoundedUniverseMember
      leftDomainUniverseMember domainBelowBound (Nat.le_of_lt domainBelowBound)
    have leftBodyMember := HasTypeDescPi.fundamentalAtBoundedSucc env bound
      bodyTyped bodyBudget
      (RawTermSubst.cons (.mkGen .gen_var ⟨0, Nat.succ_pos _⟩ .childNil) leftSubstitution)
      (ReducibleEnvAtBounded.cons leftEnv leftVariableZero)
    rw [RawTerm.subst_cons_eq_subst0_lift _body _ leftSubstitution] at leftBodyMember
    have leftBodySN := codomainOpenStronglyNormalizing_ofBoundedFilledMember leftBodyMember
    have rightVariableZero := variableZeroMemberOfBoundedUniverseMember
      rightDomainUniverseMember domainBelowBound (Nat.le_of_lt domainBelowBound)
    have rightBodyMember := HasTypeDescPi.fundamentalAtBoundedSucc env bound
      bodyTyped bodyBudget
      (RawTermSubst.cons (.mkGen .gen_var ⟨0, Nat.succ_pos _⟩ .childNil) rightSubstitution)
      (ReducibleEnvAtBounded.cons rightEnv rightVariableZero)
    rw [RawTerm.subst_cons_eq_subst0_lift _body _ rightSubstitution] at rightBodyMember
    have rightBodySN := codomainOpenStronglyNormalizing_ofBoundedFilledMember rightBodyMember
    -- assemble through the abstraction lemma with guard→unary-membership conversion at
    -- the codomain family and the body conclusion (the conjoined-env extension)
    exact binaryAbstractionMemberPairUnderClosingSubstitutionBounded
      (domainRelation := fun leftTerm rightTerm =>
        IsBinaryReducibleMemberPairAtBounded env bound
          (RawTerm.subst leftSubstitution _domainCode)
          (RawTerm.subst rightSubstitution _domainCode) leftTerm rightTerm)
      (codomainRelation := fun leftArgument rightArgument leftTerm rightTerm =>
        IsBinaryReducibleMemberPairAtBounded env bound
          (RawTerm.subst (RawTermSubst.cons leftArgument leftSubstitution) _codomainCode)
          (RawTerm.subst (RawTermSubst.cons rightArgument rightSubstitution) _codomainCode)
          leftTerm rightTerm)
      env bound
      leftDomainUnary rightDomainUnary
      (binaryReducibleTypePairFromUniverseMemberBounded domainMemberPair
        domainBelowBound).reducibleMemberPairCandidate
      leftDomainAnnSN rightDomainAnnSN
      (fun leftArgument rightArgument leftGuard rightGuard argumentsMember => by
        have codomainMemberPair := codomainFundamental
          (RawTermSubst.cons leftArgument leftSubstitution)
          (RawTermSubst.cons rightArgument rightSubstitution)
          (ReducibleEnvAtBounded.cons leftEnv
            ⟨leftDomainCandidate, leftDomainUnary, leftGuard⟩)
          (ReducibleEnvAtBounded.cons rightEnv
            ⟨rightDomainCandidate, rightDomainUnary, rightGuard⟩)
          (BinaryReducibleEnvAtBounded.cons envRelated argumentsMember)
        rw [subst_universeCodeCell] at codomainMemberPair
        rw [subst_universeCodeCell] at codomainMemberPair
        have codomainBelowBound : LevelExpr.denote _codomainLevel env < bound := by
          obtain ⟨_relation, universePairRelated, _membersIn⟩ := codomainMemberPair
          exact binaryUniverseCodeReducibleAtBounded_belowBound universePairRelated
        exact (binaryReducibleTypePairFromUniverseMemberBounded codomainMemberPair
          codomainBelowBound).reducibleMemberPairCandidate)
      (fun leftArgument rightArgument _leftGuard _rightGuard argumentsMember =>
        binaryMemberPairStronglyNormalizingAtBounded argumentsMember)
      leftBodySN rightBodySN
      (fun leftArgument rightArgument leftGuard rightGuard argumentsMember =>
        bodyFundamental (RawTermSubst.cons leftArgument leftSubstitution)
          (RawTermSubst.cons rightArgument rightSubstitution)
          (ReducibleEnvAtBounded.cons leftEnv
            ⟨leftDomainCandidate, leftDomainUnary, leftGuard⟩)
          (ReducibleEnvAtBounded.cons rightEnv
            ⟨rightDomainCandidate, rightDomainUnary, rightGuard⟩)
          (BinaryReducibleEnvAtBounded.cons envRelated argumentsMember))
  · -- piElim: the argument's unary memberships off the unary FT
    intro _scope _context _functionTerm _argument _domainCode _codomainCode
      functionTyped argumentTyped functionBudget argumentBudget
      functionFundamental argumentFundamental
    intro _targetScope leftSubstitution rightSubstitution leftEnv rightEnv envRelated
    exact applicationMemberPairUnderClosingSubstitutionBounded env bound
      (functionFundamental leftSubstitution rightSubstitution leftEnv rightEnv envRelated)
      (argumentFundamental leftSubstitution rightSubstitution leftEnv rightEnv envRelated)
      (HasTypeDescPi.fundamentalAtBoundedSucc env bound argumentTyped argumentBudget
        leftSubstitution leftEnv)
      (HasTypeDescPi.fundamentalAtBoundedSucc env bound argumentTyped argumentBudget
        rightSubstitution rightEnv)
  · -- genFormationPi (mirror of the formation genFormation arm)
    intro _scope _context generator _payload children levelsList flag rule isFormation
      nullaryBelowBound premises _premisesBudget premisesFundamental
    intro _targetScope leftSubstitution rightSubstitution leftEnv rightEnv envRelated
    by_cases isPiFormer : generator = .gen_piTyCode
    · subst isPiFormer
      obtain rfl : rule = { outputType := universeFormerOutput } :=
        Option.some.inj isFormation.symm
      match children with
      | .childCons domain (.childCons codomain .childNil) =>
          obtain ⟨domainLevel, codomainLevel, levelsShape⟩ :=
            DescTelescopePi.twoChildLevels premises
          subst levelsShape
          dsimp only [universeFormerOutput]
          have leftUnaryTelescope := premisesFundamental.1 leftSubstitution bound
            (Nat.le_refl bound) leftEnv Generator.gen_piTyCode_binderShifts_eq
          obtain ⟨leftDomainMember, leftCodomainMemberFn⟩ := leftUnaryTelescope.twoChildMembers
          have domainBelowBound : LevelExpr.denote domainLevel env < bound := by
            obtain ⟨_, domainCandidateReducible, _⟩ := leftDomainMember
            exact universeCodeReducibleAtBounded_belowBound domainCandidateReducible
          have leftVariableZero := variableZeroMemberOfBoundedUniverseMember leftDomainMember
            domainBelowBound (Nat.le_of_lt domainBelowBound)
          have leftCodomainMember := leftCodomainMemberFn _ leftVariableZero
          have codomainBelowBound : LevelExpr.denote codomainLevel env < bound := by
            obtain ⟨_, codomainCandidateReducible, _⟩ := leftCodomainMember
            exact universeCodeReducibleAtBounded_belowBound codomainCandidateReducible
          have outputBelowBound :
              LevelExpr.denote (lmaxAll [domainLevel, codomainLevel]) env < bound :=
            levelMax_lt domainBelowBound codomainBelowBound
          have leftCodomainOpenSN :=
            codomainOpenStronglyNormalizing_ofBoundedFilledMember leftCodomainMember
          have rightUnaryTelescope := premisesFundamental.1 rightSubstitution bound
            (Nat.le_refl bound) rightEnv Generator.gen_piTyCode_binderShifts_eq
          obtain ⟨rightDomainMember, rightCodomainMemberFn⟩ :=
            rightUnaryTelescope.twoChildMembers
          have rightVariableZero := variableZeroMemberOfBoundedUniverseMember rightDomainMember
            domainBelowBound (Nat.le_of_lt domainBelowBound)
          have rightCodomainOpenSN := codomainOpenStronglyNormalizing_ofBoundedFilledMember
            (rightCodomainMemberFn _ rightVariableZero)
          have domainBelowOutput :=
            denote_domainLevel_le_lmaxAll_pair domainLevel codomainLevel env
          have leftDomainUnary : IsReducibleTypeAtBounded env
              (LevelExpr.denote (lmaxAll [domainLevel, codomainLevel]) env)
              (RawTerm.subst leftSubstitution domain) :=
            isReducibleBounded_cumulative
              (universeMemberReducibleAsTypeAtDecodedLevelBounded leftDomainMember
                domainBelowBound)
              domainBelowOutput
          have rightDomainUnary : IsReducibleTypeAtBounded env
              (LevelExpr.denote (lmaxAll [domainLevel, codomainLevel]) env)
              (RawTerm.subst rightSubstitution domain) :=
            isReducibleBounded_cumulative
              (universeMemberReducibleAsTypeAtDecodedLevelBounded rightDomainMember
                domainBelowBound)
              domainBelowOutput
          exact binaryPiFormerMemberPairUnderSubstAtBounded env bound
            domainLevel codomainLevel flag leftSubstitution rightSubstitution
            outputBelowBound leftCodomainOpenSN rightCodomainOpenSN
            leftDomainUnary rightDomainUnary
            (premisesFundamental.2 leftSubstitution rightSubstitution
              (LevelExpr.denote (lmaxAll [domainLevel, codomainLevel]) env)
              (Nat.le_of_lt outputBelowBound) leftEnv rightEnv envRelated
              Generator.gen_piTyCode_binderShifts_eq)
    · by_cases isSigmaFormer : generator = .gen_sigmaTyCode
      · subst isSigmaFormer
        obtain rfl : rule = { outputType := universeFormerOutput } :=
          Option.some.inj isFormation.symm
        match children with
        | .childCons domain (.childCons codomain .childNil) =>
            obtain ⟨domainLevel, codomainLevel, levelsShape⟩ :=
              DescTelescopePi.twoChildLevels premises
            subst levelsShape
            dsimp only [universeFormerOutput]
            have leftUnaryTelescope := premisesFundamental.1 leftSubstitution bound
              (Nat.le_refl bound) leftEnv Generator.gen_sigmaTyCode_binderShifts_eq
            obtain ⟨leftDomainMember, leftCodomainMemberFn⟩ :=
              leftUnaryTelescope.twoChildMembers
            have domainBelowBound : LevelExpr.denote domainLevel env < bound := by
              obtain ⟨_, domainCandidateReducible, _⟩ := leftDomainMember
              exact universeCodeReducibleAtBounded_belowBound domainCandidateReducible
            have leftVariableZero := variableZeroMemberOfBoundedUniverseMember leftDomainMember
              domainBelowBound (Nat.le_of_lt domainBelowBound)
            have leftCodomainMember := leftCodomainMemberFn _ leftVariableZero
            have codomainBelowBound : LevelExpr.denote codomainLevel env < bound := by
              obtain ⟨_, codomainCandidateReducible, _⟩ := leftCodomainMember
              exact universeCodeReducibleAtBounded_belowBound codomainCandidateReducible
            have outputBelowBound :
                LevelExpr.denote (lmaxAll [domainLevel, codomainLevel]) env < bound :=
              levelMax_lt domainBelowBound codomainBelowBound
            have leftCodomainOpenSN :=
              codomainOpenStronglyNormalizing_ofBoundedFilledMember leftCodomainMember
            have rightUnaryTelescope := premisesFundamental.1 rightSubstitution bound
              (Nat.le_refl bound) rightEnv Generator.gen_sigmaTyCode_binderShifts_eq
            obtain ⟨rightDomainMember, rightCodomainMemberFn⟩ :=
              rightUnaryTelescope.twoChildMembers
            have rightVariableZero := variableZeroMemberOfBoundedUniverseMember
              rightDomainMember domainBelowBound (Nat.le_of_lt domainBelowBound)
            have rightCodomainOpenSN := codomainOpenStronglyNormalizing_ofBoundedFilledMember
              (rightCodomainMemberFn _ rightVariableZero)
            exact binarySigmaFormerMemberPairUnderSubstAtBounded env bound
              domainLevel codomainLevel flag leftSubstitution rightSubstitution
              outputBelowBound leftCodomainOpenSN rightCodomainOpenSN
              (premisesFundamental.2 leftSubstitution rightSubstitution
                (LevelExpr.denote (lmaxAll [domainLevel, codomainLevel]) env)
                (Nat.le_of_lt outputBelowBound) leftEnv rightEnv envRelated
                Generator.gen_sigmaTyCode_binderShifts_eq)
      · have shapeEq := premises.shiftsShape
        obtain ⟨outputFlag, outputEq⟩ := formationRowOutputLevel isFormation shapeEq _ flag
        rw [outputEq]
        obtain ⟨leftChildrenNormalizing, rightChildrenNormalizing, outputBelowBound⟩ :=
          BinaryTelescopeReducibleAtBounded.foldChildrenNormalizingAndOutputBelow shapeEq
            (formationLevelsArityBoundNonPiSigma isFormation isPiFormer isSigmaFormer shapeEq)
            (fun levelsEmpty =>
              nullaryBelowBound (formationRowNullaryIsUnit isFormation
                (by rw [levelsEmpty] at shapeEq; exact shapeEq)))
            (premisesFundamental.2 leftSubstitution rightSubstitution bound
              (Nat.le_refl bound) leftEnv rightEnv envRelated shapeEq)
        exact binaryDataFormationUnderSubstAtBounded (lmaxAll levelsList) outputFlag
          leftSubstitution rightSubstitution isFormation isPiFormer outputBelowBound
          leftChildrenNormalizing rightChildrenNormalizing
  · -- nilTelescope
    intro _baseScope _currentDepth _context _flag
    refine ⟨?_, ?_⟩
    · intro _targetScope _substitution _argLevel _argLevelLeBound _env _shapeEq
      exact True.intro
    · intro _targetScope _leftSubstitution _rightSubstitution _argLevel _argLevelLeBound
        _leftEnv _rightEnv _envRelated _shapeEq
      exact True.intro
  · -- consTelescope (mirror of the formation cons arm, grown head FT)
    intro _baseScope _currentDepth _restShifts _context _head _headLevel _restLevels _flag
      _rest headTyped _restTyped headBudget _restBudget headFundamental restFundamental
    refine ⟨?_, ?_⟩
    · intro _targetScope substitution argLevel argLevelLeBound envReducible shapeEq
      dsimp only [List.length_cons, consecutiveShifts] at shapeEq
      obtain ⟨_headShiftEq, restShapeEq⟩ := List.cons.inj shapeEq
      subst restShapeEq
      exact fundamentalTelescopeConsAtBoundedSucc env bound argLevel envReducible
        (HasTypeDescPi.fundamentalAtBoundedSucc env bound headTyped headBudget)
        (fun argument argumentMember =>
          restFundamental.1 (RawTermSubst.cons argument substitution) argLevel argLevelLeBound
            (ReducibleEnvAtBounded.cons envReducible (argumentMember.cumulative argLevelLeBound))
            rfl)
    · intro _targetScope leftSubstitution rightSubstitution argLevel argLevelLeBound
        leftEnv rightEnv envRelated shapeEq
      dsimp only [List.length_cons, consecutiveShifts] at shapeEq
      obtain ⟨_headShiftEq, restShapeEq⟩ := List.cons.inj shapeEq
      subst restShapeEq
      refine ⟨?_, ?_⟩
      · have headPair := headFundamental leftSubstitution rightSubstitution
          leftEnv rightEnv envRelated
        rw [subst_universeCodeCell] at headPair
        rwa [subst_universeCodeCell] at headPair
      · intro leftArgument rightArgument leftUnaryMember rightUnaryMember argumentsMember
        exact restFundamental.2 (RawTermSubst.cons leftArgument leftSubstitution)
          (RawTermSubst.cons rightArgument rightSubstitution) argLevel argLevelLeBound
          (ReducibleEnvAtBounded.cons leftEnv (leftUnaryMember.cumulative argLevelLeBound))
          (ReducibleEnvAtBounded.cons rightEnv (rightUnaryMember.cumulative argLevelLeBound))
          (BinaryReducibleEnvAtBounded.cons envRelated
            (isBinaryReducibleMemberPair_cumulative argumentsMember argLevelLeBound))
          rfl

/-! ## ★ The closed corollary — the abstraction-theorem doorway -/

/-- ★★ **Closed binary parametricity (the OP1-K3 doorway)**: every CLOSED well-typed term is
binary-SELF-related — at the budget-derived bound, under EVERY `+1`-closing substitution pair,
its two closures form a binary-reducible member pair at the classifier's two closures.  All
three environment premises are vacuous over the empty context, so the conjoined motive's
unary scaffolding erases entirely from the closed statement. -/
theorem HasTypeDescPi.binaryParametricityClosed {profile : PolyProfile}
    {subject classifier : RawTerm 0} (env : Nat → Nat)
    (typed : HasTypeDescPi profile TypingContext.empty subject classifier) :
    ∃ bound : Nat, ∀ {targetScope : Nat}
      (leftSubstitution rightSubstitution : RawTermSubst 0 (targetScope + 1)),
      IsBinaryReducibleMemberPairAtBounded env bound
        (RawTerm.subst leftSubstitution classifier)
        (RawTerm.subst rightSubstitution classifier)
        (RawTerm.subst leftSubstitution subject)
        (RawTerm.subst rightSubstitution subject) := by
  obtain ⟨bound, budget⟩ := BoundExceedsPi.existsBound typed
  exact ⟨bound, fun {_targetScope} leftSubstitution rightSubstitution =>
    HasTypeDescPi.binaryFundamentalConjoinedAtBounded env bound typed budget
      leftSubstitution rightSubstitution
      (ReducibleEnvAtBounded.empty leftSubstitution)
      (ReducibleEnvAtBounded.empty rightSubstitution)
      (BinaryReducibleEnvAtBounded.empty leftSubstitution rightSubstitution)⟩

end FX1Poly.Typed
