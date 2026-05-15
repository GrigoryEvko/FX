import LeanFX2.Reducibility.NeutralSNIntro.Lists

/-! # LeanFX2.Reducibility.NeutralSNIntro.Codes

`refl` / `oeqRefl` / `idStrictRefl` SN preservation +
`interval0` / `interval1` niladics + the universe / arrow / piTy
/ sigmaTy / productCode / sumCode / eitherCode / equivCode /
listCode / optionCode / idCode type-code SN witnesses.

## Root status

Layer 3 metatheory leaf.  Feeds `LeanFX2/Term/SN/DirectCases.lean`
(reflexivity + interval atoms) and
`LeanFX2/Reducibility/NeutralSNClosure/TypeCodeSN.lean` (per-leaf
typed type-code wrappers) after the Kripke pivot.  The Tait-era
`RawTerm.IsStronglyNormalizingTypeCode` payload-frontier predicate
was excised along with its sole consumer when the bypass-free
Kripke refactor landed. -/

namespace LeanFX2


/-- HoTT identity-type reflexivity introduction SN
preservation.  Unary cong over the path witness;
`RawStep.par.refl_inv` discharges each par step. -/
theorem RawTerm.refl_isStronglyNormalizing {scope : Nat}
    {rawWitness : RawTerm scope}
    (witnessIsSN : RawTerm.isStronglyNormalizing rawWitness) :
    RawTerm.isStronglyNormalizing (RawTerm.refl rawWitness) := by
  induction witnessIsSN with
  | intro currentWitness _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.refl currentWitness) ?_
    intro target progressStep
    obtain ⟨witnessTarget, targetEq, witnessStep⟩ :=
      RawStep.par.refl_inv progressStep.1
    subst targetEq
    have witnessDistinct :
        currentWitness ≠ witnessTarget := fun witnessEq =>
      progressStep.2 (congrArg RawTerm.refl witnessEq)
    exact inductiveHypothesis witnessTarget
      ⟨witnessStep, witnessDistinct⟩

/-- Observational-equality reflexivity introduction SN
preservation.  Sister to refl helper; `RawStep.par.oeqRefl_inv`
discharges each par step. -/
theorem RawTerm.oeqRefl_isStronglyNormalizing {scope : Nat}
    {witness : RawTerm scope}
    (witnessIsSN : RawTerm.isStronglyNormalizing witness) :
    RawTerm.isStronglyNormalizing (RawTerm.oeqRefl witness) := by
  induction witnessIsSN with
  | intro currentWitness _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.oeqRefl currentWitness) ?_
    intro target progressStep
    obtain ⟨witnessTarget, targetEq, witnessStep⟩ :=
      RawStep.par.oeqRefl_inv progressStep.1
    subst targetEq
    have witnessDistinct :
        currentWitness ≠ witnessTarget := fun witnessEq =>
      progressStep.2 (congrArg RawTerm.oeqRefl witnessEq)
    exact inductiveHypothesis witnessTarget
      ⟨witnessStep, witnessDistinct⟩

/-- Strict-identity reflexivity introduction SN preservation.
Same unary shape as refl / oeqRefl. -/
theorem RawTerm.idStrictRefl_isStronglyNormalizing {scope : Nat}
    {witness : RawTerm scope}
    (witnessIsSN : RawTerm.isStronglyNormalizing witness) :
    RawTerm.isStronglyNormalizing (RawTerm.idStrictRefl witness) := by
  induction witnessIsSN with
  | intro currentWitness _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.idStrictRefl currentWitness) ?_
    intro target progressStep
    obtain ⟨witnessTarget, targetEq, witnessStep⟩ :=
      RawStep.par.idStrictRefl_inv progressStep.1
    subst targetEq
    have witnessDistinct :
        currentWitness ≠ witnessTarget := fun witnessEq =>
      progressStep.2 (congrArg RawTerm.idStrictRefl witnessEq)
    exact inductiveHypothesis witnessTarget
      ⟨witnessStep, witnessDistinct⟩

/-- Cubical interval endpoint 0 SN preservation.  Atomic nullary,
only refl reduces, parProgress disequality contradicts the
.symm of `RawStep.par.interval0_inv`. -/
theorem RawTerm.interval0_isStronglyNormalizing {scope : Nat} :
    RawTerm.isStronglyNormalizing (RawTerm.interval0 : RawTerm scope) :=
  RawTerm.isStronglyNormalizing.intro
    (RawTerm.interval0 : RawTerm scope)
    (fun _ progressStep =>
      (progressStep.2 (RawStep.par.interval0_inv progressStep.1).symm).elim)

/-- Cubical interval endpoint 1 SN preservation.  Sister to
interval0; same atomic nullary shape. -/
theorem RawTerm.interval1_isStronglyNormalizing {scope : Nat} :
    RawTerm.isStronglyNormalizing (RawTerm.interval1 : RawTerm scope) :=
  RawTerm.isStronglyNormalizing.intro
    (RawTerm.interval1 : RawTerm scope)
    (fun _ progressStep =>
      (progressStep.2 (RawStep.par.interval1_inv progressStep.1).symm).elim)

/-- Universe code intro SN preservation.  `RawTerm.universeCode
innerLevel` has no β/ι rules; only `RawStep.par.refl` applies, so
`parProgress`'s source-≠-target requirement contradicts the
`.symm` of `RawStep.par.universeCode_inv`. -/
theorem RawTerm.universeCode_isStronglyNormalizing {scope : Nat}
    (innerLevel : Nat) :
    RawTerm.isStronglyNormalizing
      (RawTerm.universeCode innerLevel : RawTerm scope) :=
  RawTerm.isStronglyNormalizing.intro
    (RawTerm.universeCode innerLevel : RawTerm scope)
    (fun _ progressStep =>
      (progressStep.2
        (RawStep.par.universeCode_inv progressStep.1).symm).elim)

/-- Type-code arrow constructor SN preservation.

Unlike `universeCode`, `arrowCode` carries schematic raw payloads and
`RawStep.par` reduces under both of them.  The SN premises are therefore
real obligations; schematic type-code payloads do not normalize as
constants. -/
theorem RawTerm.arrowCode_isStronglyNormalizing {scope : Nat}
    {domainCode : RawTerm scope}
    (domainIsSN : RawTerm.isStronglyNormalizing domainCode) :
    ∀ {codomainCode : RawTerm scope},
    RawTerm.isStronglyNormalizing codomainCode →
    RawTerm.isStronglyNormalizing
      (RawTerm.arrowCode domainCode codomainCode) := by
  induction domainIsSN with
  | intro currentDomain _ domainIH =>
    intro codomainCode codomainIsSN
    induction codomainIsSN with
    | intro currentCodomain codomainClosure codomainIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.arrowCode currentDomain currentCodomain) ?_
      intro target progressStep
      obtain ⟨domainTarget, codomainTarget, targetEq,
              domainStep, codomainStep⟩ :=
        RawStep.par.arrowCode_inv progressStep.1
      subst targetEq
      by_cases domainEq : currentDomain = domainTarget
      · subst domainEq
        by_cases codomainEq : currentCodomain = codomainTarget
        · subst codomainEq
          exact False.elim (progressStep.2 rfl)
        · exact codomainIH codomainTarget ⟨codomainStep, codomainEq⟩
      · have domainProgress :
            RawStep.parProgress currentDomain domainTarget :=
          ⟨domainStep, domainEq⟩
        by_cases codomainEq : currentCodomain = codomainTarget
        · subst codomainEq
          exact domainIH domainTarget domainProgress
            (RawTerm.isStronglyNormalizing.intro
              currentCodomain codomainClosure)
        · exact domainIH domainTarget domainProgress
            (codomainClosure codomainTarget ⟨codomainStep, codomainEq⟩)

/-- Type-code dependent-Pi constructor SN preservation.

The codomain code lives under the Pi binder at `scope + 1`, so this is
not just a specialization of `arrowCode_isStronglyNormalizing`.  The
proof is the same two-payload congruence argument, with the second SN
witness indexed over the lifted scope. -/
theorem RawTerm.piTyCode_isStronglyNormalizing {scope : Nat}
    {domainCode : RawTerm scope}
    (domainIsSN : RawTerm.isStronglyNormalizing domainCode) :
    ∀ {codomainCode : RawTerm (scope + 1)},
    RawTerm.isStronglyNormalizing codomainCode →
    RawTerm.isStronglyNormalizing
      (RawTerm.piTyCode domainCode codomainCode) := by
  induction domainIsSN with
  | intro currentDomain _ domainIH =>
    intro codomainCode codomainIsSN
    induction codomainIsSN with
    | intro currentCodomain codomainClosure codomainIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.piTyCode currentDomain currentCodomain) ?_
      intro target progressStep
      obtain ⟨domainTarget, codomainTarget, targetEq,
              domainStep, codomainStep⟩ :=
        RawStep.par.piTyCode_inv progressStep.1
      subst targetEq
      by_cases domainEq : currentDomain = domainTarget
      · subst domainEq
        by_cases codomainEq : currentCodomain = codomainTarget
        · subst codomainEq
          exact False.elim (progressStep.2 rfl)
        · exact codomainIH codomainTarget ⟨codomainStep, codomainEq⟩
      · have domainProgress :
            RawStep.parProgress currentDomain domainTarget :=
          ⟨domainStep, domainEq⟩
        by_cases codomainEq : currentCodomain = codomainTarget
        · subst codomainEq
          exact domainIH domainTarget domainProgress
            (RawTerm.isStronglyNormalizing.intro
              currentCodomain codomainClosure)
        · exact domainIH domainTarget domainProgress
            (codomainClosure codomainTarget ⟨codomainStep, codomainEq⟩)

/-- Type-code dependent-Sigma constructor SN preservation.

Like `piTyCode_isStronglyNormalizing`, the second code payload is scoped
under the binder at `scope + 1`.  The proof isolates the two raw
congruence payloads and preserves SN by nested induction over them. -/
theorem RawTerm.sigmaTyCode_isStronglyNormalizing {scope : Nat}
    {firstCode : RawTerm scope}
    (firstIsSN : RawTerm.isStronglyNormalizing firstCode) :
    ∀ {secondCode : RawTerm (scope + 1)},
    RawTerm.isStronglyNormalizing secondCode →
    RawTerm.isStronglyNormalizing
      (RawTerm.sigmaTyCode firstCode secondCode) := by
  induction firstIsSN with
  | intro currentFirst _ firstIH =>
    intro secondCode secondIsSN
    induction secondIsSN with
    | intro currentSecond secondClosure secondIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.sigmaTyCode currentFirst currentSecond) ?_
      intro target progressStep
      obtain ⟨firstTarget, secondTarget, targetEq,
              firstStep, secondStep⟩ :=
        RawStep.par.sigmaTyCode_inv progressStep.1
      subst targetEq
      by_cases firstEq : currentFirst = firstTarget
      · subst firstEq
        by_cases secondEq : currentSecond = secondTarget
        · subst secondEq
          exact False.elim (progressStep.2 rfl)
        · exact secondIH secondTarget ⟨secondStep, secondEq⟩
      · have firstProgress :
            RawStep.parProgress currentFirst firstTarget :=
          ⟨firstStep, firstEq⟩
        by_cases secondEq : currentSecond = secondTarget
        · subst secondEq
          exact firstIH firstTarget firstProgress
            (RawTerm.isStronglyNormalizing.intro
              currentSecond secondClosure)
        · exact firstIH firstTarget firstProgress
            (secondClosure secondTarget ⟨secondStep, secondEq⟩)

/-- Type-code product constructor SN preservation.

`productCode` carries two same-scope schematic raw payloads.  Raw
parallel reduction reduces under both payloads, so SN of the product
code follows by nested induction over the two payload SN witnesses. -/
theorem RawTerm.productCode_isStronglyNormalizing {scope : Nat}
    {firstCode : RawTerm scope}
    (firstIsSN : RawTerm.isStronglyNormalizing firstCode) :
    ∀ {secondCode : RawTerm scope},
    RawTerm.isStronglyNormalizing secondCode →
    RawTerm.isStronglyNormalizing
      (RawTerm.productCode firstCode secondCode) := by
  induction firstIsSN with
  | intro currentFirst _ firstIH =>
    intro secondCode secondIsSN
    induction secondIsSN with
    | intro currentSecond secondClosure secondIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.productCode currentFirst currentSecond) ?_
      intro target progressStep
      obtain ⟨firstTarget, secondTarget, targetEq,
              firstStep, secondStep⟩ :=
        RawStep.par.productCode_inv progressStep.1
      subst targetEq
      by_cases firstEq : currentFirst = firstTarget
      · subst firstEq
        by_cases secondEq : currentSecond = secondTarget
        · subst secondEq
          exact False.elim (progressStep.2 rfl)
        · exact secondIH secondTarget ⟨secondStep, secondEq⟩
      · have firstProgress :
            RawStep.parProgress currentFirst firstTarget :=
          ⟨firstStep, firstEq⟩
        by_cases secondEq : currentSecond = secondTarget
        · subst secondEq
          exact firstIH firstTarget firstProgress
            (RawTerm.isStronglyNormalizing.intro
              currentSecond secondClosure)
        · exact firstIH firstTarget firstProgress
            (secondClosure secondTarget ⟨secondStep, secondEq⟩)

/-- Type-code sum constructor SN preservation.

`sumCode` mirrors `productCode`: both schematic raw payloads are in
the same scope, and raw parallel reduction only proceeds by congruence
under those payloads. -/
theorem RawTerm.sumCode_isStronglyNormalizing {scope : Nat}
    {leftCode : RawTerm scope}
    (leftIsSN : RawTerm.isStronglyNormalizing leftCode) :
    ∀ {rightCode : RawTerm scope},
    RawTerm.isStronglyNormalizing rightCode →
    RawTerm.isStronglyNormalizing
      (RawTerm.sumCode leftCode rightCode) := by
  induction leftIsSN with
  | intro currentLeft _ leftIH =>
    intro rightCode rightIsSN
    induction rightIsSN with
    | intro currentRight rightClosure rightIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.sumCode currentLeft currentRight) ?_
      intro target progressStep
      obtain ⟨leftTarget, rightTarget, targetEq,
              leftStep, rightStep⟩ :=
        RawStep.par.sumCode_inv progressStep.1
      subst targetEq
      by_cases leftEq : currentLeft = leftTarget
      · subst leftEq
        by_cases rightEq : currentRight = rightTarget
        · subst rightEq
          exact False.elim (progressStep.2 rfl)
        · exact rightIH rightTarget ⟨rightStep, rightEq⟩
      · have leftProgress :
            RawStep.parProgress currentLeft leftTarget :=
          ⟨leftStep, leftEq⟩
        by_cases rightEq : currentRight = rightTarget
        · subst rightEq
          exact leftIH leftTarget leftProgress
            (RawTerm.isStronglyNormalizing.intro
              currentRight rightClosure)
        · exact leftIH leftTarget leftProgress
            (rightClosure rightTarget ⟨rightStep, rightEq⟩)

/-- Type-code either constructor SN preservation.

`eitherCode` is the same same-scope binary type-code shape as
`sumCode`: raw parallel reduction only reduces congruently under the
left and right schematic payloads. -/
theorem RawTerm.eitherCode_isStronglyNormalizing {scope : Nat}
    {leftCode : RawTerm scope}
    (leftIsSN : RawTerm.isStronglyNormalizing leftCode) :
    ∀ {rightCode : RawTerm scope},
    RawTerm.isStronglyNormalizing rightCode →
    RawTerm.isStronglyNormalizing
      (RawTerm.eitherCode leftCode rightCode) := by
  induction leftIsSN with
  | intro currentLeft _ leftIH =>
    intro rightCode rightIsSN
    induction rightIsSN with
    | intro currentRight rightClosure rightIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.eitherCode currentLeft currentRight) ?_
      intro target progressStep
      obtain ⟨leftTarget, rightTarget, targetEq,
              leftStep, rightStep⟩ :=
        RawStep.par.eitherCode_inv progressStep.1
      subst targetEq
      by_cases leftEq : currentLeft = leftTarget
      · subst leftEq
        by_cases rightEq : currentRight = rightTarget
        · subst rightEq
          exact False.elim (progressStep.2 rfl)
        · exact rightIH rightTarget ⟨rightStep, rightEq⟩
      · have leftProgress :
            RawStep.parProgress currentLeft leftTarget :=
          ⟨leftStep, leftEq⟩
        by_cases rightEq : currentRight = rightTarget
        · subst rightEq
          exact leftIH leftTarget leftProgress
            (RawTerm.isStronglyNormalizing.intro
              currentRight rightClosure)
        · exact leftIH leftTarget leftProgress
            (rightClosure rightTarget ⟨rightStep, rightEq⟩)

/-- Type-code equivalence constructor SN preservation.

`equivCode` is congruence-only over two same-scope schematic type-code
payloads, so it follows the binary payload SN argument used by
`sumCode` and `eitherCode`. -/
theorem RawTerm.equivCode_isStronglyNormalizing {scope : Nat}
    {leftCode : RawTerm scope}
    (leftIsSN : RawTerm.isStronglyNormalizing leftCode) :
    ∀ {rightCode : RawTerm scope},
    RawTerm.isStronglyNormalizing rightCode →
    RawTerm.isStronglyNormalizing
      (RawTerm.equivCode leftCode rightCode) := by
  induction leftIsSN with
  | intro currentLeft _ leftIH =>
    intro rightCode rightIsSN
    induction rightIsSN with
    | intro currentRight rightClosure rightIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.equivCode currentLeft currentRight) ?_
      intro target progressStep
      obtain ⟨leftTarget, rightTarget, targetEq,
              leftStep, rightStep⟩ :=
        RawStep.par.equivCode_inv progressStep.1
      subst targetEq
      by_cases leftEq : currentLeft = leftTarget
      · subst leftEq
        by_cases rightEq : currentRight = rightTarget
        · subst rightEq
          exact False.elim (progressStep.2 rfl)
        · exact rightIH rightTarget ⟨rightStep, rightEq⟩
      · have leftProgress :
            RawStep.parProgress currentLeft leftTarget :=
          ⟨leftStep, leftEq⟩
        by_cases rightEq : currentRight = rightTarget
        · subst rightEq
          exact leftIH leftTarget leftProgress
            (RawTerm.isStronglyNormalizing.intro
              currentRight rightClosure)
        · exact leftIH leftTarget leftProgress
            (rightClosure rightTarget ⟨rightStep, rightEq⟩)

/-- Type-code list constructor SN preservation.

`listCode` is congruence-only over its schematic element-code
payload, so SN follows by one induction over that payload. -/
theorem RawTerm.listCode_isStronglyNormalizing {scope : Nat}
    {elementCode : RawTerm scope}
    (elementIsSN : RawTerm.isStronglyNormalizing elementCode) :
    RawTerm.isStronglyNormalizing
      (RawTerm.listCode elementCode) := by
  induction elementIsSN with
  | intro currentElement _ elementIH =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.listCode currentElement) ?_
    intro target progressStep
    obtain ⟨elementTarget, targetEq, elementStep⟩ :=
      RawStep.par.listCode_inv progressStep.1
    subst targetEq
    have elementDistinct :
        currentElement ≠ elementTarget := fun elementEq =>
      progressStep.2 (congrArg RawTerm.listCode elementEq)
    exact elementIH elementTarget
      ⟨elementStep, elementDistinct⟩

/-- Type-code option constructor SN preservation.

`optionCode` is congruence-only over its schematic element-code
payload, matching `listCode` at the raw layer. -/
theorem RawTerm.optionCode_isStronglyNormalizing {scope : Nat}
    {elementCode : RawTerm scope}
    (elementIsSN : RawTerm.isStronglyNormalizing elementCode) :
    RawTerm.isStronglyNormalizing
      (RawTerm.optionCode elementCode) := by
  induction elementIsSN with
  | intro currentElement _ elementIH =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.optionCode currentElement) ?_
    intro target progressStep
    obtain ⟨elementTarget, targetEq, elementStep⟩ :=
      RawStep.par.optionCode_inv progressStep.1
    subst targetEq
    have elementDistinct :
        currentElement ≠ elementTarget := fun elementEq =>
      progressStep.2 (congrArg RawTerm.optionCode elementEq)
    exact elementIH elementTarget
      ⟨elementStep, elementDistinct⟩

/-- Type-code identity constructor SN preservation.

`idCode` is congruence-only over its schematic carrier and endpoint
codes.  SN follows by the same payload-product induction as the
binary type-code constructors, extended to the ternary payload. -/
theorem RawTerm.idCode_isStronglyNormalizing {scope : Nat}
    {typeCode : RawTerm scope}
    (typeCodeIsSN : RawTerm.isStronglyNormalizing typeCode) :
    ∀ {leftCode : RawTerm scope},
    RawTerm.isStronglyNormalizing leftCode →
    ∀ {rightCode : RawTerm scope},
    RawTerm.isStronglyNormalizing rightCode →
  RawTerm.isStronglyNormalizing
      (RawTerm.idCode typeCode leftCode rightCode) := by
  induction typeCodeIsSN with
  | intro currentType _ typeIH =>
    intro leftCode leftCodeIsSN
    induction leftCodeIsSN with
    | intro currentLeft leftClosure leftIH =>
      intro rightCode rightCodeIsSN
      induction rightCodeIsSN with
      | intro currentRight rightClosure rightIH =>
        refine RawTerm.isStronglyNormalizing.intro
          (RawTerm.idCode currentType currentLeft currentRight) ?_
        intro target progressStep
        obtain ⟨typeTarget, leftTarget, rightTarget, targetEq,
                typeStep, leftStep, rightStep⟩ :=
          RawStep.par.idCode_inv progressStep.1
        subst targetEq
        by_cases typeEq : currentType = typeTarget
        · subst typeEq
          by_cases leftEq : currentLeft = leftTarget
          · subst leftEq
            by_cases rightEq : currentRight = rightTarget
            · subst rightEq
              exact False.elim (progressStep.2 rfl)
            · exact rightIH rightTarget ⟨rightStep, rightEq⟩
          · have leftProgress :
                RawStep.parProgress currentLeft leftTarget :=
              ⟨leftStep, leftEq⟩
            by_cases rightEq : currentRight = rightTarget
            · subst rightEq
              exact leftIH leftTarget leftProgress
                (RawTerm.isStronglyNormalizing.intro
                  currentRight rightClosure)
            · exact leftIH leftTarget leftProgress
                (rightClosure rightTarget ⟨rightStep, rightEq⟩)
        · have typeProgress :
              RawStep.parProgress currentType typeTarget :=
            ⟨typeStep, typeEq⟩
          by_cases leftEq : currentLeft = leftTarget
          · subst leftEq
            by_cases rightEq : currentRight = rightTarget
            · subst rightEq
              exact typeIH typeTarget typeProgress
                (RawTerm.isStronglyNormalizing.intro
                  currentLeft leftClosure)
                (RawTerm.isStronglyNormalizing.intro
                  currentRight rightClosure)
            · exact typeIH typeTarget typeProgress
                (RawTerm.isStronglyNormalizing.intro
                  currentLeft leftClosure)
                (rightClosure rightTarget ⟨rightStep, rightEq⟩)
          · have leftTargetIsSN :
                RawTerm.isStronglyNormalizing leftTarget :=
              leftClosure leftTarget ⟨leftStep, leftEq⟩
            by_cases rightEq : currentRight = rightTarget
            · subst rightEq
              exact typeIH typeTarget typeProgress
                leftTargetIsSN
                (RawTerm.isStronglyNormalizing.intro
                  currentRight rightClosure)
            · exact typeIH typeTarget typeProgress
                leftTargetIsSN
                (rightClosure rightTarget ⟨rightStep, rightEq⟩)

end LeanFX2
