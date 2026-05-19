import LeanFX2.Reduction.RawParRename

/-! # LeanFX2.Reduction.RawParInversion.TypeCodes

Inversion lemmas for `RawStep.par` on schematic-payload type-code
ctors plus the equiv-application and universe-code ctors.

Covered ctors (each fires only its cong rule plus refl, except
`equivApply` which has a 4-way β disjunction):

* `arrowCode`, `piTyCode`, `sigmaTyCode`
* `productCode`, `sumCode`
* `listCode`, `optionCode`, `eitherCode`
* `idCode`, `equivCode`
* `equivApply` (D3.6-S6 4-way β)
* `universeCode` (K12.20.AR.1 refl-only)

These power the `lift_full_*Code` theorems in `Term/PreservesTerm.lean`.

## Root status

Layer 2 raw parallel-step inversion helper.  Zero axioms. -/

namespace LeanFX2

/-! ### Type-code ctors

`RawTerm.arrowCode`, `piTyCode`, `sigmaTyCode`, `productCode`, `sumCode`,
`listCode`, `optionCode`, `eitherCode`, `idCode`, `equivCode` are
schematic-payload value-shaped raws: their only RawStep.par-source rules
are the cong rules listed above plus refl.  Hence each inversion is a
two-arm structural decomposition.  These power the `lift_full_*Code`
theorems in `Term/PreservesTerm.lean`. -/

/-- `RawStep.par (arrowCode dom cod) target → target = arrowCode dom' cod' ∧ pars`. -/
theorem RawStep.par.arrowCode_inv {scope : Nat}
    {domainCode codomainCode : RawTerm scope} {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.arrowCode domainCode codomainCode) target) :
    ∃ domainTarget codomainTarget,
      target = RawTerm.arrowCode domainTarget codomainTarget ∧
        RawStep.par domainCode domainTarget ∧
        RawStep.par codomainCode codomainTarget := by
  cases parallelStep with
  | refl _ =>
      exact ⟨domainCode, codomainCode, rfl,
        RawStep.par.refl _, RawStep.par.refl _⟩
  | arrowCodeCong domainStep codomainStep =>
      exact ⟨_, _, rfl, domainStep, codomainStep⟩

/-- `RawStep.par (piTyCode dom cod) target → target = piTyCode dom' cod' ∧ pars`.
Codomain raw lives at scope+1. -/
theorem RawStep.par.piTyCode_inv {scope : Nat}
    {domainCode : RawTerm scope}
    {codomainCode : RawTerm (scope + 1)}
    {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.piTyCode domainCode codomainCode) target) :
    ∃ (domainTarget : RawTerm scope) (codomainTarget : RawTerm (scope + 1)),
      target = RawTerm.piTyCode domainTarget codomainTarget ∧
        RawStep.par domainCode domainTarget ∧
        RawStep.par codomainCode codomainTarget := by
  cases parallelStep with
  | refl _ =>
      exact ⟨domainCode, codomainCode, rfl,
        RawStep.par.refl _, RawStep.par.refl _⟩
  | piTyCodeCong domainStep codomainStep =>
      exact ⟨_, _, rfl, domainStep, codomainStep⟩

/-- `RawStep.par (sigmaTyCode first second) target → target = sigmaTyCode first' second' ∧ pars`.
Second raw lives at scope+1. -/
theorem RawStep.par.sigmaTyCode_inv {scope : Nat}
    {firstCode : RawTerm scope}
    {secondCode : RawTerm (scope + 1)}
    {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.sigmaTyCode firstCode secondCode) target) :
    ∃ (firstTarget : RawTerm scope) (secondTarget : RawTerm (scope + 1)),
      target = RawTerm.sigmaTyCode firstTarget secondTarget ∧
        RawStep.par firstCode firstTarget ∧
        RawStep.par secondCode secondTarget := by
  cases parallelStep with
  | refl _ =>
      exact ⟨firstCode, secondCode, rfl,
        RawStep.par.refl _, RawStep.par.refl _⟩
  | sigmaTyCodeCong firstStep secondStep =>
      exact ⟨_, _, rfl, firstStep, secondStep⟩

/-- `RawStep.par (productCode first second) target → target = productCode first' second' ∧ pars`. -/
theorem RawStep.par.productCode_inv {scope : Nat}
    {firstCode secondCode : RawTerm scope} {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.productCode firstCode secondCode) target) :
    ∃ firstTarget secondTarget,
      target = RawTerm.productCode firstTarget secondTarget ∧
        RawStep.par firstCode firstTarget ∧
        RawStep.par secondCode secondTarget := by
  cases parallelStep with
  | refl _ =>
      exact ⟨firstCode, secondCode, rfl,
        RawStep.par.refl _, RawStep.par.refl _⟩
  | productCodeCong firstStep secondStep =>
      exact ⟨_, _, rfl, firstStep, secondStep⟩

/-- `RawStep.par (sumCode left right) target → target = sumCode left' right' ∧ pars`. -/
theorem RawStep.par.sumCode_inv {scope : Nat}
    {leftCode rightCode : RawTerm scope} {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.sumCode leftCode rightCode) target) :
    ∃ leftTarget rightTarget,
      target = RawTerm.sumCode leftTarget rightTarget ∧
        RawStep.par leftCode leftTarget ∧
        RawStep.par rightCode rightTarget := by
  cases parallelStep with
  | refl _ =>
      exact ⟨leftCode, rightCode, rfl,
        RawStep.par.refl _, RawStep.par.refl _⟩
  | sumCodeCong leftStep rightStep =>
      exact ⟨_, _, rfl, leftStep, rightStep⟩

/-- `RawStep.par (listCode element) target → target = listCode element' ∧ par`. -/
theorem RawStep.par.listCode_inv {scope : Nat}
    {elementCode : RawTerm scope} {target : RawTerm scope}
    (parallelStep : RawStep.par (RawTerm.listCode elementCode) target) :
    ∃ elementTarget,
      target = RawTerm.listCode elementTarget ∧
        RawStep.par elementCode elementTarget := by
  cases parallelStep with
  | refl _ => exact ⟨elementCode, rfl, RawStep.par.refl _⟩
  | listCodeCong elementStep => exact ⟨_, rfl, elementStep⟩

/-- `RawStep.par (optionCode element) target → target = optionCode element' ∧ par`. -/
theorem RawStep.par.optionCode_inv {scope : Nat}
    {elementCode : RawTerm scope} {target : RawTerm scope}
    (parallelStep : RawStep.par (RawTerm.optionCode elementCode) target) :
    ∃ elementTarget,
      target = RawTerm.optionCode elementTarget ∧
        RawStep.par elementCode elementTarget := by
  cases parallelStep with
  | refl _ => exact ⟨elementCode, rfl, RawStep.par.refl _⟩
  | optionCodeCong elementStep => exact ⟨_, rfl, elementStep⟩

/-- `RawStep.par (eitherCode left right) target → target = eitherCode left' right' ∧ pars`. -/
theorem RawStep.par.eitherCode_inv {scope : Nat}
    {leftCode rightCode : RawTerm scope} {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.eitherCode leftCode rightCode) target) :
    ∃ leftTarget rightTarget,
      target = RawTerm.eitherCode leftTarget rightTarget ∧
        RawStep.par leftCode leftTarget ∧
        RawStep.par rightCode rightTarget := by
  cases parallelStep with
  | refl _ =>
      exact ⟨leftCode, rightCode, rfl,
        RawStep.par.refl _, RawStep.par.refl _⟩
  | eitherCodeCong leftStep rightStep =>
      exact ⟨_, _, rfl, leftStep, rightStep⟩

/-- `RawStep.par (idCode type left right) target → target = idCode type' left' right' ∧ pars`. -/
theorem RawStep.par.idCode_inv {scope : Nat}
    {typeCode leftCode rightCode : RawTerm scope} {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.idCode typeCode leftCode rightCode) target) :
    ∃ typeTarget leftTarget rightTarget,
      target = RawTerm.idCode typeTarget leftTarget rightTarget ∧
        RawStep.par typeCode typeTarget ∧
        RawStep.par leftCode leftTarget ∧
        RawStep.par rightCode rightTarget := by
  cases parallelStep with
  | refl _ =>
      exact ⟨typeCode, leftCode, rightCode, rfl,
        RawStep.par.refl _, RawStep.par.refl _, RawStep.par.refl _⟩
  | idCodeCong typeStep leftStep rightStep =>
      exact ⟨_, _, _, rfl, typeStep, leftStep, rightStep⟩

/-- `RawStep.par (equivCode left right) target → target = equivCode left' right' ∧ pars`. -/
theorem RawStep.par.equivCode_inv {scope : Nat}
    {leftCode rightCode : RawTerm scope} {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.equivCode leftCode rightCode) target) :
    ∃ leftTarget rightTarget,
      target = RawTerm.equivCode leftTarget rightTarget ∧
        RawStep.par leftCode leftTarget ∧
        RawStep.par rightCode rightTarget := by
  cases parallelStep with
  | refl _ =>
      exact ⟨leftCode, rightCode, rfl,
        RawStep.par.refl _, RawStep.par.refl _⟩
  | equivCodeCong leftStep rightStep =>
      exact ⟨_, _, rfl, leftStep, rightStep⟩

/-- D3.6-S6 `RawStep.par (equivApply equivRaw argRaw) target` admits
four disjunctive arms: a congruent `equivApply` (cong arm), shallow
round-trip-β when the equiv is syntactically `uaToEquiv (oeqRefl
witness)` (`uaReflEquivApply` arm), or deep round-trip-β when the
equiv develops to `uaToEquiv (oeqRefl _)` via parallel reduction
(`uaReflEquivApplyDeep` arm).  Required by `RawCdLemma`'s β arms and
the `cdEquivApplyCase` activation. -/
theorem RawStep.par.equivApply_inv {scope : Nat}
    {equivRaw argRaw : RawTerm scope} {target : RawTerm scope}
    (parallelStep : RawStep.par (RawTerm.equivApply equivRaw argRaw) target) :
    (∃ equivTarget argTarget,
        target = RawTerm.equivApply equivTarget argTarget ∧
          RawStep.par equivRaw equivTarget ∧
          RawStep.par argRaw argTarget) ∨
    (∃ (witnessSource witnessTarget sourceTarget : RawTerm scope),
        equivRaw = RawTerm.uaToEquiv (RawTerm.oeqRefl witnessSource) ∧
        target = sourceTarget ∧
        RawStep.par witnessSource witnessTarget ∧
        RawStep.par argRaw sourceTarget) ∨
    (∃ (witnessTarget sourceTarget : RawTerm scope),
        target = sourceTarget ∧
        RawStep.par equivRaw
          (RawTerm.uaToEquiv (RawTerm.oeqRefl witnessTarget)) ∧
        RawStep.par argRaw sourceTarget) := by
  cases parallelStep with
  | refl _ =>
      exact Or.inl ⟨equivRaw, argRaw, rfl,
        RawStep.par.refl _, RawStep.par.refl _⟩
  | equivApplyCong equivStep argStep =>
      exact Or.inl ⟨_, _, rfl, equivStep, argStep⟩
  | uaReflEquivApply witnessStep sourceStep =>
      exact Or.inr (Or.inl
        ⟨_, _, _, rfl, rfl, witnessStep, sourceStep⟩)
  | uaReflEquivApplyDeep equivStep sourceStep =>
      exact Or.inr (Or.inr
        ⟨_, _, rfl, equivStep, sourceStep⟩)

/-- **K12.20.AR.1 universeCode parallel-step inversion** — universe
code intro at outer level.  `RawTerm.universeCode innerLevel` has
no β/ι rules and is not the source of any non-refl par ctor
(per `RawParCompatible.lean:259` it dispatches to `refl _` under
rename/subst), so the only step from it is reflexivity. -/
theorem RawStep.par.universeCode_inv {scope : Nat}
    {innerLevel : Nat} {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.universeCode innerLevel : RawTerm scope)
        target) :
    target = RawTerm.universeCode innerLevel := by
  cases parallelStep
  case refl _ => rfl

end LeanFX2
