import LeanFX2.Reducibility.Kripke.Fundamental.HoTTCodesAndEffects

/-! # LeanFX2.Reducibility.Kripke.Fundamental.SNEliminators

SN-only eliminator wrappers and closed type-code leftovers for the
Kripke fundamental layer.  These wrappers delegate to existing SN
lemmas and avoid ReducibleK closure premises.
-/

namespace LeanFX2

/-! ## SN-preservation wrappers for SN-only eliminators

Eliminators whose underlying SN preservation requires only SN of their
subterms (no full Reducible closure) ship as Kripke-namespace
fundamentals via direct delegation to `Term.X_isStronglyNormalizing`.
Eliminators that require a full `Reducible` scrutinee or arrow
application closure (`app`, `appPi`, `natElim`, `natRec`, `listElim`,
`optionMatch`, `eitherMatch`, `pathApp`) remain Phase B targets that
ship through `arrow_apply` chains. -/

/-- SN of boolElim via Kripke: SN(scrutinee), SN(then), SN(else) →
SN(boolElim scrutinee then else). -/
theorem ReducibleK.fundamental_boolElim_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {motiveType : Ty level (scope + 1)}
    {scrutineeRaw thenRaw elseRaw : RawTerm scope}
    {scrutinee : Term sourceCtx Ty.bool scrutineeRaw}
    {thenBranch :
      Term sourceCtx
        (motiveType.subst0 Ty.bool RawTerm.boolTrue)
        thenRaw}
    {elseBranch :
      Term sourceCtx
        (motiveType.subst0 Ty.bool RawTerm.boolFalse)
        elseRaw}
    (scrutineeIsSN : Term.isStronglyNormalizing scrutinee)
    (thenIsSN : Term.isStronglyNormalizing thenBranch)
    (elseIsSN : Term.isStronglyNormalizing elseBranch) :
    Term.isStronglyNormalizing
      (Term.boolElim scrutinee thenBranch elseBranch) :=
  Term.boolElim_isStronglyNormalizing scrutineeIsSN thenIsSN elseIsSN

/-- SN of idJ via Kripke: SN(base), SN(witness) → SN(idJ base witness). -/
theorem ReducibleK.fundamental_idJ_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
      Term sourceCtx (Ty.id carrier leftEndpoint rightEndpoint) witnessRaw}
    (baseCaseIsSN : Term.isStronglyNormalizing baseCase)
    (witnessIsSN : Term.isStronglyNormalizing witness) :
    Term.isStronglyNormalizing (Term.idJ baseCase witness) :=
  Term.idJ_isStronglyNormalizing baseCaseIsSN witnessIsSN

/-- SN of oeqJ via Kripke: SN(base), SN(witness) → SN(oeqJ base witness). -/
theorem ReducibleK.fundamental_oeqJ_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
      Term sourceCtx (Ty.oeq carrier leftEndpoint rightEndpoint) witnessRaw}
    (baseCaseIsSN : Term.isStronglyNormalizing baseCase)
    (witnessIsSN : Term.isStronglyNormalizing witness) :
    Term.isStronglyNormalizing (Term.oeqJ baseCase witness) :=
  Term.oeqJ_isStronglyNormalizing baseCaseIsSN witnessIsSN

/-- SN of idStrictRec via Kripke: SN(base), SN(witness) → SN. -/
theorem ReducibleK.fundamental_idStrictRec_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (modeIsStrict : mode = Mode.strict)
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
      Term sourceCtx
        (Ty.idStrict carrier leftEndpoint rightEndpoint)
        witnessRaw}
    (baseCaseIsSN : Term.isStronglyNormalizing baseCase)
    (witnessIsSN : Term.isStronglyNormalizing witness) :
    Term.isStronglyNormalizing
      (Term.idStrictRec modeIsStrict baseCase witness) :=
  Term.idStrictRec_isStronglyNormalizing modeIsStrict
    baseCaseIsSN witnessIsSN

/-- SN of equivApp via Kripke: SN(equiv), SN(argument) → SN. -/
theorem ReducibleK.fundamental_equivApp_sn
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierA carrierB : Ty level scope}
    {equivRaw argumentRaw : RawTerm scope}
    {equivTerm : Term context (Ty.equiv carrierA carrierB) equivRaw}
    {argumentTerm : Term context carrierA argumentRaw}
    (equivIsSN : Term.isStronglyNormalizing equivTerm)
    (argumentIsSN : Term.isStronglyNormalizing argumentTerm) :
    Term.isStronglyNormalizing
      (Term.equivApp equivTerm argumentTerm) :=
  Term.equivApp_isStronglyNormalizing equivIsSN argumentIsSN

/-- SN of equivApply via Kripke: SN(equiv), SN(argument) → SN. -/
theorem ReducibleK.fundamental_equivApply_sn
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierA carrierB : Ty level scope}
    {equivRaw argumentRaw : RawTerm scope}
    {equivTerm : Term context (Ty.equiv carrierA carrierB) equivRaw}
    {argumentTerm : Term context carrierA argumentRaw}
    (equivIsSN : Term.isStronglyNormalizing equivTerm)
    (argumentIsSN : Term.isStronglyNormalizing argumentTerm) :
    Term.isStronglyNormalizing
      (Term.equivApply equivTerm argumentTerm) :=
  Term.equivApply_isStronglyNormalizing equivIsSN argumentIsSN

/-- SN of modElim via Kripke: SN(inner) → SN(modElim inner). -/
theorem ReducibleK.fundamental_modElim_sn
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    {innerTerm : Term context innerType innerRaw}
    (innerIsSN : Term.isStronglyNormalizing innerTerm) :
    Term.isStronglyNormalizing (Term.modElim innerTerm) :=
  Term.modElim_isStronglyNormalizing innerIsSN

/-! ## Deferred Kripke fundamentals — natElim / natRec

Earlier this file shipped `ReducibleK.fundamental_natElim_sn` and
`ReducibleK.fundamental_natRec_sn` as Term-level SN wrappers taking
a `succAppIsSN` / `contractumIsSN` universally-quantified raw SN
hypothesis.  Per the project's banned-hypothesis-as-postulate rule
those theorems vacuously shipped over raw forms the kernel cannot
construct.  They have been DELETED.

The honest path is the M04 fundamental theorem (proves reducibility
by induction on typing), which produces the contractum-SN status of
the ι reducts as a real consequence.  Defer until M04. -/

/-! ## Closed-leaf type-code fundamentals

The five `Term.X_isStronglyNormalizing` lemmas in `NeutralSNClosure.TypeCodeSN`
plus the two `Term.intervalN_isStronglyNormalizing` lemmas in
`Term.SN.DirectCases` give the Kripke fundamental cases
for the seven closed-leaf canonical-value Term ctors that the
upstream cascade left out. -/

theorem ReducibleK.fundamental_interval0
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (stepCount : Nat) :
    @ReducibleK mode level scope sourceCtx stepCount Ty.interval
      RawTerm.interval0 (Term.interval0 (context := sourceCtx)) := by
  cases stepCount with
  | zero => trivial
  | succ subCount =>
    exact (Term.interval0_isStronglyNormalizing (sourceCtx := sourceCtx))

theorem ReducibleK.fundamental_interval1
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (stepCount : Nat) :
    @ReducibleK mode level scope sourceCtx stepCount Ty.interval
      RawTerm.interval1 (Term.interval1 (context := sourceCtx)) := by
  cases stepCount with
  | zero => trivial
  | succ subCount =>
    exact (Term.interval1_isStronglyNormalizing (sourceCtx := sourceCtx))

theorem ReducibleK.fundamental_universeCode_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (innerLevel outerLevel : UniverseLevel)
    (cumulOk : innerLevel.toNat ≤ outerLevel.toNat)
    (levelLe : outerLevel.toNat + 1 ≤ level) :
    Term.isStronglyNormalizing
      (Term.universeCode (context := sourceCtx)
        innerLevel outerLevel cumulOk levelLe) :=
  Term.universeCode_isStronglyNormalizing
    innerLevel outerLevel cumulOk levelLe

theorem ReducibleK.fundamental_piTyCode_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {domainCodeRaw : RawTerm scope}
    {codomainCodeRaw : RawTerm (scope + 1)}
    (domainCodeIsSN : RawTerm.isStronglyNormalizing domainCodeRaw)
    (codomainCodeIsSN : RawTerm.isStronglyNormalizing codomainCodeRaw) :
    Term.isStronglyNormalizing
      (Term.piTyCode (context := sourceCtx)
        outerLevel levelLe domainCodeRaw codomainCodeRaw) :=
  Term.piTyCode_isStronglyNormalizing outerLevel levelLe
    domainCodeIsSN codomainCodeIsSN

theorem ReducibleK.fundamental_sigmaTyCode_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {domainCodeRaw : RawTerm scope}
    {codomainCodeRaw : RawTerm (scope + 1)}
    (domainCodeIsSN : RawTerm.isStronglyNormalizing domainCodeRaw)
    (codomainCodeIsSN : RawTerm.isStronglyNormalizing codomainCodeRaw) :
    Term.isStronglyNormalizing
      (Term.sigmaTyCode (context := sourceCtx)
        outerLevel levelLe domainCodeRaw codomainCodeRaw) :=
  Term.sigmaTyCode_isStronglyNormalizing outerLevel levelLe
    domainCodeIsSN codomainCodeIsSN

theorem ReducibleK.fundamental_productCode_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {firstCodeRaw secondCodeRaw : RawTerm scope}
    (firstCodeIsSN : RawTerm.isStronglyNormalizing firstCodeRaw)
    (secondCodeIsSN : RawTerm.isStronglyNormalizing secondCodeRaw) :
    Term.isStronglyNormalizing
      (Term.productCode (context := sourceCtx)
        outerLevel levelLe firstCodeRaw secondCodeRaw) :=
  Term.productCode_isStronglyNormalizing outerLevel levelLe
    firstCodeIsSN secondCodeIsSN

theorem ReducibleK.fundamental_sumCode_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {leftCodeRaw rightCodeRaw : RawTerm scope}
    (leftCodeIsSN : RawTerm.isStronglyNormalizing leftCodeRaw)
    (rightCodeIsSN : RawTerm.isStronglyNormalizing rightCodeRaw) :
    Term.isStronglyNormalizing
      (Term.sumCode (context := sourceCtx)
        outerLevel levelLe leftCodeRaw rightCodeRaw) :=
  Term.sumCode_isStronglyNormalizing outerLevel levelLe
    leftCodeIsSN rightCodeIsSN

/-- SN of funextIntroHet via Kripke.  The raw projection is
`lam (refl applyARaw)`; applyBRaw is schematic and irrelevant. -/
theorem ReducibleK.fundamental_funextIntroHet_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (domainType codomainType : Ty level scope)
    {applyARaw applyBRaw : RawTerm (scope + 1)}
    (applyAIsSN : RawTerm.isStronglyNormalizing applyARaw) :
    Term.isStronglyNormalizing
      (Term.funextIntroHet (context := sourceCtx)
        domainType codomainType applyARaw applyBRaw) :=
  Term.funextIntroHet_isStronglyNormalizing
    domainType codomainType applyAIsSN

/-! ## Deleted Kripke SN fundamentals (β/ι eliminator family).

The following nine `ReducibleK.fundamental_X_sn` Term-level SN wrappers
have been DELETED:

  fundamental_codataDest_sn
  fundamental_listElim_sn
  fundamental_optionMatch_sn
  fundamental_eitherMatch_sn
  fundamental_app_sn
  fundamental_appPi_sn
  fundamental_pathApp_sn
  fundamental_transp_sn
  fundamental_hcomp_sn

Each shipped over universally-quantified raw SN postulates
(`contractumIsSN` / `inlContractumIsSN` / `inrContractumIsSN` /
`uaContractumIsSN` / `composeContractumIsSN`) — Pi-type hypotheses
over arbitrary `RawTerm scope` that are structurally false in general.
Per the project's banned-hypothesis-as-postulate rule (CLAUDE.md
"Forbidden reasoning patterns"), taking such hypotheses to "ship"
theorems vacuously is semantically identical to adding an axiom.

The `fundamental_hcomp_sn` wrapper did not take a contractum
hypothesis directly but delegated to
`Term.hcomp_isStronglyNormalizing`, which itself was part of the
same banned-pattern family from `Term.SN.DirectCases`; deleted for
consistency.

The honest path is the M04 fundamental theorem (induction on typing
derivation), which produces ι-reduct SN status as a real structural
consequence.  Defer until M04. -/

end LeanFX2
