import LeanFX2.Term.RenameInjective
import LeanFX2.Term.TypedInversion

/-! Scratch prototype — validates the `induction termA` inline children-arm
    pattern at zero axioms.  NOT for commit.  Two probes:

    * `proto_fst`: existential-child single-inhabitant (non-colliding raw),
      uses suffices-free-type + `Ty.rename_injective` + childA-fixed IH.
    * `proto_lam`: cast-bearing binder body at a colliding raw
      (`RawTerm.lam` is shared by 5 typed ctors), uses the existing
      `Term.lam_arrow_inv` to invert `termB` propext-cleanly + childA-fixed IH.

    The `app`/`appPi` cross-refutation under rename is the only remaining
    unvalidated shape; it consumes `Term.app_inv` (already shipped in
    `Term/TypedInversion.lean`) and a small `Term.noConfusion`-via-HEq
    refutation lemma to be written in-context during full assembly. -/

namespace LeanFX2

/-- Standalone probe mirroring the `fst` arm of `induction termA`:
    childA-fixed `pairIH`, existential `secondType`, inline `termB` inversion. -/
theorem Term.rename_injective_proto_fst
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (rhoInjective : RawRenamingInjective rho)
    {firstType : Ty level sourceScope} {secondTypeA : Ty level (sourceScope + 1)}
    {pairRaw : RawTerm sourceScope}
    (pairA : Term sourceCtx (Ty.sigmaTy firstType secondTypeA) pairRaw)
    (pairIH :
      ∀ {innerTargetScope : Nat} {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming sourceScope innerTargetScope}
        (innerRenaming : TermRenaming sourceCtx innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (pairB : Term sourceCtx (Ty.sigmaTy firstType secondTypeA) pairRaw),
          Term.rename innerRenaming pairA = Term.rename innerRenaming pairB →
          pairA = pairB)
    (termB : Term sourceCtx firstType (RawTerm.fst pairRaw)) :
    Term.rename termRenaming (Term.fst pairA) =
      Term.rename termRenaming termB → Term.fst pairA = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType (RawTerm.fst pairRaw)),
        Σ' (secondTypeB : Ty level (sourceScope + 1)),
          Σ' (pairB : Term sourceCtx (Ty.sigmaTy genericType secondTypeB) pairRaw),
            HEq genericTerm (Term.fst pairB) by
    obtain ⟨secondTypeB, pairB, termHEqB⟩ := key termB
    cases termHEqB
    dsimp only [Term.rename] at renameEq
    injection renameEq with scopeEq contextEq firstTypeRenameEq
      secondTypeRenameEq pairRawRenameEq pairRenameHEq
    have secondTypeEq : secondTypeA = secondTypeB :=
      Ty.rename_injective_under_injective_renaming secondTypeA
        (RawRenamingInjective.lift rhoInjective) secondTypeB secondTypeRenameEq
    cases secondTypeEq
    have pairEq : pairA = pairB :=
      pairIH termRenaming rhoInjective pairB (eq_of_heq pairRenameHEq)
    cases pairEq
    rfl
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredSecondType pairTerm
  exact ⟨inferredSecondType, pairTerm, HEq.rfl⟩

#print axioms Term.rename_injective_proto_fst

/-- Standalone probe mirroring the `lam` arm of `induction termA`:
    cast-bearing binder body, collision raw (`RawTerm.lam` is shared by 5 typed
    ctors) inverted via the existing `Term.lam_arrow_inv`, childA-fixed `bodyIH`. -/
theorem Term.rename_injective_proto_lam
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (rhoInjective : RawRenamingInjective rho)
    {domainType codomainType : Ty level sourceScope}
    {bodyRaw : RawTerm (sourceScope + 1)}
    (body : Term (sourceCtx.cons domainType) codomainType.weaken bodyRaw)
    (bodyIH :
      ∀ {innerTargetScope : Nat} {innerTargetCtx : Ctx mode level innerTargetScope}
        {innerRho : RawRenaming (sourceScope + 1) innerTargetScope}
        (innerRenaming :
          TermRenaming (sourceCtx.cons domainType) innerTargetCtx innerRho),
        RawRenamingInjective innerRho →
        ∀ (bodyB :
            Term (sourceCtx.cons domainType) codomainType.weaken bodyRaw),
          Term.rename innerRenaming body = Term.rename innerRenaming bodyB →
          body = bodyB)
    (termB :
      Term sourceCtx (Ty.arrow domainType codomainType) (RawTerm.lam bodyRaw)) :
    Term.rename termRenaming (Term.lam body) =
      Term.rename termRenaming termB → Term.lam body = termB := by
  intro renameEq
  obtain ⟨bodyB, termHEqB⟩ := Term.lam_arrow_inv termB
  cases termHEqB
  dsimp only [Term.rename] at renameEq
  injection renameEq with contextEq domainRenameEq codomainRenameEq
    bodyRawRenameEq bodyRawRenameEqAgain bodyRenameEq
  have bodyRenameUncastHEq :
      HEq (Term.rename (termRenaming.lift domainType) body)
        (Term.rename (termRenaming.lift domainType) bodyB) :=
    HEq.trans
      (HEq.symm
        (termRenameInjectiveCastHEq
          (Ty.weaken_rename_commute rho codomainType)
          (Term.rename (termRenaming.lift domainType) body)))
      (HEq.trans (heq_of_eq bodyRenameEq)
        (termRenameInjectiveCastHEq
          (Ty.weaken_rename_commute rho codomainType)
          (Term.rename (termRenaming.lift domainType) bodyB)))
  have bodyEq : body = bodyB :=
    bodyIH (termRenaming.lift domainType)
      (RawRenamingInjective.lift rhoInjective) bodyB
      (eq_of_heq bodyRenameUncastHEq)
  cases bodyEq
  rfl

#print axioms Term.rename_injective_proto_lam

/-! ## proto_snd / proto_appPi / proto_boolElim — DEFERRED (cast-on-result wall).

Three Term constructors produce raws shared with no other Term ctor BUT
whose result type involves `Ty.subst0` of an existentially-bound type
component (`Term.snd`'s `secondType.subst0 firstType ...`,
`Term.appPi`'s `codomainType.subst0 ...`, `Term.boolElim`'s
`motiveType.subst0 ...`).  The induction-with-childA-fixed-IH driver
hits a fundamental wall here:

* The `arm_pair` trick (free-type-via-suffices + sigmaTy-headed
  typeEq) does NOT transfer.  `arm_pair` works because `Term.pair`'s
  result type is `Ty.sigmaTy firstType secondType` (a Ty CONSTRUCTOR),
  letting the suffices's typeEq be `genericType = Ty.sigmaTy ifT iST`
  and `cases typeEq` extract component eqs via sigmaTy injection.

* For `Term.snd`, the suffices's typeEq would be `genericType =
  inferredSecondType.subst0 inferredFirstType pairRaw.fst` — `Ty.subst0`
  is NOT a constructor.  Decomposing the subst0 equation to extract
  `firstType = inferredFirstType` and `secondType = inferredSecondType`
  hits the dep-elim wall: `Ty.subst0` is propositionally NON-injective
  (counterexample: `subst0 (Ty.tyVar 0) X = X = subst0 X.weaken X`).

* The downstream `injection` step on
  `HEq (Term.snd (rename pairA)) (Term.snd (rename pairB))` also fails
  because Lean 4 v4.29.1's auto-generated `Term.snd.inj` is HOMOGENEOUS
  only (requires both pairs at the SAME sigmaTy).  Truly heterogeneous
  HEq between snds at different sigmaTys can't be decomposed by
  `injection` without a hand-rolled `Term.snd.injHEq` lemma which
  itself would require the wall to be already broken.

The existing `Term.rename_injective_snd_ctor` (ClosedData.lean:489)
ships zero-axiom but ASSUMES both pairs at the same sigmaTy, with a
bipartite `pairInjective : ∀ pA pB, HEq → HEq` (not childA-fixed).
That signature is incompatible with the `induction termA` driver's
asymmetric Eq-valued childA-fixed pairIH.

**Resolution options for follow-up**:

1. **Joint induction driver** — replace `induction termA generalizing
   ...` with `induction termA, termB` (would need a hand-written
   `Term.jointCasesOn` eliminator) so both pairs share existential
   slots from the start.  Estimated ~2-3K LoC driver rewrite.

2. **Ctor reformulation** — refactor `Term.snd`/`Term.appPi`/
   `Term.boolElim` to take the outer subst0 type as an explicit
   parameter + propositional Eq witness (per `feedback_lean_universe_
   constructor_block.md`'s pattern).  Estimated ~200-500 LoC ABI churn
   across 6 layers.

3. **NbE bypass** — defer T2 until K13 NbE eval+quote ships, then
   prove rename injectivity via NbE roundtrip (a la Sterling-Angiuli
   2021).  Estimated dependent on K13 being shipped.

For now, the standalone `Term.rename_injective_snd_ctor` family
suffices for any consumer that has both pairs at the same sigmaTy.
The arm-helper architecture's per-ctor coverage of these three ctors
is deferred. -/

end LeanFX2
