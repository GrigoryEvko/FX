import LeanFX2.Term.StrengtheningImage.ImageCore
import LeanFX2.Term.StrengtheningImage.RenameImageCastWrapped

/-! # Term/StrengtheningImage/ImageUnweaken

Unweaken/image equivalence corollaries and weaken-inversion specializations.
-/

namespace LeanFX2

namespace Term

/-- Image Step 2 — `unweaken?` and `strengthenTyped?` agree on success.

TAUTOLOGICAL BIJECTION: `Term.unweaken?` is defined to pattern-match on
`strengthenTyped?` and return `none` in the `none` branch.  Both
witnesses therefore succeed under identical conditions; this theorem
packages the equivalence as a one-line corollary and reveals no new
totality information.

If `Term.unweaken? weakenedTerm` returned `some originalTerm`, the
underlying `strengthenTyped?` dispatcher returned `some result`.  The
proof is case analysis on `strengthenTyped? weakenedTerm`: the `none`
branch makes `unweaken?` return `none`, contradicting the success
hypothesis. -/
theorem strengthenTyped?_some_of_unweaken?_some {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType sourceType : Ty level scope}
    {sourceRaw : RawTerm scope}
    {weakenedTerm :
      Term (context.cons newType) sourceType.weaken sourceRaw.weaken}
    {originalTerm : Term context sourceType sourceRaw}
    (unweakSuccess : Term.unweaken? weakenedTerm = some originalTerm) :
    ∃ result, strengthenTyped? weakenedTerm = some result := by
  cases dispatchOutcome : strengthenTyped? weakenedTerm with
  | none =>
      exfalso
      have noneEq : Term.unweaken? weakenedTerm = none := by
        show (match strengthenTyped? weakenedTerm with
              | none => none
              | some result => _) = none
        rw [dispatchOutcome]
      rw [noneEq] at unweakSuccess
      cases unweakSuccess
  | some result =>
      exact ⟨result, rfl⟩

/-- Generic conditional weakening inversion from an `unweaken?` success.

This is the type-generic core behind the per-type `weaken_inv_*`
specializations: it does not claim unconditional totality of
strengthening, but once `Term.unweaken?` has recovered an original term,
the weakened term is heterogeneously equal to weakening that original
term back into the extended context. -/
theorem weaken_inv_of_unweaken?_some {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType sourceType : Ty level scope}
    {sourceRaw : RawTerm scope}
    (weakenedTerm :
      Term (context.cons newType) sourceType.weaken sourceRaw.weaken)
    {originalTerm : Term context sourceType sourceRaw}
    (unweakenSuccess :
      Term.unweaken? weakenedTerm = some originalTerm) :
    HEq weakenedTerm (Term.weaken newType originalTerm) := by
  cases dispatchOutcome : strengthenTyped? weakenedTerm with
  | none =>
      exfalso
      have noneEq : Term.unweaken? weakenedTerm = none := by
        unfold Term.unweaken?
        rw [dispatchOutcome]
      rw [noneEq] at unweakenSuccess
      cases unweakenSuccess
  | some dispatchResult =>
      have soundness :
          HEq weakenedTerm dispatchResult.renamedTarget :=
        weaken_inv_of_strengthenTyped?_some
          (ContextStrengthening.dropNewest context newType)
          dispatchResult dispatchOutcome
      cases dispatchResult with
      | mk targetType targetRaw targetTerm typeStrengthens rawStrengthens
            typeRenames rawRenames =>
          have targetTypeEq : targetType = sourceType := by
            have rewritten : sourceType.weaken.strengthen? = some targetType :=
              typeStrengthens
            rw [Ty.strengthen?_weaken sourceType] at rewritten
            injection rewritten with strengthenSomeEq
            exact strengthenSomeEq.symm
          have targetRawEq : targetRaw = sourceRaw := by
            have rewritten : sourceRaw.weaken.strengthen? = some targetRaw :=
              rawStrengthens
            rw [RawTerm.strengthen?_weaken sourceRaw] at rewritten
            injection rewritten with strengthenSomeEq
            exact strengthenSomeEq.symm
          subst targetTypeEq
          subst targetRawEq
          have unfoldEq : Term.unweaken? weakenedTerm = some targetTerm := by
            unfold Term.unweaken?
            rw [dispatchOutcome]
          rw [unfoldEq] at unweakenSuccess
          injection unweakenSuccess with targetTermInj
          subst targetTermInj
          exact soundness

/-- Closed-type specialization of `weaken_inv_of_unweaken?_some` for unit. -/
theorem weaken_inv_unit {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType : Ty level scope}
    {sourceRaw : RawTerm scope}
    (weakenedTerm :
      Term (context.cons newType) Ty.unit.weaken sourceRaw.weaken)
    {originalTerm : Term context Ty.unit sourceRaw}
    (unweakenSuccess : Term.unweaken? weakenedTerm = some originalTerm) :
    HEq weakenedTerm (Term.weaken newType originalTerm) :=
  weaken_inv_of_unweaken?_some weakenedTerm unweakenSuccess

/-- Closed-type specialization of `weaken_inv_of_unweaken?_some` for bool. -/
theorem weaken_inv_bool {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType : Ty level scope}
    {sourceRaw : RawTerm scope}
    (weakenedTerm :
      Term (context.cons newType) Ty.bool.weaken sourceRaw.weaken)
    {originalTerm : Term context Ty.bool sourceRaw}
    (unweakenSuccess : Term.unweaken? weakenedTerm = some originalTerm) :
    HEq weakenedTerm (Term.weaken newType originalTerm) :=
  weaken_inv_of_unweaken?_some weakenedTerm unweakenSuccess

/-- Closed-type specialization of `weaken_inv_of_unweaken?_some` for nat. -/
theorem weaken_inv_nat {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType : Ty level scope}
    {sourceRaw : RawTerm scope}
    (weakenedTerm :
      Term (context.cons newType) Ty.nat.weaken sourceRaw.weaken)
    {originalTerm : Term context Ty.nat sourceRaw}
    (unweakenSuccess : Term.unweaken? weakenedTerm = some originalTerm) :
    HEq weakenedTerm (Term.weaken newType originalTerm) :=
  weaken_inv_of_unweaken?_some weakenedTerm unweakenSuccess

/-- Closed-type specialization of `weaken_inv_of_unweaken?_some` for empty. -/
theorem weaken_inv_empty {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType : Ty level scope}
    {sourceRaw : RawTerm scope}
    (weakenedTerm :
      Term (context.cons newType) Ty.empty.weaken sourceRaw.weaken)
    {originalTerm : Term context Ty.empty sourceRaw}
    (unweakenSuccess : Term.unweaken? weakenedTerm = some originalTerm) :
    HEq weakenedTerm (Term.weaken newType originalTerm) :=
  weaken_inv_of_unweaken?_some weakenedTerm unweakenSuccess

/-- Closed-type specialization of `weaken_inv_of_unweaken?_some` for interval. -/
theorem weaken_inv_interval {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType : Ty level scope}
    {sourceRaw : RawTerm scope}
    (weakenedTerm :
      Term (context.cons newType) Ty.interval.weaken sourceRaw.weaken)
    {originalTerm : Term context Ty.interval sourceRaw}
    (unweakenSuccess : Term.unweaken? weakenedTerm = some originalTerm) :
    HEq weakenedTerm (Term.weaken newType originalTerm) :=
  weaken_inv_of_unweaken?_some weakenedTerm unweakenSuccess

/-- Closed-type specialization of `weaken_inv_of_unweaken?_some` for universes. -/
theorem weaken_inv_universe {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType : Ty level scope}
    (universeLevel : UniverseLevel)
    (levelLe : universeLevel.toNat + 1 ≤ level)
    {sourceRaw : RawTerm scope}
    (weakenedTerm :
      Term (context.cons newType)
        (Ty.universe universeLevel levelLe).weaken sourceRaw.weaken)
    {originalTerm : Term context (Ty.universe universeLevel levelLe) sourceRaw}
    (unweakenSuccess : Term.unweaken? weakenedTerm = some originalTerm) :
    HEq weakenedTerm (Term.weaken newType originalTerm) :=
  weaken_inv_of_unweaken?_some weakenedTerm unweakenSuccess

/-- Binder-type specialization of `weaken_inv_of_unweaken?_some` for Pi. -/
theorem weaken_inv_pi {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType domainType : Ty level scope}
    {codomainType : Ty level (scope + 1)}
    {sourceRaw : RawTerm scope}
    (weakenedTerm :
      Term (context.cons newType)
        (Ty.piTy domainType codomainType).weaken sourceRaw.weaken)
    {originalTerm : Term context (Ty.piTy domainType codomainType) sourceRaw}
    (unweakenSuccess : Term.unweaken? weakenedTerm = some originalTerm) :
    HEq weakenedTerm (Term.weaken newType originalTerm) :=
  weaken_inv_of_unweaken?_some weakenedTerm unweakenSuccess

/-- Binder-type specialization of `weaken_inv_of_unweaken?_some` for Sigma. -/
theorem weaken_inv_sigma {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    {sourceRaw : RawTerm scope}
    (weakenedTerm :
      Term (context.cons newType)
        (Ty.sigmaTy firstType secondType).weaken sourceRaw.weaken)
    {originalTerm : Term context (Ty.sigmaTy firstType secondType) sourceRaw}
    (unweakenSuccess : Term.unweaken? weakenedTerm = some originalTerm) :
    HEq weakenedTerm (Term.weaken newType originalTerm) :=
  weaken_inv_of_unweaken?_some weakenedTerm unweakenSuccess

/-- Binder-family specialization of `weaken_inv_of_unweaken?_some` for Path. -/
theorem weaken_inv_path {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType carrierType : Ty level scope}
    {leftEndpoint rightEndpoint sourceRaw : RawTerm scope}
    (weakenedTerm :
      Term (context.cons newType)
        (Ty.path carrierType leftEndpoint rightEndpoint).weaken
        sourceRaw.weaken)
    {originalTerm :
      Term context (Ty.path carrierType leftEndpoint rightEndpoint) sourceRaw}
    (unweakenSuccess : Term.unweaken? weakenedTerm = some originalTerm) :
    HEq weakenedTerm (Term.weaken newType originalTerm) :=
  weaken_inv_of_unweaken?_some weakenedTerm unweakenSuccess

/-- Binder-family specialization of `weaken_inv_of_unweaken?_some` for refine. -/
theorem weaken_inv_refine {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType baseType : Ty level scope}
    {predicate : RawTerm (scope + 1)}
    {sourceRaw : RawTerm scope}
    (weakenedTerm :
      Term (context.cons newType)
        (Ty.refine baseType predicate).weaken sourceRaw.weaken)
    {originalTerm : Term context (Ty.refine baseType predicate) sourceRaw}
    (unweakenSuccess : Term.unweaken? weakenedTerm = some originalTerm) :
    HEq weakenedTerm (Term.weaken newType originalTerm) :=
  weaken_inv_of_unweaken?_some weakenedTerm unweakenSuccess

/-- Type-variable specialization of `weaken_inv_of_unweaken?_some`. -/
theorem weaken_inv_tyVar {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType : Ty level scope}
    {position : Fin scope}
    {sourceRaw : RawTerm scope}
    (weakenedTerm :
      Term (context.cons newType) (Ty.tyVar position).weaken sourceRaw.weaken)
    {originalTerm : Term context (Ty.tyVar position) sourceRaw}
    (unweakenSuccess : Term.unweaken? weakenedTerm = some originalTerm) :
    HEq weakenedTerm (Term.weaken newType originalTerm) :=
  weaken_inv_of_unweaken?_some weakenedTerm unweakenSuccess

/-- Parametric-type specialization of `weaken_inv_of_unweaken?_some` for lists. -/
theorem weaken_inv_listType {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType elementType : Ty level scope}
    {sourceRaw : RawTerm scope}
    (weakenedTerm :
      Term (context.cons newType) (Ty.listType elementType).weaken sourceRaw.weaken)
    {originalTerm : Term context (Ty.listType elementType) sourceRaw}
    (unweakenSuccess : Term.unweaken? weakenedTerm = some originalTerm) :
    HEq weakenedTerm (Term.weaken newType originalTerm) :=
  weaken_inv_of_unweaken?_some weakenedTerm unweakenSuccess

/-- Parametric-type specialization of `weaken_inv_of_unweaken?_some` for options. -/
theorem weaken_inv_optionType {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType elementType : Ty level scope}
    {sourceRaw : RawTerm scope}
    (weakenedTerm :
      Term (context.cons newType)
        (Ty.optionType elementType).weaken sourceRaw.weaken)
    {originalTerm : Term context (Ty.optionType elementType) sourceRaw}
    (unweakenSuccess : Term.unweaken? weakenedTerm = some originalTerm) :
    HEq weakenedTerm (Term.weaken newType originalTerm) :=
  weaken_inv_of_unweaken?_some weakenedTerm unweakenSuccess

/-- Parametric-type specialization of `weaken_inv_of_unweaken?_some` for either. -/
theorem weaken_inv_eitherType {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType leftType rightType : Ty level scope}
    {sourceRaw : RawTerm scope}
    (weakenedTerm :
      Term (context.cons newType)
        (Ty.eitherType leftType rightType).weaken sourceRaw.weaken)
    {originalTerm : Term context (Ty.eitherType leftType rightType) sourceRaw}
    (unweakenSuccess : Term.unweaken? weakenedTerm = some originalTerm) :
    HEq weakenedTerm (Term.weaken newType originalTerm) :=
  weaken_inv_of_unweaken?_some weakenedTerm unweakenSuccess

/-- Identity-type specialization of `weaken_inv_of_unweaken?_some`. -/
theorem weaken_inv_id {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType carrierType : Ty level scope}
    {leftEndpoint rightEndpoint sourceRaw : RawTerm scope}
    (weakenedTerm :
      Term (context.cons newType)
        (Ty.id carrierType leftEndpoint rightEndpoint).weaken
        sourceRaw.weaken)
    {originalTerm :
      Term context (Ty.id carrierType leftEndpoint rightEndpoint) sourceRaw}
    (unweakenSuccess : Term.unweaken? weakenedTerm = some originalTerm) :
    HEq weakenedTerm (Term.weaken newType originalTerm) :=
  weaken_inv_of_unweaken?_some weakenedTerm unweakenSuccess

/-- Observational-equality specialization of `weaken_inv_of_unweaken?_some`. -/
theorem weaken_inv_oeq {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType carrierType : Ty level scope}
    {leftEndpoint rightEndpoint sourceRaw : RawTerm scope}
    (weakenedTerm :
      Term (context.cons newType)
        (Ty.oeq carrierType leftEndpoint rightEndpoint).weaken
        sourceRaw.weaken)
    {originalTerm :
      Term context (Ty.oeq carrierType leftEndpoint rightEndpoint) sourceRaw}
    (unweakenSuccess : Term.unweaken? weakenedTerm = some originalTerm) :
    HEq weakenedTerm (Term.weaken newType originalTerm) :=
  weaken_inv_of_unweaken?_some weakenedTerm unweakenSuccess

/-- Strict-identity specialization of `weaken_inv_of_unweaken?_some`. -/
theorem weaken_inv_idStrict {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType carrierType : Ty level scope}
    {leftEndpoint rightEndpoint sourceRaw : RawTerm scope}
    (weakenedTerm :
      Term (context.cons newType)
        (Ty.idStrict carrierType leftEndpoint rightEndpoint).weaken
        sourceRaw.weaken)
    {originalTerm :
      Term context (Ty.idStrict carrierType leftEndpoint rightEndpoint) sourceRaw}
    (unweakenSuccess : Term.unweaken? weakenedTerm = some originalTerm) :
    HEq weakenedTerm (Term.weaken newType originalTerm) :=
  weaken_inv_of_unweaken?_some weakenedTerm unweakenSuccess

/-- Equivalence-type specialization of `weaken_inv_of_unweaken?_some`. -/
theorem weaken_inv_equiv {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType domainType codomainType : Ty level scope}
    {sourceRaw : RawTerm scope}
    (weakenedTerm :
      Term (context.cons newType)
        (Ty.equiv domainType codomainType).weaken sourceRaw.weaken)
    {originalTerm : Term context (Ty.equiv domainType codomainType) sourceRaw}
    (unweakenSuccess : Term.unweaken? weakenedTerm = some originalTerm) :
    HEq weakenedTerm (Term.weaken newType originalTerm) :=
  weaken_inv_of_unweaken?_some weakenedTerm unweakenSuccess

/-- Cubical glue specialization of `weaken_inv_of_unweaken?_some`. -/
theorem weaken_inv_glue {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType baseType : Ty level scope}
    {boundaryWitness sourceRaw : RawTerm scope}
    (weakenedTerm :
      Term (context.cons newType)
        (Ty.glue baseType boundaryWitness).weaken sourceRaw.weaken)
    {originalTerm : Term context (Ty.glue baseType boundaryWitness) sourceRaw}
    (unweakenSuccess : Term.unweaken? weakenedTerm = some originalTerm) :
    HEq weakenedTerm (Term.weaken newType originalTerm) :=
  weaken_inv_of_unweaken?_some weakenedTerm unweakenSuccess

/-- Record-type specialization of `weaken_inv_of_unweaken?_some`. -/
theorem weaken_inv_record {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType singleFieldType : Ty level scope}
    {sourceRaw : RawTerm scope}
    (weakenedTerm :
      Term (context.cons newType)
        (Ty.record singleFieldType).weaken sourceRaw.weaken)
    {originalTerm : Term context (Ty.record singleFieldType) sourceRaw}
    (unweakenSuccess : Term.unweaken? weakenedTerm = some originalTerm) :
    HEq weakenedTerm (Term.weaken newType originalTerm) :=
  weaken_inv_of_unweaken?_some weakenedTerm unweakenSuccess

/-- Codata-type specialization of `weaken_inv_of_unweaken?_some`. -/
theorem weaken_inv_codata {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType stateType outputType : Ty level scope}
    {sourceRaw : RawTerm scope}
    (weakenedTerm :
      Term (context.cons newType)
        (Ty.codata stateType outputType).weaken sourceRaw.weaken)
    {originalTerm : Term context (Ty.codata stateType outputType) sourceRaw}
    (unweakenSuccess : Term.unweaken? weakenedTerm = some originalTerm) :
    HEq weakenedTerm (Term.weaken newType originalTerm) :=
  weaken_inv_of_unweaken?_some weakenedTerm unweakenSuccess

/-- Session-type specialization of `weaken_inv_of_unweaken?_some`. -/
theorem weaken_inv_session {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType : Ty level scope}
    {protocolStep sourceRaw : RawTerm scope}
    (weakenedTerm :
      Term (context.cons newType)
        (Ty.session protocolStep).weaken sourceRaw.weaken)
    {originalTerm : Term context (Ty.session protocolStep) sourceRaw}
    (unweakenSuccess : Term.unweaken? weakenedTerm = some originalTerm) :
    HEq weakenedTerm (Term.weaken newType originalTerm) :=
  weaken_inv_of_unweaken?_some weakenedTerm unweakenSuccess

/-- Effect-type specialization of `weaken_inv_of_unweaken?_some`. -/
theorem weaken_inv_effect {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType carrierType : Ty level scope}
    {effectTag sourceRaw : RawTerm scope}
    (weakenedTerm :
      Term (context.cons newType)
        (Ty.effect carrierType effectTag).weaken sourceRaw.weaken)
    {originalTerm : Term context (Ty.effect carrierType effectTag) sourceRaw}
    (unweakenSuccess : Term.unweaken? weakenedTerm = some originalTerm) :
    HEq weakenedTerm (Term.weaken newType originalTerm) :=
  weaken_inv_of_unweaken?_some weakenedTerm unweakenSuccess

/-- Modal-type specialization of `weaken_inv_of_unweaken?_some`. -/
theorem weaken_inv_modal {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType carrierType : Ty level scope}
    {modalityTag : Nat}
    {sourceRaw : RawTerm scope}
    (weakenedTerm :
      Term (context.cons newType)
        (Ty.modal modalityTag carrierType).weaken sourceRaw.weaken)
    {originalTerm : Term context (Ty.modal modalityTag carrierType) sourceRaw}
    (unweakenSuccess : Term.unweaken? weakenedTerm = some originalTerm) :
    HEq weakenedTerm (Term.weaken newType originalTerm) :=
  weaken_inv_of_unweaken?_some weakenedTerm unweakenSuccess

/-- Image Step 3 — headline iff between `unweaken?` success and
`strengthenTyped?` success.

TAUTOLOGICAL BIJECTION: both directions are structural corollaries of
`Term.unweaken?`'s definition (it pattern-matches on `strengthenTyped?`
and returns `none` exactly when `strengthenTyped?` does).  The iff
therefore reveals no new totality content — both witnesses succeed
under identical conditions, and the headline just packages that.

For a typed term whose indices are syntactic weakenings (the canonical
input shape consumed by the typed η-redesign + Phase B+ Step.eta SR
cascade), `Term.unweaken?` recovers an original-context term IFF the
underlying `strengthenTyped?` dispatcher produces a
`StrengtheningResult`.

NOTE: unconditional totality on the weakening image — i.e., `∀
originalTerm, strengthenTyped? (Term.weaken nt originalTerm) = some _`
— is a STRONGER theorem requiring a 78-case structural induction at the
typed Term layer (parallel to `Ty.partialStrengthen?_rename_some` and
`RawTerm.partialStrengthen?_rename_some`).  The structural induction
unifies the dispatcher pattern matches with the index-level
strengthen-of-weaken lemmas across every ctor with binder-lift
threading; tracked as a follow-up after this iff packaging lands. -/
theorem weaken_image_iff_strengthenTyped?_some {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType sourceType : Ty level scope}
    {sourceRaw : RawTerm scope}
    (weakenedTerm :
      Term (context.cons newType) sourceType.weaken sourceRaw.weaken) :
    (∃ originalTerm, Term.unweaken? weakenedTerm = some originalTerm) ↔
      ∃ result, strengthenTyped? weakenedTerm = some result := by
  refine ⟨fun forwardHypothesis => ?_, fun backwardHypothesis => ?_⟩
  · obtain ⟨_, unweakSuccess⟩ := forwardHypothesis
    exact strengthenTyped?_some_of_unweaken?_some unweakSuccess
  · obtain ⟨result, dispatchSuccess⟩ := backwardHypothesis
    cases result with
    | mk targetType targetRaw targetTerm typeStrengthens rawStrengthens _ _ =>
        have targetTypeEq : targetType = sourceType := by
          have hh : sourceType.weaken.strengthen? = some targetType :=
            typeStrengthens
          rw [Ty.strengthen?_weaken] at hh
          cases hh
          rfl
        have targetRawEq : targetRaw = sourceRaw := by
          have hh : sourceRaw.weaken.strengthen? = some targetRaw :=
            rawStrengthens
          rw [RawTerm.strengthen?_weaken] at hh
          cases hh
          rfl
        cases targetTypeEq
        cases targetRawEq
        refine ⟨targetTerm, ?_⟩
        show (match strengthenTyped? weakenedTerm with
              | none => none
              | some result => _) = some targetTerm
        rw [dispatchSuccess]

/-! ## `Term.weaken_inv_arrow` — conditional existence form (Phase A close-out)

The full existence-form companion to
`Term.weaken_inv_arrow_option` (Term/TypedInversion.lean).  Packages
the soundness component of `Term.unweaken?` as an existence-form
theorem: given a weakened arrow-typed term `weakenedFn` together with
an `unweaken?`-success witness producing the original `originalFn`,
the weakened term IS heterogeneously equal to `Term.weaken newType
originalFn`.

### Architecture rationale

The Step.eta plan's spec sketches an unconditional existence form `∀
arrowTerm, ∃ origArrowTerm, arrowTerm = origArrowTerm.weaken newType`,
but that is architecturally unshippable under the current
strengthening predicate (per Phase Y close-out commit `bdd613ec`): 25
of 78 Term constructors carry sub-types whose strengthening witness
is not recoverable from the source type's structure, so a universal
`IsAggregatorTotal` headline is impossible.

The conditional existence form below threads soundness through the
already-shipped image theorem
`weaken_inv_of_strengthenTyped?_some`, extracting the canonical
`HEq weakenedFn (Term.weaken newType originalFn)` from a
`Term.unweaken?` success.  Consumers (Phase B `lift_lam`
eta-disjunct) supply the `unweaken?` success themselves from their
own structural information about the typed app shape's function
side.

### Mechanical content

1. From `Term.unweaken? weakenedFn = some originalFn` infer
   `strengthenTyped? weakenedFn = some result` for some result
   with `result.targetTerm = originalFn` (after the indices are
   cast through `Ty.strengthen?_weaken` / `RawTerm.strengthen?_weaken`).
2. Apply `weaken_inv_of_strengthenTyped?_some` to get
   `HEq weakenedFn result.renamedTarget`.
3. Observe that `renamedTarget` is `Term.rename
   strengthening.toTermRenaming result.targetTerm`, and for
   `strengthening = dropNewest`, `toTermRenaming =
   TermRenaming.weakenStep` by `rfl`
   (`ContextStrengthening.dropNewest_toTermRenaming`).
4. Conclude `HEq weakenedFn (Term.weaken newType originalFn)` via
   the `@[reducible]` definition of `Term.weaken`.

### Phase B usage

The `lift_lam` η-disjunct receives an eta-shaped raw step `RawStep.
par (RawTerm.lam (RawTerm.app fnRaw.weaken (RawTerm.var 0)))
targetRaw`.  The typed body decomposes via `app_inv` into a function
term `fnTerm` at type `(Ty.arrow domainType codomainType).weaken`
over raw `fnRaw.weaken`.  Phase B will call `Term.unweaken?` on
`fnTerm`, refuting the `none` case via the structural reasoning that
the η raw shape forces, then invoke this theorem to obtain the typed
`origFn` plus the soundness HEq. -/

/-- **Conditional existence-form weaken inversion at arrow type.**

Given an arrow-typed weakened function term plus an `unweaken?`
success witness producing the original function term, conclude that
the weakened term is heterogeneously equal to the canonical
`Term.weaken newType originalFn`.

The `HEq` rather than `Eq` is necessary because the two sides have
indices

* `weakenedFn` : `Term (context.cons newType) (Ty.arrow domainType
  codomainType).weaken fnRaw.weaken`
* `Term.weaken newType originalFn` : same indices definitionally

but the indices are computed through different paths (the
`@[reducible]` `Term.weaken` wrapper vs the raw renaming path
inside `renamedTarget`).  `HEq` accepts the propositional-equal
indices uniformly. -/
theorem weaken_inv_arrow {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType : Ty level scope}
    {domainType codomainType : Ty level scope}
    {fnRaw : RawTerm scope}
    (weakenedFn :
      Term (context.cons newType)
           (Ty.arrow domainType codomainType).weaken
           fnRaw.weaken)
    {originalFn : Term context (Ty.arrow domainType codomainType) fnRaw}
    (unweakenSuccess :
      Term.unweaken? weakenedFn = some originalFn) :
    HEq weakenedFn (Term.weaken newType originalFn) :=
  weaken_inv_of_unweaken?_some weakenedFn unweakenSuccess

end Term

end LeanFX2
