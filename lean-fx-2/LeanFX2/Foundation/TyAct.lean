import LeanFX2.Foundation.SubstActsOnTy

/-! # TyAct — Tier 3 / MEGA-Z2.6 — Native Ty.act-layer infrastructure.

This file ships three native theorems for `Ty.act`, proved WITHOUT
routing through `Ty.subst_compose` or `Ty.subst_pointwise`.  These are
the foundation for MEGA-Z2.5 (break the `Subst.compose ↔ Ty.subst`
cycle) and MEGA-Z3 (drop the legacy commute ladder).

## Architectural commitment

`Subst.compose`'s `forTy` field is `(sigma1.forTy pos).subst sigma2`.
`Subst.compose_assoc_pointwise` (Action instance law) currently
appeals to `Ty.subst_compose`, which itself proves itself via
`Ty.subst_pointwise`.  Z3 plans to retire the `Ty.subst_*` ladder, so
the ultimate witness MUST NOT route through them.  The native
`Ty.act_*` theorems below are stated and proved on the `Ty.act`
recursion engine directly, with NO call to `Ty.subst_compose` or
`Ty.subst_pointwise`.

## The three theorems

* `Ty.act_pointwise`  — extensionality.  Two actions of (possibly)
  different Containers produce equal results when they agree pointwise
  on `varToTy` and on `actOnRawTerm`, with the property propagating
  under binder lifts.

* `Ty.act_compose`    — multi-Container composition.  Three Containers
  (`first`, `second`, `composed`) plus a paired-action compatibility
  predicate that says "`composed` acts like `first` then `second`".

* `Ty.act_identity`   — when an action acts as identity (varToTy =
  tyVar, actOnRawTerm = id, propagated under lifts), `Ty.act t action
  = t`.

## Proof structure

Each theorem is a 25-case structural induction on `Ty level scope`.
Every arm uses ONLY `simp only [Ty.act]` with EXPLICIT lemma list (no
bare `simp`), the corresponding compatibility witness for raw payloads,
and IHs for recursive arms.  Specifically NO appeal to
`Ty.subst_compose`, `Ty.subst_pointwise`, or any function in
`Foundation/Subst.lean` after `Ty.subst`'s body.

## Hypothesis bundling

Each theorem packs its hypotheses as a `structure` parametric in
`scope`, allowing the binder arms to invoke the same predicate at the
lifted scope (`scope + 1`).  The consumer supplies a single instance
that is closed under `liftForTy`/`liftForRaw`.

## Audit

`Smoke/AuditMegaZ26.lean` runs `#print axioms` on every declaration in
this file.  All zero-axiom under strict policy.

## Wave

Tier 3 / MEGA-Z2.6.
-/

namespace LeanFX2

/-! ## Section 1 — `Ty.act_pointwise`.

Two actions of (possibly different) Containers agree on `Ty.act` when
they agree pointwise on the var-lookup and the raw-action operations,
and the same property survives a binder lift.  The hypothesis bundle
is universal in `scope` so the binder arms can reapply at `scope + 1`.

This is the multi-Container version of the textbook "extensionality of
the action" — supplying it without raw Container equalities means
function-typed Containers (like RawRenaming) work uniformly with
record-typed Containers (like Subst).
-/

/-- Predicate: two actions on (possibly different) Containers produce
the same effect on every `Ty.act` arm.  The predicate must hold at
every scope so the binder arms can re-invoke it under `liftForTy` /
`liftForRaw`.

The two pointwise components:
* `varAgree`: `varToTy actA pos = varToTy actB pos` for all positions
* `rawAgree`: `actOnRawTerm actA raw = actOnRawTerm actB raw` for all
  raw subterms
-/
structure ActPointwiseAgree
    (ContainerA ContainerB : Nat → Nat → Type)
    [ActsOnRawTerm ContainerA] [ActsOnRawTerm ContainerB]
    (level : Nat)
    [ActsOnTyVar ContainerA level]
    [ActsOnTyVar ContainerB level]
    (sourceScope targetScope : Nat)
    (actA : ContainerA sourceScope targetScope)
    (actB : ContainerB sourceScope targetScope) : Prop where
  /-- Var-lookup agrees pointwise. -/
  varAgree : ∀ (position : Fin sourceScope),
      (ActsOnTyVar.varToTy actA position : Ty level targetScope) =
        ActsOnTyVar.varToTy actB position
  /-- Raw-action agrees on every raw term. -/
  rawAgree : ∀ (rawTerm : RawTerm sourceScope),
      ActsOnRawTerm.actOnRawTerm actA rawTerm =
        ActsOnRawTerm.actOnRawTerm actB rawTerm

/-- Native pointwise extensionality for `Ty.act`.

If two actions (on possibly distinct Containers) agree pointwise on
`varToTy` and `actOnRawTerm`, AND the agreement survives a binder lift
in both `liftForTy` and `liftForRaw` directions, then `Ty.act` produces
the same result with either action.

The hypothesis is delivered as a function `mkAgree` that, given an
existing agreement at some scope, produces an agreement under the
lifts.  This is how Allais et al. ICFP'18 thread extensionality
through binders without raw Container equalities.

Proof: 25-case structural induction on `Ty level sourceScope`. -/
theorem Ty.act_pointwise
    {ContainerA ContainerB : Nat → Nat → Type}
    [Action ContainerA] [Action ContainerB]
    [ActsOnRawTerm ContainerA] [ActsOnRawTerm ContainerB]
    {level : Nat}
    [ActsOnTyVar ContainerA level] [ActsOnTyVar ContainerB level]
    (mkLiftForTy : ∀ {sourceScope targetScope : Nat}
        {actA : ContainerA sourceScope targetScope}
        {actB : ContainerB sourceScope targetScope},
        ActPointwiseAgree ContainerA ContainerB level
            sourceScope targetScope actA actB →
        ActPointwiseAgree ContainerA ContainerB level
            (sourceScope + 1) (targetScope + 1)
            (Action.liftForTy actA) (Action.liftForTy actB))
    (mkLiftForRaw : ∀ {sourceScope targetScope : Nat}
        {actA : ContainerA sourceScope targetScope}
        {actB : ContainerB sourceScope targetScope},
        ActPointwiseAgree ContainerA ContainerB level
            sourceScope targetScope actA actB →
        ActPointwiseAgree ContainerA ContainerB level
            (sourceScope + 1) (targetScope + 1)
            (Action.liftForRaw actA) (Action.liftForRaw actB)) :
    ∀ {sourceScope targetScope : Nat}
      (someTy : Ty level sourceScope)
      {actA : ContainerA sourceScope targetScope}
      {actB : ContainerB sourceScope targetScope}
      (agreeWitness : ActPointwiseAgree ContainerA ContainerB level
          sourceScope targetScope actA actB),
      Ty.act someTy actA = Ty.act someTy actB := by
  intro sourceScope targetScope someTy
  induction someTy generalizing targetScope with
  | unit => intros; rfl
  | bool => intros; rfl
  | nat  => intros; rfl
  | arrow domainType codomainType domainIH codomainIH =>
      intro actA actB agreeWitness
      simp only [Ty.act]
      rw [domainIH agreeWitness, codomainIH agreeWitness]
  | piTy domainType codomainType domainIH codomainIH =>
      intro actA actB agreeWitness
      simp only [Ty.act]
      rw [domainIH agreeWitness, codomainIH (mkLiftForTy agreeWitness)]
  | sigmaTy firstType secondType firstIH secondIH =>
      intro actA actB agreeWitness
      simp only [Ty.act]
      rw [firstIH agreeWitness, secondIH (mkLiftForTy agreeWitness)]
  | tyVar position =>
      intro actA actB agreeWitness
      simp only [Ty.act]
      exact agreeWitness.varAgree position
  | id carrier leftEndpoint rightEndpoint carrierIH =>
      intro actA actB agreeWitness
      simp only [Ty.act]
      rw [carrierIH agreeWitness,
          agreeWitness.rawAgree leftEndpoint,
          agreeWitness.rawAgree rightEndpoint]
  | listType elementType elementIH =>
      intro actA actB agreeWitness
      simp only [Ty.act]
      rw [elementIH agreeWitness]
  | optionType elementType elementIH =>
      intro actA actB agreeWitness
      simp only [Ty.act]
      rw [elementIH agreeWitness]
  | eitherType leftType rightType leftIH rightIH =>
      intro actA actB agreeWitness
      simp only [Ty.act]
      rw [leftIH agreeWitness, rightIH agreeWitness]
  | «universe» universeLevel levelLe => intros; rfl
  | empty => intros; rfl
  | interval => intros; rfl
  | path carrier leftEndpoint rightEndpoint carrierIH =>
      intro actA actB agreeWitness
      simp only [Ty.act]
      rw [carrierIH agreeWitness,
          agreeWitness.rawAgree leftEndpoint,
          agreeWitness.rawAgree rightEndpoint]
  | glue baseType boundaryWitness baseIH =>
      intro actA actB agreeWitness
      simp only [Ty.act]
      rw [baseIH agreeWitness, agreeWitness.rawAgree boundaryWitness]
  | oeq carrier leftEndpoint rightEndpoint carrierIH =>
      intro actA actB agreeWitness
      simp only [Ty.act]
      rw [carrierIH agreeWitness,
          agreeWitness.rawAgree leftEndpoint,
          agreeWitness.rawAgree rightEndpoint]
  | idStrict carrier leftEndpoint rightEndpoint carrierIH =>
      intro actA actB agreeWitness
      simp only [Ty.act]
      rw [carrierIH agreeWitness,
          agreeWitness.rawAgree leftEndpoint,
          agreeWitness.rawAgree rightEndpoint]
  | equiv domainType codomainType domainIH codomainIH =>
      intro actA actB agreeWitness
      simp only [Ty.act]
      rw [domainIH agreeWitness, codomainIH agreeWitness]
  | refine baseType predicate baseIH =>
      intro actA actB agreeWitness
      simp only [Ty.act]
      rw [baseIH agreeWitness,
          (mkLiftForRaw agreeWitness).rawAgree predicate]
  | record singleFieldType singleFieldIH =>
      intro actA actB agreeWitness
      simp only [Ty.act]
      rw [singleFieldIH agreeWitness]
  | codata stateType outputType stateIH outputIH =>
      intro actA actB agreeWitness
      simp only [Ty.act]
      rw [stateIH agreeWitness, outputIH agreeWitness]
  | session protocolStep =>
      intro actA actB agreeWitness
      simp only [Ty.act]
      rw [agreeWitness.rawAgree protocolStep]
  | effect carrierType effectTag carrierIH =>
      intro actA actB agreeWitness
      simp only [Ty.act]
      rw [carrierIH agreeWitness, agreeWitness.rawAgree effectTag]
  | modal modalityTag carrierType carrierIH =>
      intro actA actB agreeWitness
      simp only [Ty.act]
      rw [carrierIH agreeWitness]

/-! ## Section 2 — `Ty.act_compose`.

Three Containers (`first`, `second`, `composed`) plus compatibility
witnesses describing how the composed action mimics applying first
then second.  Witnesses are universally quantified over scope so the
binder arms can reapply at `scope + 1` after a lift.

Per the brief, this is the "multi-Container" formulation.  It does
NOT depend on `Action.compose` directly; it admits any external
"composed" Container as long as the consumer ships compatibility
witnesses.  This avoids the `Subst.compose ↔ Ty.subst` cycle.
-/

/-- Predicate: an action `composed` mimics applying `first` then
`second` on the var-lookup and raw-action level.  The composed
container's effect at every Fin position equals the second container
acting on the first container's lookup; same for raw subterms. -/
structure ActComposeCompat
    (ContainerFirst ContainerSecond ContainerComposed : Nat → Nat → Type)
    [Action ContainerFirst] [Action ContainerSecond] [Action ContainerComposed]
    [ActsOnRawTerm ContainerFirst] [ActsOnRawTerm ContainerSecond]
    [ActsOnRawTerm ContainerComposed]
    (level : Nat)
    [ActsOnTyVar ContainerFirst level] [ActsOnTyVar ContainerSecond level]
    [ActsOnTyVar ContainerComposed level]
    (sourceScope middleScope targetScope : Nat)
    (firstAction : ContainerFirst sourceScope middleScope)
    (secondAction : ContainerSecond middleScope targetScope)
    (composedAction : ContainerComposed sourceScope targetScope) : Prop where
  /-- The composed action's var-lookup at any position equals the
  result of applying second-action's `Ty.act` to first-action's
  var-lookup. -/
  varCompat : ∀ (position : Fin sourceScope),
      (ActsOnTyVar.varToTy composedAction position : Ty level targetScope) =
        Ty.act (ActsOnTyVar.varToTy firstAction position : Ty level middleScope)
            secondAction
  /-- The composed action's raw-action equals second-action's
  raw-action applied after first-action's raw-action. -/
  rawCompat : ∀ (rawTerm : RawTerm sourceScope),
      ActsOnRawTerm.actOnRawTerm composedAction rawTerm =
        ActsOnRawTerm.actOnRawTerm secondAction
            (ActsOnRawTerm.actOnRawTerm firstAction rawTerm)

/-- Native multi-Container composition for `Ty.act`.

Given three Containers (`first`, `second`, `composed`) with
compatibility witnesses (the composed Container mimics first-then-
second on var-lookup and raw-action), AND the compatibility survives
under both `liftForTy` and `liftForRaw`, we have:

```
Ty.act (Ty.act t firstAction) secondAction = Ty.act t composedAction
```

Proof: 25-case structural induction on `Ty level sourceScope`.  Every
arm rewrites by the IH plus the corresponding `varCompat`/`rawCompat`
witness for raw-payload arms.  Binder arms apply the lift hypothesis
to obtain the same predicate at `scope + 1`.

NO call to `Ty.subst_compose` or `Ty.subst_pointwise`.  The proof
relies only on `simp only [Ty.act]` (with `Ty.act` reducible) and the
supplied compatibility witnesses.

The compatibility witnesses for binder arms are delivered via the
`mkLiftForTy` / `mkLiftForRaw` parameters: given an existing
compatibility at the current scope, they produce a compatibility at
the lifted scope.  This is the standard Allais ICFP'18 "extension
under binder" strategy. -/
theorem Ty.act_compose
    {ContainerFirst ContainerSecond ContainerComposed : Nat → Nat → Type}
    [Action ContainerFirst] [Action ContainerSecond] [Action ContainerComposed]
    [ActsOnRawTerm ContainerFirst] [ActsOnRawTerm ContainerSecond]
    [ActsOnRawTerm ContainerComposed]
    {level : Nat}
    [ActsOnTyVar ContainerFirst level] [ActsOnTyVar ContainerSecond level]
    [ActsOnTyVar ContainerComposed level]
    (mkLiftForTy : ∀ {sourceScope middleScope targetScope : Nat}
        {firstAction : ContainerFirst sourceScope middleScope}
        {secondAction : ContainerSecond middleScope targetScope}
        {composedAction : ContainerComposed sourceScope targetScope},
        ActComposeCompat ContainerFirst ContainerSecond ContainerComposed level
            sourceScope middleScope targetScope
            firstAction secondAction composedAction →
        ActComposeCompat ContainerFirst ContainerSecond ContainerComposed level
            (sourceScope + 1) (middleScope + 1) (targetScope + 1)
            (Action.liftForTy firstAction)
            (Action.liftForTy secondAction)
            (Action.liftForTy composedAction))
    (mkLiftForRaw : ∀ {sourceScope middleScope targetScope : Nat}
        {firstAction : ContainerFirst sourceScope middleScope}
        {secondAction : ContainerSecond middleScope targetScope}
        {composedAction : ContainerComposed sourceScope targetScope},
        ActComposeCompat ContainerFirst ContainerSecond ContainerComposed level
            sourceScope middleScope targetScope
            firstAction secondAction composedAction →
        ActComposeCompat ContainerFirst ContainerSecond ContainerComposed level
            (sourceScope + 1) (middleScope + 1) (targetScope + 1)
            (Action.liftForRaw firstAction)
            (Action.liftForRaw secondAction)
            (Action.liftForRaw composedAction)) :
    ∀ {sourceScope middleScope targetScope : Nat}
      (someTy : Ty level sourceScope)
      {firstAction : ContainerFirst sourceScope middleScope}
      {secondAction : ContainerSecond middleScope targetScope}
      {composedAction : ContainerComposed sourceScope targetScope}
      (compatWitness : ActComposeCompat ContainerFirst ContainerSecond
          ContainerComposed level sourceScope middleScope targetScope
          firstAction secondAction composedAction),
      Ty.act (Ty.act someTy firstAction) secondAction =
        Ty.act someTy composedAction := by
  intro sourceScope middleScope targetScope someTy
  induction someTy generalizing middleScope targetScope with
  | unit => intros; rfl
  | bool => intros; rfl
  | nat  => intros; rfl
  | arrow domainType codomainType domainIH codomainIH =>
      intro firstAction secondAction composedAction compatWitness
      simp only [Ty.act]
      rw [domainIH compatWitness, codomainIH compatWitness]
  | piTy domainType codomainType domainIH codomainIH =>
      intro firstAction secondAction composedAction compatWitness
      simp only [Ty.act]
      rw [domainIH compatWitness, codomainIH (mkLiftForTy compatWitness)]
  | sigmaTy firstType secondType firstIH secondIH =>
      intro firstAction secondAction composedAction compatWitness
      simp only [Ty.act]
      rw [firstIH compatWitness, secondIH (mkLiftForTy compatWitness)]
  | tyVar position =>
      intro firstAction secondAction composedAction compatWitness
      simp only [Ty.act]
      exact (compatWitness.varCompat position).symm
  | id carrier leftEndpoint rightEndpoint carrierIH =>
      intro firstAction secondAction composedAction compatWitness
      simp only [Ty.act]
      rw [carrierIH compatWitness,
          ← compatWitness.rawCompat leftEndpoint,
          ← compatWitness.rawCompat rightEndpoint]
  | listType elementType elementIH =>
      intro firstAction secondAction composedAction compatWitness
      simp only [Ty.act]
      rw [elementIH compatWitness]
  | optionType elementType elementIH =>
      intro firstAction secondAction composedAction compatWitness
      simp only [Ty.act]
      rw [elementIH compatWitness]
  | eitherType leftType rightType leftIH rightIH =>
      intro firstAction secondAction composedAction compatWitness
      simp only [Ty.act]
      rw [leftIH compatWitness, rightIH compatWitness]
  | «universe» universeLevel levelLe => intros; rfl
  | empty => intros; rfl
  | interval => intros; rfl
  | path carrier leftEndpoint rightEndpoint carrierIH =>
      intro firstAction secondAction composedAction compatWitness
      simp only [Ty.act]
      rw [carrierIH compatWitness,
          ← compatWitness.rawCompat leftEndpoint,
          ← compatWitness.rawCompat rightEndpoint]
  | glue baseType boundaryWitness baseIH =>
      intro firstAction secondAction composedAction compatWitness
      simp only [Ty.act]
      rw [baseIH compatWitness, ← compatWitness.rawCompat boundaryWitness]
  | oeq carrier leftEndpoint rightEndpoint carrierIH =>
      intro firstAction secondAction composedAction compatWitness
      simp only [Ty.act]
      rw [carrierIH compatWitness,
          ← compatWitness.rawCompat leftEndpoint,
          ← compatWitness.rawCompat rightEndpoint]
  | idStrict carrier leftEndpoint rightEndpoint carrierIH =>
      intro firstAction secondAction composedAction compatWitness
      simp only [Ty.act]
      rw [carrierIH compatWitness,
          ← compatWitness.rawCompat leftEndpoint,
          ← compatWitness.rawCompat rightEndpoint]
  | equiv domainType codomainType domainIH codomainIH =>
      intro firstAction secondAction composedAction compatWitness
      simp only [Ty.act]
      rw [domainIH compatWitness, codomainIH compatWitness]
  | refine baseType predicate baseIH =>
      intro firstAction secondAction composedAction compatWitness
      simp only [Ty.act]
      rw [baseIH compatWitness,
          ← (mkLiftForRaw compatWitness).rawCompat predicate]
  | record singleFieldType singleFieldIH =>
      intro firstAction secondAction composedAction compatWitness
      simp only [Ty.act]
      rw [singleFieldIH compatWitness]
  | codata stateType outputType stateIH outputIH =>
      intro firstAction secondAction composedAction compatWitness
      simp only [Ty.act]
      rw [stateIH compatWitness, outputIH compatWitness]
  | session protocolStep =>
      intro firstAction secondAction composedAction compatWitness
      simp only [Ty.act]
      rw [← compatWitness.rawCompat protocolStep]
  | effect carrierType effectTag carrierIH =>
      intro firstAction secondAction composedAction compatWitness
      simp only [Ty.act]
      rw [carrierIH compatWitness, ← compatWitness.rawCompat effectTag]
  | modal modalityTag carrierType carrierIH =>
      intro firstAction secondAction composedAction compatWitness
      simp only [Ty.act]
      rw [carrierIH compatWitness]

/-! ## Section 3 — `Ty.act_identity`.

When an action behaves as identity at every scope (var-lookup returns
`Ty.tyVar`, raw-action returns the input unchanged), `Ty.act t action
= t`.  Like the others, the predicate must propagate under
`liftForTy`/`liftForRaw`.
-/

/-- Predicate: an action acts as identity — var-lookup returns the
input position back as a `Ty.tyVar`, and raw-action returns its raw
input unchanged. -/
structure ActsAsIdentity
    (Container : Nat → Nat → Type)
    [ActsOnRawTerm Container]
    (level : Nat)
    [ActsOnTyVar Container level]
    (scope : Nat)
    (someAction : Container scope scope) : Prop where
  /-- Var-lookup is identity: `varToTy action pos = Ty.tyVar pos`. -/
  varIdentity : ∀ (position : Fin scope),
      (ActsOnTyVar.varToTy someAction position : Ty level scope) =
        Ty.tyVar position
  /-- Raw-action is identity. -/
  rawIdentity : ∀ (rawTerm : RawTerm scope),
      ActsOnRawTerm.actOnRawTerm someAction rawTerm = rawTerm

/-- Native identity law for `Ty.act`.

If `someAction` acts as identity at every scope, AND the property
survives under both `liftForTy` and `liftForRaw`, then `Ty.act t
someAction = t` for every `t : Ty level scope`.

Proof: 25-case structural induction.  Each arm uses the IH plus the
identity witnesses for raw-payload arms.  Binder arms invoke the lift
hypothesis to extend the identity property to the lifted scope. -/
theorem Ty.act_identity
    {Container : Nat → Nat → Type}
    [Action Container]
    [ActsOnRawTerm Container]
    {level : Nat}
    [ActsOnTyVar Container level]
    (mkLiftForTy : ∀ {scope : Nat} {someAction : Container scope scope},
        ActsAsIdentity Container level scope someAction →
        ActsAsIdentity Container level (scope + 1)
            (Action.liftForTy someAction))
    (mkLiftForRaw : ∀ {scope : Nat} {someAction : Container scope scope},
        ActsAsIdentity Container level scope someAction →
        ActsAsIdentity Container level (scope + 1)
            (Action.liftForRaw someAction)) :
    ∀ {scope : Nat} (someTy : Ty level scope)
      {someAction : Container scope scope}
      (identityWitness : ActsAsIdentity Container level scope someAction),
      Ty.act someTy someAction = someTy := by
  intro scope someTy
  induction someTy with
  | unit => intros; rfl
  | bool => intros; rfl
  | nat  => intros; rfl
  | arrow domainType codomainType domainIH codomainIH =>
      intro someAction identityWitness
      simp only [Ty.act]
      rw [domainIH identityWitness, codomainIH identityWitness]
  | piTy domainType codomainType domainIH codomainIH =>
      intro someAction identityWitness
      simp only [Ty.act]
      rw [domainIH identityWitness, codomainIH (mkLiftForTy identityWitness)]
  | sigmaTy firstType secondType firstIH secondIH =>
      intro someAction identityWitness
      simp only [Ty.act]
      rw [firstIH identityWitness, secondIH (mkLiftForTy identityWitness)]
  | tyVar position =>
      intro someAction identityWitness
      simp only [Ty.act]
      exact identityWitness.varIdentity position
  | id carrier leftEndpoint rightEndpoint carrierIH =>
      intro someAction identityWitness
      simp only [Ty.act]
      rw [carrierIH identityWitness,
          identityWitness.rawIdentity leftEndpoint,
          identityWitness.rawIdentity rightEndpoint]
  | listType elementType elementIH =>
      intro someAction identityWitness
      simp only [Ty.act]; rw [elementIH identityWitness]
  | optionType elementType elementIH =>
      intro someAction identityWitness
      simp only [Ty.act]; rw [elementIH identityWitness]
  | eitherType leftType rightType leftIH rightIH =>
      intro someAction identityWitness
      simp only [Ty.act]; rw [leftIH identityWitness, rightIH identityWitness]
  | «universe» universeLevel levelLe => intros; rfl
  | empty => intros; rfl
  | interval => intros; rfl
  | path carrier leftEndpoint rightEndpoint carrierIH =>
      intro someAction identityWitness
      simp only [Ty.act]
      rw [carrierIH identityWitness,
          identityWitness.rawIdentity leftEndpoint,
          identityWitness.rawIdentity rightEndpoint]
  | glue baseType boundaryWitness baseIH =>
      intro someAction identityWitness
      simp only [Ty.act]
      rw [baseIH identityWitness, identityWitness.rawIdentity boundaryWitness]
  | oeq carrier leftEndpoint rightEndpoint carrierIH =>
      intro someAction identityWitness
      simp only [Ty.act]
      rw [carrierIH identityWitness,
          identityWitness.rawIdentity leftEndpoint,
          identityWitness.rawIdentity rightEndpoint]
  | idStrict carrier leftEndpoint rightEndpoint carrierIH =>
      intro someAction identityWitness
      simp only [Ty.act]
      rw [carrierIH identityWitness,
          identityWitness.rawIdentity leftEndpoint,
          identityWitness.rawIdentity rightEndpoint]
  | equiv domainType codomainType domainIH codomainIH =>
      intro someAction identityWitness
      simp only [Ty.act]
      rw [domainIH identityWitness, codomainIH identityWitness]
  | refine baseType predicate baseIH =>
      intro someAction identityWitness
      simp only [Ty.act]
      rw [baseIH identityWitness,
          (mkLiftForRaw identityWitness).rawIdentity predicate]
  | record singleFieldType singleFieldIH =>
      intro someAction identityWitness
      simp only [Ty.act]; rw [singleFieldIH identityWitness]
  | codata stateType outputType stateIH outputIH =>
      intro someAction identityWitness
      simp only [Ty.act]
      rw [stateIH identityWitness, outputIH identityWitness]
  | session protocolStep =>
      intro someAction identityWitness
      simp only [Ty.act]
      rw [identityWitness.rawIdentity protocolStep]
  | effect carrierType effectTag carrierIH =>
      intro someAction identityWitness
      simp only [Ty.act]
      rw [carrierIH identityWitness, identityWitness.rawIdentity effectTag]
  | modal modalityTag carrierType carrierIH =>
      intro someAction identityWitness
      simp only [Ty.act]; rw [carrierIH identityWitness]

end LeanFX2
