import LeanFX2.Foundation.Subst

/-! # SubstHet — Phase 12.A.B1.2 heterogeneous (level-polymorphic) Subst

`SubstHet sourceLevel targetLevel sourceScope targetScope` is the
two-level joint substitution structure carrying:
* `forTy`  — `Fin sourceScope → Ty targetLevel targetScope`
* `forRaw` — `RawTermSubst sourceScope targetScope`
* `cumulOk : sourceLevel ≤ targetLevel` — the level-shift witness

When `sourceLevel = targetLevel`, this collapses to `Subst level
sourceScope targetScope` plus `cumulOk = Nat.le_refl _`.  At cumul
boundaries (`Term.cumulUp`-related code), the level mismatch is
real, and SubstHet's `cumulOk` records it.

## Architectural choice

We keep the existing single-level `Subst` unchanged (no breaking
change to the 5 Subst-aware files: Foundation/Subst, Term/Subst,
Term/Pointwise, Term/Bridge, Term/ProofIrrel).  Introduce SubstHet
as a strict generalization:

```lean
structure SubstHet (sourceLevel targetLevel sourceScope targetScope : Nat) : Type where
  forTy   : Fin sourceScope → Ty targetLevel targetScope
  forRaw  : RawTermSubst sourceScope targetScope
  cumulOk : sourceLevel ≤ targetLevel
```

* **Same-level uses (the entire kernel except cumul)**: keep `Subst`
* **Cross-level uses (`Term.cumulUp` boundaries, ConvCumul commute)**:
  use `SubstHet`

## Application: Ty.substHet

The level-polymorphic Ty substitution:
```lean
Ty.substHet : Ty sourceLevel sourceScope → SubstHet sourceLevel targetLevel sourceScope targetScope → Ty targetLevel targetScope
```

For most ctors, `Ty.substHet` is structurally identical to `Ty.subst`
modulo level threading.  The non-trivial arm is `Ty.universe`: its
existing `levelLe : u + 1 ≤ sourceLevel` proof composes with `cumulOk`
via `Nat.le_trans` to give `u + 1 ≤ targetLevel`.

## Bridges to/from Subst

* `SubstHet.fromSubst : Subst level src tgt → SubstHet level level src tgt`
  — bridge same-level Subst into the heterogeneous form
* `SubstHet.toSubst (sigma : SubstHet level level src tgt) :
   Subst level src tgt`
  — drop the trivial cumulOk witness back to single-level Subst

## Why no Ty.lift_level needed inside SubstHet's forTy

`SubstHet.forTy : Fin sourceScope → Ty targetLevel targetScope`
already returns substituents at `targetLevel`.  No lift needed in the
function-typed signature — the user is responsible for constructing
substituents at the target level (using `Ty.lift_level` if their
substituents started at a lower level).

## Audit gates

`Smoke/AuditPhase12AB12SubstHet.lean` runs `#print axioms` on every
declaration in this file.  All zero-axiom under strict policy.
-/

namespace LeanFX2

/-- Heterogeneous joint type/raw substitution.  Generalizes `Subst`
to cross-level: substituents in `forTy` live at `targetLevel`, the
source's tyVar references live at `sourceLevel`, and `cumulOk` records
the level-shift from `sourceLevel` to `targetLevel`. -/
structure SubstHet (sourceLevel targetLevel sourceScope targetScope : Nat) :
    Type where
  forTy   : Fin sourceScope → Ty targetLevel targetScope
  forRaw  : RawTermSubst sourceScope targetScope
  cumulOk : sourceLevel ≤ targetLevel

/-- Bridge: every same-level Subst lifts to a SubstHet with `Nat.le_refl`
as cumul witness. -/
@[reducible] def SubstHet.fromSubst {level sourceScope targetScope : Nat}
    (sigma : Subst level sourceScope targetScope) :
    SubstHet level level sourceScope targetScope where
  forTy   := sigma.forTy
  forRaw  := sigma.forRaw
  cumulOk := Nat.le_refl _

/-- Bridge: a same-level SubstHet (`sourceLevel = targetLevel`)
collapses to a Subst.  The `cumulOk` proof is discarded because at
the same level it must be `Nat.le_refl`. -/
@[reducible] def SubstHet.toSubst {level sourceScope targetScope : Nat}
    (sigma : SubstHet level level sourceScope targetScope) :
    Subst level sourceScope targetScope where
  forTy  := sigma.forTy
  forRaw := sigma.forRaw

/-- Pure level-shift SubstHet: the identity on positions, but with a
non-trivial cumul witness.  This is the SubstHet that `Term.cumulUp`'s
substitution arm uses to demote the outer Subst's substituents to the
lower level (when needed). -/
@[reducible] def SubstHet.cumul {sourceLevel targetLevel scope : Nat}
    (cumulOk : sourceLevel ≤ targetLevel) :
    SubstHet sourceLevel targetLevel scope scope where
  forTy   := fun position => Ty.tyVar position
  forRaw  := RawTermSubst.identity
  cumulOk := cumulOk

/-- Identity SubstHet — same level, identity positions. -/
@[reducible] def SubstHet.identity {level scope : Nat} :
    SubstHet level level scope scope where
  forTy   := fun position => Ty.tyVar position
  forRaw  := RawTermSubst.identity
  cumulOk := Nat.le_refl _

/-- Lift a SubstHet under a binder: both `forTy` and `forRaw` lift in
lockstep, `cumulOk` passes through unchanged.  Position 0 returns the
fresh tyVar at the new outermost binder; positions k+1 weaken the
underlying SubstHet's results. -/
@[reducible] def SubstHet.lift
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    (sigma : SubstHet sourceLevel targetLevel sourceScope targetScope) :
    SubstHet sourceLevel targetLevel (sourceScope + 1) (targetScope + 1) where
  forTy
    | ⟨0, _⟩      => Ty.tyVar ⟨0, Nat.zero_lt_succ _⟩
    | ⟨k + 1, h⟩  => (sigma.forTy ⟨k, Nat.lt_of_succ_lt_succ h⟩).weaken
  forRaw  := sigma.forRaw.lift
  cumulOk := sigma.cumulOk

/-! ## Ty.substHet — heterogeneous Ty substitution

Apply a heterogeneous SubstHet to a Ty.  The cumulOk witness threads
through the `Ty.universe` arm via Nat.le_trans; all other arms are
structural recursion (level is just a parameter). -/

/-- Apply a heterogeneous joint substitution to a type.  `tyVar`
positions consult `forTy`; `Ty.universe` arm composes its existing
`levelLe` with `sigma.cumulOk` via `Nat.le_trans`; other ctors recurse
structurally. -/
def Ty.substHet {sourceLevel targetLevel : Nat} :
    ∀ {sourceScope targetScope : Nat},
      Ty sourceLevel sourceScope →
      SubstHet sourceLevel targetLevel sourceScope targetScope →
      Ty targetLevel targetScope
  | _, _, .unit, _ => .unit
  | _, _, .bool, _ => .bool
  | _, _, .nat,  _ => .nat
  | _, _, .arrow domainType codomainType, sigma =>
      .arrow (domainType.substHet sigma) (codomainType.substHet sigma)
  | _, _, .piTy domainType codomainType, sigma =>
      .piTy (domainType.substHet sigma) (codomainType.substHet sigma.lift)
  | _, _, .sigmaTy firstType secondType, sigma =>
      .sigmaTy (firstType.substHet sigma) (secondType.substHet sigma.lift)
  | _, _, .tyVar position, sigma => sigma.forTy position
  | _, _, .id carrier leftEndpoint rightEndpoint, sigma =>
      .id (carrier.substHet sigma)
          (leftEndpoint.subst sigma.forRaw)
          (rightEndpoint.subst sigma.forRaw)
  | _, _, .listType elementType, sigma =>
      .listType (elementType.substHet sigma)
  | _, _, .optionType elementType, sigma =>
      .optionType (elementType.substHet sigma)
  | _, _, .eitherType leftType rightType, sigma =>
      .eitherType (leftType.substHet sigma) (rightType.substHet sigma)
  | _, _, .universe universeLevel levelLe, sigma =>
      .universe universeLevel (Nat.le_trans levelLe sigma.cumulOk)
  | _, _, .empty, _ => .empty
  | _, _, .interval, _ => .interval
  | _, _, .path carrier leftEndpoint rightEndpoint, sigma =>
      .path (carrier.substHet sigma)
            (leftEndpoint.subst sigma.forRaw)
            (rightEndpoint.subst sigma.forRaw)
  | _, _, .glue baseType boundaryWitness, sigma =>
      .glue (baseType.substHet sigma) (boundaryWitness.subst sigma.forRaw)
  | _, _, .oeq carrier leftEndpoint rightEndpoint, sigma =>
      .oeq (carrier.substHet sigma)
           (leftEndpoint.subst sigma.forRaw)
           (rightEndpoint.subst sigma.forRaw)
  | _, _, .idStrict carrier leftEndpoint rightEndpoint, sigma =>
      .idStrict (carrier.substHet sigma)
                (leftEndpoint.subst sigma.forRaw)
                (rightEndpoint.subst sigma.forRaw)
  | _, _, .equiv domainType codomainType, sigma =>
      .equiv (domainType.substHet sigma) (codomainType.substHet sigma)
  | _, _, .refine baseType predicate, sigma =>
      .refine (baseType.substHet sigma) (predicate.subst sigma.forRaw.lift)
  | _, _, .record singleFieldType, sigma =>
      .record (singleFieldType.substHet sigma)
  | _, _, .codata stateType outputType, sigma =>
      .codata (stateType.substHet sigma) (outputType.substHet sigma)
  | _, _, .session protocolStep, sigma =>
      .session (protocolStep.subst sigma.forRaw)
  | _, _, .effect carrierType effectTag, sigma =>
      .effect (carrierType.substHet sigma) (effectTag.subst sigma.forRaw)
  | _, _, .modal modalityTag carrierType, sigma =>
      .modal modalityTag (carrierType.substHet sigma)

/-! ## Pointwise lemma for Ty.substHet — needed to bridge two SubstHets that
agree pointwise but aren't definitionally equal as records. -/

/-- Lift respects pointwise equality on the forTy component. -/
theorem SubstHet.lift_forTy_pointwise
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sigma1 sigma2 : SubstHet sourceLevel targetLevel sourceScope targetScope}
    (forTyEq : ∀ position, sigma1.forTy position = sigma2.forTy position) :
    ∀ position, sigma1.lift.forTy position = sigma2.lift.forTy position
  | ⟨0, _⟩      => rfl
  | ⟨k + 1, h⟩  => by
      show (sigma1.forTy ⟨k, _⟩).weaken = (sigma2.forTy ⟨k, _⟩).weaken
      rw [forTyEq ⟨k, Nat.lt_of_succ_lt_succ h⟩]

/-- Lift respects pointwise equality on the forRaw component. -/
theorem SubstHet.lift_forRaw_pointwise
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sigma1 sigma2 : SubstHet sourceLevel targetLevel sourceScope targetScope}
    (forRawEq : ∀ position, sigma1.forRaw position = sigma2.forRaw position) :
    ∀ position, sigma1.lift.forRaw position = sigma2.lift.forRaw position :=
  fun position => RawTermSubst.lift_pointwise forRawEq position

/-- Ty.substHet respects pointwise SubstHet equality. -/
theorem Ty.substHet_pointwise {sourceLevel targetLevel : Nat}
    {scope targetScope : Nat}
    {sigma1 sigma2 : SubstHet sourceLevel targetLevel scope targetScope}
    (forTyEq : ∀ position, sigma1.forTy position = sigma2.forTy position)
    (forRawEq : ∀ position, sigma1.forRaw position = sigma2.forRaw position)
    (cumulOkEq : sigma1.cumulOk = sigma2.cumulOk) :
    ∀ (someType : Ty sourceLevel scope),
      someType.substHet sigma1 = someType.substHet sigma2 := by
  intro someType
  induction someType generalizing targetScope with
  | unit => rfl
  | bool => rfl
  | nat  => rfl
  | arrow d c dIH cIH =>
      simp only [Ty.substHet]; rw [dIH forTyEq forRawEq cumulOkEq, cIH forTyEq forRawEq cumulOkEq]
  | piTy d c dIH cIH =>
      simp only [Ty.substHet]
      rw [dIH forTyEq forRawEq cumulOkEq,
          cIH (SubstHet.lift_forTy_pointwise forTyEq)
              (SubstHet.lift_forRaw_pointwise forRawEq)
              cumulOkEq]
  | sigmaTy fT sT fIH sIH =>
      simp only [Ty.substHet]
      rw [fIH forTyEq forRawEq cumulOkEq,
          sIH (SubstHet.lift_forTy_pointwise forTyEq)
              (SubstHet.lift_forRaw_pointwise forRawEq)
              cumulOkEq]
  | tyVar position =>
      simp only [Ty.substHet]; rw [forTyEq position]
  | id carrier left right carrierIH =>
      simp only [Ty.substHet]
      rw [carrierIH forTyEq forRawEq cumulOkEq,
          RawTerm.subst_pointwise forRawEq left,
          RawTerm.subst_pointwise forRawEq right]
  | listType e eIH => simp only [Ty.substHet]; rw [eIH forTyEq forRawEq cumulOkEq]
  | optionType e eIH => simp only [Ty.substHet]; rw [eIH forTyEq forRawEq cumulOkEq]
  | eitherType l r lIH rIH =>
      simp only [Ty.substHet]; rw [lIH forTyEq forRawEq cumulOkEq, rIH forTyEq forRawEq cumulOkEq]
  | «universe» universeLevel levelLe =>
      show Ty.universe universeLevel (Nat.le_trans levelLe sigma1.cumulOk) =
           Ty.universe universeLevel (Nat.le_trans levelLe sigma2.cumulOk)
      rw [cumulOkEq]
  | empty => rfl
  | interval => rfl
  | path carrier left right carrierIH =>
      simp only [Ty.substHet]
      rw [carrierIH forTyEq forRawEq cumulOkEq,
          RawTerm.subst_pointwise forRawEq left,
          RawTerm.subst_pointwise forRawEq right]
  | glue baseType boundaryWitness baseIH =>
      simp only [Ty.substHet]
      rw [baseIH forTyEq forRawEq cumulOkEq,
          RawTerm.subst_pointwise forRawEq boundaryWitness]
  | oeq carrier left right carrierIH =>
      simp only [Ty.substHet]
      rw [carrierIH forTyEq forRawEq cumulOkEq,
          RawTerm.subst_pointwise forRawEq left,
          RawTerm.subst_pointwise forRawEq right]
  | idStrict carrier left right carrierIH =>
      simp only [Ty.substHet]
      rw [carrierIH forTyEq forRawEq cumulOkEq,
          RawTerm.subst_pointwise forRawEq left,
          RawTerm.subst_pointwise forRawEq right]
  | equiv d c dIH cIH =>
      simp only [Ty.substHet]; rw [dIH forTyEq forRawEq cumulOkEq, cIH forTyEq forRawEq cumulOkEq]
  | refine baseType predicate baseIH =>
      simp only [Ty.substHet]
      rw [baseIH forTyEq forRawEq cumulOkEq,
          RawTerm.subst_pointwise (RawTermSubst.lift_pointwise forRawEq) predicate]
  | record singleFieldType singleFieldIH =>
      simp only [Ty.substHet]; rw [singleFieldIH forTyEq forRawEq cumulOkEq]
  | codata stateType outputType stateIH outputIH =>
      simp only [Ty.substHet]; rw [stateIH forTyEq forRawEq cumulOkEq, outputIH forTyEq forRawEq cumulOkEq]
  | session protocolStep =>
      simp only [Ty.substHet]; rw [RawTerm.subst_pointwise forRawEq protocolStep]
  | effect carrierType effectTag carrierIH =>
      simp only [Ty.substHet]
      rw [carrierIH forTyEq forRawEq cumulOkEq,
          RawTerm.subst_pointwise forRawEq effectTag]
  | modal modalityTag carrierType carrierIH =>
      simp only [Ty.substHet]; rw [carrierIH forTyEq forRawEq cumulOkEq]

/-! ## Bridge laws between Subst and SubstHet

When SubstHet has same-level (`sourceLevel = targetLevel`),
`Ty.substHet` agrees with `Ty.subst` (modulo the cumulOk = Nat.le_refl
witness).  And when SubstHet is the pure cumul witness, `Ty.substHet`
agrees with `Ty.lift_level`. -/

/-- Same-level Ty.substHet on a Subst-derived SubstHet equals Ty.subst.
The forTy/forRaw fields are equal definitionally; the only non-trivial
arm is Ty.universe where `Nat.le_trans levelLe (Nat.le_refl _)` is
proof-irrelevant to `levelLe`. -/
theorem Ty.substHet_fromSubst {level : Nat}
    {sourceScope targetScope : Nat}
    (sigma : Subst level sourceScope targetScope)
    (someType : Ty level sourceScope) :
    someType.substHet (SubstHet.fromSubst sigma) = someType.subst sigma := by
  induction someType generalizing targetScope with
  | unit => rfl
  | bool => rfl
  | nat  => rfl
  | arrow d c dIH cIH =>
      simp only [Ty.substHet, Ty.subst]; rw [dIH sigma, cIH sigma]
  | piTy d c dIH cIH =>
      simp only [Ty.substHet, Ty.subst]
      rw [dIH sigma]
      congr 1
      have liftEq : (SubstHet.fromSubst sigma).lift = SubstHet.fromSubst sigma.lift := rfl
      rw [liftEq, cIH sigma.lift]
  | sigmaTy fT sT fIH sIH =>
      simp only [Ty.substHet, Ty.subst]
      rw [fIH sigma]
      congr 1
      have liftEq : (SubstHet.fromSubst sigma).lift = SubstHet.fromSubst sigma.lift := rfl
      rw [liftEq, sIH sigma.lift]
  | tyVar position => rfl
  | id carrier left right carrierIH =>
      simp only [Ty.substHet, Ty.subst]; rw [carrierIH sigma]
  | listType e eIH => simp only [Ty.substHet, Ty.subst]; rw [eIH sigma]
  | optionType e eIH => simp only [Ty.substHet, Ty.subst]; rw [eIH sigma]
  | eitherType l r lIH rIH =>
      simp only [Ty.substHet, Ty.subst]; rw [lIH sigma, rIH sigma]
  | «universe» universeLevel levelLe =>
      show Ty.universe universeLevel
            (Nat.le_trans levelLe (SubstHet.fromSubst sigma).cumulOk) =
           Ty.universe universeLevel levelLe
      have proofIrrel :
          Nat.le_trans levelLe (SubstHet.fromSubst sigma).cumulOk = levelLe :=
        Subsingleton.elim _ _
      rw [proofIrrel]
  | empty => rfl
  | interval => rfl
  | path carrier left right carrierIH =>
      simp only [Ty.substHet, Ty.subst]; rw [carrierIH sigma]
  | glue baseType boundaryWitness baseIH =>
      simp only [Ty.substHet, Ty.subst]; rw [baseIH sigma]
  | oeq carrier left right carrierIH =>
      simp only [Ty.substHet, Ty.subst]; rw [carrierIH sigma]
  | idStrict carrier left right carrierIH =>
      simp only [Ty.substHet, Ty.subst]; rw [carrierIH sigma]
  | equiv d c dIH cIH =>
      simp only [Ty.substHet, Ty.subst]; rw [dIH sigma, cIH sigma]
  | refine baseType predicate baseIH =>
      simp only [Ty.substHet, Ty.subst]; rw [baseIH sigma]
  | record singleFieldType singleFieldIH =>
      simp only [Ty.substHet, Ty.subst]; rw [singleFieldIH sigma]
  | codata stateType outputType stateIH outputIH =>
      simp only [Ty.substHet, Ty.subst]; rw [stateIH sigma, outputIH sigma]
  | session protocolStep => rfl
  | effect carrierType effectTag carrierIH =>
      simp only [Ty.substHet, Ty.subst]; rw [carrierIH sigma]
  | modal modalityTag carrierType carrierIH =>
      simp only [Ty.substHet, Ty.subst]; rw [carrierIH sigma]

/-- The pure-cumul SubstHet (identity positions, non-trivial cumulOk)
acts on Ty exactly as `Ty.lift_level cumulOk` does.  This makes
`SubstHet.cumul` the canonical bridge from Ty.lift_level to the
SubstHet world. -/
theorem Ty.substHet_cumul
    {sourceLevel targetLevel : Nat}
    (cumulOk : sourceLevel ≤ targetLevel) :
    ∀ {scope : Nat} (someType : Ty sourceLevel scope),
      someType.substHet (SubstHet.cumul (scope := scope) cumulOk) =
        Ty.lift_level cumulOk someType := by
  intro scope someType
  induction someType with
  | unit => rfl
  | bool => rfl
  | nat  => rfl
  | arrow d c dIH cIH =>
      simp only [Ty.substHet, Ty.lift_level]; rw [dIH, cIH]
  | piTy d c dIH cIH =>
      simp only [Ty.substHet, Ty.lift_level]
      rename_i scopeInner
      rw [dIH]
      congr 1
      have forTyPw : ∀ position,
          (SubstHet.cumul (scope := scopeInner) cumulOk).lift.forTy position =
            (SubstHet.cumul (scope := scopeInner + 1) cumulOk).forTy position
        | ⟨0, _⟩      => rfl
        | ⟨k + 1, _⟩  => rfl
      have forRawPw : ∀ position,
          (SubstHet.cumul (scope := scopeInner) cumulOk).lift.forRaw position =
            (SubstHet.cumul (scope := scopeInner + 1) cumulOk).forRaw position :=
        RawTermSubst.identity_lift_pointwise
      rw [Ty.substHet_pointwise forTyPw forRawPw rfl c, cIH]
  | sigmaTy fT sT fIH sIH =>
      simp only [Ty.substHet, Ty.lift_level]
      rename_i scopeInner
      rw [fIH]
      congr 1
      have forTyPw : ∀ position,
          (SubstHet.cumul (scope := scopeInner) cumulOk).lift.forTy position =
            (SubstHet.cumul (scope := scopeInner + 1) cumulOk).forTy position
        | ⟨0, _⟩      => rfl
        | ⟨k + 1, _⟩  => rfl
      have forRawPw : ∀ position,
          (SubstHet.cumul (scope := scopeInner) cumulOk).lift.forRaw position =
            (SubstHet.cumul (scope := scopeInner + 1) cumulOk).forRaw position :=
        RawTermSubst.identity_lift_pointwise
      rw [Ty.substHet_pointwise forTyPw forRawPw rfl sT, sIH]
  | tyVar position => rfl
  | id carrier left right carrierIH =>
      simp only [Ty.substHet, Ty.lift_level]
      rw [carrierIH, RawTerm.subst_identity left, RawTerm.subst_identity right]
  | listType e eIH => simp only [Ty.substHet, Ty.lift_level]; rw [eIH]
  | optionType e eIH => simp only [Ty.substHet, Ty.lift_level]; rw [eIH]
  | eitherType l r lIH rIH =>
      simp only [Ty.substHet, Ty.lift_level]; rw [lIH, rIH]
  | «universe» universeLevel levelLe => rfl
  | empty => rfl
  | interval => rfl
  | path carrier left right carrierIH =>
      simp only [Ty.substHet, Ty.lift_level]
      rw [carrierIH, RawTerm.subst_identity left, RawTerm.subst_identity right]
  | glue baseType boundaryWitness baseIH =>
      simp only [Ty.substHet, Ty.lift_level]
      rw [baseIH, RawTerm.subst_identity boundaryWitness]
  | oeq carrier left right carrierIH =>
      simp only [Ty.substHet, Ty.lift_level]
      rw [carrierIH, RawTerm.subst_identity left, RawTerm.subst_identity right]
  | idStrict carrier left right carrierIH =>
      simp only [Ty.substHet, Ty.lift_level]
      rw [carrierIH, RawTerm.subst_identity left, RawTerm.subst_identity right]
  | equiv d c dIH cIH =>
      simp only [Ty.substHet, Ty.lift_level]; rw [dIH, cIH]
  | refine baseType predicate baseIH =>
      simp only [Ty.substHet, Ty.lift_level]
      rename_i scopeInner
      rw [baseIH]
      have predicateInv :
          predicate.subst (SubstHet.cumul (scope := scopeInner) cumulOk).forRaw.lift =
            predicate := by
        show predicate.subst RawTermSubst.identity.lift = predicate
        rw [RawTerm.subst_pointwise RawTermSubst.identity_lift_pointwise predicate,
            RawTerm.subst_identity predicate]
      rw [predicateInv]
  | record singleFieldType singleFieldIH =>
      simp only [Ty.substHet, Ty.lift_level]; rw [singleFieldIH]
  | codata stateType outputType stateIH outputIH =>
      simp only [Ty.substHet, Ty.lift_level]; rw [stateIH, outputIH]
  | session protocolStep =>
      show Ty.session (protocolStep.subst RawTermSubst.identity) =
           Ty.session protocolStep
      rw [RawTerm.subst_identity protocolStep]
  | effect carrierType effectTag carrierIH =>
      simp only [Ty.substHet, Ty.lift_level]
      rw [carrierIH, RawTerm.subst_identity effectTag]
  | modal modalityTag carrierType carrierIH =>
      simp only [Ty.substHet, Ty.lift_level]; rw [carrierIH]

/-! ## Phase 12.A.B1.3-finish: rename/substHet commute lemmas

These mirror the single-level `Ty.subst_rename_commute` and
`Ty.rename_subst_commute` for the heterogeneous SubstHet.  Used by
`Term.substHet`'s lam/lamPi/appPi/pair/snd casts to align dependent
type signatures.

* `Ty.substHet_rename_commute` — `(someType.substHet sigma).rename rho =
   someType.substHet (sigma.renameOutput rho)` — substHet then rename.
* `Ty.rename_substHet_commute` — `(someType.rename rho).substHet sigma =
   someType.substHet (sigma.precomposeRenaming rho)` — rename then substHet.

The level threading: SubstHet's source/target levels parameterize the
operation, but renaming acts only on scopes (not levels), so the
level threading is the same as in `Ty.substHet` itself. -/

/-- Post-compose a SubstHet with a renaming on the output side. -/
@[reducible] def SubstHet.renameOutput
    {sourceLevel targetLevel sourceScope middleScope targetScope : Nat}
    (sigma : SubstHet sourceLevel targetLevel sourceScope middleScope)
    (rho : RawRenaming middleScope targetScope) :
    SubstHet sourceLevel targetLevel sourceScope targetScope where
  forTy   := fun position => (sigma.forTy position).rename rho
  forRaw  := fun position => (sigma.forRaw position).rename rho
  cumulOk := sigma.cumulOk

/-- Lift commutes with renameOutput on forTy. -/
theorem SubstHet.renameOutput_lift_forTy_pointwise
    {sourceLevel targetLevel sourceScope middleScope targetScope : Nat}
    (sigma : SubstHet sourceLevel targetLevel sourceScope middleScope)
    (rho : RawRenaming middleScope targetScope) :
    ∀ position,
      (sigma.lift.forTy position).rename rho.lift =
        (SubstHet.renameOutput sigma rho).lift.forTy position
  | ⟨0, _⟩      => rfl
  | ⟨k + 1, h⟩  => by
      show ((sigma.forTy ⟨k, _⟩).rename RawRenaming.weaken).rename rho.lift =
           ((sigma.forTy ⟨k, _⟩).rename rho).rename RawRenaming.weaken
      rw [Ty.rename_compose RawRenaming.weaken rho.lift
            (sigma.forTy ⟨k, Nat.lt_of_succ_lt_succ h⟩),
          Ty.rename_compose rho RawRenaming.weaken
            (sigma.forTy ⟨k, Nat.lt_of_succ_lt_succ h⟩)]
      apply Ty.rename_pointwise
      intro pos
      exact RawRenaming.weaken_lift_commute rho pos

/-- Lift commutes with renameOutput on forRaw. -/
theorem SubstHet.renameOutput_lift_forRaw_pointwise
    {sourceLevel targetLevel sourceScope middleScope targetScope : Nat}
    (sigma : SubstHet sourceLevel targetLevel sourceScope middleScope)
    (rho : RawRenaming middleScope targetScope) :
    ∀ position,
      (sigma.lift.forRaw position).rename rho.lift =
        (SubstHet.renameOutput sigma rho).lift.forRaw position :=
  fun position => RawTermSubst.lift_then_rename_lift sigma.forRaw rho position

/-- substHet-then-rename factors through SubstHet.renameOutput. -/
theorem Ty.substHet_rename_commute
    {sourceLevel targetLevel : Nat}
    {scope middleScope targetScope : Nat}
    (sigma : SubstHet sourceLevel targetLevel scope middleScope)
    (rho : RawRenaming middleScope targetScope)
    (someType : Ty sourceLevel scope) :
    (someType.substHet sigma).rename rho =
      someType.substHet (SubstHet.renameOutput sigma rho) := by
  induction someType generalizing middleScope targetScope with
  | unit => rfl
  | bool => rfl
  | nat  => rfl
  | arrow d c dIH cIH =>
      simp only [Ty.substHet, Ty.rename]; rw [dIH sigma rho, cIH sigma rho]
  | piTy d c dIH cIH =>
      simp only [Ty.substHet, Ty.rename]
      rw [dIH sigma rho, cIH sigma.lift rho.lift]
      congr 1
      apply Ty.substHet_pointwise
      · exact SubstHet.renameOutput_lift_forTy_pointwise sigma rho
      · exact SubstHet.renameOutput_lift_forRaw_pointwise sigma rho
      · rfl
  | sigmaTy fT sT fIH sIH =>
      simp only [Ty.substHet, Ty.rename]
      rw [fIH sigma rho, sIH sigma.lift rho.lift]
      congr 1
      apply Ty.substHet_pointwise
      · exact SubstHet.renameOutput_lift_forTy_pointwise sigma rho
      · exact SubstHet.renameOutput_lift_forRaw_pointwise sigma rho
      · rfl
  | tyVar position => rfl
  | id carrier left right carrierIH =>
      simp only [Ty.substHet, Ty.rename]
      rw [carrierIH sigma rho,
          RawTerm.subst_rename_commute sigma.forRaw rho left,
          RawTerm.subst_rename_commute sigma.forRaw rho right]
  | listType e eIH => simp only [Ty.substHet, Ty.rename]; rw [eIH sigma rho]
  | optionType e eIH => simp only [Ty.substHet, Ty.rename]; rw [eIH sigma rho]
  | eitherType l r lIH rIH =>
      simp only [Ty.substHet, Ty.rename]; rw [lIH sigma rho, rIH sigma rho]
  | «universe» universeLevel levelLe => rfl
  | empty => rfl
  | interval => rfl
  | path carrier left right carrierIH =>
      simp only [Ty.substHet, Ty.rename]
      rw [carrierIH sigma rho,
          RawTerm.subst_rename_commute sigma.forRaw rho left,
          RawTerm.subst_rename_commute sigma.forRaw rho right]
  | glue baseType boundaryWitness baseIH =>
      simp only [Ty.substHet, Ty.rename]
      rw [baseIH sigma rho,
          RawTerm.subst_rename_commute sigma.forRaw rho boundaryWitness]
  | oeq carrier left right carrierIH =>
      simp only [Ty.substHet, Ty.rename]
      rw [carrierIH sigma rho,
          RawTerm.subst_rename_commute sigma.forRaw rho left,
          RawTerm.subst_rename_commute sigma.forRaw rho right]
  | idStrict carrier left right carrierIH =>
      simp only [Ty.substHet, Ty.rename]
      rw [carrierIH sigma rho,
          RawTerm.subst_rename_commute sigma.forRaw rho left,
          RawTerm.subst_rename_commute sigma.forRaw rho right]
  | equiv d c dIH cIH =>
      simp only [Ty.substHet, Ty.rename]
      rw [dIH sigma rho, cIH sigma rho]
  | refine baseType predicate baseIH =>
      simp only [Ty.substHet, Ty.rename]
      rw [baseIH sigma rho,
          RawTerm.subst_rename_commute sigma.forRaw.lift rho.lift predicate]
      congr 1
      apply RawTerm.subst_pointwise
      intro position
      exact RawTermSubst.lift_then_rename_lift sigma.forRaw rho position
  | record singleFieldType singleFieldIH =>
      simp only [Ty.substHet, Ty.rename]
      rw [singleFieldIH sigma rho]
  | codata stateType outputType stateIH outputIH =>
      simp only [Ty.substHet, Ty.rename]
      rw [stateIH sigma rho, outputIH sigma rho]
  | session protocolStep =>
      simp only [Ty.substHet, Ty.rename]
      rw [RawTerm.subst_rename_commute sigma.forRaw rho protocolStep]
  | effect carrierType effectTag carrierIH =>
      simp only [Ty.substHet, Ty.rename]
      rw [carrierIH sigma rho,
          RawTerm.subst_rename_commute sigma.forRaw rho effectTag]
  | modal modalityTag carrierType carrierIH =>
      simp only [Ty.substHet, Ty.rename]
      rw [carrierIH sigma rho]

/-- Pre-compose a renaming with a SubstHet on the input side. -/
@[reducible] def SubstHet.precomposeRenaming
    {sourceLevel targetLevel sourceScope middleScope targetScope : Nat}
    (rho : RawRenaming sourceScope middleScope)
    (sigma : SubstHet sourceLevel targetLevel middleScope targetScope) :
    SubstHet sourceLevel targetLevel sourceScope targetScope where
  forTy   := fun position => sigma.forTy (rho position)
  forRaw  := fun position => sigma.forRaw (rho position)
  cumulOk := sigma.cumulOk

/-- Lift commutes with precomposeRenaming on forTy. -/
theorem SubstHet.precomposeRenaming_lift_forTy_pointwise
    {sourceLevel targetLevel sourceScope middleScope targetScope : Nat}
    (rho : RawRenaming sourceScope middleScope)
    (sigma : SubstHet sourceLevel targetLevel middleScope targetScope) :
    ∀ position,
      sigma.lift.forTy (rho.lift position) =
        (SubstHet.precomposeRenaming rho sigma).lift.forTy position
  | ⟨0, _⟩      => rfl
  | ⟨_ + 1, _⟩  => rfl

/-- Lift commutes with precomposeRenaming on forRaw. -/
theorem SubstHet.precomposeRenaming_lift_forRaw_pointwise
    {sourceLevel targetLevel sourceScope middleScope targetScope : Nat}
    (rho : RawRenaming sourceScope middleScope)
    (sigma : SubstHet sourceLevel targetLevel middleScope targetScope) :
    ∀ position,
      sigma.lift.forRaw (rho.lift position) =
        (SubstHet.precomposeRenaming rho sigma).lift.forRaw position :=
  fun position => RawTermSubst.lift_renaming_pull rho sigma.forRaw position

/-- rename-then-substHet factors through SubstHet.precomposeRenaming. -/
theorem Ty.rename_substHet_commute
    {sourceLevel targetLevel : Nat}
    {scope middleScope targetScope : Nat}
    (rho : RawRenaming scope middleScope)
    (sigma : SubstHet sourceLevel targetLevel middleScope targetScope)
    (someType : Ty sourceLevel scope) :
    (someType.rename rho).substHet sigma =
      someType.substHet (SubstHet.precomposeRenaming rho sigma) := by
  induction someType generalizing middleScope targetScope with
  | unit => rfl
  | bool => rfl
  | nat  => rfl
  | arrow d c dIH cIH =>
      simp only [Ty.rename, Ty.substHet]; rw [dIH rho sigma, cIH rho sigma]
  | piTy d c dIH cIH =>
      simp only [Ty.rename, Ty.substHet]
      rw [dIH rho sigma, cIH rho.lift sigma.lift]
      congr 1
      apply Ty.substHet_pointwise
      · exact SubstHet.precomposeRenaming_lift_forTy_pointwise rho sigma
      · exact SubstHet.precomposeRenaming_lift_forRaw_pointwise rho sigma
      · rfl
  | sigmaTy fT sT fIH sIH =>
      simp only [Ty.rename, Ty.substHet]
      rw [fIH rho sigma, sIH rho.lift sigma.lift]
      congr 1
      apply Ty.substHet_pointwise
      · exact SubstHet.precomposeRenaming_lift_forTy_pointwise rho sigma
      · exact SubstHet.precomposeRenaming_lift_forRaw_pointwise rho sigma
      · rfl
  | tyVar position => rfl
  | id carrier left right carrierIH =>
      simp only [Ty.rename, Ty.substHet]
      rw [carrierIH rho sigma,
          RawTerm.rename_subst_commute rho sigma.forRaw left,
          RawTerm.rename_subst_commute rho sigma.forRaw right]
  | listType e eIH => simp only [Ty.rename, Ty.substHet]; rw [eIH rho sigma]
  | optionType e eIH => simp only [Ty.rename, Ty.substHet]; rw [eIH rho sigma]
  | eitherType l r lIH rIH =>
      simp only [Ty.rename, Ty.substHet]; rw [lIH rho sigma, rIH rho sigma]
  | «universe» universeLevel levelLe => rfl
  | empty => rfl
  | interval => rfl
  | path carrier left right carrierIH =>
      simp only [Ty.rename, Ty.substHet]
      rw [carrierIH rho sigma,
          RawTerm.rename_subst_commute rho sigma.forRaw left,
          RawTerm.rename_subst_commute rho sigma.forRaw right]
  | glue baseType boundaryWitness baseIH =>
      simp only [Ty.rename, Ty.substHet]
      rw [baseIH rho sigma,
          RawTerm.rename_subst_commute rho sigma.forRaw boundaryWitness]
  | oeq carrier left right carrierIH =>
      simp only [Ty.rename, Ty.substHet]
      rw [carrierIH rho sigma,
          RawTerm.rename_subst_commute rho sigma.forRaw left,
          RawTerm.rename_subst_commute rho sigma.forRaw right]
  | idStrict carrier left right carrierIH =>
      simp only [Ty.rename, Ty.substHet]
      rw [carrierIH rho sigma,
          RawTerm.rename_subst_commute rho sigma.forRaw left,
          RawTerm.rename_subst_commute rho sigma.forRaw right]
  | equiv d c dIH cIH =>
      simp only [Ty.rename, Ty.substHet]
      rw [dIH rho sigma, cIH rho sigma]
  | refine baseType predicate baseIH =>
      simp only [Ty.rename, Ty.substHet]
      rw [baseIH rho sigma,
          RawTerm.rename_subst_commute rho.lift sigma.forRaw.lift predicate]
      congr 1
      apply RawTerm.subst_pointwise
      intro position
      exact RawTermSubst.lift_renaming_pull rho sigma.forRaw position
  | record singleFieldType singleFieldIH =>
      simp only [Ty.rename, Ty.substHet]
      rw [singleFieldIH rho sigma]
  | codata stateType outputType stateIH outputIH =>
      simp only [Ty.rename, Ty.substHet]
      rw [stateIH rho sigma, outputIH rho sigma]
  | session protocolStep =>
      simp only [Ty.rename, Ty.substHet]
      rw [RawTerm.rename_subst_commute rho sigma.forRaw protocolStep]
  | effect carrierType effectTag carrierIH =>
      simp only [Ty.rename, Ty.substHet]
      rw [carrierIH rho sigma,
          RawTerm.rename_subst_commute rho sigma.forRaw effectTag]
  | modal modalityTag carrierType carrierIH =>
      simp only [Ty.rename, Ty.substHet]
      rw [carrierIH rho sigma]

/-! ## Pointwise: lift commutes with weaken-output on SubstHet -/

/-- Pointwise: lift commutes with weaken-output on forTy. -/
theorem SubstHet.weaken_lift_forTy_pointwise
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    (sigma : SubstHet sourceLevel targetLevel sourceScope targetScope) :
    ∀ position,
      sigma.lift.forTy (RawRenaming.weaken position) =
        (sigma.forTy position).rename RawRenaming.weaken :=
  fun _ => rfl

/-- Pointwise: lift commutes with weaken-output on forRaw. -/
theorem SubstHet.weaken_lift_forRaw_pointwise
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    (sigma : SubstHet sourceLevel targetLevel sourceScope targetScope) :
    ∀ position,
      sigma.lift.forRaw (RawRenaming.weaken position) =
        (sigma.forRaw position).rename RawRenaming.weaken :=
  fun _ => rfl

/-- weaken-after-substHet equals substHet-after-weaken on Ty.  Load-bearing
for the lam case of typed `Term.substHet` (body's weakened codomain). -/
theorem Ty.weaken_substHet_commute
    {sourceLevel targetLevel : Nat}
    {sourceScope targetScope : Nat}
    (sigma : SubstHet sourceLevel targetLevel sourceScope targetScope)
    (someType : Ty sourceLevel sourceScope) :
    someType.weaken.substHet sigma.lift = (someType.substHet sigma).weaken := by
  show (someType.rename RawRenaming.weaken).substHet sigma.lift =
       (someType.substHet sigma).rename RawRenaming.weaken
  rw [Ty.rename_substHet_commute RawRenaming.weaken sigma.lift someType,
      Ty.substHet_rename_commute sigma RawRenaming.weaken someType]
  apply Ty.substHet_pointwise
  · exact SubstHet.weaken_lift_forTy_pointwise sigma
  · exact SubstHet.weaken_lift_forRaw_pointwise sigma
  · rfl

/-! ## SubstHet composition with same-level Subst (left and right)

We need to commute substHet over substitutions for Ty.subst0_substHet_commute.
Two composition patterns:

* `Subst.composeSubstHet` — `(Subst sourceLevel src mid).compose (SubstHet sourceLevel targetLevel mid tgt) = SubstHet sourceLevel targetLevel src tgt`
* `SubstHet.composeSubst` — `(SubstHet sourceLevel targetLevel src mid).compose (Subst targetLevel mid tgt) = SubstHet sourceLevel targetLevel src tgt`

Both threaded with cumulOk preserved. -/

/-- Compose Subst (at sourceLevel) followed by SubstHet (sourceLevel→targetLevel).
The sourceLevel substituents from the first get substHet-applied via the second. -/
@[reducible] def Subst.composeSubstHet
    {sourceLevel targetLevel sourceScope middleScope targetScope : Nat}
    (sigma : Subst sourceLevel sourceScope middleScope)
    (tau : SubstHet sourceLevel targetLevel middleScope targetScope) :
    SubstHet sourceLevel targetLevel sourceScope targetScope where
  forTy   := fun position => (sigma.forTy position).substHet tau
  forRaw  := RawTermSubst.compose sigma.forRaw tau.forRaw
  cumulOk := tau.cumulOk

/-- Compose SubstHet (sourceLevel→targetLevel) followed by Subst (at targetLevel).
The targetLevel substituents from the first get subst-applied via the second. -/
@[reducible] def SubstHet.composeSubst
    {sourceLevel targetLevel sourceScope middleScope targetScope : Nat}
    (sigma : SubstHet sourceLevel targetLevel sourceScope middleScope)
    (tau : Subst targetLevel middleScope targetScope) :
    SubstHet sourceLevel targetLevel sourceScope targetScope where
  forTy   := fun position => (sigma.forTy position).subst tau
  forRaw  := RawTermSubst.compose sigma.forRaw tau.forRaw
  cumulOk := sigma.cumulOk

/-- Lift commutes with composeSubstHet on forTy. -/
theorem Subst.composeSubstHet_lift_forTy_pointwise
    {sourceLevel targetLevel sourceScope middleScope targetScope : Nat}
    (sigma : Subst sourceLevel sourceScope middleScope)
    (tau : SubstHet sourceLevel targetLevel middleScope targetScope) :
    ∀ position,
      (Subst.composeSubstHet sigma tau).lift.forTy position =
        (Subst.composeSubstHet sigma.lift tau.lift).forTy position
  | ⟨0, _⟩      => rfl
  | ⟨k + 1, h⟩  => by
      show ((sigma.forTy ⟨k, _⟩).substHet tau).weaken =
           ((sigma.forTy ⟨k, _⟩).weaken).substHet tau.lift
      exact (Ty.weaken_substHet_commute tau (sigma.forTy ⟨k, Nat.lt_of_succ_lt_succ h⟩)).symm

/-- Lift commutes with composeSubstHet on forRaw. -/
theorem Subst.composeSubstHet_lift_forRaw_pointwise
    {sourceLevel targetLevel sourceScope middleScope targetScope : Nat}
    (sigma : Subst sourceLevel sourceScope middleScope)
    (tau : SubstHet sourceLevel targetLevel middleScope targetScope) :
    ∀ position,
      (Subst.composeSubstHet sigma tau).lift.forRaw position =
        (Subst.composeSubstHet sigma.lift tau.lift).forRaw position :=
  fun position => RawTermSubst.lift_compose_pointwise sigma.forRaw tau.forRaw position

/-- subst-then-substHet factors through Subst.composeSubstHet.  Mirror of
Ty.subst_compose for the cross-level case. -/
theorem Ty.subst_substHet_compose
    {sourceLevel targetLevel : Nat}
    {scope middleScope targetScope : Nat}
    (sigma : Subst sourceLevel scope middleScope)
    (tau : SubstHet sourceLevel targetLevel middleScope targetScope)
    (someType : Ty sourceLevel scope) :
    (someType.subst sigma).substHet tau =
      someType.substHet (Subst.composeSubstHet sigma tau) := by
  induction someType generalizing middleScope targetScope with
  | unit => rfl
  | bool => rfl
  | nat  => rfl
  | arrow d c dIH cIH =>
      simp only [Ty.subst, Ty.substHet]; rw [dIH sigma tau, cIH sigma tau]
  | piTy d c dIH cIH =>
      simp only [Ty.subst, Ty.substHet]
      rw [dIH sigma tau, cIH sigma.lift tau.lift]
      congr 1
      apply Ty.substHet_pointwise
      · exact fun p => (Subst.composeSubstHet_lift_forTy_pointwise sigma tau p).symm
      · exact fun p => (Subst.composeSubstHet_lift_forRaw_pointwise sigma tau p).symm
      · rfl
  | sigmaTy fT sT fIH sIH =>
      simp only [Ty.subst, Ty.substHet]
      rw [fIH sigma tau, sIH sigma.lift tau.lift]
      congr 1
      apply Ty.substHet_pointwise
      · exact fun p => (Subst.composeSubstHet_lift_forTy_pointwise sigma tau p).symm
      · exact fun p => (Subst.composeSubstHet_lift_forRaw_pointwise sigma tau p).symm
      · rfl
  | tyVar position => rfl
  | id carrier left right carrierIH =>
      simp only [Ty.subst, Ty.substHet]
      rw [carrierIH sigma tau,
          RawTerm.subst_compose sigma.forRaw tau.forRaw left,
          RawTerm.subst_compose sigma.forRaw tau.forRaw right]
  | listType e eIH => simp only [Ty.subst, Ty.substHet]; rw [eIH sigma tau]
  | optionType e eIH => simp only [Ty.subst, Ty.substHet]; rw [eIH sigma tau]
  | eitherType l r lIH rIH =>
      simp only [Ty.subst, Ty.substHet]; rw [lIH sigma tau, rIH sigma tau]
  | «universe» universeLevel levelLe => rfl
  | empty => rfl
  | interval => rfl
  | path carrier left right carrierIH =>
      simp only [Ty.subst, Ty.substHet]
      rw [carrierIH sigma tau,
          RawTerm.subst_compose sigma.forRaw tau.forRaw left,
          RawTerm.subst_compose sigma.forRaw tau.forRaw right]
  | glue baseType boundaryWitness baseIH =>
      simp only [Ty.subst, Ty.substHet]
      rw [baseIH sigma tau,
          RawTerm.subst_compose sigma.forRaw tau.forRaw boundaryWitness]
  | oeq carrier left right carrierIH =>
      simp only [Ty.subst, Ty.substHet]
      rw [carrierIH sigma tau,
          RawTerm.subst_compose sigma.forRaw tau.forRaw left,
          RawTerm.subst_compose sigma.forRaw tau.forRaw right]
  | idStrict carrier left right carrierIH =>
      simp only [Ty.subst, Ty.substHet]
      rw [carrierIH sigma tau,
          RawTerm.subst_compose sigma.forRaw tau.forRaw left,
          RawTerm.subst_compose sigma.forRaw tau.forRaw right]
  | equiv d c dIH cIH =>
      simp only [Ty.subst, Ty.substHet]
      rw [dIH sigma tau, cIH sigma tau]
  | refine baseType predicate baseIH =>
      simp only [Ty.subst, Ty.substHet]
      rw [baseIH sigma tau,
          RawTerm.subst_compose sigma.forRaw.lift tau.forRaw.lift predicate]
      congr 1
      apply RawTerm.subst_pointwise
      intro position
      exact (RawTermSubst.lift_compose_pointwise sigma.forRaw tau.forRaw position).symm
  | record singleFieldType singleFieldIH =>
      simp only [Ty.subst, Ty.substHet]
      rw [singleFieldIH sigma tau]
  | codata stateType outputType stateIH outputIH =>
      simp only [Ty.subst, Ty.substHet]
      rw [stateIH sigma tau, outputIH sigma tau]
  | session protocolStep =>
      simp only [Ty.subst, Ty.substHet]
      rw [RawTerm.subst_compose sigma.forRaw tau.forRaw protocolStep]
  | effect carrierType effectTag carrierIH =>
      simp only [Ty.subst, Ty.substHet]
      rw [carrierIH sigma tau,
          RawTerm.subst_compose sigma.forRaw tau.forRaw effectTag]
  | modal modalityTag carrierType carrierIH =>
      simp only [Ty.subst, Ty.substHet]
      rw [carrierIH sigma tau]

/-- Lift commutes with composeSubst on forTy. -/
theorem SubstHet.composeSubst_lift_forTy_pointwise
    {sourceLevel targetLevel sourceScope middleScope targetScope : Nat}
    (sigma : SubstHet sourceLevel targetLevel sourceScope middleScope)
    (tau : Subst targetLevel middleScope targetScope) :
    ∀ position,
      (SubstHet.composeSubst sigma tau).lift.forTy position =
        (SubstHet.composeSubst sigma.lift tau.lift).forTy position
  | ⟨0, _⟩      => rfl
  | ⟨k + 1, h⟩  => by
      show ((sigma.forTy ⟨k, _⟩).subst tau).weaken =
           ((sigma.forTy ⟨k, _⟩).weaken).subst tau.lift
      exact (Ty.weaken_subst_commute tau (sigma.forTy ⟨k, Nat.lt_of_succ_lt_succ h⟩)).symm

/-- Lift commutes with composeSubst on forRaw. -/
theorem SubstHet.composeSubst_lift_forRaw_pointwise
    {sourceLevel targetLevel sourceScope middleScope targetScope : Nat}
    (sigma : SubstHet sourceLevel targetLevel sourceScope middleScope)
    (tau : Subst targetLevel middleScope targetScope) :
    ∀ position,
      (SubstHet.composeSubst sigma tau).lift.forRaw position =
        (SubstHet.composeSubst sigma.lift tau.lift).forRaw position :=
  fun position => RawTermSubst.lift_compose_pointwise sigma.forRaw tau.forRaw position

/-- substHet-then-subst factors through SubstHet.composeSubst.  Mirror of
Ty.subst_compose for the cross-level case. -/
theorem Ty.substHet_subst_compose
    {sourceLevel targetLevel : Nat}
    {scope middleScope targetScope : Nat}
    (sigma : SubstHet sourceLevel targetLevel scope middleScope)
    (tau : Subst targetLevel middleScope targetScope)
    (someType : Ty sourceLevel scope) :
    (someType.substHet sigma).subst tau =
      someType.substHet (SubstHet.composeSubst sigma tau) := by
  induction someType generalizing middleScope targetScope with
  | unit => rfl
  | bool => rfl
  | nat  => rfl
  | arrow d c dIH cIH =>
      simp only [Ty.substHet, Ty.subst]; rw [dIH sigma tau, cIH sigma tau]
  | piTy d c dIH cIH =>
      simp only [Ty.substHet, Ty.subst]
      rw [dIH sigma tau, cIH sigma.lift tau.lift]
      congr 1
      apply Ty.substHet_pointwise
      · exact fun p => (SubstHet.composeSubst_lift_forTy_pointwise sigma tau p).symm
      · exact fun p => (SubstHet.composeSubst_lift_forRaw_pointwise sigma tau p).symm
      · rfl
  | sigmaTy fT sT fIH sIH =>
      simp only [Ty.substHet, Ty.subst]
      rw [fIH sigma tau, sIH sigma.lift tau.lift]
      congr 1
      apply Ty.substHet_pointwise
      · exact fun p => (SubstHet.composeSubst_lift_forTy_pointwise sigma tau p).symm
      · exact fun p => (SubstHet.composeSubst_lift_forRaw_pointwise sigma tau p).symm
      · rfl
  | tyVar position => rfl
  | id carrier left right carrierIH =>
      simp only [Ty.substHet, Ty.subst]
      rw [carrierIH sigma tau,
          RawTerm.subst_compose sigma.forRaw tau.forRaw left,
          RawTerm.subst_compose sigma.forRaw tau.forRaw right]
  | listType e eIH => simp only [Ty.substHet, Ty.subst]; rw [eIH sigma tau]
  | optionType e eIH => simp only [Ty.substHet, Ty.subst]; rw [eIH sigma tau]
  | eitherType l r lIH rIH =>
      simp only [Ty.substHet, Ty.subst]; rw [lIH sigma tau, rIH sigma tau]
  | «universe» universeLevel levelLe => rfl
  | empty => rfl
  | interval => rfl
  | path carrier left right carrierIH =>
      simp only [Ty.substHet, Ty.subst]
      rw [carrierIH sigma tau,
          RawTerm.subst_compose sigma.forRaw tau.forRaw left,
          RawTerm.subst_compose sigma.forRaw tau.forRaw right]
  | glue baseType boundaryWitness baseIH =>
      simp only [Ty.substHet, Ty.subst]
      rw [baseIH sigma tau,
          RawTerm.subst_compose sigma.forRaw tau.forRaw boundaryWitness]
  | oeq carrier left right carrierIH =>
      simp only [Ty.substHet, Ty.subst]
      rw [carrierIH sigma tau,
          RawTerm.subst_compose sigma.forRaw tau.forRaw left,
          RawTerm.subst_compose sigma.forRaw tau.forRaw right]
  | idStrict carrier left right carrierIH =>
      simp only [Ty.substHet, Ty.subst]
      rw [carrierIH sigma tau,
          RawTerm.subst_compose sigma.forRaw tau.forRaw left,
          RawTerm.subst_compose sigma.forRaw tau.forRaw right]
  | equiv d c dIH cIH =>
      simp only [Ty.substHet, Ty.subst]
      rw [dIH sigma tau, cIH sigma tau]
  | refine baseType predicate baseIH =>
      simp only [Ty.substHet, Ty.subst]
      rw [baseIH sigma tau,
          RawTerm.subst_compose sigma.forRaw.lift tau.forRaw.lift predicate]
      congr 1
      apply RawTerm.subst_pointwise
      intro position
      exact (RawTermSubst.lift_compose_pointwise sigma.forRaw tau.forRaw position).symm
  | record singleFieldType singleFieldIH =>
      simp only [Ty.substHet, Ty.subst]
      rw [singleFieldIH sigma tau]
  | codata stateType outputType stateIH outputIH =>
      simp only [Ty.substHet, Ty.subst]
      rw [stateIH sigma tau, outputIH sigma tau]
  | session protocolStep =>
      simp only [Ty.substHet, Ty.subst]
      rw [RawTerm.subst_compose sigma.forRaw tau.forRaw protocolStep]
  | effect carrierType effectTag carrierIH =>
      simp only [Ty.substHet, Ty.subst]
      rw [carrierIH sigma tau,
          RawTerm.subst_compose sigma.forRaw tau.forRaw effectTag]
  | modal modalityTag carrierType carrierIH =>
      simp only [Ty.substHet, Ty.subst]
      rw [carrierIH sigma tau]

/-! ## Ty.subst0_substHet_commute via subst-substHet composition

The key Ty subst0 commute lemma for Term.substHet's appPi/pair/snd casts.
Given a `Subst.singleton substituent rawArg` then `substHet sigma`,
we want to factor through a `sigma.lift` then `Subst.singleton (substHet
substituent) (subst rawArg)`. -/

/-- Pointwise: composing singleton with substHet sigma agrees with composing
sigma.lift with substHet-renamed singleton on forTy. -/
theorem SubstHet.singleton_substHet_swap_forTy_pointwise
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    (substituent : Ty sourceLevel sourceScope) (rawArg : RawTerm sourceScope)
    (sigma : SubstHet sourceLevel targetLevel sourceScope targetScope) :
    ∀ position,
      (Subst.composeSubstHet (Subst.singleton substituent rawArg) sigma).forTy position =
        (SubstHet.composeSubst sigma.lift
          (Subst.singleton (substituent.substHet sigma) (rawArg.subst sigma.forRaw))).forTy
          position
  | ⟨0, _⟩      => rfl
  | ⟨k + 1, h⟩  => by
      show sigma.forTy ⟨k, Nat.lt_of_succ_lt_succ h⟩ =
           (sigma.forTy ⟨k, Nat.lt_of_succ_lt_succ h⟩).weaken.subst
             (Subst.singleton (substituent.substHet sigma) (rawArg.subst sigma.forRaw))
      exact (Ty.weaken_subst_singleton (sigma.forTy ⟨k, _⟩)
              (substituent.substHet sigma) (rawArg.subst sigma.forRaw)).symm

/-- Pointwise: composing singleton with substHet sigma agrees with composing
sigma.lift with substHet-renamed singleton on forRaw. -/
theorem SubstHet.singleton_substHet_swap_forRaw_pointwise
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    (substituent : Ty sourceLevel sourceScope) (rawArg : RawTerm sourceScope)
    (sigma : SubstHet sourceLevel targetLevel sourceScope targetScope) :
    ∀ position,
      (Subst.composeSubstHet (Subst.singleton substituent rawArg) sigma).forRaw position =
        (SubstHet.composeSubst sigma.lift
          (Subst.singleton (substituent.substHet sigma) (rawArg.subst sigma.forRaw))).forRaw
          position
  | ⟨0, _⟩      => rfl
  | ⟨k + 1, h⟩  => by
      show sigma.forRaw ⟨k, Nat.lt_of_succ_lt_succ h⟩ =
           (sigma.forRaw ⟨k, Nat.lt_of_succ_lt_succ h⟩).weaken.subst
             (RawTermSubst.singleton (rawArg.subst sigma.forRaw))
      exact (RawTerm.weaken_subst_singleton (sigma.forRaw ⟨k, _⟩)
              (rawArg.subst sigma.forRaw)).symm

/-- subst0 then substHet equals substHet.lift then subst0.  Load-bearing for
typed `Term.substHet` on β-redex result types: `(cod.subst0 dom argRaw).substHet sigma`
matches `(cod.substHet sigma.lift).subst0 (dom.substHet sigma) (argRaw.subst sigma.forRaw)`. -/
theorem Ty.subst0_substHet_commute
    {sourceLevel targetLevel scope targetScope : Nat}
    (codomainType : Ty sourceLevel (scope + 1))
    (argType : Ty sourceLevel scope) (argRaw : RawTerm scope)
    (sigma : SubstHet sourceLevel targetLevel scope targetScope) :
    (codomainType.subst0 argType argRaw).substHet sigma =
      (codomainType.substHet sigma.lift).subst0
        (argType.substHet sigma) (argRaw.subst sigma.forRaw) := by
  show (codomainType.subst (Subst.singleton argType argRaw)).substHet sigma =
       (codomainType.substHet sigma.lift).subst
         (Subst.singleton (argType.substHet sigma) (argRaw.subst sigma.forRaw))
  rw [Ty.subst_substHet_compose (Subst.singleton argType argRaw) sigma codomainType,
      Ty.substHet_subst_compose sigma.lift
        (Subst.singleton (argType.substHet sigma) (argRaw.subst sigma.forRaw)) codomainType]
  apply Ty.substHet_pointwise
  · exact SubstHet.singleton_substHet_swap_forTy_pointwise argType argRaw sigma
  · exact SubstHet.singleton_substHet_swap_forRaw_pointwise argType argRaw sigma
  · rfl

end LeanFX2
