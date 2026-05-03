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

end LeanFX2
