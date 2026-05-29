import FX1Poly.Core.RemainingDim0Eliminators

/-! # Foundation/PolyCell/Core/IdEliminatorLayer
   — full compositional layer for `idJ` and `idStrictRec`

V2-L3.1 phase D step 26 (2026-05-27).  Completes dim-0 eliminator
coverage.  Both `gen_idJ` and `gen_idStrictRec` are 2-child
same-scope eliminators (not 3-child as the family above).

## Child layout (shared)

`(baseCase, identityWitness)` — both at same scope as parent.

Semantically:
* `idJ`:          dependent J-eliminator on Id types.  baseCase is
  the motive evaluated at `refl`; identityWitness is the equality.
* `idStrictRec`:  strict (non-dependent) variant of J.  Same shape.

## What this file ships (18 declarations)

For each of `gen_idJ` and `gen_idStrictRec`, 9 declarations:

  * INTRO (1): build HCC from baseCase + idWitness cells.
  * 2 PROJECTIONS: baseCase + idWitness.
  * Rename probe + preservation (2).
  * Subst probe + preservation (2).
  * Subst0 probe + preservation (2).

## Coverage milestone

After this iteration:

| Category                    | Generators                                              | Count |
|-----------------------------|---------------------------------------------------------|-------|
| Nullary leaves              | 7                                                       | 7     |
| Compound constructors       | 9                                                       | 9     |
| 1-child eliminators (NEW)   | fst, snd                                                | 2     |
| 2-child eliminators         | idJ, idStrictRec                                        | **2** |
| 3-child eliminators         | boolElim, natElim, natRec, listElim, optionMatch, eitherMatch | 6 |
| **Total dim-0 surface**     |                                                         | **26** |

**All 7 dim-0 eliminators now have full compositional support.**
The compositional infrastructure for SR-cong is COMPLETE across
all the term-level shapes that the existing 16 SR iota arms touch.

## Zero-axiom verification

Same proven template as `PairEliminatorLayer` (1-child) and the
3-child eliminator files.  Audit-gated.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation

/-! ## idJ — dependent J-eliminator -/

/-- **Intro: idJ's structural admission from base + witness cells.** -/
theorem HasCertifiedCellDim0.idJ
    {profile : PolyProfile} {scope : Nat}
    {baseCaseTerm identityWitnessTerm : RawTerm scope}
    (baseCaseCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase baseCaseTerm))
    (identityWitnessCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase identityWitnessTerm)) :
    HasCertifiedCellDim0 (profile := profile)
      ((.mkGen .gen_idJ ()
        (.childCons baseCaseTerm
          (.childCons identityWitnessTerm .childNil))) : RawTerm scope) :=
  .intro .term
    (PolyCell.gen
      SupportedGenerator.gen_idJ
      (genPayloadEvidence (generator := .gen_idJ)
                           (scope := scope) ())
      (CertifiedTermSpine.cons baseCaseCell
        (CertifiedTermSpine.cons identityWitnessCell
          CertifiedTermSpine.nil)))

/-- **Projection: `gen_idJ` → baseCase child's cert.** -/
theorem HasCertifiedCellDim0.idJ_baseCase_projection
    {profile : PolyProfile} {scope : Nat}
    (baseCaseTerm identityWitnessTerm : RawTerm scope)
    (cert : HasCertifiedCellDim0 (profile := profile)
              ((.mkGen .gen_idJ ()
                (.childCons baseCaseTerm
                  (.childCons identityWitnessTerm .childNil)))
                : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) baseCaseTerm := by
  obtain ⟨_, cell⟩ := cert
  cases cell with
  | gen _ _ spine =>
    exact ⟨.term, spine.headAtDim0 rfl⟩

/-- **Projection: `gen_idJ` → identityWitness child's cert.** -/
theorem HasCertifiedCellDim0.idJ_identityWitness_projection
    {profile : PolyProfile} {scope : Nat}
    (baseCaseTerm identityWitnessTerm : RawTerm scope)
    (cert : HasCertifiedCellDim0 (profile := profile)
              ((.mkGen .gen_idJ ()
                (.childCons baseCaseTerm
                  (.childCons identityWitnessTerm .childNil)))
                : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) identityWitnessTerm := by
  obtain ⟨_, cell⟩ := cert
  cases cell with
  | gen _ _ spine =>
    exact ⟨.term, spine.tail.headAtDim0 rfl⟩

/-- **Probe: rename distributes over `gen_idJ`.** -/
theorem RawTerm.rename_idJ_reduces
    {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (baseCaseTerm identityWitnessTerm : RawTerm sourceScope) :
    RawTerm.rename rawRenaming
        ((.mkGen .gen_idJ ()
          (.childCons baseCaseTerm
            (.childCons identityWitnessTerm .childNil)))
          : RawTerm sourceScope) =
      ((.mkGen .gen_idJ ()
        (.childCons (RawTerm.rename rawRenaming baseCaseTerm)
          (.childCons (RawTerm.rename rawRenaming identityWitnessTerm)
            .childNil)))
        : RawTerm targetScope) := rfl

/-- **`idJ` preserved by rename (compositional).** -/
theorem HasCertifiedCellDim0.idJ_preservedByRename
    {profile : PolyProfile} {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (baseCaseTerm identityWitnessTerm : RawTerm sourceScope)
    (renamedBaseCaseCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.rename rawRenaming baseCaseTerm)))
    (renamedIdentityWitnessCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.rename rawRenaming identityWitnessTerm))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.rename rawRenaming
        (.mkGen .gen_idJ ()
          (.childCons baseCaseTerm
            (.childCons identityWitnessTerm .childNil)))) := by
  rw [RawTerm.rename_idJ_reduces]
  exact HasCertifiedCellDim0.idJ renamedBaseCaseCell renamedIdentityWitnessCell

/-- **Probe: subst distributes over `gen_idJ`.** -/
theorem RawTerm.subst_idJ_reduces
    {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (baseCaseTerm identityWitnessTerm : RawTerm sourceScope) :
    RawTerm.subst substitution
        ((.mkGen .gen_idJ ()
          (.childCons baseCaseTerm
            (.childCons identityWitnessTerm .childNil)))
          : RawTerm sourceScope) =
      ((.mkGen .gen_idJ ()
        (.childCons (RawTerm.subst substitution baseCaseTerm)
          (.childCons (RawTerm.subst substitution identityWitnessTerm)
            .childNil)))
        : RawTerm targetScope) := rfl

/-- **`idJ` preserved by subst (compositional).** -/
theorem HasCertifiedCellDim0.idJ_preservedBySubst
    {profile : PolyProfile} {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (baseCaseTerm identityWitnessTerm : RawTerm sourceScope)
    (substBaseCaseCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.subst substitution baseCaseTerm)))
    (substIdentityWitnessCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.subst substitution identityWitnessTerm))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst substitution
        (.mkGen .gen_idJ ()
          (.childCons baseCaseTerm
            (.childCons identityWitnessTerm .childNil)))) := by
  rw [RawTerm.subst_idJ_reduces]
  exact HasCertifiedCellDim0.idJ substBaseCaseCell substIdentityWitnessCell

/-- **Probe: subst0 distributes over `gen_idJ`.** -/
theorem RawTerm.subst0_idJ_reduces
    {scope : Nat} (rawArg : RawTerm scope)
    (baseCaseTerm identityWitnessTerm : RawTerm (scope + 1)) :
    RawTerm.subst0
        ((.mkGen .gen_idJ ()
          (.childCons baseCaseTerm
            (.childCons identityWitnessTerm .childNil)))
          : RawTerm (scope + 1))
        rawArg =
      (.mkGen .gen_idJ ()
        (.childCons (RawTerm.subst0 baseCaseTerm rawArg)
          (.childCons (RawTerm.subst0 identityWitnessTerm rawArg) .childNil))
        : RawTerm scope) := rfl

/-- **Beta-redex preservation for `gen_idJ`.** -/
theorem HasCertifiedCellDim0.subst0_idJ_preservation
    {profile : PolyProfile} {scope : Nat}
    (rawArg : RawTerm scope)
    (baseCaseTerm identityWitnessTerm : RawTerm (scope + 1))
    (substBaseCaseCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase (RawTerm.subst0 baseCaseTerm rawArg)))
    (substIdentityWitnessCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase (RawTerm.subst0 identityWitnessTerm rawArg))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst0
        ((.mkGen .gen_idJ ()
          (.childCons baseCaseTerm
            (.childCons identityWitnessTerm .childNil)))
          : RawTerm (scope + 1))
        rawArg) := by
  rw [RawTerm.subst0_idJ_reduces]
  exact HasCertifiedCellDim0.idJ substBaseCaseCell substIdentityWitnessCell

/-! ## idStrictRec — strict (non-dependent) variant of J -/

/-- **Intro: idStrictRec's structural admission from base + witness cells.** -/
theorem HasCertifiedCellDim0.idStrictRec
    {profile : PolyProfile} {scope : Nat}
    {baseCaseTerm identityWitnessTerm : RawTerm scope}
    (baseCaseCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase baseCaseTerm))
    (identityWitnessCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase identityWitnessTerm)) :
    HasCertifiedCellDim0 (profile := profile)
      ((.mkGen .gen_idStrictRec ()
        (.childCons baseCaseTerm
          (.childCons identityWitnessTerm .childNil))) : RawTerm scope) :=
  .intro .term
    (PolyCell.gen
      SupportedGenerator.gen_idStrictRec
      (genPayloadEvidence (generator := .gen_idStrictRec)
                           (scope := scope) ())
      (CertifiedTermSpine.cons baseCaseCell
        (CertifiedTermSpine.cons identityWitnessCell
          CertifiedTermSpine.nil)))

/-- **Projection: `gen_idStrictRec` → baseCase child's cert.** -/
theorem HasCertifiedCellDim0.idStrictRec_baseCase_projection
    {profile : PolyProfile} {scope : Nat}
    (baseCaseTerm identityWitnessTerm : RawTerm scope)
    (cert : HasCertifiedCellDim0 (profile := profile)
              ((.mkGen .gen_idStrictRec ()
                (.childCons baseCaseTerm
                  (.childCons identityWitnessTerm .childNil)))
                : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) baseCaseTerm := by
  obtain ⟨_, cell⟩ := cert
  cases cell with
  | gen _ _ spine =>
    exact ⟨.term, spine.headAtDim0 rfl⟩

/-- **Projection: `gen_idStrictRec` → identityWitness child's cert.** -/
theorem HasCertifiedCellDim0.idStrictRec_identityWitness_projection
    {profile : PolyProfile} {scope : Nat}
    (baseCaseTerm identityWitnessTerm : RawTerm scope)
    (cert : HasCertifiedCellDim0 (profile := profile)
              ((.mkGen .gen_idStrictRec ()
                (.childCons baseCaseTerm
                  (.childCons identityWitnessTerm .childNil)))
                : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) identityWitnessTerm := by
  obtain ⟨_, cell⟩ := cert
  cases cell with
  | gen _ _ spine =>
    exact ⟨.term, spine.tail.headAtDim0 rfl⟩

/-- **Probe: rename distributes over `gen_idStrictRec`.** -/
theorem RawTerm.rename_idStrictRec_reduces
    {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (baseCaseTerm identityWitnessTerm : RawTerm sourceScope) :
    RawTerm.rename rawRenaming
        ((.mkGen .gen_idStrictRec ()
          (.childCons baseCaseTerm
            (.childCons identityWitnessTerm .childNil)))
          : RawTerm sourceScope) =
      ((.mkGen .gen_idStrictRec ()
        (.childCons (RawTerm.rename rawRenaming baseCaseTerm)
          (.childCons (RawTerm.rename rawRenaming identityWitnessTerm)
            .childNil)))
        : RawTerm targetScope) := rfl

/-- **`idStrictRec` preserved by rename (compositional).** -/
theorem HasCertifiedCellDim0.idStrictRec_preservedByRename
    {profile : PolyProfile} {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (baseCaseTerm identityWitnessTerm : RawTerm sourceScope)
    (renamedBaseCaseCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.rename rawRenaming baseCaseTerm)))
    (renamedIdentityWitnessCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.rename rawRenaming identityWitnessTerm))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.rename rawRenaming
        (.mkGen .gen_idStrictRec ()
          (.childCons baseCaseTerm
            (.childCons identityWitnessTerm .childNil)))) := by
  rw [RawTerm.rename_idStrictRec_reduces]
  exact HasCertifiedCellDim0.idStrictRec renamedBaseCaseCell
    renamedIdentityWitnessCell

/-- **Probe: subst distributes over `gen_idStrictRec`.** -/
theorem RawTerm.subst_idStrictRec_reduces
    {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (baseCaseTerm identityWitnessTerm : RawTerm sourceScope) :
    RawTerm.subst substitution
        ((.mkGen .gen_idStrictRec ()
          (.childCons baseCaseTerm
            (.childCons identityWitnessTerm .childNil)))
          : RawTerm sourceScope) =
      ((.mkGen .gen_idStrictRec ()
        (.childCons (RawTerm.subst substitution baseCaseTerm)
          (.childCons (RawTerm.subst substitution identityWitnessTerm)
            .childNil)))
        : RawTerm targetScope) := rfl

/-- **`idStrictRec` preserved by subst (compositional).** -/
theorem HasCertifiedCellDim0.idStrictRec_preservedBySubst
    {profile : PolyProfile} {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (baseCaseTerm identityWitnessTerm : RawTerm sourceScope)
    (substBaseCaseCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.subst substitution baseCaseTerm)))
    (substIdentityWitnessCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.subst substitution identityWitnessTerm))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst substitution
        (.mkGen .gen_idStrictRec ()
          (.childCons baseCaseTerm
            (.childCons identityWitnessTerm .childNil)))) := by
  rw [RawTerm.subst_idStrictRec_reduces]
  exact HasCertifiedCellDim0.idStrictRec substBaseCaseCell
    substIdentityWitnessCell

/-- **Probe: subst0 distributes over `gen_idStrictRec`.** -/
theorem RawTerm.subst0_idStrictRec_reduces
    {scope : Nat} (rawArg : RawTerm scope)
    (baseCaseTerm identityWitnessTerm : RawTerm (scope + 1)) :
    RawTerm.subst0
        ((.mkGen .gen_idStrictRec ()
          (.childCons baseCaseTerm
            (.childCons identityWitnessTerm .childNil)))
          : RawTerm (scope + 1))
        rawArg =
      (.mkGen .gen_idStrictRec ()
        (.childCons (RawTerm.subst0 baseCaseTerm rawArg)
          (.childCons (RawTerm.subst0 identityWitnessTerm rawArg) .childNil))
        : RawTerm scope) := rfl

/-- **Beta-redex preservation for `gen_idStrictRec`.** -/
theorem HasCertifiedCellDim0.subst0_idStrictRec_preservation
    {profile : PolyProfile} {scope : Nat}
    (rawArg : RawTerm scope)
    (baseCaseTerm identityWitnessTerm : RawTerm (scope + 1))
    (substBaseCaseCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase (RawTerm.subst0 baseCaseTerm rawArg)))
    (substIdentityWitnessCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase (RawTerm.subst0 identityWitnessTerm rawArg))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst0
        ((.mkGen .gen_idStrictRec ()
          (.childCons baseCaseTerm
            (.childCons identityWitnessTerm .childNil)))
          : RawTerm (scope + 1))
        rawArg) := by
  rw [RawTerm.subst0_idStrictRec_reduces]
  exact HasCertifiedCellDim0.idStrictRec substBaseCaseCell
    substIdentityWitnessCell

end FX1Poly.Core
