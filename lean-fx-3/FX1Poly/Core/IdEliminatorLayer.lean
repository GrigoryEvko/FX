import FX1Poly.Core.RemainingDim0Eliminators

/-! # Foundation/PolyCell/Core/IdEliminatorLayer
   — full compositional layer for `idJ` and `idStrictRec`

Full compositional layer for `idJ` and `idStrictRec`.  Both
`gen_idJ` and `gen_idStrictRec` carry the Phase-Z motive shape:
3-child eliminators at `binderShifts [2, 0, 0]` (not flat 2-child
as the legacy substrate).

## Child layout (shared)

`(motive, baseCase, identityWitness)` — the motive a term under
TWO binders (at `scope + 2`: var 1 = the endpoint, var 0 = the
path), the baseCase and identityWitness at the ambient `scope`,
the witness LAST (the principal child).

Semantically:
* `idJ`:          dependent J-eliminator on Id types.  baseCase is
  the motive evaluated at `refl`; identityWitness is the equality.
  The motive is the family being eliminated into; the refl-ι
  DISCARDS it (pure base-case projection).
* `idStrictRec`:  strict (non-dependent) variant of J.  Same shape.

## Contents (20 declarations)

For each of `gen_idJ` and `gen_idStrictRec`, 10 declarations:

  * INTRO (1): build HCC from motive + baseCase + idWitness cells.
  * 3 PROJECTIONS: motive + baseCase + idWitness.
  * Rename probe + preservation (the motive child renamed under the
    DOUBLE-lifted renaming `RawRenaming.lift (RawRenaming.lift …)`).
  * Subst probe + preservation (the motive child substituted under
    the DOUBLE-lifted substitution).
  * Subst0 probe + preservation (the motive child substituted under
    the DOUBLE-lifted singleton).

## Coverage

| Category                    | Generators                                              | Count |
|-----------------------------|---------------------------------------------------------|-------|
| Nullary leaves              | 7                                                       | 7     |
| Compound constructors       | 9                                                       | 9     |
| 1-child eliminators         | fst, snd                                                | 2     |
| 3-child eliminators (idElim)| idJ, idStrictRec (Phase-Z motive shape, shifts [2,0,0]) | **2** |
| 4-child eliminators         | boolElim, natElim, natRec, listElim, optionMatch, eitherMatch | 6 |
| **Total dim-0 surface**     |                                                         | **26** |

All 7 dim-0 eliminators have full compositional support.  The
compositional infrastructure for SR-cong covers all the term-level
shapes that the 16 SR iota arms touch.

## Zero-axiom verification

Same template as `PairEliminatorLayer` (1-child) and the 3-child
eliminator files.  Audit-gated.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation

/-! ## idJ — dependent J-eliminator -/

/-- **Intro: idJ's structural admission from motive + base + witness cells**
(Phase-Z motive shape: the motive head child lives at `scope + 2`, the base case and witness
at the ambient `scope`, the witness LAST). -/
theorem HasCertifiedCellDim0.idJ
    {profile : PolyProfile} {scope : Nat}
    {motiveTerm : RawTerm (scope + 2)}
    {baseCaseTerm identityWitnessTerm : RawTerm scope}
    (motiveCell :
      PolyCell profile .term 0 (scope + 2) CellBoundary.trivial
        (.termBase motiveTerm))
    (baseCaseCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase baseCaseTerm))
    (identityWitnessCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase identityWitnessTerm)) :
    HasCertifiedCellDim0 (profile := profile)
      ((.mkGen .gen_idJ ()
        (.childCons motiveTerm
          (.childCons baseCaseTerm
            (.childCons identityWitnessTerm .childNil)))) : RawTerm scope) :=
  .intro .term
    (PolyCell.gen
      SupportedGenerator.gen_idJ
      (genPayloadEvidence (generator := .gen_idJ)
                           (scope := scope) ())
      (CertifiedTermSpine.cons motiveCell
        (CertifiedTermSpine.cons baseCaseCell
          (CertifiedTermSpine.cons identityWitnessCell
            CertifiedTermSpine.nil))))

/-- **Projection: `gen_idJ` → motive child's cert** (the head child, at `scope + 2`). -/
theorem HasCertifiedCellDim0.idJ_motive_projection
    {profile : PolyProfile} {scope : Nat}
    (motiveTerm : RawTerm (scope + 2))
    (baseCaseTerm identityWitnessTerm : RawTerm scope)
    (cert : HasCertifiedCellDim0 (profile := profile)
              ((.mkGen .gen_idJ ()
                (.childCons motiveTerm
                  (.childCons baseCaseTerm
                    (.childCons identityWitnessTerm .childNil))))
                : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) motiveTerm := by
  obtain ⟨_, cell⟩ := cert
  cases cell with
  | gen _ _ spine =>
    exact ⟨.term, spine.headAtDim0 rfl⟩

/-- **Projection: `gen_idJ` → baseCase child's cert** (child 1). -/
theorem HasCertifiedCellDim0.idJ_baseCase_projection
    {profile : PolyProfile} {scope : Nat}
    (motiveTerm : RawTerm (scope + 2))
    (baseCaseTerm identityWitnessTerm : RawTerm scope)
    (cert : HasCertifiedCellDim0 (profile := profile)
              ((.mkGen .gen_idJ ()
                (.childCons motiveTerm
                  (.childCons baseCaseTerm
                    (.childCons identityWitnessTerm .childNil))))
                : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) baseCaseTerm := by
  obtain ⟨_, cell⟩ := cert
  cases cell with
  | gen _ _ spine =>
    exact ⟨.term, spine.tail.headAtDim0 rfl⟩

/-- **Projection: `gen_idJ` → identityWitness child's cert** (the LAST child, child 2). -/
theorem HasCertifiedCellDim0.idJ_identityWitness_projection
    {profile : PolyProfile} {scope : Nat}
    (motiveTerm : RawTerm (scope + 2))
    (baseCaseTerm identityWitnessTerm : RawTerm scope)
    (cert : HasCertifiedCellDim0 (profile := profile)
              ((.mkGen .gen_idJ ()
                (.childCons motiveTerm
                  (.childCons baseCaseTerm
                    (.childCons identityWitnessTerm .childNil))))
                : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) identityWitnessTerm := by
  obtain ⟨_, cell⟩ := cert
  cases cell with
  | gen _ _ spine =>
    exact ⟨.term, spine.tail.tail.headAtDim0 rfl⟩

/-- **Probe: rename distributes over `gen_idJ`.**  The motive head child (binderShift `2`) renames under
the DOUBLE-lifted renaming `RawRenaming.lift (RawRenaming.lift rawRenaming)`; the two same-scope children
rename under the plain `rawRenaming`. -/
theorem RawTerm.rename_idJ_reduces
    {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (motiveTerm : RawTerm (sourceScope + 2))
    (baseCaseTerm identityWitnessTerm : RawTerm sourceScope) :
    RawTerm.rename rawRenaming
        ((.mkGen .gen_idJ ()
          (.childCons motiveTerm
            (.childCons baseCaseTerm
              (.childCons identityWitnessTerm .childNil))))
          : RawTerm sourceScope) =
      ((.mkGen .gen_idJ ()
        (.childCons (RawTerm.rename (RawRenaming.lift (RawRenaming.lift rawRenaming)) motiveTerm)
          (.childCons (RawTerm.rename rawRenaming baseCaseTerm)
            (.childCons (RawTerm.rename rawRenaming identityWitnessTerm)
              .childNil))))
        : RawTerm targetScope) := rfl

/-- **`idJ` preserved by rename (compositional).** -/
theorem HasCertifiedCellDim0.idJ_preservedByRename
    {profile : PolyProfile} {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (motiveTerm : RawTerm (sourceScope + 2))
    (baseCaseTerm identityWitnessTerm : RawTerm sourceScope)
    (renamedMotiveCell :
      PolyCell profile .term 0 (targetScope + 2) CellBoundary.trivial
        (.termBase (RawTerm.rename (RawRenaming.lift (RawRenaming.lift rawRenaming)) motiveTerm)))
    (renamedBaseCaseCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.rename rawRenaming baseCaseTerm)))
    (renamedIdentityWitnessCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.rename rawRenaming identityWitnessTerm))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.rename rawRenaming
        (.mkGen .gen_idJ ()
          (.childCons motiveTerm
            (.childCons baseCaseTerm
              (.childCons identityWitnessTerm .childNil))))) := by
  rw [RawTerm.rename_idJ_reduces]
  exact HasCertifiedCellDim0.idJ renamedMotiveCell renamedBaseCaseCell renamedIdentityWitnessCell

/-- **Probe: subst distributes over `gen_idJ`.**  The motive head child (binderShift `2`) substitutes
under the DOUBLE-lifted substitution `RawTermSubst.lift (RawTermSubst.lift substitution)`; the two
same-scope children under the plain `substitution`. -/
theorem RawTerm.subst_idJ_reduces
    {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (motiveTerm : RawTerm (sourceScope + 2))
    (baseCaseTerm identityWitnessTerm : RawTerm sourceScope) :
    RawTerm.subst substitution
        ((.mkGen .gen_idJ ()
          (.childCons motiveTerm
            (.childCons baseCaseTerm
              (.childCons identityWitnessTerm .childNil))))
          : RawTerm sourceScope) =
      ((.mkGen .gen_idJ ()
        (.childCons (RawTerm.subst (RawTermSubst.lift (RawTermSubst.lift substitution)) motiveTerm)
          (.childCons (RawTerm.subst substitution baseCaseTerm)
            (.childCons (RawTerm.subst substitution identityWitnessTerm)
              .childNil))))
        : RawTerm targetScope) := rfl

/-- **`idJ` preserved by subst (compositional).** -/
theorem HasCertifiedCellDim0.idJ_preservedBySubst
    {profile : PolyProfile} {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (motiveTerm : RawTerm (sourceScope + 2))
    (baseCaseTerm identityWitnessTerm : RawTerm sourceScope)
    (substMotiveCell :
      PolyCell profile .term 0 (targetScope + 2) CellBoundary.trivial
        (.termBase (RawTerm.subst (RawTermSubst.lift (RawTermSubst.lift substitution)) motiveTerm)))
    (substBaseCaseCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.subst substitution baseCaseTerm)))
    (substIdentityWitnessCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.subst substitution identityWitnessTerm))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst substitution
        (.mkGen .gen_idJ ()
          (.childCons motiveTerm
            (.childCons baseCaseTerm
              (.childCons identityWitnessTerm .childNil))))) := by
  rw [RawTerm.subst_idJ_reduces]
  exact HasCertifiedCellDim0.idJ substMotiveCell substBaseCaseCell substIdentityWitnessCell

/-- **Probe: subst0 distributes over `gen_idJ`.**  The cell lives at `scope + 1`, so its motive head child
lives at `scope + 3`; under subst0 that motive substitutes with the DOUBLE-lifted singleton
`RawTermSubst.lift (RawTermSubst.lift (RawTermSubst.singleton rawArg))`, while the two same-scope children
(at `scope + 1`) use `RawTerm.subst0 … rawArg`. -/
theorem RawTerm.subst0_idJ_reduces
    {scope : Nat} (rawArg : RawTerm scope)
    (motiveTerm : RawTerm (scope + 3))
    (baseCaseTerm identityWitnessTerm : RawTerm (scope + 1)) :
    RawTerm.subst0
        ((.mkGen .gen_idJ ()
          (.childCons motiveTerm
            (.childCons baseCaseTerm
              (.childCons identityWitnessTerm .childNil))))
          : RawTerm (scope + 1))
        rawArg =
      (.mkGen .gen_idJ ()
        (.childCons
          (RawTerm.subst (RawTermSubst.lift (RawTermSubst.lift (RawTermSubst.singleton rawArg))) motiveTerm)
          (.childCons (RawTerm.subst0 baseCaseTerm rawArg)
            (.childCons (RawTerm.subst0 identityWitnessTerm rawArg) .childNil)))
        : RawTerm scope) := rfl

/-- **Beta-redex preservation for `gen_idJ`** (the motive head child substitutes under the double-lifted
singleton, the base case and witness under `subst0`). -/
theorem HasCertifiedCellDim0.subst0_idJ_preservation
    {profile : PolyProfile} {scope : Nat}
    (rawArg : RawTerm scope)
    (motiveTerm : RawTerm (scope + 3))
    (baseCaseTerm identityWitnessTerm : RawTerm (scope + 1))
    (substMotiveCell :
      PolyCell profile .term 0 (scope + 2) CellBoundary.trivial
        (.termBase (RawTerm.subst
          (RawTermSubst.lift (RawTermSubst.lift (RawTermSubst.singleton rawArg))) motiveTerm)))
    (substBaseCaseCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase (RawTerm.subst0 baseCaseTerm rawArg)))
    (substIdentityWitnessCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase (RawTerm.subst0 identityWitnessTerm rawArg))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst0
        ((.mkGen .gen_idJ ()
          (.childCons motiveTerm
            (.childCons baseCaseTerm
              (.childCons identityWitnessTerm .childNil))))
          : RawTerm (scope + 1))
        rawArg) := by
  rw [RawTerm.subst0_idJ_reduces]
  exact HasCertifiedCellDim0.idJ substMotiveCell substBaseCaseCell substIdentityWitnessCell

/-! ## idStrictRec — strict (non-dependent) variant of J -/

/-- **Intro: idStrictRec's structural admission from motive + base + witness cells**
(Phase-Z motive shape: the motive head child lives at `scope + 2`, the base case and witness
at the ambient `scope`, the witness LAST). -/
theorem HasCertifiedCellDim0.idStrictRec
    {profile : PolyProfile} {scope : Nat}
    {motiveTerm : RawTerm (scope + 2)}
    {baseCaseTerm identityWitnessTerm : RawTerm scope}
    (motiveCell :
      PolyCell profile .term 0 (scope + 2) CellBoundary.trivial
        (.termBase motiveTerm))
    (baseCaseCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase baseCaseTerm))
    (identityWitnessCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase identityWitnessTerm)) :
    HasCertifiedCellDim0 (profile := profile)
      ((.mkGen .gen_idStrictRec ()
        (.childCons motiveTerm
          (.childCons baseCaseTerm
            (.childCons identityWitnessTerm .childNil)))) : RawTerm scope) :=
  .intro .term
    (PolyCell.gen
      SupportedGenerator.gen_idStrictRec
      (genPayloadEvidence (generator := .gen_idStrictRec)
                           (scope := scope) ())
      (CertifiedTermSpine.cons motiveCell
        (CertifiedTermSpine.cons baseCaseCell
          (CertifiedTermSpine.cons identityWitnessCell
            CertifiedTermSpine.nil))))

/-- **Projection: `gen_idStrictRec` → motive child's cert** (the head child, at `scope + 2`). -/
theorem HasCertifiedCellDim0.idStrictRec_motive_projection
    {profile : PolyProfile} {scope : Nat}
    (motiveTerm : RawTerm (scope + 2))
    (baseCaseTerm identityWitnessTerm : RawTerm scope)
    (cert : HasCertifiedCellDim0 (profile := profile)
              ((.mkGen .gen_idStrictRec ()
                (.childCons motiveTerm
                  (.childCons baseCaseTerm
                    (.childCons identityWitnessTerm .childNil))))
                : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) motiveTerm := by
  obtain ⟨_, cell⟩ := cert
  cases cell with
  | gen _ _ spine =>
    exact ⟨.term, spine.headAtDim0 rfl⟩

/-- **Projection: `gen_idStrictRec` → baseCase child's cert** (child 1). -/
theorem HasCertifiedCellDim0.idStrictRec_baseCase_projection
    {profile : PolyProfile} {scope : Nat}
    (motiveTerm : RawTerm (scope + 2))
    (baseCaseTerm identityWitnessTerm : RawTerm scope)
    (cert : HasCertifiedCellDim0 (profile := profile)
              ((.mkGen .gen_idStrictRec ()
                (.childCons motiveTerm
                  (.childCons baseCaseTerm
                    (.childCons identityWitnessTerm .childNil))))
                : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) baseCaseTerm := by
  obtain ⟨_, cell⟩ := cert
  cases cell with
  | gen _ _ spine =>
    exact ⟨.term, spine.tail.headAtDim0 rfl⟩

/-- **Projection: `gen_idStrictRec` → identityWitness child's cert** (the LAST child, child 2). -/
theorem HasCertifiedCellDim0.idStrictRec_identityWitness_projection
    {profile : PolyProfile} {scope : Nat}
    (motiveTerm : RawTerm (scope + 2))
    (baseCaseTerm identityWitnessTerm : RawTerm scope)
    (cert : HasCertifiedCellDim0 (profile := profile)
              ((.mkGen .gen_idStrictRec ()
                (.childCons motiveTerm
                  (.childCons baseCaseTerm
                    (.childCons identityWitnessTerm .childNil))))
                : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile) identityWitnessTerm := by
  obtain ⟨_, cell⟩ := cert
  cases cell with
  | gen _ _ spine =>
    exact ⟨.term, spine.tail.tail.headAtDim0 rfl⟩

/-- **Probe: rename distributes over `gen_idStrictRec`.**  The motive head child (binderShift `2`)
renames under the DOUBLE-lifted renaming `RawRenaming.lift (RawRenaming.lift rawRenaming)`; the two
same-scope children rename under the plain `rawRenaming`. -/
theorem RawTerm.rename_idStrictRec_reduces
    {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (motiveTerm : RawTerm (sourceScope + 2))
    (baseCaseTerm identityWitnessTerm : RawTerm sourceScope) :
    RawTerm.rename rawRenaming
        ((.mkGen .gen_idStrictRec ()
          (.childCons motiveTerm
            (.childCons baseCaseTerm
              (.childCons identityWitnessTerm .childNil))))
          : RawTerm sourceScope) =
      ((.mkGen .gen_idStrictRec ()
        (.childCons (RawTerm.rename (RawRenaming.lift (RawRenaming.lift rawRenaming)) motiveTerm)
          (.childCons (RawTerm.rename rawRenaming baseCaseTerm)
            (.childCons (RawTerm.rename rawRenaming identityWitnessTerm)
              .childNil))))
        : RawTerm targetScope) := rfl

/-- **`idStrictRec` preserved by rename (compositional).** -/
theorem HasCertifiedCellDim0.idStrictRec_preservedByRename
    {profile : PolyProfile} {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (motiveTerm : RawTerm (sourceScope + 2))
    (baseCaseTerm identityWitnessTerm : RawTerm sourceScope)
    (renamedMotiveCell :
      PolyCell profile .term 0 (targetScope + 2) CellBoundary.trivial
        (.termBase (RawTerm.rename (RawRenaming.lift (RawRenaming.lift rawRenaming)) motiveTerm)))
    (renamedBaseCaseCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.rename rawRenaming baseCaseTerm)))
    (renamedIdentityWitnessCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.rename rawRenaming identityWitnessTerm))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.rename rawRenaming
        (.mkGen .gen_idStrictRec ()
          (.childCons motiveTerm
            (.childCons baseCaseTerm
              (.childCons identityWitnessTerm .childNil))))) := by
  rw [RawTerm.rename_idStrictRec_reduces]
  exact HasCertifiedCellDim0.idStrictRec renamedMotiveCell renamedBaseCaseCell
    renamedIdentityWitnessCell

/-- **Probe: subst distributes over `gen_idStrictRec`.**  The motive head child (binderShift `2`)
substitutes under the DOUBLE-lifted substitution `RawTermSubst.lift (RawTermSubst.lift substitution)`;
the two same-scope children under the plain `substitution`. -/
theorem RawTerm.subst_idStrictRec_reduces
    {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (motiveTerm : RawTerm (sourceScope + 2))
    (baseCaseTerm identityWitnessTerm : RawTerm sourceScope) :
    RawTerm.subst substitution
        ((.mkGen .gen_idStrictRec ()
          (.childCons motiveTerm
            (.childCons baseCaseTerm
              (.childCons identityWitnessTerm .childNil))))
          : RawTerm sourceScope) =
      ((.mkGen .gen_idStrictRec ()
        (.childCons (RawTerm.subst (RawTermSubst.lift (RawTermSubst.lift substitution)) motiveTerm)
          (.childCons (RawTerm.subst substitution baseCaseTerm)
            (.childCons (RawTerm.subst substitution identityWitnessTerm)
              .childNil))))
        : RawTerm targetScope) := rfl

/-- **`idStrictRec` preserved by subst (compositional).** -/
theorem HasCertifiedCellDim0.idStrictRec_preservedBySubst
    {profile : PolyProfile} {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (motiveTerm : RawTerm (sourceScope + 2))
    (baseCaseTerm identityWitnessTerm : RawTerm sourceScope)
    (substMotiveCell :
      PolyCell profile .term 0 (targetScope + 2) CellBoundary.trivial
        (.termBase (RawTerm.subst (RawTermSubst.lift (RawTermSubst.lift substitution)) motiveTerm)))
    (substBaseCaseCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.subst substitution baseCaseTerm)))
    (substIdentityWitnessCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.subst substitution identityWitnessTerm))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst substitution
        (.mkGen .gen_idStrictRec ()
          (.childCons motiveTerm
            (.childCons baseCaseTerm
              (.childCons identityWitnessTerm .childNil))))) := by
  rw [RawTerm.subst_idStrictRec_reduces]
  exact HasCertifiedCellDim0.idStrictRec substMotiveCell substBaseCaseCell
    substIdentityWitnessCell

/-- **Probe: subst0 distributes over `gen_idStrictRec`.**  The cell lives at `scope + 1`, so its motive
head child lives at `scope + 3`; under subst0 that motive substitutes with the DOUBLE-lifted singleton
`RawTermSubst.lift (RawTermSubst.lift (RawTermSubst.singleton rawArg))`, while the two same-scope children
(at `scope + 1`) use `RawTerm.subst0 … rawArg`. -/
theorem RawTerm.subst0_idStrictRec_reduces
    {scope : Nat} (rawArg : RawTerm scope)
    (motiveTerm : RawTerm (scope + 3))
    (baseCaseTerm identityWitnessTerm : RawTerm (scope + 1)) :
    RawTerm.subst0
        ((.mkGen .gen_idStrictRec ()
          (.childCons motiveTerm
            (.childCons baseCaseTerm
              (.childCons identityWitnessTerm .childNil))))
          : RawTerm (scope + 1))
        rawArg =
      (.mkGen .gen_idStrictRec ()
        (.childCons
          (RawTerm.subst (RawTermSubst.lift (RawTermSubst.lift (RawTermSubst.singleton rawArg))) motiveTerm)
          (.childCons (RawTerm.subst0 baseCaseTerm rawArg)
            (.childCons (RawTerm.subst0 identityWitnessTerm rawArg) .childNil)))
        : RawTerm scope) := rfl

/-- **Beta-redex preservation for `gen_idStrictRec`** (the motive head child substitutes under the
double-lifted singleton, the base case and witness under `subst0`). -/
theorem HasCertifiedCellDim0.subst0_idStrictRec_preservation
    {profile : PolyProfile} {scope : Nat}
    (rawArg : RawTerm scope)
    (motiveTerm : RawTerm (scope + 3))
    (baseCaseTerm identityWitnessTerm : RawTerm (scope + 1))
    (substMotiveCell :
      PolyCell profile .term 0 (scope + 2) CellBoundary.trivial
        (.termBase (RawTerm.subst
          (RawTermSubst.lift (RawTermSubst.lift (RawTermSubst.singleton rawArg))) motiveTerm)))
    (substBaseCaseCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase (RawTerm.subst0 baseCaseTerm rawArg)))
    (substIdentityWitnessCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase (RawTerm.subst0 identityWitnessTerm rawArg))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst0
        ((.mkGen .gen_idStrictRec ()
          (.childCons motiveTerm
            (.childCons baseCaseTerm
              (.childCons identityWitnessTerm .childNil))))
          : RawTerm (scope + 1))
        rawArg) := by
  rw [RawTerm.subst0_idStrictRec_reduces]
  exact HasCertifiedCellDim0.idStrictRec substMotiveCell substBaseCaseCell
    substIdentityWitnessCell

end FX1Poly.Core
