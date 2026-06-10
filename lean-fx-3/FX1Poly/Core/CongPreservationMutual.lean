import FX1Poly.Core.SubstPreservationMutual
import FX1Poly.Core.Step

/-! # Foundation/PolyCell/Core/CongPreservationMutual
   — spine-level core for uniform congruence preservation

The endpoint is `HasCertifiedCellDim0.preservedByCong`, a structural
SR arm.

This layer avoids the Step/StepChildren circularity by
parameterizing the spine recursion over a sort-preserving cell-level
step preserver.  The recursive work over `StepChildren` is real and
generic: one `here` arm rebuilds the stepped head, and one `there`
arm rebuilds the unchanged head plus recursively-preserved tail.

The instantiating layer supplies the parameter with the mutual
`Step` dispatcher (`beta`, `cong`, and the 16 iotas).
-/

namespace FX1Poly.Core

open FX1Poly.Foundation

/-- Prop-packaged exact-sort dim-0 preservation for one `Step`.

This is the instantiable form for the final `Step` / `StepChildren`
mutual proof.  `Step` lives in `Prop`, so the target cell is carried
under an existential in `Prop`, which is strong enough for the final
`HasCertifiedCellDim0` endpoint and for rebuilding spines inside a
Prop-valued proof. -/
def StepCellPreserverWitness (profile : PolyProfile) : Prop :=
  ∀ {scope : Nat} {sort : CellSort}
    {source target : RawTerm scope},
    PolyCell profile sort 0 scope CellBoundary.trivial
      (.termBase source) →
    Step source target →
    ∃ _targetCell :
      PolyCell profile sort 0 scope CellBoundary.trivial
        (.termBase target),
      True

/-- Exact beta preservation at the Prop-packaged `PolyCell` layer.

This is the concrete beta arm needed by the
`StepCellPreserverWitness` mutual dispatcher.  The source app cell
exposes the lambda and argument cells through its certified spine; the
lambda cell exposes the body cell; the structural substitution
driver then certifies `subst0 body rawArg` at the exact `.term` sort. -/
theorem PolyCell.exists_preservedByBeta_dim0
    {profile : PolyProfile} {scope : Nat}
    {domainAnn : RawTerm scope} {body : RawTerm (scope + 1)} {rawArg : RawTerm scope}
    (sourceCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase
          ((.mkGen .gen_app ()
            (.childCons
              (.mkGen .gen_lam () (.childCons domainAnn (.childCons body .childNil)))
              (.childCons rawArg .childNil))) : RawTerm scope))) :
    ∃ _targetCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase (RawTerm.subst0 body rawArg)),
      True := by
  generalize hSourceSort : CellSort.term = sourceSort at sourceCell
  cases sourceCell with
  | gen _ _ sourceSpine =>
      have lamCell :
          PolyCell profile .term 0 scope CellBoundary.trivial
            (.termBase
              ((.mkGen .gen_lam () (.childCons domainAnn (.childCons body .childNil))) :
                RawTerm scope)) :=
        sourceSpine.headAtDim0 rfl
      have argCell :
          PolyCell profile .term 0 scope CellBoundary.trivial
            (.termBase rawArg) :=
        sourceSpine.tail.headAtDim0 rfl
      generalize hLamSort : CellSort.term = lamSort at lamCell
      cases lamCell with
      | gen _ _ lamSpine =>
          let bodyCell :
              PolyCell profile .term 0 (scope + 1) CellBoundary.trivial
                (.termBase body) :=
            lamSpine.tail.headAtDim0 rfl
          exact ⟨
            PolyCell.subst_dim0
              (RawTermSubst.singleton rawArg)
              (PolyCell.singletonSubstDim0Cells rawArg argCell)
              bodyCell,
            True.intro⟩

/-! ## Exact projection iota witnesses

These are the iota arms whose target is already a certified child of
the source spine.  They avoid the sort-existential
`HasCertifiedCellDim0` wrapper and return exact `.term` cells under
`Exists`, making them directly usable by the final Prop-valued
`StepCellPreserverWitness` dispatcher. -/

/-- Exact witness for `boolElim boolTrue thenBranch elseBranch ↝ thenBranch`. -/
theorem PolyCell.exists_preservedByIotaBoolTrue_dim0
    {profile : PolyProfile} {scope : Nat}
    {thenBranch elseBranch : RawTerm scope}
    (sourceCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase
          ((.mkGen .gen_boolElim ()
            (.childCons (.mkGen .gen_boolTrue () .childNil)
              (.childCons thenBranch
                (.childCons elseBranch .childNil)))) : RawTerm scope))) :
    ∃ _targetCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase thenBranch),
      True := by
  generalize hSourceSort : CellSort.term = sourceSort at sourceCell
  cases sourceCell with
  | gen _ _ sourceSpine =>
      exact ⟨sourceSpine.tail.headAtDim0 rfl, True.intro⟩

/-- Exact witness for `boolElim boolFalse thenBranch elseBranch ↝ elseBranch`. -/
theorem PolyCell.exists_preservedByIotaBoolFalse_dim0
    {profile : PolyProfile} {scope : Nat}
    {thenBranch elseBranch : RawTerm scope}
    (sourceCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase
          ((.mkGen .gen_boolElim ()
            (.childCons (.mkGen .gen_boolFalse () .childNil)
              (.childCons thenBranch
                (.childCons elseBranch .childNil)))) : RawTerm scope))) :
    ∃ _targetCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase elseBranch),
      True := by
  generalize hSourceSort : CellSort.term = sourceSort at sourceCell
  cases sourceCell with
  | gen _ _ sourceSpine =>
      exact ⟨sourceSpine.tail.tail.headAtDim0 rfl, True.intro⟩

/-- Exact witness for `fst (pair firstValue secondValue) ↝ firstValue`. -/
theorem PolyCell.exists_preservedByIotaFstPair_dim0
    {profile : PolyProfile} {scope : Nat}
    {firstValue secondValue : RawTerm scope}
    (sourceCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase
          ((.mkGen .gen_fst ()
            (.childCons
              (.mkGen .gen_pair ()
                (.childCons firstValue
                  (.childCons secondValue .childNil)))
              .childNil)) : RawTerm scope))) :
    ∃ _targetCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase firstValue),
      True := by
  generalize hSourceSort : CellSort.term = sourceSort at sourceCell
  cases sourceCell with
  | gen _ _ sourceSpine =>
      have pairCell :
          PolyCell profile .term 0 scope CellBoundary.trivial
            (.termBase
              ((.mkGen .gen_pair ()
                (.childCons firstValue
                  (.childCons secondValue .childNil))) : RawTerm scope)) :=
        sourceSpine.headAtDim0 rfl
      generalize hPairSort : CellSort.term = pairSort at pairCell
      cases pairCell with
      | gen _ _ pairSpine =>
          exact ⟨pairSpine.headAtDim0 rfl, True.intro⟩

/-- Exact witness for `snd (pair firstValue secondValue) ↝ secondValue`. -/
theorem PolyCell.exists_preservedByIotaSndPair_dim0
    {profile : PolyProfile} {scope : Nat}
    {firstValue secondValue : RawTerm scope}
    (sourceCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase
          ((.mkGen .gen_snd ()
            (.childCons
              (.mkGen .gen_pair ()
                (.childCons firstValue
                  (.childCons secondValue .childNil)))
              .childNil)) : RawTerm scope))) :
    ∃ _targetCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase secondValue),
      True := by
  generalize hSourceSort : CellSort.term = sourceSort at sourceCell
  cases sourceCell with
  | gen _ _ sourceSpine =>
      have pairCell :
          PolyCell profile .term 0 scope CellBoundary.trivial
            (.termBase
              ((.mkGen .gen_pair ()
                (.childCons firstValue
                  (.childCons secondValue .childNil))) : RawTerm scope)) :=
        sourceSpine.headAtDim0 rfl
      generalize hPairSort : CellSort.term = pairSort at pairCell
      cases pairCell with
      | gen _ _ pairSpine =>
          exact ⟨pairSpine.tail.headAtDim0 rfl, True.intro⟩

/-- Exact witness for `natElim natZero zeroBranch succBranch ↝ zeroBranch`. -/
theorem PolyCell.exists_preservedByIotaNatElimZero_dim0
    {profile : PolyProfile} {scope : Nat}
    {zeroBranch succBranch : RawTerm scope}
    (sourceCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase
          ((.mkGen .gen_natElim ()
            (.childCons (.mkGen .gen_natZero () .childNil)
              (.childCons zeroBranch
                (.childCons succBranch .childNil)))) : RawTerm scope))) :
    ∃ _targetCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase zeroBranch),
      True := by
  generalize hSourceSort : CellSort.term = sourceSort at sourceCell
  cases sourceCell with
  | gen _ _ sourceSpine =>
      exact ⟨sourceSpine.tail.headAtDim0 rfl, True.intro⟩

/-- Exact witness for `natRec natZero zeroBranch succBranch ↝ zeroBranch`. -/
theorem PolyCell.exists_preservedByIotaNatRecZero_dim0
    {profile : PolyProfile} {scope : Nat}
    {zeroBranch succBranch : RawTerm scope}
    (sourceCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase
          ((.mkGen .gen_natRec ()
            (.childCons (.mkGen .gen_natZero () .childNil)
              (.childCons zeroBranch
                (.childCons succBranch .childNil)))) : RawTerm scope))) :
    ∃ _targetCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase zeroBranch),
      True := by
  generalize hSourceSort : CellSort.term = sourceSort at sourceCell
  cases sourceCell with
  | gen _ _ sourceSpine =>
      exact ⟨sourceSpine.tail.headAtDim0 rfl, True.intro⟩

/-- Exact witness for `listElim listNil nilBranch consBranch ↝ nilBranch`. -/
theorem PolyCell.exists_preservedByIotaListElimNil_dim0
    {profile : PolyProfile} {scope : Nat}
    {nilBranch consBranch : RawTerm scope}
    (sourceCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase
          ((.mkGen .gen_listElim ()
            (.childCons (.mkGen .gen_listNil () .childNil)
              (.childCons nilBranch
                (.childCons consBranch .childNil)))) : RawTerm scope))) :
    ∃ _targetCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase nilBranch),
      True := by
  generalize hSourceSort : CellSort.term = sourceSort at sourceCell
  cases sourceCell with
  | gen _ _ sourceSpine =>
      exact ⟨sourceSpine.tail.headAtDim0 rfl, True.intro⟩

/-- Exact witness for `optionMatch optionNone noneBranch someBranch ↝ noneBranch`. -/
theorem PolyCell.exists_preservedByIotaOptionMatchNone_dim0
    {profile : PolyProfile} {scope : Nat}
    {noneBranch someBranch : RawTerm scope}
    (sourceCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase
          ((.mkGen .gen_optionMatch ()
            (.childCons (.mkGen .gen_optionNone () .childNil)
              (.childCons noneBranch
                (.childCons someBranch .childNil)))) : RawTerm scope))) :
    ∃ _targetCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase noneBranch),
      True := by
  generalize hSourceSort : CellSort.term = sourceSort at sourceCell
  cases sourceCell with
  | gen _ _ sourceSpine =>
      exact ⟨sourceSpine.tail.headAtDim0 rfl, True.intro⟩

/-- Exact witness for `idJ baseCase (refl rawWitness) ↝ baseCase`. -/
theorem PolyCell.exists_preservedByIotaIdJRefl_dim0
    {profile : PolyProfile} {scope : Nat}
    {baseCase rawWitness : RawTerm scope}
    (sourceCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase
          ((.mkGen .gen_idJ ()
            (.childCons baseCase
              (.childCons
                (.mkGen .gen_refl ()
                  (.childCons rawWitness .childNil))
                .childNil))) : RawTerm scope))) :
    ∃ _targetCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase baseCase),
      True := by
  generalize hSourceSort : CellSort.term = sourceSort at sourceCell
  cases sourceCell with
  | gen _ _ sourceSpine =>
      exact ⟨sourceSpine.headAtDim0 rfl, True.intro⟩

/-- Exact witness for `idStrictRec baseCase (refl rawWitness) ↝ baseCase`. -/
theorem PolyCell.exists_preservedByIotaIdStrictRecRefl_dim0
    {profile : PolyProfile} {scope : Nat}
    {baseCase rawWitness : RawTerm scope}
    (sourceCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase
          ((.mkGen .gen_idStrictRec ()
            (.childCons baseCase
              (.childCons
                (.mkGen .gen_refl ()
                  (.childCons rawWitness .childNil))
                .childNil))) : RawTerm scope))) :
    ∃ _targetCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase baseCase),
      True := by
  generalize hSourceSort : CellSort.term = sourceSort at sourceCell
  cases sourceCell with
  | gen _ _ sourceSpine =>
      exact ⟨sourceSpine.headAtDim0 rfl, True.intro⟩

/-! ## Exact compound iota witnesses

These iota arms build a fresh target term from certified children of
the source.  They are the exact-cell counterparts of the existing
`HasCertifiedCellDim0.preservedByIota*` compound proofs, but return a
target cell at sort `.term` directly for the Prop-valued final
`StepCellPreserverWitness` dispatcher. -/

/-- Exact witness for `optionMatch (optionSome value) none some ↝ app some value`. -/
theorem PolyCell.exists_preservedByIotaOptionMatchSome_dim0
    {profile : PolyProfile} {scope : Nat}
    {value noneBranch someBranch : RawTerm scope}
    (sourceCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase
          ((.mkGen .gen_optionMatch ()
            (.childCons
              (.mkGen .gen_optionSome () (.childCons value .childNil))
              (.childCons noneBranch
                (.childCons someBranch .childNil)))) : RawTerm scope))) :
    ∃ _targetCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase
          ((.mkGen .gen_app ()
            (.childCons someBranch
              (.childCons value .childNil))) : RawTerm scope)),
      True := by
  generalize hSourceSort : CellSort.term = sourceSort at sourceCell
  cases sourceCell with
  | gen _ _ sourceSpine =>
      cases sourceSpine with
      | cons optionSomeCell restAfterOptionSome =>
          cases restAfterOptionSome with
          | cons _noneBranchCell restAfterNone =>
              cases restAfterNone with
              | cons someBranchCell _ =>
                  generalize hOptionSort :
                      (ChildSpec.termSameScope.cellSort) = optionSort
                    at optionSomeCell
                  cases optionSomeCell with
                  | gen _ _ optionSomeSpine =>
                      cases optionSomeSpine with
                      | cons valueCell _ =>
                          exact ⟨
                            PolyCell.gen
                              SupportedGenerator.gen_app
                              (genPayloadEvidence (generator := .gen_app)
                                (scope := scope) ())
                              (CertifiedTermSpine.cons someBranchCell
                                (CertifiedTermSpine.cons valueCell
                                  CertifiedTermSpine.nil)),
                            True.intro⟩

/-- Exact witness for `eitherMatch (eitherInl value) left right ↝ app left value`. -/
theorem PolyCell.exists_preservedByIotaEitherMatchInl_dim0
    {profile : PolyProfile} {scope : Nat}
    {value leftBranch rightBranch : RawTerm scope}
    (sourceCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase
          ((.mkGen .gen_eitherMatch ()
            (.childCons
              (.mkGen .gen_eitherInl () (.childCons value .childNil))
              (.childCons leftBranch
                (.childCons rightBranch .childNil)))) : RawTerm scope))) :
    ∃ _targetCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase
          ((.mkGen .gen_app ()
            (.childCons leftBranch
              (.childCons value .childNil))) : RawTerm scope)),
      True := by
  generalize hSourceSort : CellSort.term = sourceSort at sourceCell
  cases sourceCell with
  | gen _ _ sourceSpine =>
      cases sourceSpine with
      | cons eitherInlCell restAfterEitherInl =>
          cases restAfterEitherInl with
          | cons leftBranchCell _restAfterLeft =>
              generalize hEitherSort :
                  (ChildSpec.termSameScope.cellSort) = eitherSort
                at eitherInlCell
              cases eitherInlCell with
              | gen _ _ eitherInlSpine =>
                  cases eitherInlSpine with
                  | cons valueCell _ =>
                      exact ⟨
                        PolyCell.gen
                          SupportedGenerator.gen_app
                          (genPayloadEvidence (generator := .gen_app)
                            (scope := scope) ())
                          (CertifiedTermSpine.cons leftBranchCell
                            (CertifiedTermSpine.cons valueCell
                              CertifiedTermSpine.nil)),
                        True.intro⟩

/-- Exact witness for `eitherMatch (eitherInr value) left right ↝ app right value`. -/
theorem PolyCell.exists_preservedByIotaEitherMatchInr_dim0
    {profile : PolyProfile} {scope : Nat}
    {value leftBranch rightBranch : RawTerm scope}
    (sourceCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase
          ((.mkGen .gen_eitherMatch ()
            (.childCons
              (.mkGen .gen_eitherInr () (.childCons value .childNil))
              (.childCons leftBranch
                (.childCons rightBranch .childNil)))) : RawTerm scope))) :
    ∃ _targetCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase
          ((.mkGen .gen_app ()
            (.childCons rightBranch
              (.childCons value .childNil))) : RawTerm scope)),
      True := by
  generalize hSourceSort : CellSort.term = sourceSort at sourceCell
  cases sourceCell with
  | gen _ _ sourceSpine =>
      cases sourceSpine with
      | cons eitherInrCell restAfterEitherInr =>
          cases restAfterEitherInr with
          | cons _leftBranchCell restAfterLeft =>
              cases restAfterLeft with
              | cons rightBranchCell _ =>
                  generalize hEitherSort :
                      (ChildSpec.termSameScope.cellSort) = eitherSort
                    at eitherInrCell
                  cases eitherInrCell with
                  | gen _ _ eitherInrSpine =>
                      cases eitherInrSpine with
                      | cons valueCell _ =>
                          exact ⟨
                            PolyCell.gen
                              SupportedGenerator.gen_app
                              (genPayloadEvidence (generator := .gen_app)
                                (scope := scope) ())
                              (CertifiedTermSpine.cons rightBranchCell
                                (CertifiedTermSpine.cons valueCell
                                  CertifiedTermSpine.nil)),
                            True.intro⟩

/-- Exact witness for `natElim (natSucc n) z s ↝ app (app s n) (natElim n z s)`. -/
theorem PolyCell.exists_preservedByIotaNatElimSucc_dim0
    {profile : PolyProfile} {scope : Nat}
    {predecessor zeroBranch succBranch : RawTerm scope}
    (sourceCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase
          ((.mkGen .gen_natElim ()
            (.childCons
              (.mkGen .gen_natSucc ()
                (.childCons predecessor .childNil))
              (.childCons zeroBranch
                (.childCons succBranch .childNil)))) : RawTerm scope))) :
    ∃ _targetCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase
          ((.mkGen .gen_app ()
            (.childCons
              (.mkGen .gen_app ()
                (.childCons succBranch
                  (.childCons predecessor .childNil)))
              (.childCons
                (.mkGen .gen_natElim ()
                  (.childCons predecessor
                    (.childCons zeroBranch
                      (.childCons succBranch .childNil))))
                .childNil))) : RawTerm scope)),
      True := by
  generalize hSourceSort : CellSort.term = sourceSort at sourceCell
  cases sourceCell with
  | gen _ _ sourceSpine =>
      cases sourceSpine with
      | cons natSuccCell restAfterNatSucc =>
          cases restAfterNatSucc with
          | cons zeroBranchCell restAfterZero =>
              cases restAfterZero with
              | cons succBranchCell _ =>
                  generalize hNatSuccSort :
                      (ChildSpec.termSameScope.cellSort) = natSuccSort
                    at natSuccCell
                  cases natSuccCell with
                  | gen _ _ natSuccSpine =>
                      cases natSuccSpine with
                      | cons predecessorCell _ =>
                          let innerAppCell :
                              PolyCell profile .term 0 scope
                                CellBoundary.trivial
                                (.termBase
                                  ((.mkGen .gen_app ()
                                    (.childCons succBranch
                                      (.childCons predecessor
                                        .childNil))) : RawTerm scope)) :=
                            PolyCell.gen
                              SupportedGenerator.gen_app
                              (genPayloadEvidence (generator := .gen_app)
                                (scope := scope) ())
                              (CertifiedTermSpine.cons succBranchCell
                                (CertifiedTermSpine.cons predecessorCell
                                  CertifiedTermSpine.nil))
                          let recursiveNatElimCell :
                              PolyCell profile .term 0 scope
                                CellBoundary.trivial
                                (.termBase
                                  ((.mkGen .gen_natElim ()
                                    (.childCons predecessor
                                      (.childCons zeroBranch
                                        (.childCons succBranch
                                          .childNil)))) :
                                    RawTerm scope)) :=
                            PolyCell.gen
                              SupportedGenerator.gen_natElim
                              (genPayloadEvidence
                                (generator := .gen_natElim)
                                (scope := scope) ())
                              (CertifiedTermSpine.cons predecessorCell
                                (CertifiedTermSpine.cons zeroBranchCell
                                  (CertifiedTermSpine.cons succBranchCell
                                    CertifiedTermSpine.nil)))
                          exact ⟨
                            PolyCell.gen
                              SupportedGenerator.gen_app
                              (genPayloadEvidence (generator := .gen_app)
                                (scope := scope) ())
                              (CertifiedTermSpine.cons innerAppCell
                                (CertifiedTermSpine.cons
                                  recursiveNatElimCell
                                  CertifiedTermSpine.nil)),
                            True.intro⟩

/-- Exact witness for `natRec (natSucc n) z s ↝ app (app s n) (natRec n z s)`. -/
theorem PolyCell.exists_preservedByIotaNatRecSucc_dim0
    {profile : PolyProfile} {scope : Nat}
    {predecessor zeroBranch succBranch : RawTerm scope}
    (sourceCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase
          ((.mkGen .gen_natRec ()
            (.childCons
              (.mkGen .gen_natSucc ()
                (.childCons predecessor .childNil))
              (.childCons zeroBranch
                (.childCons succBranch .childNil)))) : RawTerm scope))) :
    ∃ _targetCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase
          ((.mkGen .gen_app ()
            (.childCons
              (.mkGen .gen_app ()
                (.childCons succBranch
                  (.childCons predecessor .childNil)))
              (.childCons
                (.mkGen .gen_natRec ()
                  (.childCons predecessor
                    (.childCons zeroBranch
                      (.childCons succBranch .childNil))))
                .childNil))) : RawTerm scope)),
      True := by
  generalize hSourceSort : CellSort.term = sourceSort at sourceCell
  cases sourceCell with
  | gen _ _ sourceSpine =>
      cases sourceSpine with
      | cons natSuccCell restAfterNatSucc =>
          cases restAfterNatSucc with
          | cons zeroBranchCell restAfterZero =>
              cases restAfterZero with
              | cons succBranchCell _ =>
                  generalize hNatSuccSort :
                      (ChildSpec.termSameScope.cellSort) = natSuccSort
                    at natSuccCell
                  cases natSuccCell with
                  | gen _ _ natSuccSpine =>
                      cases natSuccSpine with
                      | cons predecessorCell _ =>
                          let innerAppCell :
                              PolyCell profile .term 0 scope
                                CellBoundary.trivial
                                (.termBase
                                  ((.mkGen .gen_app ()
                                    (.childCons succBranch
                                      (.childCons predecessor
                                        .childNil))) : RawTerm scope)) :=
                            PolyCell.gen
                              SupportedGenerator.gen_app
                              (genPayloadEvidence (generator := .gen_app)
                                (scope := scope) ())
                              (CertifiedTermSpine.cons succBranchCell
                                (CertifiedTermSpine.cons predecessorCell
                                  CertifiedTermSpine.nil))
                          let recursiveNatRecCell :
                              PolyCell profile .term 0 scope
                                CellBoundary.trivial
                                (.termBase
                                  ((.mkGen .gen_natRec ()
                                    (.childCons predecessor
                                      (.childCons zeroBranch
                                        (.childCons succBranch
                                          .childNil)))) :
                                    RawTerm scope)) :=
                            PolyCell.gen
                              SupportedGenerator.gen_natRec
                              (genPayloadEvidence
                                (generator := .gen_natRec)
                                (scope := scope) ())
                              (CertifiedTermSpine.cons predecessorCell
                                (CertifiedTermSpine.cons zeroBranchCell
                                  (CertifiedTermSpine.cons succBranchCell
                                    CertifiedTermSpine.nil)))
                          exact ⟨
                            PolyCell.gen
                              SupportedGenerator.gen_app
                              (genPayloadEvidence (generator := .gen_app)
                                (scope := scope) ())
                              (CertifiedTermSpine.cons innerAppCell
                                (CertifiedTermSpine.cons
                                  recursiveNatRecCell
                                  CertifiedTermSpine.nil)),
                            True.intro⟩

/-- Exact witness for `listElim (listCons h t) n c ↝ app (app (app c h) t) (listElim t n c)`. -/
theorem PolyCell.exists_preservedByIotaListElimCons_dim0
    {profile : PolyProfile} {scope : Nat}
    {headVal tailVal nilBranch consBranch : RawTerm scope}
    (sourceCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase
          ((.mkGen .gen_listElim ()
            (.childCons
              (.mkGen .gen_listCons ()
                (.childCons headVal
                  (.childCons tailVal .childNil)))
              (.childCons nilBranch
                (.childCons consBranch .childNil)))) : RawTerm scope))) :
    ∃ _targetCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase
          ((.mkGen .gen_app ()
            (.childCons
              (.mkGen .gen_app ()
                (.childCons
                  (.mkGen .gen_app ()
                    (.childCons consBranch
                      (.childCons headVal .childNil)))
                  (.childCons tailVal .childNil)))
              (.childCons
                (.mkGen .gen_listElim ()
                  (.childCons tailVal
                    (.childCons nilBranch
                      (.childCons consBranch .childNil))))
                .childNil))) : RawTerm scope)),
      True := by
  generalize hSourceSort : CellSort.term = sourceSort at sourceCell
  cases sourceCell with
  | gen _ _ sourceSpine =>
      cases sourceSpine with
      | cons listConsCell restAfterListCons =>
          cases restAfterListCons with
          | cons nilBranchCell restAfterNil =>
              cases restAfterNil with
              | cons consBranchCell _ =>
                  generalize hListConsSort :
                      (ChildSpec.termSameScope.cellSort) = listConsSort
                    at listConsCell
                  cases listConsCell with
                  | gen _ _ listConsSpine =>
                      cases listConsSpine with
                      | cons headValCell restAfterHead =>
                          cases restAfterHead with
                          | cons tailValCell _ =>
                              let firstAppCell :
                                  PolyCell profile .term 0 scope
                                    CellBoundary.trivial
                                    (.termBase
                                      ((.mkGen .gen_app ()
                                        (.childCons consBranch
                                          (.childCons headVal
                                            .childNil))) :
                                        RawTerm scope)) :=
                                PolyCell.gen
                                  SupportedGenerator.gen_app
                                  (genPayloadEvidence
                                    (generator := .gen_app)
                                    (scope := scope) ())
                                  (CertifiedTermSpine.cons
                                    consBranchCell
                                    (CertifiedTermSpine.cons
                                      headValCell
                                      CertifiedTermSpine.nil))
                              let secondAppCell :
                                  PolyCell profile .term 0 scope
                                    CellBoundary.trivial
                                    (.termBase
                                      ((.mkGen .gen_app ()
                                        (.childCons
                                          (.mkGen .gen_app ()
                                            (.childCons consBranch
                                              (.childCons headVal
                                                .childNil)))
                                          (.childCons tailVal
                                            .childNil))) :
                                        RawTerm scope)) :=
                                PolyCell.gen
                                  SupportedGenerator.gen_app
                                  (genPayloadEvidence
                                    (generator := .gen_app)
                                    (scope := scope) ())
                                  (CertifiedTermSpine.cons
                                    firstAppCell
                                    (CertifiedTermSpine.cons
                                      tailValCell
                                      CertifiedTermSpine.nil))
                              let recursiveListElimCell :
                                  PolyCell profile .term 0 scope
                                    CellBoundary.trivial
                                    (.termBase
                                      ((.mkGen .gen_listElim ()
                                        (.childCons tailVal
                                          (.childCons nilBranch
                                            (.childCons consBranch
                                              .childNil)))) :
                                        RawTerm scope)) :=
                                PolyCell.gen
                                  SupportedGenerator.gen_listElim
                                  (genPayloadEvidence
                                    (generator := .gen_listElim)
                                    (scope := scope) ())
                                  (CertifiedTermSpine.cons
                                    tailValCell
                                    (CertifiedTermSpine.cons
                                      nilBranchCell
                                      (CertifiedTermSpine.cons
                                        consBranchCell
                                        CertifiedTermSpine.nil)))
                              exact ⟨
                                PolyCell.gen
                                  SupportedGenerator.gen_app
                                  (genPayloadEvidence
                                    (generator := .gen_app)
                                    (scope := scope) ())
                                  (CertifiedTermSpine.cons
                                    secondAppCell
                                    (CertifiedTermSpine.cons
                                      recursiveListElimCell
                                      CertifiedTermSpine.nil)),
                                True.intro⟩

/-- Prop-packaged preservation of a certified child spine across a
`StepChildren` witness, using a Prop-valued exact-sort step preserver.

This is the version the mutual proof instantiates.  The `here` arm
obtains its stepped head cell from a Prop existential, which composes
with the Prop-valued `StepChildren` recursion. -/
theorem CertifiedTermSpine.exists_preservedByChildStep_via_stepPreserverWitness
    {profile : PolyProfile} {parentScope : Nat} {binderShifts : List Nat}
    {children children' : RawTermChildren binderShifts parentScope}
    (stepPreserver : StepCellPreserverWitness profile)
    (childStep : StepChildren children children') :
    ∀ {childSpecs : List ChildSpec},
    (specShiftsMatch :
      childSpecs.map ChildSpec.scopeShift = binderShifts) →
    (allChildrenDim0 :
      ∀ childSpec ∈ childSpecs, childSpec.cellDimension = 0) →
    (sourceSpine :
      CertifiedTermSpine profile childSpecs parentScope binderShifts
        children) →
    ∃ _targetSpine :
        CertifiedTermSpine profile childSpecs parentScope binderShifts
          children',
        True := by
  refine StepChildren.rec
    (motive_1 := fun {_scope} _source _target _step => True)
    (motive_2 := fun {parentScope} {binderShifts} children children' _childStep =>
      ∀ {childSpecs : List ChildSpec},
      (specShiftsMatch :
        childSpecs.map ChildSpec.scopeShift = binderShifts) →
      (allChildrenDim0 :
        ∀ childSpec ∈ childSpecs, childSpec.cellDimension = 0) →
      (sourceSpine :
        CertifiedTermSpine profile childSpecs parentScope binderShifts
          children) →
      ∃ _targetSpine :
        CertifiedTermSpine profile childSpecs parentScope binderShifts
          children',
        True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ childStep
  all_goals try
    (intros
     exact True.intro)
  · intro _childParentScope _headShift _restShifts
      _headRaw _headRawAfter restRaws headStep _headStepMotive
    intro childSpecs specShiftsMatch allChildrenDim0 sourceSpine
    cases childSpecs with
    | nil =>
        cases specShiftsMatch
    | cons headSpec restSpecs =>
        injection specShiftsMatch with headShiftEq restShiftsEq
        cases headShiftEq
        cases sourceSpine with
        | cons headCell restSpine =>
            let headDim0 :
                headSpec.cellDimension = 0 :=
              allChildrenDim0 headSpec List.mem_cons_self
            let headCellDim0 :=
              CertifiedTermSpine.headAtDim0 headDim0
                (CertifiedTermSpine.cons headCell restSpine)
            obtain ⟨preservedHeadCell, _⟩ :=
              stepPreserver
                (scope := _childParentScope + headSpec.scopeShift)
                headCellDim0
                headStep
            exact ⟨
                CertifiedTermSpine.consStep_dim0Trivial
                  (profile := profile)
                  (parentScope := _childParentScope)
                  (headSpec := headSpec)
                  (restSpecs := restSpecs)
                  headDim0
                  preservedHeadCell
                  restSpine,
              True.intro⟩
  · intro _childParentScope _headShift _restShifts
      headRaw _restRaws _restRawsAfter restStep preservedRest
    intro childSpecs specShiftsMatch allChildrenDim0 sourceSpine
    cases childSpecs with
    | nil =>
        cases specShiftsMatch
    | cons headSpec restSpecs =>
        injection specShiftsMatch with headShiftEq restShiftsEq
        cases headShiftEq
        cases sourceSpine with
        | cons headCell restSpine =>
            let headDim0 :
                headSpec.cellDimension = 0 :=
              allChildrenDim0 headSpec List.mem_cons_self
            let restChildrenDim0 :
                ∀ childSpec ∈ restSpecs, childSpec.cellDimension = 0 :=
              fun childSpec childSpecMem =>
                allChildrenDim0 childSpec
                  (List.mem_cons_of_mem headSpec childSpecMem)
            let headCellDim0 :=
              CertifiedTermSpine.headAtDim0 headDim0
                (CertifiedTermSpine.cons headCell restSpine)
            obtain ⟨preservedRestSpine, _⟩ :=
              preservedRest
                (childSpecs := restSpecs)
                restShiftsEq
                restChildrenDim0
                restSpine
            exact ⟨
                CertifiedTermSpine.consStep_dim0Trivial
                  (profile := profile)
                  (parentScope := _childParentScope)
                  (headSpec := headSpec)
                  (restSpecs := restSpecs)
                  headDim0
                  headCellDim0
                  preservedRestSpine,
              True.intro⟩

/-- Parent-level congruence preservation, parameterized by the
Prop-valued exact-sort step preserver used for the stepped child. -/
theorem HasCertifiedCellDim0.preservedByCong_via_stepPreserverWitness
    {profile : PolyProfile} {scope : Nat}
    (stepPreserver : StepCellPreserverWitness profile)
    {generator : Generator} {payload : generator.payload scope}
    {children children' : RawTermChildren generator.binderShifts scope}
    (childStep : StepChildren children children')
    (sourceCert : HasCertifiedCellDim0 (profile := profile)
      (.mkGen generator payload children)) :
    HasCertifiedCellDim0 (profile := profile)
      (.mkGen generator payload children') := by
  cases sourceCert with
  | intro _sourceSort sourceCell =>
      cases sourceCell with
      | gen admission payloadEvidence childSpine =>
          obtain ⟨targetSpine, _⟩ :=
            CertifiedTermSpine.exists_preservedByChildStep_via_stepPreserverWitness
              (profile := profile)
              (stepPreserver := stepPreserver)
              (childStep := childStep)
              (childSpecs := generator.childSpecs)
              (Generator.childSpecs_scopeShifts_eq_binderShifts generator)
              (Generator.childSpecs_cellDimension_zero generator)
              (sourceSpine := childSpine)
          exact .intro generator.cellSort
            (PolyCell.gen
              admission
              payloadEvidence
              targetSpine)

/-- Prop-valued exact-sort preserver for every `Step`.

This is the mutual core: the `Step` motive proves exact cell
preservation, while the `StepChildren` motive proves certified-spine
preservation.  The `cong` arm consumes the `StepChildren` motive
directly, avoiding the invalid Prop-to-Type elimination route. -/
theorem StepCellPreserverWitness.polyCell (profile : PolyProfile) :
    StepCellPreserverWitness profile := by
  intro scope sort source target sourceCell stepRel
  exact
    (Step.rec
      (motive_1 := fun {scope} source target _stepRel =>
        ∀ {sort : CellSort},
          PolyCell profile sort 0 scope CellBoundary.trivial
            (.termBase source) →
          ∃ _targetCell :
            PolyCell profile sort 0 scope CellBoundary.trivial
              (.termBase target),
            True)
      (motive_2 := fun {parentScope} {binderShifts}
          children children' _childStep =>
        ∀ {childSpecs : List ChildSpec},
          (specShiftsMatch :
            childSpecs.map ChildSpec.scopeShift = binderShifts) →
          (allChildrenDim0 :
            ∀ childSpec ∈ childSpecs, childSpec.cellDimension = 0) →
          (sourceSpine :
            CertifiedTermSpine profile childSpecs parentScope binderShifts
              children) →
          ∃ _targetSpine :
            CertifiedTermSpine profile childSpecs parentScope binderShifts
              children',
            True)
      (beta := by
        intro _scope _domainAnn _body _arg _sort sourceCell
        cases sourceCell with
        | gen admission payloadEvidence sourceSpine =>
            exact PolyCell.exists_preservedByBeta_dim0
              (PolyCell.gen admission payloadEvidence sourceSpine))
      (cong := by
        intro _scope generator _payload _children _children'
          _childStep preservedChildren
        intro _sort sourceCell
        cases sourceCell with
        | gen admission payloadEvidence childSpine =>
            obtain ⟨targetSpine, _⟩ :=
              preservedChildren
                (childSpecs := generator.childSpecs)
                (Generator.childSpecs_scopeShifts_eq_binderShifts
                  generator)
                (Generator.childSpecs_cellDimension_zero generator)
                childSpine
            exact ⟨
              PolyCell.gen admission payloadEvidence targetSpine,
              True.intro⟩)
      (iotaBoolTrue := by
        intro _scope _thenBranch _elseBranch _sort sourceCell
        cases sourceCell with
        | gen admission payloadEvidence sourceSpine =>
            exact PolyCell.exists_preservedByIotaBoolTrue_dim0
              (PolyCell.gen admission payloadEvidence sourceSpine))
      (iotaBoolFalse := by
        intro _scope _thenBranch _elseBranch _sort sourceCell
        cases sourceCell with
        | gen admission payloadEvidence sourceSpine =>
            exact PolyCell.exists_preservedByIotaBoolFalse_dim0
              (PolyCell.gen admission payloadEvidence sourceSpine))
      (iotaFstPair := by
        intro _scope _firstValue _secondValue _sort sourceCell
        cases sourceCell with
        | gen admission payloadEvidence sourceSpine =>
            exact PolyCell.exists_preservedByIotaFstPair_dim0
              (PolyCell.gen admission payloadEvidence sourceSpine))
      (iotaSndPair := by
        intro _scope _firstValue _secondValue _sort sourceCell
        cases sourceCell with
        | gen admission payloadEvidence sourceSpine =>
            exact PolyCell.exists_preservedByIotaSndPair_dim0
              (PolyCell.gen admission payloadEvidence sourceSpine))
      (iotaNatElimZero := by
        intro _scope _zeroBranch _succBranch _sort sourceCell
        cases sourceCell with
        | gen admission payloadEvidence sourceSpine =>
            exact PolyCell.exists_preservedByIotaNatElimZero_dim0
              (PolyCell.gen admission payloadEvidence sourceSpine))
      (iotaNatRecZero := by
        intro _scope _zeroBranch _succBranch _sort sourceCell
        cases sourceCell with
        | gen admission payloadEvidence sourceSpine =>
            exact PolyCell.exists_preservedByIotaNatRecZero_dim0
              (PolyCell.gen admission payloadEvidence sourceSpine))
      (iotaListElimNil := by
        intro _scope _nilBranch _consBranch _sort sourceCell
        cases sourceCell with
        | gen admission payloadEvidence sourceSpine =>
            exact PolyCell.exists_preservedByIotaListElimNil_dim0
              (PolyCell.gen admission payloadEvidence sourceSpine))
      (iotaOptionMatchNone := by
        intro _scope _noneBranch _someBranch _sort sourceCell
        cases sourceCell with
        | gen admission payloadEvidence sourceSpine =>
            exact PolyCell.exists_preservedByIotaOptionMatchNone_dim0
              (PolyCell.gen admission payloadEvidence sourceSpine))
      (iotaOptionMatchSome := by
        intro _scope _value _noneBranch _someBranch _sort sourceCell
        cases sourceCell with
        | gen admission payloadEvidence sourceSpine =>
            exact PolyCell.exists_preservedByIotaOptionMatchSome_dim0
              (PolyCell.gen admission payloadEvidence sourceSpine))
      (iotaEitherMatchInl := by
        intro _scope _value _leftBranch _rightBranch _sort sourceCell
        cases sourceCell with
        | gen admission payloadEvidence sourceSpine =>
            exact PolyCell.exists_preservedByIotaEitherMatchInl_dim0
              (PolyCell.gen admission payloadEvidence sourceSpine))
      (iotaEitherMatchInr := by
        intro _scope _value _leftBranch _rightBranch _sort sourceCell
        cases sourceCell with
        | gen admission payloadEvidence sourceSpine =>
            exact PolyCell.exists_preservedByIotaEitherMatchInr_dim0
              (PolyCell.gen admission payloadEvidence sourceSpine))
      (iotaNatElimSucc := by
        intro _scope _predecessor _zeroBranch _succBranch _sort sourceCell
        cases sourceCell with
        | gen admission payloadEvidence sourceSpine =>
            exact PolyCell.exists_preservedByIotaNatElimSucc_dim0
              (PolyCell.gen admission payloadEvidence sourceSpine))
      (iotaNatRecSucc := by
        intro _scope _predecessor _zeroBranch _succBranch _sort sourceCell
        cases sourceCell with
        | gen admission payloadEvidence sourceSpine =>
            exact PolyCell.exists_preservedByIotaNatRecSucc_dim0
              (PolyCell.gen admission payloadEvidence sourceSpine))
      (iotaListElimCons := by
        intro _scope _headVal _tailVal _nilBranch _consBranch _sort
          sourceCell
        cases sourceCell with
        | gen admission payloadEvidence sourceSpine =>
            exact PolyCell.exists_preservedByIotaListElimCons_dim0
              (PolyCell.gen admission payloadEvidence sourceSpine))
      (iotaIdJRefl := by
        intro _scope _baseCase _rawWitness _sort sourceCell
        cases sourceCell with
        | gen admission payloadEvidence sourceSpine =>
            exact PolyCell.exists_preservedByIotaIdJRefl_dim0
              (PolyCell.gen admission payloadEvidence sourceSpine))
      (iotaIdStrictRecRefl := by
        intro _scope _baseCase _rawWitness _sort sourceCell
        cases sourceCell with
        | gen admission payloadEvidence sourceSpine =>
            exact PolyCell.exists_preservedByIotaIdStrictRecRefl_dim0
              (PolyCell.gen admission payloadEvidence sourceSpine))
      (here := by
        intro parentScope _headShift _restShifts _head _head'
          _rest _childStep preservedHead
        intro childSpecs specShiftsMatch allChildrenDim0 sourceSpine
        cases childSpecs with
        | nil => cases specShiftsMatch
        | cons headSpec restSpecs =>
            injection specShiftsMatch with headShiftEq restShiftsEq
            cases headShiftEq
            cases sourceSpine with
            | cons headCell restSpine =>
                let headDim0 : headSpec.cellDimension = 0 :=
                  allChildrenDim0 headSpec List.mem_cons_self
                let headCellDim0 :=
                  CertifiedTermSpine.headAtDim0 headDim0
                    (CertifiedTermSpine.cons headCell restSpine)
                obtain ⟨preservedHeadCell, _⟩ :=
                  preservedHead headCellDim0
                exact ⟨
                  CertifiedTermSpine.consStep_dim0Trivial
                    (profile := profile)
                    (parentScope := parentScope)
                    (headSpec := headSpec)
                    (restSpecs := restSpecs)
                    headDim0
                    preservedHeadCell
                    restSpine,
                  True.intro⟩)
      (there := by
        intro parentScope _headShift _restShifts _head _rest _rest'
          _restStep preservedRest
        intro childSpecs specShiftsMatch allChildrenDim0 sourceSpine
        cases childSpecs with
        | nil => cases specShiftsMatch
        | cons headSpec restSpecs =>
            injection specShiftsMatch with headShiftEq restShiftsEq
            cases headShiftEq
            cases sourceSpine with
            | cons headCell restSpine =>
                let headDim0 : headSpec.cellDimension = 0 :=
                  allChildrenDim0 headSpec List.mem_cons_self
                let restChildrenDim0 :
                    ∀ childSpec ∈ restSpecs,
                      childSpec.cellDimension = 0 :=
                  fun childSpec childSpecMem =>
                    allChildrenDim0 childSpec
                      (List.mem_cons_of_mem headSpec childSpecMem)
                let headCellDim0 :=
                  CertifiedTermSpine.headAtDim0 headDim0
                    (CertifiedTermSpine.cons headCell restSpine)
                obtain ⟨preservedRestSpine, _⟩ :=
                  preservedRest
                    (childSpecs := restSpecs)
                    restShiftsEq
                    restChildrenDim0
                    restSpine
                exact ⟨
                  CertifiedTermSpine.consStep_dim0Trivial
                    (profile := profile)
                    (parentScope := parentScope)
                    (headSpec := headSpec)
                    (restSpecs := restSpecs)
                    headDim0
                    headCellDim0
                    preservedRestSpine,
                  True.intro⟩)
      stepRel)
      sourceCell

/-- Public Prop-level spine preservation using the final mutual
`StepCellPreserverWitness`. -/
theorem CertifiedTermSpine.exists_preservedByChildStep
    {profile : PolyProfile} {parentScope : Nat} {binderShifts : List Nat}
    {children children' : RawTermChildren binderShifts parentScope}
    (childStep : StepChildren children children') :
    ∀ {childSpecs : List ChildSpec},
    (specShiftsMatch :
      childSpecs.map ChildSpec.scopeShift = binderShifts) →
    (allChildrenDim0 :
      ∀ childSpec ∈ childSpecs, childSpec.cellDimension = 0) →
    (sourceSpine :
      CertifiedTermSpine profile childSpecs parentScope binderShifts
        children) →
    ∃ _targetSpine :
        CertifiedTermSpine profile childSpecs parentScope binderShifts
          children',
        True :=
  CertifiedTermSpine.exists_preservedByChildStep_via_stepPreserverWitness
    (profile := profile)
    (stepPreserver := StepCellPreserverWitness.polyCell profile)
    (childStep := childStep)

/-- SR arm: uniform congruence preservation for any generator
whose child spine takes one `StepChildren` step. -/
theorem HasCertifiedCellDim0.preservedByCong
    {profile : PolyProfile} {scope : Nat}
    {generator : Generator} {payload : generator.payload scope}
    {children children' : RawTermChildren generator.binderShifts scope}
    (childStep : StepChildren children children')
    (sourceCert : HasCertifiedCellDim0 (profile := profile)
      (.mkGen generator payload children)) :
    HasCertifiedCellDim0 (profile := profile)
      (.mkGen generator payload children') :=
  HasCertifiedCellDim0.preservedByCong_via_stepPreserverWitness
    (profile := profile)
    (stepPreserver := StepCellPreserverWitness.polyCell profile)
    childStep
    sourceCert

end FX1Poly.Core
