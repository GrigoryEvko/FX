import FX1Poly.Core.CellNonVarStepRenamer
import FX1Poly.Core.CellNonVarStepSubstituter
import FX1Poly.Core.SpineRenameStep
import FX1Poly.Core.SpineSubstStep
import FX1Poly.Core.StructuralInductionWrapper
import FX1Poly.Core.BetaRedexEndToEnd

/-! # Foundation/PolyCell/Core/SubstPreservationMutual
   — generic structural preservation drivers for rename/subst

The structural-induction block for rename/subst preservation over the
certified cell/spine mutual structure:

* rename half: `PolyCell.rename_dim0`, `CertifiedTermSpine.rename_dim0`
* subst half:  `PolyCell.subst_dim0`,  `CertifiedTermSpine.subst_dim0`

These definitions drive the non-recursive step helpers as a real
recursion.  The substitution half depends on the rename half to certify
lifted substitutions under binders, because `RawTermSubst.lift` weakens
old substituents, and weakening is rawRenaming by `RawRenaming.weaken`.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation

mutual

/-- Rename a certified dim-0 cell structurally.

The var case uses the dedicated var step.  The non-var case recurses
through the certified child spine and rebuilds the parent with
`PolyCell.rename_dim0_nonVarStep`. -/
def PolyCell.rename_dim0
    {profile : PolyProfile} {srcScope tgtScope : Nat}
    (rawRenaming : RawRenaming srcScope tgtScope)
    {sort : CellSort} {source : RawTerm srcScope}
    (sourceCell :
      PolyCell profile sort 0 srcScope CellBoundary.trivial
        (.termBase source)) :
    PolyCell profile sort 0 tgtScope CellBoundary.trivial
      (.termBase (RawTerm.rename rawRenaming source)) :=
  match source with
  | .mkGen generator payload children =>
    match sourceCell with
    | .gen admission _payloadEvidence childSpine =>
      if isVarGenerator : generator = .gen_var then
        by
          subst isVarGenerator
          cases children with
          | childNil =>
              exact PolyCell.rename_dim0_varStep rawRenaming payload
      else
        PolyCell.rename_dim0_nonVarStep
          (profile := profile)
          (srcScope := srcScope)
          (tgtScope := tgtScope)
          rawRenaming
          isVarGenerator
          payload
          children
          admission
          (CertifiedTermSpine.rename_dim0
            (profile := profile)
            rawRenaming
            (Generator.childSpecs_cellDimension_zero generator)
            childSpine)

/-- Rename a certified term-spine structurally.

The `allChildrenDim0` hypothesis is exactly the profile invariant
needed to collapse each cons head's boundary to the dim-0 trivial
boundary before calling `PolyCell.rename_dim0`.  For generator spines
callers pass `Generator.childSpecs_cellDimension_zero generator`. -/
def CertifiedTermSpine.rename_dim0
    {profile : PolyProfile} {srcScope tgtScope : Nat}
    (rawRenaming : RawRenaming srcScope tgtScope)
    {childSpecs : List ChildSpec} {binderShifts : List Nat}
    {children : RawTermChildren binderShifts srcScope}
    (allChildrenDim0 :
      ∀ childSpec ∈ childSpecs, childSpec.cellDimension = 0)
    (sourceSpine :
      CertifiedTermSpine profile childSpecs srcScope binderShifts
        children) :
    CertifiedTermSpine profile childSpecs tgtScope binderShifts
      (foldChildren GenAlgebra.canonical rawRenaming children) :=
  match sourceSpine with
  | .nil =>
      CertifiedTermSpine.renameNilStep rawRenaming
  | .cons (headSpec := headSpec) (restSpecs := restSpecs)
      (restShifts := restShifts) (headRaw := headRaw)
      (restRaws := restRaws) headCell restSpine =>
      let headDim0 :
          headSpec.cellDimension = 0 :=
        allChildrenDim0 headSpec List.mem_cons_self
      let restChildrenDim0 :
          ∀ childSpec ∈ restSpecs, childSpec.cellDimension = 0 :=
        fun childSpec childSpecMem =>
          allChildrenDim0 childSpec
            (List.mem_cons_of_mem headSpec childSpecMem)
      let headCellDim0 :
          PolyCell profile headSpec.cellSort 0
            (srcScope + headSpec.scopeShift) CellBoundary.trivial
            (.termBase headRaw) :=
        CertifiedTermSpine.headAtDim0 headDim0
          (CertifiedTermSpine.cons headCell restSpine)
      CertifiedTermSpine.renameConsStep_dim0Trivial
        (profile := profile)
        (srcScope := srcScope)
        (tgtScope := tgtScope)
        (headSpec := headSpec)
        (restSpecs := restSpecs)
        (restShifts := restShifts)
        headDim0
        rawRenaming
        (PolyCell.rename_dim0
          (iterateLiftRaw rawRenaming headSpec.scopeShift)
          headCellDim0)
        (CertifiedTermSpine.rename_dim0
          (profile := profile)
          rawRenaming
          restChildrenDim0
          restSpine)

end

/-- Public HCC-level generic rename preservation. -/
theorem HasCertifiedCellDim0.preservedByRename
    {profile : PolyProfile} {srcScope tgtScope : Nat}
    (rawRenaming : RawRenaming srcScope tgtScope)
    {source : RawTerm srcScope}
    (sourceCert : HasCertifiedCellDim0 (profile := profile) source) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.rename rawRenaming source) :=
  HasCertifiedCellDim0.preservedByRename_via_renamer
    rawRenaming
    (fun sourceCell => PolyCell.rename_dim0 rawRenaming sourceCell)
    sourceCert

/-- Certify the pointwise outputs of a one-step lifted substitution.

`RawTermSubst.lift` maps the fresh variable to `var 0` and maps each
old variable to the weakened old substituent.  The old-substituent
case is exactly why the rename half above is needed. -/
def PolyCell.liftSubstDim0Cells
    {profile : PolyProfile} {srcScope tgtScope : Nat}
    (sigma : RawTermSubst srcScope tgtScope)
    (sigmaCells :
      ∀ variableIndex : Fin srcScope,
        PolyCell profile .term 0 tgtScope CellBoundary.trivial
          (.termBase (sigma variableIndex))) :
    ∀ liftedIndex : Fin (srcScope + 1),
      PolyCell profile .term 0 (tgtScope + 1) CellBoundary.trivial
        (.termBase (RawTermSubst.lift sigma liftedIndex)) := by
  intro liftedIndex
  cases liftedIndex with
  | mk liftedIndexValue liftedIndexBound =>
      cases liftedIndexValue with
      | zero =>
          show PolyCell profile .term 0 (tgtScope + 1)
            CellBoundary.trivial
            (.termBase
              (.mkGen .gen_var
                (⟨0, Nat.zero_lt_succ tgtScope⟩ : Fin (tgtScope + 1))
                .childNil))
          exact PolyCell.gen
            SupportedGenerator.gen_var
            (genPayloadEvidence (generator := .gen_var)
              (scope := tgtScope + 1)
              (⟨0, Nat.zero_lt_succ tgtScope⟩ : Fin (tgtScope + 1)))
            .nil
      | succ priorIndexValue =>
          show PolyCell profile .term 0 (tgtScope + 1)
            CellBoundary.trivial
            (.termBase
              (RawTerm.weaken
                (sigma
                  (⟨priorIndexValue,
                    Nat.lt_of_succ_lt_succ liftedIndexBound⟩ :
                    Fin srcScope))))
          rw [RawTerm.weaken_eq_rename]
          exact PolyCell.rename_dim0
            RawRenaming.weaken
            (sigmaCells
              (⟨priorIndexValue,
                Nat.lt_of_succ_lt_succ liftedIndexBound⟩ :
                Fin srcScope))

/-- Certify the pointwise outputs of an iterated lifted substitution. -/
def PolyCell.iterateLiftSubstDim0Cells
    {profile : PolyProfile} {srcScope tgtScope : Nat}
    (sigma : RawTermSubst srcScope tgtScope)
    (sigmaCells :
      ∀ variableIndex : Fin srcScope,
        PolyCell profile .term 0 tgtScope CellBoundary.trivial
          (.termBase (sigma variableIndex))) :
    (binderDepth : Nat) →
    ∀ liftedIndex : Fin (srcScope + binderDepth),
      PolyCell profile .term 0 (tgtScope + binderDepth)
        CellBoundary.trivial
        (.termBase (iterateLiftRaw sigma binderDepth liftedIndex))
  | 0, liftedIndex => sigmaCells liftedIndex
  | binderDepth + 1, liftedIndex =>
      PolyCell.liftSubstDim0Cells
        (profile := profile)
        (sigma := iterateLiftRaw sigma binderDepth)
        (sigmaCells :=
          PolyCell.iterateLiftSubstDim0Cells
            (profile := profile)
            sigma
            sigmaCells
            binderDepth)
        liftedIndex

mutual

/-- Substitute through a certified dim-0 cell structurally. -/
def PolyCell.subst_dim0
    {profile : PolyProfile} {srcScope tgtScope : Nat}
    (sigma : RawTermSubst srcScope tgtScope)
    (sigmaCells :
      ∀ variableIndex : Fin srcScope,
        PolyCell profile .term 0 tgtScope CellBoundary.trivial
          (.termBase (sigma variableIndex)))
    {sort : CellSort} {source : RawTerm srcScope}
    (sourceCell :
      PolyCell profile sort 0 srcScope CellBoundary.trivial
        (.termBase source)) :
    PolyCell profile sort 0 tgtScope CellBoundary.trivial
      (.termBase (RawTerm.subst sigma source)) :=
  match source with
  | .mkGen generator payload children =>
    match sourceCell with
    | .gen admission _payloadEvidence childSpine =>
      if isVarGenerator : generator = .gen_var then
        by
          subst isVarGenerator
          cases children with
          | childNil =>
              exact PolyCell.subst_dim0_varStep
                sigma payload (sigmaCells payload)
      else
        PolyCell.subst_dim0_nonVarStep
          (profile := profile)
          (srcScope := srcScope)
          (tgtScope := tgtScope)
          sigma
          isVarGenerator
          payload
          children
          admission
          (CertifiedTermSpine.subst_dim0
            (profile := profile)
            sigma
            sigmaCells
            (Generator.childSpecs_cellDimension_zero generator)
            childSpine)

/-- Substitute through a certified term-spine structurally. -/
def CertifiedTermSpine.subst_dim0
    {profile : PolyProfile} {srcScope tgtScope : Nat}
    (sigma : RawTermSubst srcScope tgtScope)
    (sigmaCells :
      ∀ variableIndex : Fin srcScope,
        PolyCell profile .term 0 tgtScope CellBoundary.trivial
          (.termBase (sigma variableIndex)))
    {childSpecs : List ChildSpec} {binderShifts : List Nat}
    {children : RawTermChildren binderShifts srcScope}
    (allChildrenDim0 :
      ∀ childSpec ∈ childSpecs, childSpec.cellDimension = 0)
    (sourceSpine :
      CertifiedTermSpine profile childSpecs srcScope binderShifts
        children) :
    CertifiedTermSpine profile childSpecs tgtScope binderShifts
      (foldChildren GenAlgebra.canonical sigma children) :=
  match sourceSpine with
  | .nil =>
      CertifiedTermSpine.substNilStep sigma
  | .cons (headSpec := headSpec) (restSpecs := restSpecs)
      (restShifts := restShifts) (headRaw := headRaw)
      (restRaws := restRaws) headCell restSpine =>
      let headDim0 :
          headSpec.cellDimension = 0 :=
        allChildrenDim0 headSpec List.mem_cons_self
      let restChildrenDim0 :
          ∀ childSpec ∈ restSpecs, childSpec.cellDimension = 0 :=
        fun childSpec childSpecMem =>
          allChildrenDim0 childSpec
            (List.mem_cons_of_mem headSpec childSpecMem)
      let headCellDim0 :
          PolyCell profile headSpec.cellSort 0
            (srcScope + headSpec.scopeShift) CellBoundary.trivial
            (.termBase headRaw) :=
        CertifiedTermSpine.headAtDim0 headDim0
          (CertifiedTermSpine.cons headCell restSpine)
      CertifiedTermSpine.substConsStep_dim0Trivial
        (profile := profile)
        (srcScope := srcScope)
        (tgtScope := tgtScope)
        (headSpec := headSpec)
        (restSpecs := restSpecs)
        (restShifts := restShifts)
        headDim0
        sigma
        (PolyCell.subst_dim0
          (iterateLiftRaw sigma headSpec.scopeShift)
          (PolyCell.iterateLiftSubstDim0Cells
            (profile := profile)
            sigma
            sigmaCells
            headSpec.scopeShift)
          headCellDim0)
        (CertifiedTermSpine.subst_dim0
          (profile := profile)
          sigma
          sigmaCells
          restChildrenDim0
          restSpine)

end

/-- Public HCC-level generic substitution preservation, with
sort-precise certified substituents. -/
theorem HasCertifiedCellDim0.preservedBySubst
    {profile : PolyProfile} {srcScope tgtScope : Nat}
    (sigma : RawTermSubst srcScope tgtScope)
    (sigmaCells :
      ∀ variableIndex : Fin srcScope,
        PolyCell profile .term 0 tgtScope CellBoundary.trivial
          (.termBase (sigma variableIndex)))
    {source : RawTerm srcScope}
    (sourceCert : HasCertifiedCellDim0 (profile := profile) source) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst sigma source) :=
  HasCertifiedCellDim0.preservedBySubst_via_substituter
    sigma
    (fun sourceCell => PolyCell.subst_dim0 sigma sigmaCells sourceCell)
    sourceCert

/-- Certify every output of the singleton substitution used by
`RawTerm.subst0`. -/
def PolyCell.singletonSubstDim0Cells
    {profile : PolyProfile} {scope : Nat}
    (rawArg : RawTerm scope)
    (argCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase rawArg)) :
    ∀ variableIndex : Fin (scope + 1),
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase (RawTermSubst.singleton rawArg variableIndex)) := by
  intro variableIndex
  cases variableIndex with
  | mk variableIndexValue variableIndexBound =>
      cases variableIndexValue with
      | zero =>
          show PolyCell profile .term 0 scope CellBoundary.trivial
            (.termBase rawArg)
          exact argCell
      | succ priorIndexValue =>
          show PolyCell profile .term 0 scope CellBoundary.trivial
            (.termBase
              (.mkGen .gen_var
                (⟨priorIndexValue,
                  Nat.lt_of_succ_lt_succ variableIndexBound⟩ :
                  Fin scope)
                .childNil))
          exact PolyCell.gen
            SupportedGenerator.gen_var
            (genPayloadEvidence (generator := .gen_var)
              (scope := scope)
              (⟨priorIndexValue,
                Nat.lt_of_succ_lt_succ variableIndexBound⟩ :
                Fin scope))
            .nil

/-- Generic `subst0` preservation, parameterized by a sort-precise
certified argument cell. -/
theorem HasCertifiedCellDim0.preservedBySubst0
    {profile : PolyProfile} {scope : Nat}
    {body : RawTerm (scope + 1)} {rawArg : RawTerm scope}
    (bodyCert : HasCertifiedCellDim0 (profile := profile) body)
    (argCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase rawArg)) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst0 body rawArg) :=
  HasCertifiedCellDim0.preservedBySubst
    (RawTermSubst.singleton rawArg)
    (PolyCell.singletonSubstDim0Cells rawArg argCell)
    bodyCert

/-- SR-beta structural preservation.

The SR-beta endpoint: from a certified beta-redex source
`app (lam body) arg`, certify its structural beta target
`subst0 body arg`.  The proof extracts the sort-precise argument cell
from the source spine, then feeds the generic `subst0` theorem through
the existing beta assembly bridge. -/
theorem HasCertifiedCellDim0.preservedByBeta
    {profile : PolyProfile} {scope : Nat}
    {body : RawTerm (scope + 1)} {rawArg : RawTerm scope}
    (sourceCert : HasCertifiedCellDim0 (profile := profile)
      ((.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_lam () (.childCons body .childNil))
          (.childCons rawArg .childNil))) : RawTerm scope)) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst0 body rawArg) := by
  let originalSourceCert := sourceCert
  obtain ⟨_, sourceCell⟩ := sourceCert
  cases sourceCell with
  | gen _ _ spine =>
      have argCell :
          PolyCell profile .term 0 scope CellBoundary.trivial
            (.termBase rawArg) :=
        spine.tail.headAtDim0 rfl
      exact HasCertifiedCellDim0.beta_redex_assembly body rawArg
        originalSourceCert
        (fun bodyCert _argCert =>
          HasCertifiedCellDim0.preservedBySubst0 bodyCert argCell)

end FX1Poly.Core
