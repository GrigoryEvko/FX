import FX1Poly.Core.StepOverTable
import FX1Poly.Core.RawTermSubstLiftWeaken

/-! # FX1Poly/Core/EtaRowFiringSubstrate
    — bespoke-`Step.eta`-FREE raw/table shape lemmas for the eta critical pairs.

These four `RawTerm` weakening-shape lemmas and the one table-row firing
decomposition were historically housed inside `Core/StepEtaCriticalPairs`,
but they reference NO bespoke `Step.eta` relation: they are pure
weakening/renaming term-shape facts (`weaken_lam`,
`weaken_eq_lam_implies_source_lam`, and their path-lambda twins) plus the
`pathBetaIotaRow` table-row firing decomposition
(`pathBetaRowFiringDecompose`).  They are relocated here so the table-native
join consumers (`Typed/TableBetaEtaRootChildJoin*`,
`Typed/HasTypeUnionSubjectReduction`) can keep consuming them without
importing — and thus keeping alive — the bespoke `Step.eta` cascade.

## Zero-axiom verification

All five decls are structural `cases`/`injection`/`rw` proofs over
weakening, renaming, and the iota-table primary-head firing; no `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Gated in `FX1PolyAudit/AuditCoreSubstrateEta.lean`. -/

namespace FX1Poly.Core

-- `RawRenaming` lives in `FX1Poly.Foundation`, which does not enclose
-- `FX1Poly.Core`, so open it explicitly.
open FX1Poly.Foundation

namespace RawTerm

/-- Weakening a lambda preserves the lambda head and lifts weakening under
the lambda binder. -/
theorem weaken_lam {scope : Nat} (domainAnn : RawTerm scope) (body : RawTerm (scope + 1)) :
    RawTerm.weaken
        (RawTerm.mkGen .gen_lam () (.childCons domainAnn (.childCons body .childNil))) =
      RawTerm.mkGen .gen_lam ()
        (.childCons
          (RawTerm.rename RawRenaming.weaken domainAnn)
          (.childCons
            (RawTerm.rename (RawRenaming.lift RawRenaming.weaken) body)
            .childNil)) := by
  rw [RawTerm.weaken_eq_rename]
  rw [RawTerm.rename_nonVar_reduces RawRenaming.weaken
    (by decide : Generator.gen_lam ≠ .gen_var)]
  rfl

/-- If weakening a source-scope term has lambda shape, the source term was
already a lambda and the weakened body is the binder-lifted weakening of its
source body. -/
theorem weaken_eq_lam_implies_source_lam {scope : Nat}
    {innerFunction : RawTerm scope}
    {weakenedDomain : RawTerm (scope + 1)}
    {weakenedBody : RawTerm (scope + 2)}
    (weakenedEq :
      RawTerm.weaken innerFunction =
        RawTerm.mkGen .gen_lam ()
          (.childCons weakenedDomain (.childCons weakenedBody .childNil))) :
    ∃ (domainAnn : RawTerm scope) (body : RawTerm (scope + 1)),
      innerFunction =
          RawTerm.mkGen .gen_lam ()
            (.childCons domainAnn (.childCons body .childNil)) ∧
        weakenedDomain = RawTerm.rename RawRenaming.weaken domainAnn ∧
        weakenedBody =
          RawTerm.rename (RawRenaming.lift RawRenaming.weaken) body := by
  cases innerFunction with
  | mkGen generator payload children =>
      by_cases generatorIsVar : generator = .gen_var
      · subst generator
        dsimp [RawTerm.weaken, RawTerm.rename, fold] at weakenedEq
        cases weakenedEq
      · by_cases generatorIsLam : generator = .gen_lam
        · subst generator
          cases payload
          cases children with
          | childCons domainHead rest =>
              cases rest with
              | childCons bodyHead restTail =>
                  cases restTail
                  rw [RawTerm.weaken_lam] at weakenedEq
                  injection weakenedEq with _ _ _ childrenEq
                  injection childrenEq with _ _ _ childDomainEq childrenTailEq
                  injection childrenTailEq with _ _ _ childBodyEq _
                  exact ⟨domainHead, bodyHead, rfl, childDomainEq.symm, childBodyEq.symm⟩
        · rw [RawTerm.weaken_eq_rename] at weakenedEq
          rw [RawTerm.rename_nonVar_reduces RawRenaming.weaken
            generatorIsVar] at weakenedEq
          injection weakenedEq
          exact False.elim (generatorIsLam (by assumption))

/-- Weakening a path-lambda preserves the path-lambda head and lifts
weakening under the single path binder.  The path-lambda twin of
`weaken_lam` (no domain annotation child). -/
theorem weaken_pathLam {scope : Nat} (body : RawTerm (scope + 1)) :
    RawTerm.weaken
        (RawTerm.mkGen .gen_pathLam () (.childCons body .childNil)) =
      RawTerm.mkGen .gen_pathLam ()
        (.childCons
          (RawTerm.rename (RawRenaming.lift RawRenaming.weaken) body)
          .childNil) := by
  rw [RawTerm.weaken_eq_rename]
  rw [RawTerm.rename_nonVar_reduces RawRenaming.weaken
    (by decide : Generator.gen_pathLam ≠ .gen_var)]
  rfl

/-- If weakening a source-scope term has path-lambda shape, the source
term was already a path-lambda and the weakened body is the binder-lifted
weakening of its source body.  The path-lambda twin of
`weaken_eq_lam_implies_source_lam`. -/
theorem weaken_eq_pathLam_implies_source_pathLam {scope : Nat}
    {innerPath : RawTerm scope}
    {weakenedBody : RawTerm (scope + 2)}
    (weakenedEq :
      RawTerm.weaken innerPath =
        RawTerm.mkGen .gen_pathLam ()
          (.childCons weakenedBody .childNil)) :
    ∃ body : RawTerm (scope + 1),
      innerPath =
          RawTerm.mkGen .gen_pathLam () (.childCons body .childNil) ∧
        weakenedBody =
          RawTerm.rename (RawRenaming.lift RawRenaming.weaken) body := by
  cases innerPath with
  | mkGen generator payload children =>
      by_cases generatorIsVar : generator = .gen_var
      · subst generator
        dsimp [RawTerm.weaken, RawTerm.rename, fold] at weakenedEq
        cases weakenedEq
      · by_cases generatorIsPathLam : generator = .gen_pathLam
        · subst generator
          cases payload
          cases children with
          | childCons bodyHead restTail =>
              cases restTail
              rw [RawTerm.weaken_pathLam] at weakenedEq
              injection weakenedEq with _ _ _ childrenEq
              injection childrenEq with _ _ _ childBodyEq _
              exact ⟨bodyHead, rfl, childBodyEq.symm⟩
        · rw [RawTerm.weaken_eq_rename] at weakenedEq
          rw [RawTerm.rename_nonVar_reduces RawRenaming.weaken
            generatorIsVar] at weakenedEq
          injection weakenedEq
          exact False.elim (generatorIsPathLam (by assumption))

end RawTerm

/-- The table-native endpoint-β row's firing decomposed: a firing on a
literal two-child `pathApp` spine forces the function slot to be a
path-lambda and pins the reduct to its single-substitution.  The
path-lambda twin of `betaRowFiringToHeadStep`, surfaced as a structural
decomposition for the eta-vs-pathBeta critical pair. -/
theorem pathBetaRowFiringDecompose {scope : Nat}
    {functionChild argumentChild reduct : RawTerm scope}
    (fires : pathBetaIotaRow.firesOn? ()
        (.childCons functionChild (.childCons argumentChild .childNil))
      = some reduct) :
    ∃ pathBody : RawTerm (scope + 1),
      functionChild =
          RawTerm.mkGen .gen_pathLam () (.childCons pathBody .childNil) ∧
        reduct = RawTerm.subst0 pathBody argumentChild := by
  cases functionChild with
  | mkGen functionGenerator functionPayload functionChildren =>
      have isHead := IotaRuleDesc.firesOn?_some_primaryHead fires rfl rfl
      subst isHead
      cases functionPayload
      cases functionChildren with
      | childCons pathBody pathNil =>
          cases pathNil
          exact ⟨pathBody, rfl, (Option.some.inj fires).symm⟩

end FX1Poly.Core
