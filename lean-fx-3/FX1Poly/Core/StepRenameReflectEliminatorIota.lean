import FX1Poly.Core.StepRenameReflect

/-! # FX1Poly/Core/StepRenameReflectEliminatorIota
    — the base-case eliminator ι arms of arbitrary-renaming `Step` reflection

`StepRenameReflect.lean` ships the arbitrary-renaming `Step` reflection-with-image
(`Step (rename rho t) u → ∃ t', Step t t' ∧ rename rho t' = u`, the Kripke-arrow-CR3 ingredient) arm by
arm: the β arm (`Step.reflectBeta`) and the `boolElim` / `fst` / `snd` redex projection arms.  This file
adds the remaining PURE-PROJECTION eliminator ι arms — the base cases that eliminate a NULLARY value and
project the matching branch, structurally identical to `Step.reflectIotaBoolTrue`:

  * `Step.reflectIotaNatElimZero` / `Step.reflectIotaNatRecZero` — `natElim`/`natRec` on `natZero` project
    the zero-branch (the `gen_natElim` / `gen_natRec` pair share arity, so the two arms are identical).
  * `Step.reflectIotaListElimNil` — `listElim` on `listNil` projects the nil-branch.
  * `Step.reflectIotaOptionMatchNone` — `optionMatch` on `optionNone` projects the none-branch.

Each is the `reflectIotaBoolTrue` recipe verbatim with the eliminator/value generators swapped: recover the
eliminator head (`rename_eq_mkGen`), a concrete-`gen` `rfl`-distribution of `rename` over the three-child
spine, `injection` to expose the children, recover the NULLARY scrutinee head (`rename_eq_mkGen` again,
`childNil`), and return the matching branch with its recovered renaming witnessing the contractum image.
Complete standalone cases (ι is a base case — no sub-reflection hypothesis).

These advance the full `Step` rename-reflection toward Kripke-arrow CR3
(`KripkeCandidateRenameClosure.lean:63`), the renaming dimension of the dependent-arrow reducibility
candidate the open-context (Kripke) logical relation requires.  Remaining for the full reflection: the
app-chain ι arms (`optionMatch`/`eitherMatch` on the wrapped value), the recursive ι arms
(`natElimSucc` / `natRecSucc` / `listElimCons`), the identity ι arms, and the recursive `cong` arm.

## Zero-axiom verification

`RawTerm.rename_eq_mkGen` + concrete `rfl`-distribution + `injection` + the matching `Step.iota*`
constructor — the verbatim `Step.reflectIotaBoolTrue` chain.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation
open StepStar

/-- **The `natElim`-on-`natZero` ι arm of arbitrary-renaming `Step` reflection.**  If `rename rho term` is
the ι-redex `natElim natZero zeroBranch succBranch`, then `term` is the source redex `natElim natZero
sourceZero sourceSucc` (the `gen_natElim` head and the nullary `gen_natZero` scrutinee head both recovered
by `rename_eq_mkGen`), it ι-reduces to its zero-branch, and that source zero-branch renames to `renamedZero`.
The base-case pure-projection recipe of `Step.reflectIotaBoolTrue` with `gen_natElim` / `gen_natZero`. -/
theorem Step.reflectIotaNatElimZero {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope) {term : RawTerm sourceScope}
    {renamedZero renamedSucc : RawTerm targetScope}
    (renameEquation : RawTerm.rename rho term =
      .mkGen .gen_natElim ()
        (.childCons (.mkGen .gen_natZero () .childNil)
          (.childCons renamedZero (.childCons renamedSucc .childNil)))) :
    ∃ sourceReduct : RawTerm sourceScope,
      Step term sourceReduct ∧ RawTerm.rename rho sourceReduct = renamedZero := by
  obtain ⟨payload, children, termEq⟩ := RawTerm.rename_eq_mkGen rho renameEquation
  subst termEq
  match payload, children with
  | (), .childCons scrutinee (.childCons zeroBranch (.childCons succBranch .childNil)) =>
      rw [show RawTerm.rename rho
            (.mkGen .gen_natElim ()
              (.childCons scrutinee (.childCons zeroBranch (.childCons succBranch .childNil)))) =
            (.mkGen .gen_natElim ()
              (.childCons (RawTerm.rename rho scrutinee)
                (.childCons (RawTerm.rename rho zeroBranch)
                  (.childCons (RawTerm.rename rho succBranch) .childNil)))
              : RawTerm targetScope) from rfl] at renameEquation
      injection renameEquation with _scopeEq _generatorEq _payloadEq childrenEq
      injection childrenEq with _ _ _ scrutineeEq tailEq
      injection tailEq with _ _ _ zeroEq tail2Eq
      injection tail2Eq with _ _ _ _succEq _nilEq
      obtain ⟨_scrutPayload, _scrutChildren, scrutTermEq⟩ := RawTerm.rename_eq_mkGen rho scrutineeEq
      subst scrutTermEq
      match _scrutPayload, _scrutChildren with
      | (), .childNil =>
          exact ⟨zeroBranch, Step.iotaNatElimZero, zeroEq⟩

/-- **The `natRec`-on-`natZero` ι arm of arbitrary-renaming `Step` reflection.**  The dependent-recursor
twin of `reflectIotaNatElimZero`: `gen_natRec` shares `gen_natElim`'s arity, so the base-case projection of
the zero-branch is structurally identical. -/
theorem Step.reflectIotaNatRecZero {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope) {term : RawTerm sourceScope}
    {renamedZero renamedSucc : RawTerm targetScope}
    (renameEquation : RawTerm.rename rho term =
      .mkGen .gen_natRec ()
        (.childCons (.mkGen .gen_natZero () .childNil)
          (.childCons renamedZero (.childCons renamedSucc .childNil)))) :
    ∃ sourceReduct : RawTerm sourceScope,
      Step term sourceReduct ∧ RawTerm.rename rho sourceReduct = renamedZero := by
  obtain ⟨payload, children, termEq⟩ := RawTerm.rename_eq_mkGen rho renameEquation
  subst termEq
  match payload, children with
  | (), .childCons scrutinee (.childCons zeroBranch (.childCons succBranch .childNil)) =>
      rw [show RawTerm.rename rho
            (.mkGen .gen_natRec ()
              (.childCons scrutinee (.childCons zeroBranch (.childCons succBranch .childNil)))) =
            (.mkGen .gen_natRec ()
              (.childCons (RawTerm.rename rho scrutinee)
                (.childCons (RawTerm.rename rho zeroBranch)
                  (.childCons (RawTerm.rename rho succBranch) .childNil)))
              : RawTerm targetScope) from rfl] at renameEquation
      injection renameEquation with _scopeEq _generatorEq _payloadEq childrenEq
      injection childrenEq with _ _ _ scrutineeEq tailEq
      injection tailEq with _ _ _ zeroEq tail2Eq
      injection tail2Eq with _ _ _ _succEq _nilEq
      obtain ⟨_scrutPayload, _scrutChildren, scrutTermEq⟩ := RawTerm.rename_eq_mkGen rho scrutineeEq
      subst scrutTermEq
      match _scrutPayload, _scrutChildren with
      | (), .childNil =>
          exact ⟨zeroBranch, Step.iotaNatRecZero, zeroEq⟩

/-- **The `listElim`-on-`listNil` ι arm of arbitrary-renaming `Step` reflection.**  If `rename rho term` is
the ι-redex `listElim listNil nilBranch consBranch`, then `term` is the source redex projecting its
nil-branch, recovered with its renaming as the contractum image.  Same nullary-scrutinee projection recipe
with `gen_listElim` / `gen_listNil`. -/
theorem Step.reflectIotaListElimNil {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope) {term : RawTerm sourceScope}
    {renamedNil renamedCons : RawTerm targetScope}
    (renameEquation : RawTerm.rename rho term =
      .mkGen .gen_listElim ()
        (.childCons (.mkGen .gen_listNil () .childNil)
          (.childCons renamedNil (.childCons renamedCons .childNil)))) :
    ∃ sourceReduct : RawTerm sourceScope,
      Step term sourceReduct ∧ RawTerm.rename rho sourceReduct = renamedNil := by
  obtain ⟨payload, children, termEq⟩ := RawTerm.rename_eq_mkGen rho renameEquation
  subst termEq
  match payload, children with
  | (), .childCons scrutinee (.childCons nilBranch (.childCons consBranch .childNil)) =>
      rw [show RawTerm.rename rho
            (.mkGen .gen_listElim ()
              (.childCons scrutinee (.childCons nilBranch (.childCons consBranch .childNil)))) =
            (.mkGen .gen_listElim ()
              (.childCons (RawTerm.rename rho scrutinee)
                (.childCons (RawTerm.rename rho nilBranch)
                  (.childCons (RawTerm.rename rho consBranch) .childNil)))
              : RawTerm targetScope) from rfl] at renameEquation
      injection renameEquation with _scopeEq _generatorEq _payloadEq childrenEq
      injection childrenEq with _ _ _ scrutineeEq tailEq
      injection tailEq with _ _ _ nilEq tail2Eq
      injection tail2Eq with _ _ _ _consEq _nilEq
      obtain ⟨_scrutPayload, _scrutChildren, scrutTermEq⟩ := RawTerm.rename_eq_mkGen rho scrutineeEq
      subst scrutTermEq
      match _scrutPayload, _scrutChildren with
      | (), .childNil =>
          exact ⟨nilBranch, Step.iotaListElimNil, nilEq⟩

/-- **The `optionMatch`-on-`optionNone` ι arm of arbitrary-renaming `Step` reflection.**  If `rename rho
term` is the ι-redex `optionMatch optionNone noneBranch someBranch`, then `term` is the source redex
projecting its none-branch, recovered with its renaming as the contractum image.  Same nullary-scrutinee
projection recipe with `gen_optionMatch` / `gen_optionNone`. -/
theorem Step.reflectIotaOptionMatchNone {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope) {term : RawTerm sourceScope}
    {renamedNone renamedSome : RawTerm targetScope}
    (renameEquation : RawTerm.rename rho term =
      .mkGen .gen_optionMatch ()
        (.childCons (.mkGen .gen_optionNone () .childNil)
          (.childCons renamedNone (.childCons renamedSome .childNil)))) :
    ∃ sourceReduct : RawTerm sourceScope,
      Step term sourceReduct ∧ RawTerm.rename rho sourceReduct = renamedNone := by
  obtain ⟨payload, children, termEq⟩ := RawTerm.rename_eq_mkGen rho renameEquation
  subst termEq
  match payload, children with
  | (), .childCons scrutinee (.childCons noneBranch (.childCons someBranch .childNil)) =>
      rw [show RawTerm.rename rho
            (.mkGen .gen_optionMatch ()
              (.childCons scrutinee (.childCons noneBranch (.childCons someBranch .childNil)))) =
            (.mkGen .gen_optionMatch ()
              (.childCons (RawTerm.rename rho scrutinee)
                (.childCons (RawTerm.rename rho noneBranch)
                  (.childCons (RawTerm.rename rho someBranch) .childNil)))
              : RawTerm targetScope) from rfl] at renameEquation
      injection renameEquation with _scopeEq _generatorEq _payloadEq childrenEq
      injection childrenEq with _ _ _ scrutineeEq tailEq
      injection tailEq with _ _ _ noneEq tail2Eq
      injection tail2Eq with _ _ _ _someEq _nilEq
      obtain ⟨_scrutPayload, _scrutChildren, scrutTermEq⟩ := RawTerm.rename_eq_mkGen rho scrutineeEq
      subst scrutTermEq
      match _scrutPayload, _scrutChildren with
      | (), .childNil =>
          exact ⟨noneBranch, Step.iotaOptionMatchNone, noneEq⟩

end FX1Poly.Core
