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

This file ALSO ships the app-chain (step-case) eliminator ι arms below — `optionMatch` on `optionSome`,
`eitherMatch` on `eitherInl`/`eitherInr` — which match a UNARY value and reduce to the branch APPLIED to
the wrapped value (constructed `app` contractum + two-level scrutinee injection).

These advance the full `Step` rename-reflection toward Kripke-arrow CR3
(`KripkeCandidateRenameClosure.lean:63`), the renaming dimension of the dependent-arrow reducibility
candidate the open-context (Kripke) logical relation requires.  This file ALSO ships the identity-eliminator
ι arms (`idJRefl` / `idStrictRecRefl`, projection past the `refl` scrutinee), the recursive Nat-recursor
ι arms (`natElimSucc` / `natRecSucc`, nested app-chain with a recursive call), and the deepest reduct —
`listElimCons` (`Step.reflectIotaListElimCons`, a TRIPLE-curried application of the cons-branch to head, tail,
and the recursive `listElim` over the tail, with a binary `listCons` scrutinee) below.  With it, every
REDEX-LEAF arm of arbitrary-`rho` reflection is shipped; the ONLY remaining arm for the full reflection is the
recursive `cong` arm (the general congruence case, needs the sub-reflection IH — the substantive last piece).

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

/-! ## The app-chain (step-case) eliminator ι arms

Unlike the base-case arms above (nullary scrutinee, contractum = a branch child), the step-case
eliminators match on a UNARY value (`optionSome v` / `eitherInl v` / `eitherInr v`) and reduce to the
branch APPLIED to the wrapped value: `optionMatch (optionSome v) n s ↝ app s v`.  So the contractum is a
constructed `app` cell, and the image equation `rename rho (app branch value) = app renamedBranch
renamedValue` closes by a `rfl`-distribution of `rename` over the `app` cell composed with the recovered
branch and value renamings (instead of a bare child equation).  The unary scrutinee additionally needs a
TWO-level injection (the `optionSome`/`eitherInl`/`eitherInr` `mkGen` then its `childCons`) to expose the
value. -/

/-- **The `optionMatch`-on-`optionSome` ι arm of arbitrary-renaming `Step` reflection.**  If `rename rho
term` is the ι-redex `optionMatch (optionSome renamedValue) renamedNone renamedSome`, then `term` is the
source redex `optionMatch (optionSome value) noneBranch someBranch`, it ι-reduces to `app someBranch
value`, and that source contractum renames to `app renamedSome renamedValue` (`rename`-over-`app`
distribution + the recovered `someBranch`/`value` renamings).  The app-chain (step-case) twin of
`reflectIotaOptionMatchNone`. -/
theorem Step.reflectIotaOptionMatchSome {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope) {term : RawTerm sourceScope}
    {renamedValue renamedNone renamedSome : RawTerm targetScope}
    (renameEquation : RawTerm.rename rho term =
      .mkGen .gen_optionMatch ()
        (.childCons (.mkGen .gen_optionSome () (.childCons renamedValue .childNil))
          (.childCons renamedNone (.childCons renamedSome .childNil)))) :
    ∃ sourceReduct : RawTerm sourceScope,
      Step term sourceReduct ∧
        RawTerm.rename rho sourceReduct =
          .mkGen .gen_app () (.childCons renamedSome (.childCons renamedValue .childNil)) := by
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
      injection tailEq with _ _ _ _noneEq tail2Eq
      injection tail2Eq with _ _ _ someEq _nilEq
      obtain ⟨_scrutPayload, _scrutChildren, scrutTermEq⟩ := RawTerm.rename_eq_mkGen rho scrutineeEq
      subst scrutTermEq
      match _scrutPayload, _scrutChildren with
      | (), .childCons value .childNil =>
          rw [show RawTerm.rename rho (.mkGen .gen_optionSome () (.childCons value .childNil)) =
                (.mkGen .gen_optionSome () (.childCons (RawTerm.rename rho value) .childNil)
                  : RawTerm targetScope) from rfl] at scrutineeEq
          injection scrutineeEq with _ _ _ scrutChildrenEq
          injection scrutChildrenEq with _ _ _ valueEq _nilEq2
          refine ⟨.mkGen .gen_app () (.childCons someBranch (.childCons value .childNil)),
            Step.iotaOptionMatchSome, ?_⟩
          rw [show RawTerm.rename rho
                (.mkGen .gen_app () (.childCons someBranch (.childCons value .childNil))) =
                (.mkGen .gen_app ()
                  (.childCons (RawTerm.rename rho someBranch)
                    (.childCons (RawTerm.rename rho value) .childNil))
                  : RawTerm targetScope) from rfl, someEq, valueEq]

/-- **The `eitherMatch`-on-`eitherInl` ι arm of arbitrary-renaming `Step` reflection.**  Reflects the
ι-redex `eitherMatch (eitherInl renamedValue) renamedLeft renamedRight` to the source redex reducing to
`app leftBranch value`, recovered with the `rename`-over-`app` image.  The left coproduct app-chain twin. -/
theorem Step.reflectIotaEitherMatchInl {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope) {term : RawTerm sourceScope}
    {renamedValue renamedLeft renamedRight : RawTerm targetScope}
    (renameEquation : RawTerm.rename rho term =
      .mkGen .gen_eitherMatch ()
        (.childCons (.mkGen .gen_eitherInl () (.childCons renamedValue .childNil))
          (.childCons renamedLeft (.childCons renamedRight .childNil)))) :
    ∃ sourceReduct : RawTerm sourceScope,
      Step term sourceReduct ∧
        RawTerm.rename rho sourceReduct =
          .mkGen .gen_app () (.childCons renamedLeft (.childCons renamedValue .childNil)) := by
  obtain ⟨payload, children, termEq⟩ := RawTerm.rename_eq_mkGen rho renameEquation
  subst termEq
  match payload, children with
  | (), .childCons scrutinee (.childCons leftBranch (.childCons rightBranch .childNil)) =>
      rw [show RawTerm.rename rho
            (.mkGen .gen_eitherMatch ()
              (.childCons scrutinee (.childCons leftBranch (.childCons rightBranch .childNil)))) =
            (.mkGen .gen_eitherMatch ()
              (.childCons (RawTerm.rename rho scrutinee)
                (.childCons (RawTerm.rename rho leftBranch)
                  (.childCons (RawTerm.rename rho rightBranch) .childNil)))
              : RawTerm targetScope) from rfl] at renameEquation
      injection renameEquation with _scopeEq _generatorEq _payloadEq childrenEq
      injection childrenEq with _ _ _ scrutineeEq tailEq
      injection tailEq with _ _ _ leftEq tail2Eq
      injection tail2Eq with _ _ _ _rightEq _nilEq
      obtain ⟨_scrutPayload, _scrutChildren, scrutTermEq⟩ := RawTerm.rename_eq_mkGen rho scrutineeEq
      subst scrutTermEq
      match _scrutPayload, _scrutChildren with
      | (), .childCons value .childNil =>
          rw [show RawTerm.rename rho (.mkGen .gen_eitherInl () (.childCons value .childNil)) =
                (.mkGen .gen_eitherInl () (.childCons (RawTerm.rename rho value) .childNil)
                  : RawTerm targetScope) from rfl] at scrutineeEq
          injection scrutineeEq with _ _ _ scrutChildrenEq
          injection scrutChildrenEq with _ _ _ valueEq _nilEq2
          refine ⟨.mkGen .gen_app () (.childCons leftBranch (.childCons value .childNil)),
            Step.iotaEitherMatchInl, ?_⟩
          rw [show RawTerm.rename rho
                (.mkGen .gen_app () (.childCons leftBranch (.childCons value .childNil))) =
                (.mkGen .gen_app ()
                  (.childCons (RawTerm.rename rho leftBranch)
                    (.childCons (RawTerm.rename rho value) .childNil))
                  : RawTerm targetScope) from rfl, leftEq, valueEq]

/-- **The `eitherMatch`-on-`eitherInr` ι arm of arbitrary-renaming `Step` reflection.**  The symmetric
right-coproduct twin of `reflectIotaEitherMatchInl`: reflects `eitherMatch (eitherInr renamedValue) …` to
the source redex reducing to `app rightBranch value`. -/
theorem Step.reflectIotaEitherMatchInr {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope) {term : RawTerm sourceScope}
    {renamedValue renamedLeft renamedRight : RawTerm targetScope}
    (renameEquation : RawTerm.rename rho term =
      .mkGen .gen_eitherMatch ()
        (.childCons (.mkGen .gen_eitherInr () (.childCons renamedValue .childNil))
          (.childCons renamedLeft (.childCons renamedRight .childNil)))) :
    ∃ sourceReduct : RawTerm sourceScope,
      Step term sourceReduct ∧
        RawTerm.rename rho sourceReduct =
          .mkGen .gen_app () (.childCons renamedRight (.childCons renamedValue .childNil)) := by
  obtain ⟨payload, children, termEq⟩ := RawTerm.rename_eq_mkGen rho renameEquation
  subst termEq
  match payload, children with
  | (), .childCons scrutinee (.childCons leftBranch (.childCons rightBranch .childNil)) =>
      rw [show RawTerm.rename rho
            (.mkGen .gen_eitherMatch ()
              (.childCons scrutinee (.childCons leftBranch (.childCons rightBranch .childNil)))) =
            (.mkGen .gen_eitherMatch ()
              (.childCons (RawTerm.rename rho scrutinee)
                (.childCons (RawTerm.rename rho leftBranch)
                  (.childCons (RawTerm.rename rho rightBranch) .childNil)))
              : RawTerm targetScope) from rfl] at renameEquation
      injection renameEquation with _scopeEq _generatorEq _payloadEq childrenEq
      injection childrenEq with _ _ _ scrutineeEq tailEq
      injection tailEq with _ _ _ _leftEq tail2Eq
      injection tail2Eq with _ _ _ rightEq _nilEq
      obtain ⟨_scrutPayload, _scrutChildren, scrutTermEq⟩ := RawTerm.rename_eq_mkGen rho scrutineeEq
      subst scrutTermEq
      match _scrutPayload, _scrutChildren with
      | (), .childCons value .childNil =>
          rw [show RawTerm.rename rho (.mkGen .gen_eitherInr () (.childCons value .childNil)) =
                (.mkGen .gen_eitherInr () (.childCons (RawTerm.rename rho value) .childNil)
                  : RawTerm targetScope) from rfl] at scrutineeEq
          injection scrutineeEq with _ _ _ scrutChildrenEq
          injection scrutChildrenEq with _ _ _ valueEq _nilEq2
          refine ⟨.mkGen .gen_app () (.childCons rightBranch (.childCons value .childNil)),
            Step.iotaEitherMatchInr, ?_⟩
          rw [show RawTerm.rename rho
                (.mkGen .gen_app () (.childCons rightBranch (.childCons value .childNil))) =
                (.mkGen .gen_app ()
                  (.childCons (RawTerm.rename rho rightBranch)
                    (.childCons (RawTerm.rename rho value) .childNil))
                  : RawTerm targetScope) from rfl, rightEq, valueEq]

/-! ## The identity-eliminator ι arms (projection past the `refl` scrutinee)

`idJ` / `idStrictRec` on a `refl` witness project the BASE-CASE branch: `idJ baseCase (refl w) ↝ baseCase`.
Unlike the data eliminators above, the eliminated value (`refl`) sits at child-1 and the projected
contractum (`baseCase`) sits at child-0; the `refl` scrutinee is unary (carries the witness) but the
witness is irrelevant to the contractum, so after recovering the `refl` shape the base-case child's own
recovered renaming IS the contractum image. -/

/-- **The `idJ`-on-`refl` ι arm of arbitrary-renaming `Step` reflection.**  Reflects the ι-redex `idJ
renamedBase (refl renamedWitness)` to the source redex `idJ baseCase (refl witness)` projecting its
base-case branch, recovered with the base-case's own renaming as the contractum image. -/
theorem Step.reflectIotaIdJRefl {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope) {term : RawTerm sourceScope}
    {renamedBase renamedWitness : RawTerm targetScope}
    (renameEquation : RawTerm.rename rho term =
      .mkGen .gen_idJ ()
        (.childCons renamedBase
          (.childCons (.mkGen .gen_refl () (.childCons renamedWitness .childNil)) .childNil))) :
    ∃ sourceReduct : RawTerm sourceScope,
      Step term sourceReduct ∧ RawTerm.rename rho sourceReduct = renamedBase := by
  obtain ⟨payload, children, termEq⟩ := RawTerm.rename_eq_mkGen rho renameEquation
  subst termEq
  match payload, children with
  | (), .childCons baseCase (.childCons reflChild .childNil) =>
      rw [show RawTerm.rename rho
            (.mkGen .gen_idJ () (.childCons baseCase (.childCons reflChild .childNil))) =
            (.mkGen .gen_idJ ()
              (.childCons (RawTerm.rename rho baseCase)
                (.childCons (RawTerm.rename rho reflChild) .childNil))
              : RawTerm targetScope) from rfl] at renameEquation
      injection renameEquation with _scopeEq _generatorEq _payloadEq childrenEq
      injection childrenEq with _ _ _ baseEq tailEq
      injection tailEq with _ _ _ reflEq _nilEq
      obtain ⟨_reflPayload, _reflChildren, reflTermEq⟩ := RawTerm.rename_eq_mkGen rho reflEq
      subst reflTermEq
      match _reflPayload, _reflChildren with
      | (), .childCons witness .childNil =>
          exact ⟨baseCase, Step.iotaIdJRefl, baseEq⟩

/-- **The `idStrictRec`-on-`refl` ι arm of arbitrary-renaming `Step` reflection.**  The strict
identity-eliminator twin of `reflectIotaIdJRefl` (same arity / projection shape). -/
theorem Step.reflectIotaIdStrictRecRefl {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope) {term : RawTerm sourceScope}
    {renamedBase renamedWitness : RawTerm targetScope}
    (renameEquation : RawTerm.rename rho term =
      .mkGen .gen_idStrictRec ()
        (.childCons renamedBase
          (.childCons (.mkGen .gen_refl () (.childCons renamedWitness .childNil)) .childNil))) :
    ∃ sourceReduct : RawTerm sourceScope,
      Step term sourceReduct ∧ RawTerm.rename rho sourceReduct = renamedBase := by
  obtain ⟨payload, children, termEq⟩ := RawTerm.rename_eq_mkGen rho renameEquation
  subst termEq
  match payload, children with
  | (), .childCons baseCase (.childCons reflChild .childNil) =>
      rw [show RawTerm.rename rho
            (.mkGen .gen_idStrictRec () (.childCons baseCase (.childCons reflChild .childNil))) =
            (.mkGen .gen_idStrictRec ()
              (.childCons (RawTerm.rename rho baseCase)
                (.childCons (RawTerm.rename rho reflChild) .childNil))
              : RawTerm targetScope) from rfl] at renameEquation
      injection renameEquation with _scopeEq _generatorEq _payloadEq childrenEq
      injection childrenEq with _ _ _ baseEq tailEq
      injection tailEq with _ _ _ reflEq _nilEq
      obtain ⟨_reflPayload, _reflChildren, reflTermEq⟩ := RawTerm.rename_eq_mkGen rho reflEq
      subst reflTermEq
      match _reflPayload, _reflChildren with
      | (), .childCons witness .childNil =>
          exact ⟨baseCase, Step.iotaIdStrictRecRefl, baseEq⟩

/-! ## The recursive (step-case) Nat-recursor ι arms

`natElim` / `natRec` on `natSucc predecessor` build a NESTED app-chain containing a RECURSIVE call on the
predecessor: `natElim (natSucc p) z s ↝ app (app s p) (natElim p z s)`.  The contractum re-uses the
ELIMINATOR over the predecessor, so the image equation is a deep `rename`-over-(`app`/`app`/`natElim`)
distribution; after recovering the predecessor (from the unary `natSucc` scrutinee, two-level injection)
and the zero/succ branches, substituting the three recovered renamings collapses the image to `rfl`. -/

/-- **The `natElim`-on-`natSucc` ι arm of arbitrary-renaming `Step` reflection.**  Reflects the ι-redex
`natElim (natSucc renamedPred) renamedZero renamedSucc` to the source redex reducing to `app (app
succBranch predecessor) (natElim predecessor zeroBranch succBranch)`, the contractum recovered by
substituting the predecessor/zero/succ renamings into the nested-app image (closing by `rfl`). -/
theorem Step.reflectIotaNatElimSucc {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope) {term : RawTerm sourceScope}
    {renamedPred renamedZero renamedSucc : RawTerm targetScope}
    (renameEquation : RawTerm.rename rho term =
      .mkGen .gen_natElim ()
        (.childCons (.mkGen .gen_natSucc () (.childCons renamedPred .childNil))
          (.childCons renamedZero (.childCons renamedSucc .childNil)))) :
    ∃ sourceReduct : RawTerm sourceScope,
      Step term sourceReduct ∧
        RawTerm.rename rho sourceReduct =
          .mkGen .gen_app ()
            (.childCons
              (.mkGen .gen_app () (.childCons renamedSucc (.childCons renamedPred .childNil)))
              (.childCons
                (.mkGen .gen_natElim ()
                  (.childCons renamedPred (.childCons renamedZero (.childCons renamedSucc .childNil))))
                .childNil)) := by
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
      injection tail2Eq with _ _ _ succEq _nilEq
      obtain ⟨_scrutPayload, _scrutChildren, scrutTermEq⟩ := RawTerm.rename_eq_mkGen rho scrutineeEq
      subst scrutTermEq
      match _scrutPayload, _scrutChildren with
      | (), .childCons predecessor .childNil =>
          rw [show RawTerm.rename rho (.mkGen .gen_natSucc () (.childCons predecessor .childNil)) =
                (.mkGen .gen_natSucc () (.childCons (RawTerm.rename rho predecessor) .childNil)
                  : RawTerm targetScope) from rfl] at scrutineeEq
          injection scrutineeEq with _ _ _ scrutChildrenEq
          injection scrutChildrenEq with _ _ _ predEq _nilEq2
          subst predEq; subst zeroEq; subst succEq
          exact ⟨.mkGen .gen_app ()
              (.childCons
                (.mkGen .gen_app () (.childCons succBranch (.childCons predecessor .childNil)))
                (.childCons
                  (.mkGen .gen_natElim ()
                    (.childCons predecessor (.childCons zeroBranch (.childCons succBranch .childNil))))
                  .childNil)),
            Step.iotaNatElimSucc, rfl⟩

/-- **The `natRec`-on-`natSucc` ι arm of arbitrary-renaming `Step` reflection.**  The dependent-recursor
twin of `reflectIotaNatElimSucc` (`gen_natRec` shares `gen_natElim`'s arity and step-case ι shape). -/
theorem Step.reflectIotaNatRecSucc {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope) {term : RawTerm sourceScope}
    {renamedPred renamedZero renamedSucc : RawTerm targetScope}
    (renameEquation : RawTerm.rename rho term =
      .mkGen .gen_natRec ()
        (.childCons (.mkGen .gen_natSucc () (.childCons renamedPred .childNil))
          (.childCons renamedZero (.childCons renamedSucc .childNil)))) :
    ∃ sourceReduct : RawTerm sourceScope,
      Step term sourceReduct ∧
        RawTerm.rename rho sourceReduct =
          .mkGen .gen_app ()
            (.childCons
              (.mkGen .gen_app () (.childCons renamedSucc (.childCons renamedPred .childNil)))
              (.childCons
                (.mkGen .gen_natRec ()
                  (.childCons renamedPred (.childCons renamedZero (.childCons renamedSucc .childNil))))
                .childNil)) := by
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
      injection tail2Eq with _ _ _ succEq _nilEq
      obtain ⟨_scrutPayload, _scrutChildren, scrutTermEq⟩ := RawTerm.rename_eq_mkGen rho scrutineeEq
      subst scrutTermEq
      match _scrutPayload, _scrutChildren with
      | (), .childCons predecessor .childNil =>
          rw [show RawTerm.rename rho (.mkGen .gen_natSucc () (.childCons predecessor .childNil)) =
                (.mkGen .gen_natSucc () (.childCons (RawTerm.rename rho predecessor) .childNil)
                  : RawTerm targetScope) from rfl] at scrutineeEq
          injection scrutineeEq with _ _ _ scrutChildrenEq
          injection scrutChildrenEq with _ _ _ predEq _nilEq2
          subst predEq; subst zeroEq; subst succEq
          exact ⟨.mkGen .gen_app ()
              (.childCons
                (.mkGen .gen_app () (.childCons succBranch (.childCons predecessor .childNil)))
                (.childCons
                  (.mkGen .gen_natRec ()
                    (.childCons predecessor (.childCons zeroBranch (.childCons succBranch .childNil))))
                  .childNil)),
            Step.iotaNatRecSucc, rfl⟩

/-- **The `listElim`-on-`listCons` ι arm of arbitrary-renaming `Step` reflection.**  The deepest reduct in
the design: `listElim (listCons h t) n c ↝ app (app (app c h) t) (listElim t n c)` — a TRIPLE-curried
application of the cons-branch to head, tail, and the recursive call.  The `listCons` scrutinee is BINARY
(head + tail, so a two-level injection recovers both), and the contractum re-uses the eliminator over the
tail; substituting the four recovered renamings (head / tail / nil-branch / cons-branch) collapses the
deep `rename`-over-(`app`/`app`/`app`/`listElim`) image to `rfl`.  With the base / app-chain / identity /
recursive-Nat arms above, this completes every REDEX-LEAF arm of arbitrary-`rho` `Step`
reflection-with-image; the recursive `cong` arm (general congruence) is the remaining inductive backbone. -/
theorem Step.reflectIotaListElimCons {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope) {term : RawTerm sourceScope}
    {renamedHead renamedTail renamedNil renamedCons : RawTerm targetScope}
    (renameEquation : RawTerm.rename rho term =
      .mkGen .gen_listElim ()
        (.childCons
          (.mkGen .gen_listCons () (.childCons renamedHead (.childCons renamedTail .childNil)))
          (.childCons renamedNil (.childCons renamedCons .childNil)))) :
    ∃ sourceReduct : RawTerm sourceScope,
      Step term sourceReduct ∧
        RawTerm.rename rho sourceReduct =
          .mkGen .gen_app ()
            (.childCons
              (.mkGen .gen_app ()
                (.childCons
                  (.mkGen .gen_app () (.childCons renamedCons (.childCons renamedHead .childNil)))
                  (.childCons renamedTail .childNil)))
              (.childCons
                (.mkGen .gen_listElim ()
                  (.childCons renamedTail (.childCons renamedNil (.childCons renamedCons .childNil))))
                .childNil)) := by
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
      injection childrenEq with _ _ _ scrutineeEq restEq
      injection restEq with _ _ _ nilBEq rest2Eq
      injection rest2Eq with _ _ _ consEq _nilEq
      obtain ⟨_scrutPayload, _scrutChildren, scrutTermEq⟩ := RawTerm.rename_eq_mkGen rho scrutineeEq
      subst scrutTermEq
      match _scrutPayload, _scrutChildren with
      | (), .childCons headVal (.childCons tailVal .childNil) =>
          rw [show RawTerm.rename rho
                (.mkGen .gen_listCons () (.childCons headVal (.childCons tailVal .childNil))) =
                (.mkGen .gen_listCons ()
                  (.childCons (RawTerm.rename rho headVal)
                    (.childCons (RawTerm.rename rho tailVal) .childNil))
                  : RawTerm targetScope) from rfl] at scrutineeEq
          injection scrutineeEq with _ _ _ scrutChildrenEq
          injection scrutChildrenEq with _ _ _ headEq scrutTail1Eq
          injection scrutTail1Eq with _ _ _ tailEqV _nilEq2
          subst headEq; subst tailEqV; subst nilBEq; subst consEq
          exact ⟨.mkGen .gen_app ()
              (.childCons
                (.mkGen .gen_app ()
                  (.childCons
                    (.mkGen .gen_app () (.childCons consBranch (.childCons headVal .childNil)))
                    (.childCons tailVal .childNil)))
                (.childCons
                  (.mkGen .gen_listElim ()
                    (.childCons tailVal (.childCons nilBranch (.childCons consBranch .childNil))))
                  .childNil)),
            Step.iotaListElimCons, rfl⟩

end FX1Poly.Core
