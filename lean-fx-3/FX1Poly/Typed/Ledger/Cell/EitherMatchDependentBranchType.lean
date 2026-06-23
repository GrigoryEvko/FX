import FX1Poly.Typed.Ledger.Cell.CellConstructors
import FX1Poly.Typed.Ledger.Cell.CellSubstitution
import FX1Poly.Typed.Ledger.Cell.CellRenaming
import FX1Poly.Tier0.Term.Subst.RawTermSubstCompose
import FX1Poly.Tier0.Term.Subst.RawTermSubstPointwise
import FX1Poly.Tier0.Term.Subst.RawTermSubst0
import FX1Poly.Tier0.Term.Subst.RawTermSubstConsCommute
import FX1Poly.Tier0.Term.Rename.RawTermRenameAsSubst
import FX1Poly.Tier0.Term.Rename.RawTermRenameComposeFusion

/-! # FX1Poly/Typed/Ledger/Cell/EitherMatchDependentBranchType
    — the dependent `eitherMatch` inl/inr branch CODOMAINS (the one-binder dependent-eliminator branch crux)

The dependent coproduct eliminator `eitherMatch motive leftBranch rightBranch scrutinee` carries a motive
`motive : RawTerm (scope + 1)` (`var 0` = the coproduct scrutinee) and TWO branches, each a single-binder
dependent function: `leftBranch : (a : A) → motive (inl a)` and `rightBranch : (b : B) → motive (inr b)`.
Eliminating a `inl payload` reduces (ι) to `leftBranch payload`, whose type is the Π codomain instantiated at
`payload` — and subject reduction needs that to be the eliminator's output type `motive (inl payload)`.

Unlike `boolElim`'s NULLARY branches (whose dependent classifiers are the binder-free `subst0 motive boolTrue`)
and unlike `natElim`'s TWO-binder recursive succ branch (`natElimDependentSuccBranchType`, predecessor + IH),
the coproduct branches each bind exactly ONE variable.  Their classifier is the motive re-based at
`inl (var 0)` / `inr (var 0)` with the motive's own context shifted past the single fresh injection binder:

  `eitherMatchDependentInlBranchCodomain motive := subst (cons (inl (var 0)) (shift-by-1)) motive`.

This file ships the two codomains (`inl` / `inr`) and the four naturality laws each branch type needs:

  * the ι type-preservation pin (`subst0 codomain payload = subst0 motive (inl payload)`) — subject reduction
    for the inl/inr ι reduct `leftBranch payload`;
  * the FT-bridge general form (under an outer closing substitution `tailSubst`), the shape the bounded
    fundamental-theorem elim row consumes;
  * substitution-stability (`subst (lift σ) codomain = codomain (subst (lift σ) motive)`) for
    `HasTypeUnion.substRespectingContext`;
  * renaming-stability (the `iterateLiftRaw _ 1` rename twin) for `HasTypeUnion.renameRespectsContext`.

The `eitherMatchDependentInlBranchType` / `...InrBranchType` defs wrap each codomain in `piTyCodeCell` at the
branch's domain type — the classifier the dependent `eitherMatchElimRule` assigns to its branch obligations.

## Zero-axiom verification

`RawTerm.subst_compose` + `RawTerm.subst_pointwise` (axiom-free term-axis polynomial-monad laws) over a
two-arm `Fin` match; the per-position arms compute by `rfl` (the `Fin` bound proofs collapse under `Prop`
irrelevance, the injection cells `subst`-map structurally, `cons` / `singleton` reduce on concrete positions).
The single-binder weakening's bound is `Nat.add_lt_add_right` (NO `omega`); the position-(k+1) reconciliation
routes `weaken` through `weaken_subst_cons` + the renaming-as-substitution bridge.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Tier0.Syntax

/-- **Weakening as the shift-by-one substitution.**  `RawTerm.weaken` (raise scope by one via the `Fin.succ`
shift) equals substituting every variable by the variable shifted up by one — the substitution
`fun position => var (position + 1)`.  Proof: the renaming-as-substitution bridge at the weakening renaming,
whose injected image is exactly `var (position + 1)` (`RawRenaming.weaken position = Fin.succ position`,
definitionally `⟨position.val + 1, _⟩`).  The one-binder analog of `natElim`'s `doubleWeaken_eq_substShiftBy2`;
consumed by the dependent branch-codomain substitution naturality to reconcile the lifted substitution's
variable image at `k + 1` (`lift σ` reads `weaken (σ k)`) with the cons-tail single-shift the re-basing carries
(`weaken_subst_cons` strips the injection-binder slot, leaving exactly this shift-by-one substitution). -/
theorem weaken_eq_substShiftBy1 {scope : Nat} (sourceTerm : RawTerm scope) :
    RawTerm.weaken sourceTerm
      = RawTerm.subst
          (fun position => .mkGen .gen_var ⟨position.val + 1, Nat.add_lt_add_right position.isLt 1⟩ .childNil)
          sourceTerm := by
  rw [RawTerm.weaken_eq_rename sourceTerm]
  exact RawTerm.rename_eq_subst_ofRenaming RawRenaming.weaken sourceTerm

/-! ## The `inl` branch codomain -/

/-- The dependent `inl`-branch codomain: `motive` re-based at `inl (var 0)` (the single injection binder),
the motive's context shifted past that one fresh binder.  The classifier BODY of the left branch
`(a : A) → motive (inl a)` — under the `a : A` binder the result type is `motive (inl a)`. -/
def eitherMatchDependentInlBranchCodomain {scope : Nat} (motive : RawTerm (scope + 1)) :
    RawTerm (scope + 1) :=
  RawTerm.subst
    (RawTermSubst.cons
      (eitherInlCell (.mkGen .gen_var ⟨0, Nat.zero_lt_succ scope⟩ .childNil))
      (fun position => .mkGen .gen_var ⟨position.val + 1, Nat.add_lt_add_right position.isLt 1⟩ .childNil))
    motive

/-- **The inl-ι type-preservation pin.**  Instantiating the left branch's codomain at the injected payload
(the ι reduct `leftBranch payload` has the Π codomain at `payload`) carries the dependent branch type to the
eliminator's output type at `inl payload`.  The composite substitution collapses to `singleton (inl payload)`
(position 0 ↦ `inl payload`, position k+1 ↦ `var k`). -/
theorem subst0_eitherMatchDependentInlBranchCodomain_inlIota {scope : Nat}
    (motive : RawTerm (scope + 1)) (payload : RawTerm scope) :
    RawTerm.subst0 (eitherMatchDependentInlBranchCodomain motive) payload
      = RawTerm.subst0 motive (eitherInlCell payload) := by
  unfold eitherMatchDependentInlBranchCodomain RawTerm.subst0
  rw [RawTerm.subst_compose]
  apply RawTerm.subst_pointwise
  intro position
  match position with
  | ⟨0, _⟩ => rfl
  | ⟨_k + 1, _⟩ => rfl

/-- **The inl-branch codomain identity UNDER AN OUTER SUBSTITUTION** (the FT-bridge generalization of
`subst0_eitherMatchDependentInlBranchCodomain_inlIota`).  In the bounded fundamental theorem the inl obligation
is discharged under a closing substitution `tailSubst`, and the single injection binder is filled with the
payload.  The type-side substitution `cons payload tailSubst` composes with the codomain's defining re-basing
to `cons (inl payload) tailSubst`, which `subst_cons_eq_subst0_lift` presents as
`subst0 (subst (lift tailSubst) motive) (inl payload)` — the dependent eliminator's output type at
`inl payload` under `tailSubst`.  The ι pin is the `tailSubst = singleton`-tail special case. -/
theorem subst_eitherMatchDependentInlBranchCodomain_general {scope targetScope : Nat}
    (motive : RawTerm (scope + 1)) (payload : RawTerm targetScope)
    (tailSubst : RawTermSubst scope targetScope) :
    RawTerm.subst (RawTermSubst.cons payload tailSubst)
        (eitherMatchDependentInlBranchCodomain motive)
      = RawTerm.subst0 (RawTerm.subst (RawTermSubst.lift tailSubst) motive) (eitherInlCell payload) := by
  rw [← RawTerm.subst_cons_eq_subst0_lift motive (eitherInlCell payload) tailSubst]
  unfold eitherMatchDependentInlBranchCodomain
  rw [RawTerm.subst_compose]
  apply RawTerm.subst_pointwise
  intro position
  match position with
  | ⟨0, _⟩ => rfl
  | ⟨_k + 1, _⟩ => rfl

/-- **Substitution naturality of the dependent inl-branch codomain** (the substitution-stability obligation for
the dependent `eitherMatch` rule's inl premise, consumed by `HasTypeUnion.substRespectingContext`).
Substituting under the single injection binder (`lift substitution`) commutes with the motive re-basing.
Proof by the polynomial-monad substitution law (`subst_compose` twice) over a two-arm `Fin` match: position 0
↦ `inl (var 0)` on both sides (`rfl`); position k+1 ↦ the ambient context var shifted up by one — the LHS reads
`lift σ` at `k+1` (`weaken (σ k)`), the RHS strips the injection-binder substituent via `weaken_subst_cons`,
and both land on `subst (shift-by-1) (σ k)` (the renaming bridge `weaken_eq_substShiftBy1`). -/
theorem subst_eitherMatchDependentInlBranchCodomain_substLift {scope targetScope : Nat}
    (motive : RawTerm (scope + 1)) (substitution : RawTermSubst scope targetScope) :
    RawTerm.subst (RawTermSubst.lift substitution)
        (eitherMatchDependentInlBranchCodomain motive)
      = eitherMatchDependentInlBranchCodomain (RawTerm.subst (RawTermSubst.lift substitution) motive) := by
  unfold eitherMatchDependentInlBranchCodomain
  rw [RawTerm.subst_compose, RawTerm.subst_compose]
  apply RawTerm.subst_pointwise
  intro position
  cases position with
  | mk positionValue positionBound =>
    cases positionValue with
    | zero => rfl
    | succ priorValue =>
        dsimp only [RawTermSubst.compose, RawTermSubst.lift, RawTermSubst.cons]
        simp only [RawTerm.weaken_eq_rename]
        rw [RawTerm.weaken_subst_cons, ← weaken_eq_substShiftBy1]
        rfl

/-- **`iterateLiftRaw` form** of `subst_eitherMatchDependentInlBranchCodomain_substLift` — the shape the union
substitution-stability arm consumes, where the single injection binder is crossed via `iterateLiftRaw _ 1`
(definitionally `lift _`, by the structural `Nat` recursion of `iterateLiftRaw` + the `liftForRaw` instance). -/
theorem subst_eitherMatchDependentInlBranchCodomain_iterateLift {scope targetScope : Nat}
    (motive : RawTerm (scope + 1)) (substitution : RawTermSubst scope targetScope) :
    RawTerm.subst (iterateLiftRaw substitution 1)
        (eitherMatchDependentInlBranchCodomain motive)
      = eitherMatchDependentInlBranchCodomain (RawTerm.subst (iterateLiftRaw substitution 1) motive) :=
  subst_eitherMatchDependentInlBranchCodomain_substLift motive substitution

/-- **Renaming naturality of the dependent inl-branch codomain** — the RENAME twin of
`subst_eitherMatchDependentInlBranchCodomain_iterateLift`, the form the union renaming-stability arm
(`HasTypeUnion.renameRespectsContext`) consumes.  Routed through the substitution version via the
renaming-as-substitution bridge and the `ofRenaming`/`iterateLiftRaw` pointwise commutation. -/
theorem rename_eitherMatchDependentInlBranchCodomain_iterateLift {scope targetScope : Nat}
    (motive : RawTerm (scope + 1)) (someRenaming : RawRenaming scope targetScope) :
    RawTerm.rename (iterateLiftRaw someRenaming 1)
        (eitherMatchDependentInlBranchCodomain motive)
      = eitherMatchDependentInlBranchCodomain (RawTerm.rename (iterateLiftRaw someRenaming 1) motive) := by
  rw [RawTerm.rename_eq_subst_ofRenaming (iterateLiftRaw someRenaming 1),
    ← RawTerm.subst_pointwise (RawTermSubst.ofRenaming_iterateLift_pointwise someRenaming 1),
    subst_eitherMatchDependentInlBranchCodomain_iterateLift,
    RawTerm.subst_pointwise (RawTermSubst.ofRenaming_iterateLift_pointwise someRenaming 1),
    ← RawTerm.rename_eq_subst_ofRenaming (iterateLiftRaw someRenaming 1)]

/-! ## The `inr` branch codomain (the right-injection twin) -/

/-- The dependent `inr`-branch codomain: `motive` re-based at `inr (var 0)` (the single injection binder),
the motive's context shifted past that one fresh binder.  The classifier BODY of the right branch
`(b : B) → motive (inr b)`. -/
def eitherMatchDependentInrBranchCodomain {scope : Nat} (motive : RawTerm (scope + 1)) :
    RawTerm (scope + 1) :=
  RawTerm.subst
    (RawTermSubst.cons
      (eitherInrCell (.mkGen .gen_var ⟨0, Nat.zero_lt_succ scope⟩ .childNil))
      (fun position => .mkGen .gen_var ⟨position.val + 1, Nat.add_lt_add_right position.isLt 1⟩ .childNil))
    motive

/-- **The inr-ι type-preservation pin** — the `inr` twin of
`subst0_eitherMatchDependentInlBranchCodomain_inlIota`. -/
theorem subst0_eitherMatchDependentInrBranchCodomain_inrIota {scope : Nat}
    (motive : RawTerm (scope + 1)) (payload : RawTerm scope) :
    RawTerm.subst0 (eitherMatchDependentInrBranchCodomain motive) payload
      = RawTerm.subst0 motive (eitherInrCell payload) := by
  unfold eitherMatchDependentInrBranchCodomain RawTerm.subst0
  rw [RawTerm.subst_compose]
  apply RawTerm.subst_pointwise
  intro position
  match position with
  | ⟨0, _⟩ => rfl
  | ⟨_k + 1, _⟩ => rfl

/-- **The inr-branch codomain identity UNDER AN OUTER SUBSTITUTION** — the `inr` twin of
`subst_eitherMatchDependentInlBranchCodomain_general`. -/
theorem subst_eitherMatchDependentInrBranchCodomain_general {scope targetScope : Nat}
    (motive : RawTerm (scope + 1)) (payload : RawTerm targetScope)
    (tailSubst : RawTermSubst scope targetScope) :
    RawTerm.subst (RawTermSubst.cons payload tailSubst)
        (eitherMatchDependentInrBranchCodomain motive)
      = RawTerm.subst0 (RawTerm.subst (RawTermSubst.lift tailSubst) motive) (eitherInrCell payload) := by
  rw [← RawTerm.subst_cons_eq_subst0_lift motive (eitherInrCell payload) tailSubst]
  unfold eitherMatchDependentInrBranchCodomain
  rw [RawTerm.subst_compose]
  apply RawTerm.subst_pointwise
  intro position
  match position with
  | ⟨0, _⟩ => rfl
  | ⟨_k + 1, _⟩ => rfl

/-- **Substitution naturality of the dependent inr-branch codomain** — the `inr` twin of
`subst_eitherMatchDependentInlBranchCodomain_substLift`. -/
theorem subst_eitherMatchDependentInrBranchCodomain_substLift {scope targetScope : Nat}
    (motive : RawTerm (scope + 1)) (substitution : RawTermSubst scope targetScope) :
    RawTerm.subst (RawTermSubst.lift substitution)
        (eitherMatchDependentInrBranchCodomain motive)
      = eitherMatchDependentInrBranchCodomain (RawTerm.subst (RawTermSubst.lift substitution) motive) := by
  unfold eitherMatchDependentInrBranchCodomain
  rw [RawTerm.subst_compose, RawTerm.subst_compose]
  apply RawTerm.subst_pointwise
  intro position
  cases position with
  | mk positionValue positionBound =>
    cases positionValue with
    | zero => rfl
    | succ priorValue =>
        dsimp only [RawTermSubst.compose, RawTermSubst.lift, RawTermSubst.cons]
        simp only [RawTerm.weaken_eq_rename]
        rw [RawTerm.weaken_subst_cons, ← weaken_eq_substShiftBy1]
        rfl

/-- **`iterateLiftRaw` form** of `subst_eitherMatchDependentInrBranchCodomain_substLift`. -/
theorem subst_eitherMatchDependentInrBranchCodomain_iterateLift {scope targetScope : Nat}
    (motive : RawTerm (scope + 1)) (substitution : RawTermSubst scope targetScope) :
    RawTerm.subst (iterateLiftRaw substitution 1)
        (eitherMatchDependentInrBranchCodomain motive)
      = eitherMatchDependentInrBranchCodomain (RawTerm.subst (iterateLiftRaw substitution 1) motive) :=
  subst_eitherMatchDependentInrBranchCodomain_substLift motive substitution

/-- **Renaming naturality of the dependent inr-branch codomain** — the `inr` twin of
`rename_eitherMatchDependentInlBranchCodomain_iterateLift`. -/
theorem rename_eitherMatchDependentInrBranchCodomain_iterateLift {scope targetScope : Nat}
    (motive : RawTerm (scope + 1)) (someRenaming : RawRenaming scope targetScope) :
    RawTerm.rename (iterateLiftRaw someRenaming 1)
        (eitherMatchDependentInrBranchCodomain motive)
      = eitherMatchDependentInrBranchCodomain (RawTerm.rename (iterateLiftRaw someRenaming 1) motive) := by
  rw [RawTerm.rename_eq_subst_ofRenaming (iterateLiftRaw someRenaming 1),
    ← RawTerm.subst_pointwise (RawTermSubst.ofRenaming_iterateLift_pointwise someRenaming 1),
    subst_eitherMatchDependentInrBranchCodomain_iterateLift,
    RawTerm.subst_pointwise (RawTermSubst.ofRenaming_iterateLift_pointwise someRenaming 1),
    ← RawTerm.rename_eq_subst_ofRenaming (iterateLiftRaw someRenaming 1)]

/-! ## The branch TYPES (the `piTyCodeCell`-wrapped classifiers the rule consumes) -/

/-- The dependent left-branch classifier `(a : leftType) → motive (inl a)` — the `piTyCodeCell` over the
domain type `leftType` and the inl-branch codomain.  The classifier the dependent `eitherMatchElimRule`
assigns to its left-branch obligation. -/
def eitherMatchDependentInlBranchType {scope : Nat} (motive : RawTerm (scope + 1))
    (leftType : RawTerm scope) : RawTerm scope :=
  piTyCodeCell leftType (eitherMatchDependentInlBranchCodomain motive)

/-- The dependent right-branch classifier `(b : rightType) → motive (inr b)` — the `piTyCodeCell` over the
domain type `rightType` and the inr-branch codomain. -/
def eitherMatchDependentInrBranchType {scope : Nat} (motive : RawTerm (scope + 1))
    (rightType : RawTerm scope) : RawTerm scope :=
  piTyCodeCell rightType (eitherMatchDependentInrBranchCodomain motive)

/-! ## Substitution / renaming naturality of the WRAPPED branch types (the union-cascade consumers) -/

/-- **Substitution naturality of the dependent inl-branch TYPE** — the wrapped (`piTyCodeCell`-level) form
the dependent `eitherMatch` rule's `HasTypeUnion.substRespectingContext` arm consumes: substituting the whole
left-branch classifier `(a : A) → motive (inl a)` re-bases the domain by `substitution` and the codomain's
motive by one binder lift.  `subst_piTyCodeCell` (the Π distribution) composed with the codomain naturality
`subst_eitherMatchDependentInlBranchCodomain_iterateLift`.  The `eitherMatch` twin of
`subst_natElimDependentSuccBranchType_iterateLift`. -/
theorem subst_eitherMatchDependentInlBranchType_iterateLift {scope targetScope : Nat}
    (motive : RawTerm (scope + 1)) (leftType : RawTerm scope)
    (substitution : RawTermSubst scope targetScope) :
    RawTerm.subst substitution (eitherMatchDependentInlBranchType motive leftType)
      = eitherMatchDependentInlBranchType (RawTerm.subst (iterateLiftRaw substitution 1) motive)
          (RawTerm.subst substitution leftType) := by
  unfold eitherMatchDependentInlBranchType
  rw [subst_piTyCodeCell, subst_eitherMatchDependentInlBranchCodomain_iterateLift]

/-- **Substitution naturality of the dependent inr-branch TYPE** — the `inr` twin of
`subst_eitherMatchDependentInlBranchType_iterateLift`. -/
theorem subst_eitherMatchDependentInrBranchType_iterateLift {scope targetScope : Nat}
    (motive : RawTerm (scope + 1)) (rightType : RawTerm scope)
    (substitution : RawTermSubst scope targetScope) :
    RawTerm.subst substitution (eitherMatchDependentInrBranchType motive rightType)
      = eitherMatchDependentInrBranchType (RawTerm.subst (iterateLiftRaw substitution 1) motive)
          (RawTerm.subst substitution rightType) := by
  unfold eitherMatchDependentInrBranchType
  rw [subst_piTyCodeCell, subst_eitherMatchDependentInrBranchCodomain_iterateLift]

/-- **Renaming naturality of the dependent inl-branch TYPE** — the RENAME twin of
`subst_eitherMatchDependentInlBranchType_iterateLift`, the form the union renaming-stability arm
(`HasTypeUnion.renameRespectsContext`) consumes.  `rename_piTyCodeCell` composed with the codomain rename
naturality `rename_eitherMatchDependentInlBranchCodomain_iterateLift`. -/
theorem rename_eitherMatchDependentInlBranchType_iterateLift {scope targetScope : Nat}
    (motive : RawTerm (scope + 1)) (leftType : RawTerm scope)
    (someRenaming : RawRenaming scope targetScope) :
    RawTerm.rename someRenaming (eitherMatchDependentInlBranchType motive leftType)
      = eitherMatchDependentInlBranchType (RawTerm.rename (iterateLiftRaw someRenaming 1) motive)
          (RawTerm.rename someRenaming leftType) := by
  unfold eitherMatchDependentInlBranchType
  rw [rename_piTyCodeCell, rename_eitherMatchDependentInlBranchCodomain_iterateLift]

/-- **Renaming naturality of the dependent inr-branch TYPE** — the `inr` twin of
`rename_eitherMatchDependentInlBranchType_iterateLift`. -/
theorem rename_eitherMatchDependentInrBranchType_iterateLift {scope targetScope : Nat}
    (motive : RawTerm (scope + 1)) (rightType : RawTerm scope)
    (someRenaming : RawRenaming scope targetScope) :
    RawTerm.rename someRenaming (eitherMatchDependentInrBranchType motive rightType)
      = eitherMatchDependentInrBranchType (RawTerm.rename (iterateLiftRaw someRenaming 1) motive)
          (RawTerm.rename someRenaming rightType) := by
  unfold eitherMatchDependentInrBranchType
  rw [rename_piTyCodeCell, rename_eitherMatchDependentInrBranchCodomain_iterateLift]

end FX1Poly.Typed
