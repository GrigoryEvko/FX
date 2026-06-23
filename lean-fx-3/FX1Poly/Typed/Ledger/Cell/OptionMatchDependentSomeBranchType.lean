import FX1Poly.Typed.Ledger.Cell.CellConstructors
import FX1Poly.Typed.Ledger.Cell.CellSubstitution
import FX1Poly.Typed.Ledger.Cell.CellRenaming
import FX1Poly.Typed.Ledger.Cell.EitherMatchDependentBranchType
import FX1Poly.Tier0.Term.Subst.RawTermSubstCompose
import FX1Poly.Tier0.Term.Subst.RawTermSubstPointwise
import FX1Poly.Tier0.Term.Subst.RawTermSubst0
import FX1Poly.Tier0.Term.Subst.RawTermSubstConsCommute
import FX1Poly.Tier0.Term.Rename.RawTermRenameAsSubst
import FX1Poly.Tier0.Term.Rename.RawTermRenameComposeFusion

/-! # FX1Poly/Typed/Ledger/Cell/OptionMatchDependentSomeBranchType
    — the dependent `optionMatch` `some` branch CODOMAIN (the one-binder dependent-eliminator branch crux)

The dependent option eliminator `optionMatch motive noneBranch someBranch scrutinee` carries a motive
`motive : RawTerm (scope + 1)` (`var 0` = the option scrutinee) and TWO branches.  Unlike `eitherMatch`'s two
Π-typed branches, option is a `bool`/`either` HYBRID: the `none` branch is NULLARY (its dependent classifier is
the binder-free `subst0 motive optionNoneCell`, `bool`-style — no codomain ledger needed) and only the `some`
branch is a single-binder dependent function `someBranch : (a : A) → motive (some a)` (`either`-style).
Eliminating a `some payload` reduces (ι) to `someBranch payload`, whose type is the Π codomain instantiated at
`payload` — and subject reduction needs that to be the eliminator's output type `motive (some payload)`.

This file ships the SOME-branch codomain (the `option` analogue of `eitherMatchDependentInlBranchCodomain`,
with `optionSomeCell` in place of `eitherInlCell`) and the naturality laws it needs:

  * the ι type-preservation pin (`subst0 codomain payload = subst0 motive (some payload)`) — subject reduction
    for the `some`-ι reduct `someBranch payload`;
  * the FT-bridge general form (under an outer closing substitution `tailSubst`);
  * substitution / renaming stability (for `HasTypeUnion.substRespectingContext` / `renameRespectsContext`);
  * the `piTyCodeCell`-wrapped `optionMatchDependentSomeBranchType` + its subst/rename naturality wrappers.

`weaken_eq_substShiftBy1` is reused from `EitherMatchDependentBranchType` (the shared single-binder weakening
bridge).  There is no `none`-side codomain — the `none` branch obligation is `subst0 motive optionNoneCell`
directly (the `bool`-style nullary classifier), discharged in the rule without a ledger entry.

## Zero-axiom verification

`RawTerm.subst_compose` + `RawTerm.subst_pointwise` (axiom-free term-axis polynomial-monad laws) over a two-arm
`Fin` match; the per-position arms compute by `rfl`.  The single-binder weakening reconciliation routes through
`weaken_subst_cons` + `weaken_eq_substShiftBy1` (the renaming-as-substitution bridge).  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Tier0.Syntax

/-! ## The `some` branch codomain -/

/-- The dependent `some`-branch codomain: `motive` re-based at `some (var 0)` (the single value binder), the
motive's context shifted past that one fresh binder.  The classifier BODY of the some branch
`(a : A) → motive (some a)` — under the `a : A` binder the result type is `motive (some a)`. -/
def optionMatchDependentSomeBranchCodomain {scope : Nat} (motive : RawTerm (scope + 1)) :
    RawTerm (scope + 1) :=
  RawTerm.subst
    (RawTermSubst.cons
      (optionSomeCell (.mkGen .gen_var ⟨0, Nat.zero_lt_succ scope⟩ .childNil))
      (fun position => .mkGen .gen_var ⟨position.val + 1, Nat.add_lt_add_right position.isLt 1⟩ .childNil))
    motive

/-- **The some-ι type-preservation pin.**  Instantiating the some branch's codomain at the injected payload
(the ι reduct `someBranch payload` has the Π codomain at `payload`) carries the dependent branch type to the
eliminator's output type at `some payload`.  The composite substitution collapses to `singleton (some payload)`
(position 0 ↦ `some payload`, position k+1 ↦ `var k`). -/
theorem subst0_optionMatchDependentSomeBranchCodomain_someIota {scope : Nat}
    (motive : RawTerm (scope + 1)) (payload : RawTerm scope) :
    RawTerm.subst0 (optionMatchDependentSomeBranchCodomain motive) payload
      = RawTerm.subst0 motive (optionSomeCell payload) := by
  unfold optionMatchDependentSomeBranchCodomain RawTerm.subst0
  rw [RawTerm.subst_compose]
  apply RawTerm.subst_pointwise
  intro position
  match position with
  | ⟨0, _⟩ => rfl
  | ⟨_k + 1, _⟩ => rfl

/-- **The some-branch codomain identity UNDER AN OUTER SUBSTITUTION** (the FT-bridge generalization of
`subst0_optionMatchDependentSomeBranchCodomain_someIota`).  In the bounded fundamental theorem the some
obligation is discharged under a closing substitution `tailSubst`, with the single value binder filled by the
payload.  The type-side substitution `cons payload tailSubst` composes with the codomain's defining re-basing
to `cons (some payload) tailSubst`, which `subst_cons_eq_subst0_lift` presents as
`subst0 (subst (lift tailSubst) motive) (some payload)` — the dependent eliminator's output type at
`some payload` under `tailSubst`. -/
theorem subst_optionMatchDependentSomeBranchCodomain_general {scope targetScope : Nat}
    (motive : RawTerm (scope + 1)) (payload : RawTerm targetScope)
    (tailSubst : RawTermSubst scope targetScope) :
    RawTerm.subst (RawTermSubst.cons payload tailSubst)
        (optionMatchDependentSomeBranchCodomain motive)
      = RawTerm.subst0 (RawTerm.subst (RawTermSubst.lift tailSubst) motive) (optionSomeCell payload) := by
  rw [← RawTerm.subst_cons_eq_subst0_lift motive (optionSomeCell payload) tailSubst]
  unfold optionMatchDependentSomeBranchCodomain
  rw [RawTerm.subst_compose]
  apply RawTerm.subst_pointwise
  intro position
  match position with
  | ⟨0, _⟩ => rfl
  | ⟨_k + 1, _⟩ => rfl

/-- **Substitution naturality of the dependent some-branch codomain** (the substitution-stability obligation for
the dependent `optionMatch` rule's some premise, consumed by `HasTypeUnion.substRespectingContext`).
Substituting under the single value binder (`lift substitution`) commutes with the motive re-basing.  Proof by
the polynomial-monad substitution law (`subst_compose` twice) over a two-arm `Fin` match: position 0 ↦
`some (var 0)` on both sides (`rfl`); position k+1 ↦ the ambient context var shifted up by one (`weaken_subst_cons`
+ the renaming bridge `weaken_eq_substShiftBy1`). -/
theorem subst_optionMatchDependentSomeBranchCodomain_substLift {scope targetScope : Nat}
    (motive : RawTerm (scope + 1)) (substitution : RawTermSubst scope targetScope) :
    RawTerm.subst (RawTermSubst.lift substitution)
        (optionMatchDependentSomeBranchCodomain motive)
      = optionMatchDependentSomeBranchCodomain (RawTerm.subst (RawTermSubst.lift substitution) motive) := by
  unfold optionMatchDependentSomeBranchCodomain
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

/-- **`iterateLiftRaw` form** of `subst_optionMatchDependentSomeBranchCodomain_substLift` — the shape the union
substitution-stability arm consumes (`iterateLiftRaw _ 1` is definitionally `lift _`). -/
theorem subst_optionMatchDependentSomeBranchCodomain_iterateLift {scope targetScope : Nat}
    (motive : RawTerm (scope + 1)) (substitution : RawTermSubst scope targetScope) :
    RawTerm.subst (iterateLiftRaw substitution 1)
        (optionMatchDependentSomeBranchCodomain motive)
      = optionMatchDependentSomeBranchCodomain (RawTerm.subst (iterateLiftRaw substitution 1) motive) :=
  subst_optionMatchDependentSomeBranchCodomain_substLift motive substitution

/-- **Renaming naturality of the dependent some-branch codomain** — the RENAME twin of
`subst_optionMatchDependentSomeBranchCodomain_iterateLift`, the form the union renaming-stability arm
(`HasTypeUnion.renameRespectsContext`) consumes.  Routed through the substitution version via the
renaming-as-substitution bridge and the `ofRenaming`/`iterateLiftRaw` pointwise commutation. -/
theorem rename_optionMatchDependentSomeBranchCodomain_iterateLift {scope targetScope : Nat}
    (motive : RawTerm (scope + 1)) (someRenaming : RawRenaming scope targetScope) :
    RawTerm.rename (iterateLiftRaw someRenaming 1)
        (optionMatchDependentSomeBranchCodomain motive)
      = optionMatchDependentSomeBranchCodomain (RawTerm.rename (iterateLiftRaw someRenaming 1) motive) := by
  rw [RawTerm.rename_eq_subst_ofRenaming (iterateLiftRaw someRenaming 1),
    ← RawTerm.subst_pointwise (RawTermSubst.ofRenaming_iterateLift_pointwise someRenaming 1),
    subst_optionMatchDependentSomeBranchCodomain_iterateLift,
    RawTerm.subst_pointwise (RawTermSubst.ofRenaming_iterateLift_pointwise someRenaming 1),
    ← RawTerm.rename_eq_subst_ofRenaming (iterateLiftRaw someRenaming 1)]

/-! ## The branch TYPE (the `piTyCodeCell`-wrapped classifier the rule consumes) -/

/-- The dependent some-branch classifier `(a : valueType) → motive (some a)` — the `piTyCodeCell` over the
domain type `valueType` and the some-branch codomain.  The classifier the dependent `optionMatchElimRule`
assigns to its some-branch obligation. -/
def optionMatchDependentSomeBranchType {scope : Nat} (motive : RawTerm (scope + 1))
    (valueType : RawTerm scope) : RawTerm scope :=
  piTyCodeCell valueType (optionMatchDependentSomeBranchCodomain motive)

/-- **Substitution naturality of the dependent some-branch TYPE** — the wrapped (`piTyCodeCell`-level) form the
dependent `optionMatch` rule's `HasTypeUnion.substRespectingContext` arm consumes.  `subst_piTyCodeCell` (the Π
distribution) composed with the codomain naturality `subst_optionMatchDependentSomeBranchCodomain_iterateLift`. -/
theorem subst_optionMatchDependentSomeBranchType_iterateLift {scope targetScope : Nat}
    (motive : RawTerm (scope + 1)) (valueType : RawTerm scope)
    (substitution : RawTermSubst scope targetScope) :
    RawTerm.subst substitution (optionMatchDependentSomeBranchType motive valueType)
      = optionMatchDependentSomeBranchType (RawTerm.subst (iterateLiftRaw substitution 1) motive)
          (RawTerm.subst substitution valueType) := by
  unfold optionMatchDependentSomeBranchType
  rw [subst_piTyCodeCell, subst_optionMatchDependentSomeBranchCodomain_iterateLift]

/-- **Renaming naturality of the dependent some-branch TYPE** — the RENAME twin of
`subst_optionMatchDependentSomeBranchType_iterateLift`.  `rename_piTyCodeCell` composed with the codomain rename
naturality `rename_optionMatchDependentSomeBranchCodomain_iterateLift`. -/
theorem rename_optionMatchDependentSomeBranchType_iterateLift {scope targetScope : Nat}
    (motive : RawTerm (scope + 1)) (valueType : RawTerm scope)
    (someRenaming : RawRenaming scope targetScope) :
    RawTerm.rename someRenaming (optionMatchDependentSomeBranchType motive valueType)
      = optionMatchDependentSomeBranchType (RawTerm.rename (iterateLiftRaw someRenaming 1) motive)
          (RawTerm.rename someRenaming valueType) := by
  unfold optionMatchDependentSomeBranchType
  rw [rename_piTyCodeCell, rename_optionMatchDependentSomeBranchCodomain_iterateLift]

end FX1Poly.Typed
