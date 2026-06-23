import FX1Poly.Typed.Ledger.Cell.CellConstructors
import FX1Poly.Typed.Ledger.Cell.CellSubstitution
import FX1Poly.Typed.Ledger.Cell.CellRenaming
import FX1Poly.Typed.Ledger.Cell.NatElimDependentSuccType
import FX1Poly.Tier0.Term.Subst.RawTermSubstCompose
import FX1Poly.Tier0.Term.Subst.RawTermSubstPointwise
import FX1Poly.Tier0.Term.Subst.RawTermSubst0
import FX1Poly.Tier0.Term.Subst.RawTermSubstConsCommute
import FX1Poly.Tier0.Term.Rename.RawTermRenameAsSubst
import FX1Poly.Tier0.Term.Rename.RawTermRenameComposeFusion

/-! # FX1Poly/Typed/Ledger/Cell/ListElimDependentConsType
    — the dependent `listElim` CONS-branch type (DEP-LIST sub-D1, the three-binder recursive Pi crux)

The dependent recursive eliminator `listElim motive nilBranch consBranch scrutinee` carries a motive
`motive : RawTerm (scope + 1)` (`var 0` = the list scrutinee) and a cons branch that is a THREE-binder
dependent function:

  `consBranch : (head : A) → (tail : List A) → (rec : motive tail) → motive (cons head tail)`.

Unlike `boolElim`'s NULLARY branches and unlike `eitherMatch`'s / `optionMatch`'s ONE-binder injection
branches, and unlike `natElim`'s succ branch (whose ι reduct SUBSTITUTES — so its classifier is the bare
re-based codomain at `scope + 2`, binder-form), the `list` cons-ι reduct is an APP SPINE
(`app (app (app consBranch head) tail) (listElim … tail)`, no substitution).  So the cons branch is a Π-typed
VALUE at `scope` — the binary, recursive generalization of `eitherMatch`'s inl/inr branches: TWO data binders
(`head : A`, `tail : List A`) plus a recursive-result binder (`rec : motive tail`) whose type is itself motive
dependent.

This file ships the two motive re-basings the three-binder Π needs, with the same naturality discipline as the
nat / either dependent branch types:

  * `listElimDependentConsBranchCodomain motive` (at `scope + 3`) — `motive` re-based at `cons (var 2) (var 1)`
    (`head`, `tail`), the motive's own context shifted past the three cons binders.  The codomain of the cons
    branch's innermost Π — under `head`, `tail`, `rec` the result type is `motive (cons head tail)`.
  * `listElimDependentRecBinderType motive` (at `scope + 2`) — `motive` re-based at `var 0` (`tail`), the
    motive's context shifted past the `head` binder.  The recursive-result binder's type `motive tail` under
    `head`, `tail`.

plus, for each re-basing, the same four laws the nat / either branch types ship:

  * the ι type-preservation pin (`subst (cons rec (cons tail (singleton head))) codomain
    = subst0 motive (cons head tail)`) — the three-binder collapse the cons-ι app-spine output type rides;
  * the FT-bridge general form (under an outer closing substitution `tailSubst`);
  * substitution-stability (`lift³` for the codomain, `lift²` for the rec-binder type) for
    `HasTypeUnion.substRespectingContext`;
  * renaming-stability (the `iterateLiftRaw _ 3` / `_ 2` rename twins) for
    `HasTypeUnion.renameRespectsContext`.

`listElimDependentConsBranchType motive elementType` wraps the two re-basings in the three nested
`piTyCodeCell`s — the classifier the dependent `listElimRule` assigns to its cons-branch obligation.  The
substitution / renaming naturality of the WRAPPED type lives downstream with the cascade (it needs
`subst_listTypeCell` / `rename_listTypeCell`, which sit in the union layer, not the cell ledger).

## Zero-axiom verification

`RawTerm.subst_compose` + `RawTerm.subst_pointwise` (axiom-free term-axis polynomial-monad laws) over two-arm
`Fin` matches; the per-position arms compute by `rfl`.  The three-binder weakening's bound is
`Nat.add_lt_add_right` (NO `omega`); the deep position-(k+1) reconciliation routes `weaken` through
`weaken_subst_cons` + the triple-shift renaming bridge `tripleWeaken_eq_substShiftBy3` (the `+3` analog of
`natElim`'s `doubleWeaken_eq_substShiftBy2`).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Tier0.Syntax

/-- **Triple weakening as the shift-by-three substitution.**  `weaken ∘ weaken ∘ weaken` (raise scope by three
via three `Fin.succ` shifts) equals substituting every variable by the variable shifted up by three — the
substitution `fun position => var (position + 3)`.  The `+3` analog of `natElim`'s `doubleWeaken_eq_substShiftBy2`;
consumed by the dependent cons-branch codomain naturality to reconcile the triply-lifted substitution's variable
image at `k + 3` (`lift³ σ` reads `weaken (weaken (weaken (σ k)))`) with the cons-tail triple-shift the codomain
re-basing carries (`weaken_subst_cons` strips the cons-binder slot, leaving exactly this `shiftBy3`
substitution).  Proof: the renaming-as-substitution bridge at the thrice-composed weakening renaming, whose
injected image is `var (position + 3)`. -/
theorem tripleWeaken_eq_substShiftBy3 {scope : Nat} (sourceTerm : RawTerm scope) :
    RawTerm.weaken (RawTerm.weaken (RawTerm.weaken sourceTerm))
      = RawTerm.subst
          (fun position => .mkGen .gen_var ⟨position.val + 3, Nat.add_lt_add_right position.isLt 3⟩ .childNil)
          sourceTerm := by
  rw [RawTerm.weaken_eq_rename (RawTerm.weaken (RawTerm.weaken sourceTerm)),
    RawTerm.weaken_eq_rename (RawTerm.weaken sourceTerm),
    RawTerm.weaken_eq_rename sourceTerm,
    RawTerm.rename_compose, RawTerm.rename_compose]
  exact RawTerm.rename_eq_subst_ofRenaming
    (RawRenaming.compose (RawRenaming.compose RawRenaming.weaken RawRenaming.weaken) RawRenaming.weaken)
    sourceTerm

/-! ## The cons-branch codomain `motive (cons head tail)` (at `scope + 3`) -/

/-- The dependent cons-branch codomain: `motive` re-based at `cons (var 2) (var 1)` (the `head` / `tail`
binders), the motive's own context shifted past the three cons binders (`var 0` = recursive result, `var 1` =
tail, `var 2` = head).  The result type of the cons branch under `head`, `tail`, `rec`. -/
def listElimDependentConsBranchCodomain {scope : Nat} (motive : RawTerm (scope + 1)) :
    RawTerm (scope + 3) :=
  RawTerm.subst
    (RawTermSubst.cons
      (listConsCell
        (.mkGen .gen_var ⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ scope))⟩ .childNil)
        (.mkGen .gen_var ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ (scope + 1))⟩ .childNil))
      (fun position => .mkGen .gen_var ⟨position.val + 3, Nat.add_lt_add_right position.isLt 3⟩ .childNil))
    motive

/-- **The cons-ι type-preservation pin.**  The cons-ι reduct is the app spine
`app (app (app consBranch head) tail) (listElim … tail)`, whose output type is the cons branch's innermost Π
codomain with the three binders filled by `head`, `tail`, and the recursive call.  Filling the codomain's three
binders (`var 0` ↦ recursive call, irrelevant to the type; `var 1` ↦ tail; `var 2` ↦ head) carries the
dependent codomain to the eliminator's output type at `cons head tail`.  The composite substitution collapses
to `singleton (cons head tail)` (position 0 ↦ `cons head tail`, position k+1 ↦ `var k`). -/
theorem subst_listElimDependentConsBranchCodomain_consIota {scope : Nat}
    (motive : RawTerm (scope + 1)) (recursiveResult tailVal headVal : RawTerm scope) :
    RawTerm.subst
        (RawTermSubst.cons recursiveResult (RawTermSubst.cons tailVal (RawTermSubst.singleton headVal)))
        (listElimDependentConsBranchCodomain motive)
      = RawTerm.subst0 motive (listConsCell headVal tailVal) := by
  unfold listElimDependentConsBranchCodomain RawTerm.subst0
  rw [RawTerm.subst_compose]
  apply RawTerm.subst_pointwise
  intro position
  match position with
  | ⟨0, _⟩ => rfl
  | ⟨_k + 1, _⟩ => rfl

/-- **The cons-branch codomain identity UNDER AN OUTER SUBSTITUTION** (the FT-bridge generalization of
`subst_listElimDependentConsBranchCodomain_consIota`).  In the bounded fundamental theorem the cons obligation
is discharged under a closing substitution `tailSubst`, and the three cons binders are filled with the recursive
call (irrelevant to the type), the tail, and the head.  The type-side substitution
`cons recursiveResult (cons tailVal (cons headVal tailSubst))` composes with the codomain's defining re-basing
to `cons (cons headVal tailVal) tailSubst`, which `subst_cons_eq_subst0_lift` presents as
`subst0 (subst (lift tailSubst) motive) (cons headVal tailVal)` — the dependent eliminator's output type at
`cons headVal tailVal` under `tailSubst`.  The ι pin is the `tailSubst = singleton`-tail special case. -/
theorem subst_listElimDependentConsBranchCodomain_general {scope targetScope : Nat}
    (motive : RawTerm (scope + 1)) (recursiveResult tailVal headVal : RawTerm targetScope)
    (tailSubst : RawTermSubst scope targetScope) :
    RawTerm.subst
        (RawTermSubst.cons recursiveResult (RawTermSubst.cons tailVal (RawTermSubst.cons headVal tailSubst)))
        (listElimDependentConsBranchCodomain motive)
      = RawTerm.subst0 (RawTerm.subst (RawTermSubst.lift tailSubst) motive) (listConsCell headVal tailVal) := by
  rw [← RawTerm.subst_cons_eq_subst0_lift motive (listConsCell headVal tailVal) tailSubst]
  unfold listElimDependentConsBranchCodomain
  rw [RawTerm.subst_compose]
  apply RawTerm.subst_pointwise
  intro position
  match position with
  | ⟨0, _⟩ => rfl
  | ⟨_k + 1, _⟩ => rfl

/-- **Substitution naturality of the dependent cons-branch codomain** (the substitution-stability obligation for
the dependent `listElim` rule's cons premise codomain, the depth-3 analog of
`subst_natElimDependentSuccBranchType_substLiftLift`).  Substituting under the three cons binders
(`lift (lift (lift substitution))`) commutes with the motive re-basing.  Two-arm `Fin` match: position 0 ↦
`cons (var 2) (var 1)` on both sides (`rfl`); position k+1 ↦ the ambient context var shifted up by three — the
LHS reads `lift³` at `k+3` (`weaken∘weaken∘weaken`), the RHS strips the cons-binder substituent via
`weaken_subst_cons`, and both land on the `shiftBy3` substitution (`tripleWeaken_eq_substShiftBy3`). -/
theorem subst_listElimDependentConsBranchCodomain_substLiftLiftLift {scope targetScope : Nat}
    (motive : RawTerm (scope + 1)) (substitution : RawTermSubst scope targetScope) :
    RawTerm.subst (RawTermSubst.lift (RawTermSubst.lift (RawTermSubst.lift substitution)))
        (listElimDependentConsBranchCodomain motive)
      = listElimDependentConsBranchCodomain (RawTerm.subst (RawTermSubst.lift substitution) motive) := by
  unfold listElimDependentConsBranchCodomain
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
        rw [RawTerm.weaken_subst_cons, ← tripleWeaken_eq_substShiftBy3]
        rfl

/-- **`iterateLiftRaw` form** of `subst_listElimDependentConsBranchCodomain_substLiftLiftLift` — the shape the
union substitution-stability arm consumes, where the three cons binders are crossed via `iterateLiftRaw _ 3`
(definitionally `lift (lift (lift _))`, by the structural `Nat` recursion of `iterateLiftRaw` + the `liftForRaw`
instance), so it closes by the underlying lemma directly. -/
theorem subst_listElimDependentConsBranchCodomain_iterateLift {scope targetScope : Nat}
    (motive : RawTerm (scope + 1)) (substitution : RawTermSubst scope targetScope) :
    RawTerm.subst (iterateLiftRaw substitution 3)
        (listElimDependentConsBranchCodomain motive)
      = listElimDependentConsBranchCodomain (RawTerm.subst (iterateLiftRaw substitution 1) motive) :=
  subst_listElimDependentConsBranchCodomain_substLiftLiftLift motive substitution

/-- **Renaming naturality of the dependent cons-branch codomain** — the RENAME twin of
`subst_listElimDependentConsBranchCodomain_iterateLift`, routed through the substitution version via the
renaming-as-substitution bridge and the `ofRenaming`/`iterateLiftRaw` pointwise commutation. -/
theorem rename_listElimDependentConsBranchCodomain_iterateLift {scope targetScope : Nat}
    (motive : RawTerm (scope + 1)) (someRenaming : RawRenaming scope targetScope) :
    RawTerm.rename (iterateLiftRaw someRenaming 3)
        (listElimDependentConsBranchCodomain motive)
      = listElimDependentConsBranchCodomain (RawTerm.rename (iterateLiftRaw someRenaming 1) motive) := by
  rw [RawTerm.rename_eq_subst_ofRenaming (iterateLiftRaw someRenaming 3),
    ← RawTerm.subst_pointwise (RawTermSubst.ofRenaming_iterateLift_pointwise someRenaming 3),
    subst_listElimDependentConsBranchCodomain_iterateLift,
    RawTerm.subst_pointwise (RawTermSubst.ofRenaming_iterateLift_pointwise someRenaming 1),
    ← RawTerm.rename_eq_subst_ofRenaming (iterateLiftRaw someRenaming 1)]

/-! ## The recursive-result binder type `motive tail` (at `scope + 2`) -/

/-- The dependent recursive-result binder's type: `motive` re-based at `var 0` (the `tail` binder), the motive's
context shifted past the single `head` binder.  Under `head`, `tail` the recursive-result binder `rec` has type
`motive tail`.  The middle, motive-dependent binder that distinguishes the recursive `list` cons branch from the
non-recursive `either` / `option` injection branches. -/
def listElimDependentRecBinderType {scope : Nat} (motive : RawTerm (scope + 1)) :
    RawTerm (scope + 2) :=
  RawTerm.subst
    (RawTermSubst.cons
      (.mkGen .gen_var ⟨0, Nat.zero_lt_succ (scope + 1)⟩ .childNil)
      (fun position => .mkGen .gen_var ⟨position.val + 2, Nat.add_lt_add_right position.isLt 2⟩ .childNil))
    motive

/-- **Substitution naturality of the dependent recursive-result binder type** (the substitution-stability
obligation for the rec binder's context classifier, the depth-2 twin of the codomain naturality).  Two-arm `Fin`
match: position 0 ↦ `var 0` on both sides (`rfl`); position k+1 ↦ the context var shifted up by two, reconciled
via `weaken_subst_cons` + `doubleWeaken_eq_substShiftBy2`. -/
theorem subst_listElimDependentRecBinderType_substLiftLift {scope targetScope : Nat}
    (motive : RawTerm (scope + 1)) (substitution : RawTermSubst scope targetScope) :
    RawTerm.subst (RawTermSubst.lift (RawTermSubst.lift substitution))
        (listElimDependentRecBinderType motive)
      = listElimDependentRecBinderType (RawTerm.subst (RawTermSubst.lift substitution) motive) := by
  unfold listElimDependentRecBinderType
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
        rw [RawTerm.weaken_subst_cons, ← doubleWeaken_eq_substShiftBy2]
        rfl

/-- **`iterateLiftRaw` form** of `subst_listElimDependentRecBinderType_substLiftLift` (`iterateLiftRaw _ 2`). -/
theorem subst_listElimDependentRecBinderType_iterateLift {scope targetScope : Nat}
    (motive : RawTerm (scope + 1)) (substitution : RawTermSubst scope targetScope) :
    RawTerm.subst (iterateLiftRaw substitution 2)
        (listElimDependentRecBinderType motive)
      = listElimDependentRecBinderType (RawTerm.subst (iterateLiftRaw substitution 1) motive) :=
  subst_listElimDependentRecBinderType_substLiftLift motive substitution

/-- **Renaming naturality of the dependent recursive-result binder type** — the RENAME twin of
`subst_listElimDependentRecBinderType_iterateLift`. -/
theorem rename_listElimDependentRecBinderType_iterateLift {scope targetScope : Nat}
    (motive : RawTerm (scope + 1)) (someRenaming : RawRenaming scope targetScope) :
    RawTerm.rename (iterateLiftRaw someRenaming 2)
        (listElimDependentRecBinderType motive)
      = listElimDependentRecBinderType (RawTerm.rename (iterateLiftRaw someRenaming 1) motive) := by
  rw [RawTerm.rename_eq_subst_ofRenaming (iterateLiftRaw someRenaming 2),
    ← RawTerm.subst_pointwise (RawTermSubst.ofRenaming_iterateLift_pointwise someRenaming 2),
    subst_listElimDependentRecBinderType_iterateLift,
    RawTerm.subst_pointwise (RawTermSubst.ofRenaming_iterateLift_pointwise someRenaming 1),
    ← RawTerm.rename_eq_subst_ofRenaming (iterateLiftRaw someRenaming 1)]

/-! ## The cons-branch TYPE (the three-nested-`piTyCodeCell` classifier the rule consumes) -/

/-- The dependent cons-branch classifier `(head : A) → (tail : List A) → (rec : motive tail) → motive (cons head
tail)` — the three nested `piTyCodeCell`s over the element type `A`, the list type `List A` (weakened past the
`head` binder), the recursive-result binder type `motive tail`, and the cons-branch codomain
`motive (cons head tail)`.  The classifier the dependent `listElimRule` assigns to its cons-branch obligation.
A CONSTANT motive (`weaken resultType`) recovers the old non-dependent `listStepFunctionType A C`.  The
substitution / renaming naturality of this WRAPPED type ships downstream with the union cascade (it needs
`subst_listTypeCell` / `rename_listTypeCell`). -/
def listElimDependentConsBranchType {scope : Nat} (motive : RawTerm (scope + 1))
    (elementType : RawTerm scope) : RawTerm scope :=
  piTyCodeCell elementType
    (piTyCodeCell (listTypeCell (RawTerm.weaken elementType))
      (piTyCodeCell (listElimDependentRecBinderType motive)
        (listElimDependentConsBranchCodomain motive)))

end FX1Poly.Typed
