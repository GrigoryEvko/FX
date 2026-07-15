import FX1Poly.Typed.Cell.CellConstructors
import FX1Poly.Axis.Term.Subst.RawTermSubstCompose
import FX1Poly.Axis.Term.Subst.RawTermSubstPointwise
import FX1Poly.Axis.Term.Subst.RawTermSubst0
import FX1Poly.Axis.Term.Subst.RawTermSubstConsCommute
import FX1Poly.Axis.Term.Rename.RawTermRenameAsSubst
import FX1Poly.Axis.Term.Rename.RawTermRenameComposeFusion

/-! # FX1Poly/Typed/Cell/NatElimDependentSuccType
    — the dependent `natElim` / `natRec` SUCC-branch type (DEP-NAT-WIRE, the two-binder recursor crux)

The recursor's succ branch binds TWO variables — `var 1` the predecessor `n : Nat`, `var 0` the recursive
result of type `motive n` — and its body inhabits `motive (Nat.succ n)`.  Unlike `boolElim`'s NULLARY
constructors (whose dependent branch types are the binder-free `subst0 motive boolTrue/False`), the recursive
succ branch is the FIRST genuinely two-binder dependent eliminator branch in the kernel.  Its classifier is the
motive re-based at `natSucc (var 1)` with the motive's own context shifted past the two fresh binders:

  `natElimDependentSuccBranchType motive := subst (cons (natSucc (var 1)) (weaken-by-2)) motive`.

## The substitution-correctness pin (the design's whole point)

The succ-ι reduct substitutes the recursive call for `var 0` and the predecessor for `var 1`
(`Step.iotaNatElimSucc` uses `cons recursiveResult (singleton predecessor)`).  Subject reduction needs that
substitution to carry the branch's classifier to the output type `subst0 motive (natSucc predecessor)`.
`subst_natElimDependentSuccBranchType_succIota` proves exactly this, GENERICALLY over the recursive-call head
(the branch type never mentions `var 0`, so the recursive call is irrelevant to the *type*): the composite
substitution collapses — `(cons head (singleton pred)) ∘ (cons (natSucc (var 1)) (weaken-by-2))
= singleton (natSucc pred)` pointwise (position 0 ↦ `natSucc pred`, position k+1 ↦ `var k`) — so by
`subst_compose` + `subst_pointwise` the result is `subst0 motive (natSucc pred)`.

## Zero-axiom verification

`RawTerm.subst_compose` + `RawTerm.subst_pointwise` (both axiom-free, the term-axis polynomial-monad laws) over a
two-arm `Fin` match; the per-position arms compute by `rfl` (Lean's definitional `Prop`-irrelevance collapses the
`Fin` bound proofs, `subst_natSuccCell` is `rfl`, `cons`/`singleton` reduce on concrete positions).  The `+2`
weakening's bound is `Nat.add_lt_add_right` (NO `omega`).  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Axis.Syntax

/-- The dependent recursor succ-branch type: `motive` re-based at `natSucc (var 1)` (the predecessor binder),
the motive's context shifted past the two succ-branch binders (`var 0` = recursive result, `var 1` =
predecessor).  Shared by `natElim` and `natRec` (the branch TYPE is the same; only the cell former differs). -/
def natElimDependentSuccBranchType {scope : Nat} (motive : RawTerm (scope + 1)) : RawTerm (scope + 2) :=
  RawTerm.subst
    (RawTermSubst.cons
      (natSuccCell (.mkGen .gen_var ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ scope)⟩ .childNil))
      (fun position => .mkGen .gen_var ⟨position.val + 2, Nat.add_lt_add_right position.isLt 2⟩ .childNil))
    motive

/-- **The succ-ι type-preservation pin.**  Substituting the recursive call (`recursiveResult`, irrelevant to the
type) for `var 0` and the predecessor for `var 1` carries the dependent succ-branch type to the output type at
`natSucc predecessor`.  This is the subject-reduction obligation for the `natElim` / `natRec` succ-iota; the
composite substitution collapses to `singleton (natSucc predecessor)`. -/
theorem subst_natElimDependentSuccBranchType_succIota {scope : Nat}
    (motive : RawTerm (scope + 1)) (recursiveResult predecessor : RawTerm scope) :
    RawTerm.subst (RawTermSubst.cons recursiveResult (RawTermSubst.singleton predecessor))
        (natElimDependentSuccBranchType motive)
      = RawTerm.subst0 motive (natSuccCell predecessor) := by
  unfold natElimDependentSuccBranchType
  rw [RawTerm.subst_compose]
  show RawTerm.subst _ motive
    = RawTerm.subst (RawTermSubst.singleton (natSuccCell predecessor)) motive
  apply RawTerm.subst_pointwise
  intro position
  match position with
  | ⟨0, _⟩ => rfl
  | ⟨_k + 1, _⟩ => rfl

/-- **The succ-branch type identity UNDER AN OUTER SUBSTITUTION** (the FT-bridge generalization of
`subst_natElimDependentSuccBranchType_succIota`).  In the bounded fundamental theorem the succ obligation is
discharged under a closing substitution `tailSubst`, and the two succ binders are filled with the recursive
call (irrelevant to the type) and the predecessor.  The resulting type-side substitution
`cons recursiveResult (cons predecessor tailSubst)` composes with the succ-branch type's defining
re-basing to `cons (natSucc predecessor) tailSubst`, which `subst_cons_eq_subst0_lift` presents as
`subst0 (subst (lift tailSubst) motive) (natSucc predecessor)` — exactly the dependent recursor's output type
at `natSucc predecessor` under `tailSubst`.  The succ-ι pin is the `tailSubst = singleton`-tail special case;
this is the form the FT row consumes. -/
theorem subst_natElimDependentSuccBranchType_general {scope targetScope : Nat}
    (motive : RawTerm (scope + 1)) (recursiveResult predecessor : RawTerm targetScope)
    (tailSubst : RawTermSubst scope targetScope) :
    RawTerm.subst (RawTermSubst.cons recursiveResult (RawTermSubst.cons predecessor tailSubst))
        (natElimDependentSuccBranchType motive)
      = RawTerm.subst0 (RawTerm.subst (RawTermSubst.lift tailSubst) motive) (natSuccCell predecessor) := by
  rw [← RawTerm.subst_cons_eq_subst0_lift motive (natSuccCell predecessor) tailSubst]
  unfold natElimDependentSuccBranchType
  rw [RawTerm.subst_compose]
  apply RawTerm.subst_pointwise
  intro position
  match position with
  | ⟨0, _⟩ => rfl
  | ⟨_k + 1, _⟩ => rfl

/-- **The succ-branch SUBJECT identity** (the FT-bridge subject-side twin).  The recursor's succ-ι reduct
substitutes the recursive call for `var 0` and the predecessor for `var 1` into the succ branch already
closed by the doubly-lifted outer substitution.  By substitution composition that two-stage substitution
collapses to the single `cons recursiveResult (cons predecessor tailSubst)` — the same filling the succ
obligation's fundamental conclusion produces.  General over the branch body (no `natElim`-specific content):
the two outer binders introduced by `lift (lift tailSubst)` are exactly the slots
`cons recursiveResult (singleton predecessor)` fills, so they annihilate (`weaken_subst_cons` +
`weaken_subst_singleton`). -/
theorem subst_consSingleton_substLiftLift {scope targetScope : Nat}
    (body : RawTerm (scope + 2)) (recursiveResult predecessor : RawTerm targetScope)
    (tailSubst : RawTermSubst scope targetScope) :
    RawTerm.subst (RawTermSubst.cons recursiveResult (RawTermSubst.singleton predecessor))
        (RawTerm.subst (RawTermSubst.lift (RawTermSubst.lift tailSubst)) body)
      = RawTerm.subst (RawTermSubst.cons recursiveResult (RawTermSubst.cons predecessor tailSubst)) body := by
  rw [RawTerm.subst_compose]
  apply RawTerm.subst_pointwise
  intro position
  cases position with
  | mk positionValue positionBound =>
    cases positionValue with
    | zero => rfl
    | succ priorValue =>
      cases priorValue with
      | zero => rfl
      | succ deepValue =>
          dsimp only [RawTermSubst.compose, RawTermSubst.lift, RawTermSubst.cons]
          rw [RawTerm.weaken_eq_rename, RawTerm.weaken_subst_cons, RawTerm.weaken_subst_singleton]

/-- **Double weakening as a double-shift substitution.**  `weaken ∘ weaken` (raise scope by two via two
`Fin.succ` shifts) equals substituting every variable by the variable shifted up by two — the substitution
`fun position => var (position + 2)`.  Proof: the renaming-as-substitution bridge
(`rename_eq_subst_ofRenaming`) at the composed weakening renaming `compose weaken weaken`, whose injected
image is exactly `var (position + 2)` (`compose weaken weaken position = Fin.succ (Fin.succ position)`,
definitionally `⟨position.val + 2, _⟩`).  Consumed by the dependent succ-branch naturality below to
reconcile the doubly-lifted substitution's variable image at `k + 2` (`lift² s` reads
`weaken (weaken (s k))`) with the cons-tail double-shift the branch re-basing carries
(`weaken_subst_cons` strips the succ-binder slot, leaving exactly this `shiftBy2` substitution). -/
theorem doubleWeaken_eq_substShiftBy2 {scope : Nat} (sourceTerm : RawTerm scope) :
    RawTerm.weaken (RawTerm.weaken sourceTerm)
      = RawTerm.subst
          (fun position => .mkGen .gen_var ⟨position.val + 2, Nat.add_lt_add_right position.isLt 2⟩ .childNil)
          sourceTerm := by
  rw [RawTerm.weaken_eq_rename (RawTerm.weaken sourceTerm),
    RawTerm.weaken_eq_rename sourceTerm, RawTerm.rename_compose]
  exact RawTerm.rename_eq_subst_ofRenaming
    (RawRenaming.compose RawRenaming.weaken RawRenaming.weaken) sourceTerm

/-- **Substitution naturality of the dependent succ-branch type** (the substitution-stability obligation for
the dependent `natElim` / `natRec` rule's succ premise, consumed by `HasTypeUnion.substRespectingContext`).
Substituting under the two succ binders (`lift (lift substitution)`) commutes with the motive re-basing: the
branch type of the substituted motive equals the substituted branch type.  Proof by the polynomial-monad
substitution law (`subst_compose` twice) over a two-arm `Fin` match: position 0 ↦ `natSucc (var 1)` on both
sides (`rfl`); position k+1 ↦ the ambient context var shifted up by two — the LHS reads `lift²` at `k+2`
(`weaken∘weaken`), the RHS strips the succ-binder substituent via `weaken_subst_cons`, and both land on
`rename (weaken∘weaken)` (the renaming-as-substitution bridge `rename_eq_subst_ofRenaming`). -/
theorem subst_natElimDependentSuccBranchType_substLiftLift {scope targetScope : Nat}
    (motive : RawTerm (scope + 1)) (substitution : RawTermSubst scope targetScope) :
    RawTerm.subst (RawTermSubst.lift (RawTermSubst.lift substitution))
        (natElimDependentSuccBranchType motive)
      = natElimDependentSuccBranchType (RawTerm.subst (RawTermSubst.lift substitution) motive) := by
  unfold natElimDependentSuccBranchType
  rw [RawTerm.subst_compose, RawTerm.subst_compose]
  apply RawTerm.subst_pointwise
  intro position
  cases position with
  | mk positionValue positionBound =>
    cases positionValue with
    | zero => rfl
    | succ priorValue =>
        -- `dsimp` reduces the inner applications: `σ₀ (priorValue+1)` ↦ `var (priorValue+2)` (the
        -- re-basing's double-shift tail) on the LHS, `(lift s) (priorValue+1)` ↦ `weaken (s priorValue)`
        -- on the RHS, leaving the OUTER `lift² s` (LHS) and `cons … shiftBy2` (RHS) standalone.
        dsimp only [RawTermSubst.compose, RawTermSubst.lift, RawTermSubst.cons]
        -- Normalize `RawTerm.weaken` ↦ `rename weaken` (no-op if `dsimp` already did) so
        -- `weaken_subst_cons` matches; it strips the succ-binder slot, leaving the `shiftBy2` tail.
        simp only [RawTerm.weaken_eq_rename]
        rw [RawTerm.weaken_subst_cons, ← doubleWeaken_eq_substShiftBy2]
        -- Goal: `subst (lift² s) (var (priorValue+2)) = weaken (weaken (s priorValue))`; both sides
        -- reduce to `weaken (weaken (s priorValue))` (the LHS via the subst-on-var + double-lift
        -- definitional dispatch), so `rfl` closes.
        rfl

/-- **`iterateLiftRaw` form** of `subst_natElimDependentSuccBranchType_substLiftLift` — the shape the union
substitution-stability arm (`HasTypeUnion.substRespectingContext`, the `natElim` / `natRec` rows) consumes,
where the two succ-branch binders are crossed via `iterateLiftRaw substitution 2`.  Definitionally identical
to the `lift (lift _)` form (`iterateLiftRaw σ 2 ≡ lift (lift σ)`, `iterateLiftRaw σ 1 ≡ lift σ`, by the
structural `Nat` recursion of `iterateLiftRaw` + the `liftForRaw := RawTermSubst.lift` instance), so it
closes by the underlying lemma directly. -/
theorem subst_natElimDependentSuccBranchType_iterateLift {scope targetScope : Nat}
    (motive : RawTerm (scope + 1)) (substitution : RawTermSubst scope targetScope) :
    RawTerm.subst (iterateLiftRaw substitution 2)
        (natElimDependentSuccBranchType motive)
      = natElimDependentSuccBranchType (RawTerm.subst (iterateLiftRaw substitution 1) motive) :=
  subst_natElimDependentSuccBranchType_substLiftLift motive substitution

/-- **Renaming naturality of the dependent succ-branch type** — the RENAME twin of
`subst_natElimDependentSuccBranchType_iterateLift`, the form the union renaming-stability arm
(`HasTypeUnion.renameRespectsContext`, the `natElim` / `natRec` rows in `HasTypeUnionWeakening`) consumes.
Proved by routing through the substitution version via the renaming-as-substitution bridge
(`rename_eq_subst_ofRenaming`) and the `ofRenaming`/`iterateLiftRaw` pointwise commutation
(`ofRenaming_iterateLift_pointwise`): a renaming acts as the substitution that injects each renamed
position, and that injection commutes with the binder lifts. -/
theorem rename_natElimDependentSuccBranchType_iterateLift {scope targetScope : Nat}
    (motive : RawTerm (scope + 1)) (someRenaming : RawRenaming scope targetScope) :
    RawTerm.rename (iterateLiftRaw someRenaming 2)
        (natElimDependentSuccBranchType motive)
      = natElimDependentSuccBranchType (RawTerm.rename (iterateLiftRaw someRenaming 1) motive) := by
  rw [RawTerm.rename_eq_subst_ofRenaming (iterateLiftRaw someRenaming 2),
    ← RawTerm.subst_pointwise (RawTermSubst.ofRenaming_iterateLift_pointwise someRenaming 2),
    subst_natElimDependentSuccBranchType_iterateLift,
    RawTerm.subst_pointwise (RawTermSubst.ofRenaming_iterateLift_pointwise someRenaming 1),
    ← RawTerm.rename_eq_subst_ofRenaming (iterateLiftRaw someRenaming 1)]

end FX1Poly.Typed
