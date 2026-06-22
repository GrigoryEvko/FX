import FX1Poly.Typed.Ledger.Cell.CellConstructors
import FX1Poly.Tier0.Term.Subst.RawTermSubstCompose
import FX1Poly.Tier0.Term.Subst.RawTermSubstPointwise
import FX1Poly.Tier0.Term.Subst.RawTermSubst0

/-! # FX1Poly/Typed/Ledger/Cell/NatElimDependentSuccType
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

open FX1Poly.Core FX1Poly.Tier0.Syntax

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

end FX1Poly.Typed
