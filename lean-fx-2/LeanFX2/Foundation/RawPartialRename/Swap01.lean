import LeanFX2.Foundation.RawSubst.RenameDefs

/-! # LeanFX2.Foundation.RawPartialRename.Swap01

`RawRenaming.swap01` — swap de Bruijn indices 0 and 1 at scope `k + 2`.
Foundation primitive earmarked for the D2.5.5 `transpPi` β-rule
contractum, which must re-order the `pathLam`-binder (i) and the
outer `lam`-binder (x) in the codomain when synthesizing
`λ x ⇒ transp (pathLam B[x ↔ i]) (fn.weaken x)`.  Used nowhere yet at
the par layer — kept self-contained so the swap mechanics audit
clean before the cascade plugs in.

Per `feedback_d255_d256_blocker_2026_05_15.md`, the D2.5.5 cascade is
still pending Phases E-K (par ctor + compat + cd + cd_lemma + typed
mirror) after the Path A foundation shipped at commits 9015b54 +
ae244dd.  This file is one of the small prep primitives the par
ctor's contractum design will reference.

## Root status

Layer 0 raw-syntax extension.  Strict zero-axiom — proofs avoid
`omega` and `simp` to dodge propext leaks from the indexed-inductive
partial-match trap (`feedback_lean_indexed_partial_match.md`). -/

namespace LeanFX2

/-- Swap renaming at indices 0 and 1.

Behavior on `Fin (scope + 2)`:
* `⟨0, _⟩ ↦ ⟨1, _⟩`
* `⟨1, _⟩ ↦ ⟨0, _⟩`
* `⟨k + 2, h⟩ ↦ ⟨k + 2, h⟩`

The transpPi β-rule's contractum at scope `N` produces
`λ x ⇒ transp (pathLam B') (app fn.weaken var0)` where `B'` is the
original Pi-codomain at scope `N + 2` with the `Pi`-binder (slot 0)
and `pathLam`-binder (slot 1) exchanged so the outer-`lam` variable
threads through the inner `pathLam`'s scope. -/
@[reducible]
def RawRenaming.swap01 {scope : Nat} : RawRenaming (scope + 2) (scope + 2)
  | ⟨0, _⟩      => ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩
  | ⟨1, _⟩      => ⟨0, Nat.zero_lt_succ _⟩
  | ⟨_ + 2, h⟩  => ⟨_ + 2, h⟩

/-- Swap-01 is its own inverse: applying twice is the identity at
every position.  Decided structurally by case analysis on the
`Fin (scope + 2)` position. -/
theorem RawRenaming.swap01_involution {scope : Nat}
    (position : Fin (scope + 2)) :
    (RawRenaming.swap01 (scope := scope))
      (RawRenaming.swap01 (scope := scope) position) = position := by
  match position with
  | ⟨0, _⟩      => rfl
  | ⟨1, _⟩      => rfl
  | ⟨_ + 2, _⟩  => rfl

/-- Swap-01 commutes with double-`lift` of any renaming.

The transpPi β-rule's contractum nests the codomain `B` of the path
under a `swap01` inside an outer `lam` and inner `pathLam`.  When the
whole construct is renamed by an outer `rho`, the renaming descends
through both binders as `rho.lift.lift`.  This lemma states that
applying `swap01` before or after `rho.lift.lift` produces the same
`Fin`, pointwise.

Geometry: `swap01` only acts on the bottom two slots and is the
identity above; `rho.lift.lift` keeps slots 0 and 1 fixed and maps
slot `k + 2` to `rho k + 2`.  The two operations are disjoint at the
slot level, so they commute pointwise.  Per-case `rfl` succeeds
because Lean 4 has definitional Prop-irrelevance on `Fin`'s upper-
bound proofs. -/
theorem RawRenaming.swap01_lift_lift_commute {source target : Nat}
    (rho : RawRenaming source target)
    (position : Fin (source + 2)) :
    RawRenaming.swap01 (rho.lift.lift position) =
    rho.lift.lift (RawRenaming.swap01 position) := by
  match position with
  | ⟨0, _⟩      => rfl
  | ⟨1, _⟩      => rfl
  | ⟨_ + 2, _⟩  => rfl

end LeanFX2
