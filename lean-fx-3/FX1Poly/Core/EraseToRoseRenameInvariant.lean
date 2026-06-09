import FX1Poly.Core.RawIotaRpoBridge
import FX1Poly.Core.SubstPreservationProbes
import FX1Poly.Core.RawTermFoldNonVarCommute
import FX1Poly.Core.RawTermRenamePointwise

/-!
# `eraseToRose` is rename-invariant — the eta-embedding substrate

`eraseToRose : RawTerm scope → RoseTerm Generator` (RawIotaRpoBridge)
forgets the payload and every binder shift, keeping only the generator
head + child structure.  Renaming touches only the payload (the var
index) and recurses structurally into children, so the rose image is
unchanged.

This is the load-bearing fact for embedding eta-reduction into the
iota recursive-path order (`Rpo` over `eraseToRose`).  Each
eta-contraction leaves a SUBTERM of the source MODULO a weakening
rename (the `etaLam` / `etaPathLam` arms put the inner function under
one extra binder, reached by `RawTerm.weaken`).  Because `eraseToRose`
is rename-invariant, that weakened subterm has the SAME rose image as
the bare subterm, so eta RPO-decreases the exact order the iota
fragment already uses — which is what lets the combined iota+eta
reduction inherit strong normalization without a fresh measure.

## Contents

* `eraseToRose_rename` / `eraseChildren_rename` — the mutual
  rename-invariance pair (term + children spine).
* `eraseToRose_weaken` — the `RawTerm.weaken` corollary the binder
  eta arms consume directly.

The proof mirrors `RawTerm.rename_pointwise`: a single-constructor
`match` on the term, `by_cases` on `gen = .gen_var`, the var arm
closing definitionally (rename's var-arm discards children and the
rose map drops the payload), the non-var arm dispatching through
`RawTerm.rename_mkGen_of_ne_var` + the children IH.  The children
cons case forces the `RawTermChildren.rename` reduction by `show`
(it is definitional, exactly as in `rename_pointwise`).
-/

open FX1Poly.Foundation
open FX1Poly.Core.RawIotaRpo
open FX1Poly.Core.RpoInductive

namespace FX1Poly.Core

mutual

/-- Renaming leaves the rose image of a term unchanged: `eraseToRose`
forgets the payload (the only thing the var-arm rename rewrites) and
recurses structurally into children, which renaming preserves shape of. -/
theorem eraseToRose_rename {sourceScope targetScope : Nat}
    (someRenaming : RawRenaming sourceScope targetScope)
    (sourceTerm : RawTerm sourceScope) :
    eraseToRose (RawTerm.rename someRenaming sourceTerm) =
      eraseToRose sourceTerm := by
  match sourceTerm with
  | .mkGen someGenerator somePayload someChildren =>
    by_cases hVar : someGenerator = .gen_var
    case pos =>
      -- Variable arm: `gen_var`'s child list is empty (`binderShifts
      -- gen_var = []`), so `cases` forces `.childNil`, and the whole
      -- goal closes definitionally — rename's var-arm reduces (it IS
      -- `rfl`, see `RawTerm.rename_var_reduces`) and `eraseToRose`
      -- drops the renamed payload.
      subst hVar
      cases someChildren
      rfl
    case neg =>
      -- Non-variable arm: rename preserves the generator + transports
      -- the (scope-invariant) payload + renames the children.
      -- `eraseToRose` drops the transported payload, so only the
      -- children differ; the children IH closes the goal.
      rw [RawTerm.rename_mkGen_of_ne_var someRenaming hVar]
      show RoseTerm.node someGenerator
              (eraseChildren (RawTermChildren.rename someRenaming someChildren)) =
            RoseTerm.node someGenerator (eraseChildren someChildren)
      rw [eraseChildren_rename someRenaming someChildren]

/-- Renaming leaves the rose images of a children spine unchanged.
In the cons case the head sits under `headShift`-many binders, so its
recursive call uses the lifted renaming `iterateLiftRaw someRenaming
headShift`; the `eraseToRose_rename` sibling is general over every
renaming, so the lift is no obstruction. -/
theorem eraseChildren_rename {binderShifts : List Nat}
    {sourceScope targetScope : Nat}
    (someRenaming : RawRenaming sourceScope targetScope)
    (someChildren : RawTermChildren binderShifts sourceScope) :
    eraseChildren (RawTermChildren.rename someRenaming someChildren) =
      eraseChildren someChildren := by
  match binderShifts, someChildren with
  | [], .childNil =>
      rfl
  | headShift :: _, .childCons childHead childTail =>
      -- `RawTermChildren.rename` on a cons reduces definitionally to
      -- `childCons (rename (iterateLiftRaw r headShift) head)
      --            (rename r tail)`, and `eraseChildren` on a cons to
      -- `eraseToRose head :: eraseChildren tail`; the `show` forces
      -- both reductions, then the two IHs close the goal.
      show eraseToRose
              (RawTerm.rename (iterateLiftRaw someRenaming headShift) childHead)
            :: eraseChildren (RawTermChildren.rename someRenaming childTail) =
            eraseToRose childHead :: eraseChildren childTail
      rw [eraseToRose_rename (iterateLiftRaw someRenaming headShift) childHead,
          eraseChildren_rename someRenaming childTail]

end

/-- The weakening corollary: weakening (a rename by `RawRenaming.weaken`)
leaves the rose image unchanged.  This is the exact shape the binder
eta arms (`etaLam`, `etaPathLam`) need — their target sits under one
extra binder, reached by `RawTerm.weaken`. -/
theorem eraseToRose_weaken {scope : Nat} (sourceTerm : RawTerm scope) :
    eraseToRose (RawTerm.weaken sourceTerm) = eraseToRose sourceTerm := by
  rw [RawTerm.weaken, eraseToRose_rename]

end FX1Poly.Core
