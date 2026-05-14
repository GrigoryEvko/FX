import LeanFX2.Foundation.RawPartialRename.Helpers

/-! # LeanFX2.Foundation.RawPartialRename.Inversion.OptionPatterns

Generic `Option`-shaped inversion lemmas powering the per-ctor-family
arm helpers used by `RawTerm.partialRename?_imp_rename`.

The headline induction's per-ctor arms collapse into five mechanical
patterns based on how each ctor's `partialRename?` clause aggregates
sub-result options:

* **Nullary** — the ctor has no sub-`partialRename?` calls; the result
  is unconditionally `some thisCtor`.  `injection success` then `rfl`
  closes the arm.
* **One-child match-form** — the ctor's clause is a literal
  `match RawTerm.partialRename? child pr with | some r => some (wrap r)
   | none => none`.  Definitionally equal to
   `Option.map wrap (RawTerm.partialRename? child pr)`; inverted by
   `Option.map_eq_some_inversion`.
* **Two-child `Option.mapTwo`** — inverted by
  `Option.mapTwo_eq_some` (lives in `Inversion.lean`).
* **Three-child `Option.mapThree`** — inverted by
  `Option.mapThree_eq_some` (lives in `Inversion.lean`).
* **Binder** — same shape as one-child / mapTwo, but the inner IH is
  fed `partialRenaming.lift` and the lifted "injects back" witness.

The match-form vs `Option.map` definitional equality is `rfl` modulo
iota-reduction (Lean's `Option.map` IS a `match`), so every per-ctor
arm helper can recast its source via a `rfl`-typed reshape and invoke
the generic `Option.map_eq_some_inversion` lemma.

Zero axioms: all proofs go through `cases` + `injection` (no-confusion
based) rather than `Option.some.injEq` (a `propext`-using iff).
`Option.map`'s reduction is `rfl`, so no `simp` / no `propext` leak. -/

namespace LeanFX2

/-! ### Inversion: `Option.map_eq_some` decomposes a successful
`Option.map` into the per-input `some` witness.

Driver for all one-child match-form ctor arms.  Each one-child arm's
`partialRename?` clause is definitionally `Option.map wrapCtor (...)`
because Lean's `Option.map` reduces by literal `match`, so the
arm's `partialRename? (wrap child) pr = some extracted` hypothesis
unfolds to `Option.map wrap (partialRename? child pr) = some
extracted` via `rfl`, which this lemma inverts.

Proof: forward case-split on the inner `Option`.  Each branch's
`Option.map _ _` reduces definitionally and we either `cases success`
(`none`) or `injection success` (`some`).  No `Option.some.injEq`. -/
theorem Option.map_eq_some_inversion
    {sourceType resultType : Type _}
    {forwardMap : sourceType → resultType}
    {sourceOption : Option sourceType}
    {result : resultType}
    (success : Option.map forwardMap sourceOption = some result) :
    ∃ sourceValue,
      sourceOption = some sourceValue ∧
      result = forwardMap sourceValue := by
  cases sourceOption with
  | none => cases success
  | some sourceValue =>
      injection success with eqResult
      exact ⟨sourceValue, rfl, eqResult.symm⟩

end LeanFX2
