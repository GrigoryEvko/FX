import FX1Poly.Core.RawTermSubst
import FX1Poly.Core.RawTermRename

/-! # FX1Poly/Core/RawTermFoldNonVarCommute — generic NON-VARIABLE cell commutation for fold traversals
    (the cascade-death substrate for substitution/renaming through an ABSTRACT formation cell)

Every shape-preserving traversal — `RawTerm.subst`, `RawTerm.rename`, `RawTerm.weaken` — is `fold`
with the canonical "rebuild `.mkGen`" algebra and its own `Container`.  The fold dispatches on whether
the head generator is `.gen_var`:

  * VARIABLE case — consult the `Container` (substitute / renumber the de Bruijn index).
  * NON-VARIABLE case — recurse into the children spine and rebuild the cell, casting the payload
    across scopes via `Generator.payload_scope_invariant_of_not_var` (the 203-generator enumeration
    in ONE place — every non-`gen_var` payload type is scope-invariant).

For a CONCRETE non-var generator (`.gen_pair`, `.gen_lam`, …) the dispatch reduces by `rfl`, which is
why `CompoundSubstPreservation` ships a per-generator `rfl` probe for each.  But for an ABSTRACT
non-var generator the `if hVar : generator = .gen_var` is STUCK — so traversal-through-a-cell cannot
be stated generically over the generator without this file.

## Why this is the cascade-death brick

The formation-family metatheory consumers (`HasTypeDescSubstitution` / `…Weakening` / the grown twins)
RECONSTRUCT a formation cell `.mkGen generator payload children` after substituting/renaming its
children.  They currently `by_cases generator = gen_piTyCode / gen_sigmaTyCode` PRECISELY to make the
generator concrete so the fold reduces — an enumeration that breaks the moment a third formation row
(a data type code) lands.  These lemmas state the commutation ONCE for ANY non-var generator, so the
consumers migrate to a generator-agnostic reconstruction and a new formation row touches none of them.

`generator ≠ .gen_var` is free for every formation generator: `typingRuleDescOf .gen_var = none`, so a
generator carrying a formation rule is automatically non-`gen_var`.

## Zero-axiom verification

Each closes via the established propext-safe unfold idiom `dsimp only [traversal, fold]` (NOT `unfold`,
which pulls `Quot.sound` through the mutual `fold`/`foldChildren` block) + the decidable-branch selector
`dif_neg hNotVar` + the canonical-algebra rebuild equation + the children-spine `def` unfolding.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Audit-gated.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation

/-- **Generic non-variable `fold` commutation.**  For any non-`gen_var` generator, folding a cell
equals applying the algebra to the (scope-cast) payload and the folded children spine — the
NON-VARIABLE branch of `fold`, exposed for an ABSTRACT generator.  The payload cast is
`Generator.payload_scope_invariant_of_not_var` (the one-site 203-generator enumeration).

`dsimp only [fold]` reduces the match on the explicit `.mkGen` constructor to the `if hVar : … then …
else …`; `dif_neg hNotVar` selects the non-variable branch verbatim. -/
theorem fold_mkGen_of_ne_var
    {Container : Nat → Nat → Type} [LiftsRaw Container] [ActsOnRawTermVar Container]
    (algebra : GenAlgebra)
    {sourceScope targetScope : Nat}
    (someAction : Container sourceScope targetScope)
    {generator : Generator} (hNotVar : generator ≠ .gen_var)
    (payload : generator.payload sourceScope)
    (children : RawTermChildren generator.binderShifts sourceScope) :
    fold algebra someAction (.mkGen generator payload children) =
      algebra.algebra generator
        (Generator.payload_scope_invariant_of_not_var hNotVar sourceScope targetScope ▸ payload)
        (foldChildren algebra someAction children) := by
  dsimp only [fold]
  rw [dif_neg hNotVar]

/-- **Generic non-variable SUBSTITUTION commutation.**  Substituting into a non-`gen_var` cell
distributes: substitute the children spine, rebuild the SAME generator with the scope-cast payload.
The traversal-agnostic statement the formation-family consumers reconstruct through. -/
theorem RawTerm.subst_mkGen_of_ne_var
    {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    {generator : Generator} (hNotVar : generator ≠ .gen_var)
    (payload : generator.payload sourceScope)
    (children : RawTermChildren generator.binderShifts sourceScope) :
    RawTerm.subst substitution (.mkGen generator payload children) =
      .mkGen generator
        (Generator.payload_scope_invariant_of_not_var hNotVar sourceScope targetScope ▸ payload)
        (RawTermChildren.subst substitution children) := by
  rw [RawTerm.subst_eq_fold, fold_mkGen_of_ne_var GenAlgebra.canonical substitution hNotVar,
    GenAlgebra.canonical_algebra_eq_mkGen, RawTermChildren.subst_eq_foldChildren]

/-- **Generic non-variable RENAMING commutation.**  The rename twin of `subst_mkGen_of_ne_var` — same
fold engine, different `Container`. -/
theorem RawTerm.rename_mkGen_of_ne_var
    {sourceScope targetScope : Nat}
    (someRenaming : RawRenaming sourceScope targetScope)
    {generator : Generator} (hNotVar : generator ≠ .gen_var)
    (payload : generator.payload sourceScope)
    (children : RawTermChildren generator.binderShifts sourceScope) :
    RawTerm.rename someRenaming (.mkGen generator payload children) =
      .mkGen generator
        (Generator.payload_scope_invariant_of_not_var hNotVar sourceScope targetScope ▸ payload)
        (RawTermChildren.rename someRenaming children) := by
  rw [RawTerm.rename_eq_fold, fold_mkGen_of_ne_var GenAlgebra.canonical someRenaming hNotVar,
    GenAlgebra.canonical_algebra_eq_mkGen, RawTermChildren.rename_eq_foldChildren]

end FX1Poly.Core
