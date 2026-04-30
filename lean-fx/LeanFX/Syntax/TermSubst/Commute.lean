import LeanFX.Syntax.TermSubst.Commute.SingletonRename
import LeanFX.Syntax.TermSubst.Commute.Subst0Rename
import LeanFX.Syntax.TermSubst.Commute.SubstWeaken

/-! # Term substitution / renaming commute umbrella.

Re-exports the cross-operation commutation laws that thread
substitution and renaming past each other.  These laws are the
heart of every β-arm in `Step.rename_compatible`,
`Step.subst_compatible`, and the `Step.par.*_compatible`
counterparts — they show that `subst (rename t) =
rename (subst t)` (with the appropriate Subst / Renaming
adjustments) so a β-redex's reduct can be re-derived after a
rename or a substitution.

Layout (linear chain — each file imports the previous):

  * `Subst0Subst` — `subst0` interaction with arbitrary `subst`
    (deepest leaf, transitively pulls everything below in this
    module's directory).
  * `Subst0Rename` — `subst0` past renamings.
  * `SubstWeaken` — substitution past `weaken`.
  * `SingletonRename` — singleton substitution
    (`Subst.singleton`, `Subst.termSingleton`) past renamings.
  * `RenameAfter` / `RenameSubst` / `Precompose` — composition
    laws between `Renaming` and `Subst`.

Convention: zero axioms; every theorem here is structural
induction on `Term`.  Most arms are one-liners after the
relevant `Term.subst` / `Term.rename` reduction (Wave 2 made
those `@[reducible]` so the unfolding fires). -/
