import LeanFX.Syntax.TermSubst.Rename.Weaken

/-! # Term renaming algebra umbrella.

Re-exports the rename-side counterparts of `TermSubst/Core.lean`
and friends.  Renaming is structurally simpler than full
substitution (no Term inputs, just index reindexing) so these
files are typically pure structural induction.

Layout (linear chain):

  * `Pointwise` — `Renaming.pointwiseEq` lifted to terms.
  * `Identity` — `Term.rename Renaming.id t = t`.
  * `Compose` — `Term.rename ρ₁ (Term.rename ρ₂ t) =
    Term.rename (Renaming.compose ρ₁ ρ₂) t`.
  * `Weaken` — `Term.weaken` algebra (the file this umbrella
    imports), built on top of the compose / identity laws.

These laws underpin the typed reduction layer: `Step` and
`Step.par` rename compat (`Reduction/Rename.lean`,
`Reduction/ParCompatible.lean`) reduces to applying the right
rename-algebra lemma in each constructor arm. -/
