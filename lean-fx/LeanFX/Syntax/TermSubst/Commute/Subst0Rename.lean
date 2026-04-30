import LeanFX.Syntax.TermSubst.Commute.RenameSubst
import LeanFX.Syntax.TermSubst.Commute.SingletonRename

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ## `subst0` and term renaming.

The β-preservation proof for `Step.rename_compatible` needs the
term-level fact that renaming commutes with one-hole substitution.
The proof factors through the already-established substitution/rename
commutation theorems plus the singleton pointwise bridge. -/

/-- Renaming commutes with one-hole substitution, up to HEq. -/
theorem Term.rename_subst0_HEq
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rawRenaming : Renaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rawRenaming)
    {argumentType : Ty level sourceScope}
    {bodyType : Ty level (sourceScope + 1)}
    (bodyTerm : Term (sourceCtx.cons argumentType) bodyType)
    (argumentTerm : Term sourceCtx argumentType) :
    HEq
      (Term.rename termRenaming (Term.subst0 bodyTerm argumentTerm))
      (Term.subst0
        (Term.rename (TermRenaming.lift termRenaming argumentType) bodyTerm)
        (Term.rename termRenaming argumentTerm)) := by
  show HEq
      (Term.rename termRenaming (Term.subst (TermSubst.singleton argumentTerm) bodyTerm))
      (Term.subst (TermSubst.singleton (Term.rename termRenaming argumentTerm))
        (Term.rename (TermRenaming.lift termRenaming argumentType) bodyTerm))
  apply HEq.trans
    (Term.subst_rename_commute_HEq (TermSubst.singleton argumentTerm) termRenaming bodyTerm)
  apply HEq.trans
    (Term.subst_HEq_pointwise rfl
      (TermSubst.renameAfter (TermSubst.singleton argumentTerm) termRenaming)
      (TermSubst.precompose (TermRenaming.lift termRenaming argumentType)
        (TermSubst.singleton (Term.rename termRenaming argumentTerm)))
      (Subst.singleton_renameAfter_equiv_precompose argumentType rawRenaming)
      (TermSubst.singleton_renameAfter_pointwise termRenaming argumentTerm)
      bodyTerm)
  exact HEq.symm
    (Term.rename_subst_commute_HEq
      (TermRenaming.lift termRenaming argumentType)
      (TermSubst.singleton (Term.rename termRenaming argumentTerm))
      bodyTerm)

/-- Renaming commutes with the term-bearing one-hole substitution,
up to HEq.  Same proof template as `rename_subst0_HEq`, threading
through the `termSingleton` flavors of the bridge lemmas.  Uses
`Term.toRaw_rename` to align the raw projection of the renamed
argument with the renamed raw projection. -/
theorem Term.rename_subst0_term_HEq
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rawRenaming : Renaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rawRenaming)
    {argumentType : Ty level sourceScope}
    {bodyType : Ty level (sourceScope + 1)}
    (bodyTerm : Term (sourceCtx.cons argumentType) bodyType)
    (argumentTerm : Term sourceCtx argumentType) :
    HEq
      (Term.rename termRenaming (Term.subst0_term bodyTerm argumentTerm))
      (Term.subst0_term
        (Term.rename (TermRenaming.lift termRenaming argumentType) bodyTerm)
        (Term.rename termRenaming argumentTerm)) := by
  -- Rewrite the renamed argument's raw projection back to the unrenamed
  -- raw projection, then use the termSingleton-flavored equivalence.
  have toRawRenameEq :
      Term.toRaw (Term.rename termRenaming argumentTerm) =
        (Term.toRaw argumentTerm).rename rawRenaming :=
    Term.toRaw_rename termRenaming argumentTerm
  show HEq
      (Term.rename termRenaming
        (Term.subst (TermSubst.termSingleton argumentTerm) bodyTerm))
      (Term.subst (TermSubst.termSingleton (Term.rename termRenaming argumentTerm))
        (Term.rename (TermRenaming.lift termRenaming argumentType) bodyTerm))
  apply HEq.trans
    (Term.subst_rename_commute_HEq
      (TermSubst.termSingleton argumentTerm) termRenaming bodyTerm)
  -- Bridge: renameAfter (termSingleton) ρ
  --        = precompose ρ.lift (termSingleton (rename arg))
  -- The equiv goes through termSingleton_renameAfter_equiv_precompose
  -- composed with the rewrite (toRaw arg).rename ρ = toRaw (rename arg).
  have sigmaEquiv :
      Subst.equiv
        (Subst.renameAfter (Subst.termSingleton argumentType
          (Term.toRaw argumentTerm)) rawRenaming)
        (Subst.precompose rawRenaming.lift
          (Subst.termSingleton (argumentType.rename rawRenaming)
            (Term.toRaw (Term.rename termRenaming argumentTerm)))) := by
    rw [toRawRenameEq]
    exact Subst.termSingleton_renameAfter_equiv_precompose argumentType
      (Term.toRaw argumentTerm) rawRenaming
  apply HEq.trans
    (Term.subst_HEq_pointwise rfl
      (TermSubst.renameAfter (TermSubst.termSingleton argumentTerm) termRenaming)
      (TermSubst.precompose (TermRenaming.lift termRenaming argumentType)
        (TermSubst.termSingleton (Term.rename termRenaming argumentTerm)))
      sigmaEquiv
      (TermSubst.termSingleton_renameAfter_pointwise termRenaming argumentTerm)
      bodyTerm)
  exact HEq.symm
    (Term.rename_subst_commute_HEq
      (TermRenaming.lift termRenaming argumentType)
      (TermSubst.termSingleton (Term.rename termRenaming argumentTerm))
      bodyTerm)

end LeanFX.Syntax
