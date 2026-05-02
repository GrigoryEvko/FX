import LeanFX2.Term.Rename
import LeanFX2.Term.Subst
import LeanFX2.Term.HEqCongr
import LeanFX2.Term.Pointwise

/-! # Term/ProofIrrel — TermRenaming / TermSubst proof irrelevance

`TermRenaming` and `TermSubst` are both `Prop`-shaped consistency
predicates over the underlying raw `RawRenaming` / `Subst`.  Two
proofs of the same predicate are propositionally equal (Lean 4
proof irrelevance), so the renaming/substitution operations don't
depend on the specific proof — only on the underlying raw data.

These lemmas make this **explicit** so that downstream code can
simplify renaming/subst over different proof shapes (e.g., `lift` of
two different proofs of the same TermRenaming) to a single canonical
form.

## Why useful

* `Compat.lean` β-arms construct `TermRenaming.lift` of
  `(termRenaming.lift _)` — a doubly-lifted proof.  Without proof
  irrelevance, comparing this against the directly-applied lift
  would require unfolding both sides of the lift defs.  With proof
  irrelevance, they're literally equal.
* `Algo/Eval` substitution uses different TermSubst proofs at
  different unfolding depths; proof-irrelevance lets us treat them
  uniformly.
-/

namespace LeanFX2

/-- Term.rename only depends on the underlying RawRenaming, not on
the consistency proof.  Two TermRenaming proofs over the same `rho`
produce literally equal Terms. -/
theorem Term.rename_proof_irrel
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming1 termRenaming2 : TermRenaming sourceCtx targetCtx rho)
    {someType : Ty level sourceScope} {raw : RawTerm sourceScope}
    (someTerm : Term sourceCtx someType raw) :
    Term.rename termRenaming1 someTerm = Term.rename termRenaming2 someTerm := by
  rfl

/-- Term.subst only depends on the underlying TermSubst function
(positions ↦ Term values), not on its packaging.  Two structurally
identical TermSubst values produce literally equal Terms. -/
theorem Term.subst_proof_irrel
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst1 termSubst2 : TermSubst sourceCtx targetCtx sigma)
    (positionsAgree : ∀ position, termSubst1 position = termSubst2 position)
    {someType : Ty level sourceScope} {raw : RawTerm sourceScope}
    (someTerm : Term sourceCtx someType raw) :
    Term.subst termSubst1 someTerm = Term.subst termSubst2 someTerm :=
  Term.subst_pointwise positionsAgree someTerm

end LeanFX2
