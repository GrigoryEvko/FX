import FX1Poly.Tier0.Term.Subst.RawTermSubstCompose
import FX1Poly.Tier0.Term.Subst.RawTermSubstPointwise
import FX1Poly.Tier0.Term.Subst.RawTermSubst0Commute

/-! # Tier0/Term — the term-native β-substitution bridge (`term-beta` re-home)

`context-9` (`Tier0/Context/SubstitutionFree.lean`) surfaces a `×term` bridge corollary —
`RawTerm.subst (SubstVec.cons arg sigma).toRawTermSubst body
  = RawTerm.subst (SubstVec.singleton arg).toRawTermSubst (RawTerm.subst sigma.lift.toRawTermSubst body)`
— and its docstring states plainly: *"This is TERM-axis content … its home is term-2 / term-26 …
it is surfaced here only as the operational shadow of the context β-law and is excluded from the
`fxSubstitutionFree` bundle … When `term-26` lands it is re-derived there."*

This file is that re-derivation — the β-law stated and proved **entirely in the term axis's own
`RawTermSubst` vocabulary** (`cons` / `lift` / `singleton` / `compose`), with **zero lateral
`term → context` import** (no `SubstVec`).  It is the genuine "migrate to the term axis for purity"
move: the term axis now OWNS its β-substitution law rather than borrowing the context shadow.

## The law

Substituting the extended substitution `cons arg sigma` into `body` equals: lift `sigma`,
substitute, then single-substitute `arg` — `body[cons arg sigma] = body[sigma⁺][⟨arg⟩]`.  This is
exactly what the structural β-engine computes for `(λ body) arg` under a pending substitution
`sigma`: it never forms the composite `cons arg sigma`; it lifts `sigma`, applies it, and finally
single-substitutes `arg`.  (At `sigma = id`, `cons arg id` is ordinary β.)

## The proof

`RawTerm.subst_compose` folds the right-hand `subst (singleton arg) ∘ subst sigma.lift` into a single
`subst (compose sigma.lift (singleton arg))`; then the two parallel substitutions `cons arg sigma`
and `compose sigma.lift (singleton arg)` agree POINTWISE — at variable `0` both are `arg`
(definitionally, `RawTerm.subst0_var_zero` is `rfl`), and at variable `k+1` both are `sigma k`
(`RawTerm.weaken_subst_singleton` cancels the lift's weakening) — so `RawTerm.subst_pointwise`
concludes.  No `funext` (which would pull `Quot.sound`): the pointwise lemma is the funext-free door.

## Zero-axiom verification

One theorem, proved by `subst_compose` + `subst_pointwise` over a structural `Fin` match using only
the safe `⟨0, _⟩` / `⟨k+1, h⟩` anonymous-constructor patterns (no `Fin.cases`).  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Gated in
`FX1PolyAudit/AuditTier0TermAxis.lean`.
-/

namespace FX1Poly.Core

/-- ★ **The term-native `×term` β-substitution bridge** (`term-beta`, re-homed from `context-9`).
Substituting the consed substitution `cons arg sigma` into `body` IS: lift `sigma`, substitute,
then single-substitute `arg` — `body[cons arg sigma] = body[sigma⁺][⟨arg⟩]`.  Proved purely in the
term axis's `RawTermSubst` algebra (no `SubstVec`, no context import) via `subst_compose` +
pointwise agreement (`subst0_var_zero` at `0`, `weaken_subst_singleton` at `k+1`). -/
theorem RawTerm.subst_cons_eq_singleton_after_lift {targetScope sourceScope : Nat}
    (arg : RawTerm targetScope) (sigma : RawTermSubst sourceScope targetScope)
    (body : RawTerm (sourceScope + 1)) :
    RawTerm.subst (RawTermSubst.cons arg sigma) body
      = RawTerm.subst (RawTermSubst.singleton arg)
          (RawTerm.subst sigma.lift body) := by
  rw [RawTerm.subst_compose sigma.lift (RawTermSubst.singleton arg) body]
  refine RawTerm.subst_pointwise ?_ body
  intro position
  match position with
  | ⟨0, _⟩ => rfl
  | ⟨innerPosition + 1, hBound⟩ =>
      exact (RawTerm.weaken_subst_singleton
        (sigma ⟨innerPosition, Nat.lt_of_succ_lt_succ hBound⟩) arg).symm

end FX1Poly.Core
