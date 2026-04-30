import LeanFX.Syntax.TermSubst.Commute.Subst0Subst

/-! # Term substitution / renaming umbrella module.

Re-exports the term-level substitution and renaming algebra,
the typed counterpart of `RawSubst.lean`'s raw operations.  The
single import pulls in the entire dependency tree:

  * `TermSubst.Core` — definitions of `Term.subst`,
    `Term.rename`, plus `Term.subst0` and `Term.subst0_term`
    (β-substitution shorthand).  Carries the `Term.weaken`
    helper too.
  * `TermSubst.Compose` — composition laws for term-level
    substitutions (subst-after-subst, rename-after-rename).
  * `TermSubst.Pointwise` — `Subst.pointwiseEq` lifted to terms,
    used to thread substitution agreement through proofs.
  * `TermSubst.HEqCongr` — heterogeneous-equality congruence
    lemmas (subst arguments propagate through HEq).
  * `TermSubst.Rename` — rename-side identity / composition /
    pointwise / weaken laws.
  * `TermSubst.Commute.*` — interaction between substitution
    and renaming (rename-after-subst, subst-after-rename,
    singleton + subst0 specializations).  The Commute family
    closes by importing `Subst0Subst`, the deepest leaf.

Convention: every layer here keeps zero axioms (verified via
`Tools.AuditAll.lean`'s gates).  The `Term.subst*` family is
marked `@[reducible]` per Wave 2 (W2.4) so `▸` casts and the
elaborator's type-equality checker can unfold as needed. -/
