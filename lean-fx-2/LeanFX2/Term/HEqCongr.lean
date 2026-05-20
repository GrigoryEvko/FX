import LeanFX2.Term.HEqCongr.Compound
import LeanFX2.Term.HEqCongr.Atomic

/-! # Term/HEqCongr — HEq congruence lemmas for Term constructors (shim)

When two raw-aware Term values have indices that differ via Eq (Ty
indices, RawTerm indices), HEq lets us state "these are equal modulo
Type alignment".  These congruence lemmas are the building blocks
for the HEq cascades in Reduction/Compat (rename / subst preserve
β-redex shape) and for the typed-confluence cd_lemma bridge.

## Pattern

Each lemma:
1. Quantifies over two parallel sets of indices (LHS and RHS)
2. Takes Eq witnesses for each varying index
3. Takes HEq witnesses for sub-Term values (whose indices may
   differ before the Eqs are applied)
4. Produces HEq for the constructed Term

The proof technique is uniform:
* `subst` each Eq to align the indices
* After alignment, HEq sub-values become Eq via `eq_of_heq`
* `cases` the resulting Eqs to replace LHS by RHS
* Conclude with `rfl` (HEq.refl since both sides are now identical)

## Module split

To keep elaboration parallelism healthy (per the build-performance
note in `CLAUDE.md`), the 77 congruences live in two sub-modules:

* `Term/HEqCongr/Compound.lean` — Π/Σ binders, ι-recursors, identity
  J, observational and strict identity, modal wrappers
  (modIntro/modElim/subsume/cumulUp), and HoTT-special reflexivity
  witnesses (35 theorems)
* `Term/HEqCongr/Atomic.lean` — public shim for atomic congruence
  leaves:
  * `Atomic/Base.lean` — variables, closed atomics, interval primitives
  * `Atomic/Cubical.lean` — path, glue, transport, hcomp
  * `Atomic/Structural.lean` — record/refine/codata/session/effect
  * `Atomic/TypeCodes.lean` — universe and type-code values
  * `Atomic/HeterogeneousIntro.lean` — HoTT heterogeneous intros

This shim re-exports both so existing consumers keep their
`import LeanFX2.Term.HEqCongr` statement unchanged.

## Zero-axiom discipline

`subst`, `cases` on Eq, and `eq_of_heq` are all axiom-free in Lean 4
(they use the Eq.casesOn / HEq.casesOn structural eliminators).  Each
lemma is verified zero-axiom by an audit gate in
`Smoke/AuditPhase2HEqCongr.lean`. -/
