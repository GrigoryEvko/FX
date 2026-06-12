import FX1Poly.Core.StepStar
import FX1Poly.Core.StepRename
import FX1Poly.Core.StepSubst
import FX1Poly.Core.HeadStep

/-! # Foundation/PolyCell/Core/StepStarLength
   — Nat-indexed counted parallel of StepStar (well-founded measure)

The well-founded recursion measure for `StepStar` chains.  Since
`StepStar` is `Prop`-valued, defining a function
`StepStar.length : StepStar a b → Nat` would require large elimination
from `Prop` into `Nat` — blocked without `Classical.choice` /
`propext`, banned by the strict zero-axiom discipline.

The standard workaround: a Nat-indexed counted variant
`StepStarN n a b : Prop` that PARALLELS `StepStar a b` with an
explicit Nat index.  Equivalent in power; reasoning about "length"
becomes reasoning about the index.

## API surface

* `StepStarN n a b` — Prop-valued counted chain at length n.
* `StepStarN.reflN t : StepStarN 0 t t` — reflexivity at length 0.
* `StepStarN.transN s r : StepStarN (n+1) a c` — left-extension.
* `StepStarN.toStepStar : StepStarN n a b → StepStar a b` — forget count.
* `StepStar.exists_N : StepStar a b → ∃ n, StepStarN n a b` — recover
  count existentially via Prop-to-Prop induction.
* `StepStarN.single : Step a b → StepStarN 1 a b` — single-step embed.
* `StepStarN.trans_compose : StepStarN m a b → StepStarN n b c →
  StepStarN (m+n) a c` — chain composition; lengths sum.
* `StepStarN.rename` / `StepStarN.subst` — length-preserving rename/subst
  monotonicity (renaming/substituting a chain produces an equal-length
  chain).

## Why no `length : StepStar a b → Nat`

`StepStar` is in `Prop`.  Defining a function `StepStar → Nat`
requires large elimination from `Prop` into `Type` — Lean blocks this
without `Classical.choice` / `propext`.  The Nat-indexed counted
variant is the standard zero-axiom workaround: induct on the index,
reason about the explicit count.

Downstream consumers (the STRICT-COMPLEXITY witness, NbE soundness via
length-induction, the strip property) all reason about the existential
`∃ n, StepStarN n a b` without needing a function — the existential
gives a concrete bound when paired with SN.

## Connection to other substrate

* `Step.rename` / `StepStar.rename` (`StepRename.lean`) is consumed
  by `StepStarN.rename`.
* `Step.subst` / `StepStar.subst` (`StepSubst.lean`) is consumed by
  `StepStarN.subst`.
* `Nat.succ_add` (core Nat lemma) drives the `trans_compose`
  arithmetic — no `omega`.

## Zero-axiom verification

All declarations close by structural induction + a single
`rw [Nat.succ_add]` for the trans_compose arithmetic.  No `simp`,
no `omega`, no `propext`, no `Quot.sound`, no `Classical.choice`.
Audit-gated in `Tools/AuditAll/AuditPolyCell.lean`. -/

namespace FX1Poly.Core

-- `RawRenaming` lives in `FX1Poly.Foundation`, which does not enclose
-- `FX1Poly.Core`, so open it explicitly.
open FX1Poly.Foundation

/-- Nat-indexed counted parallel of `StepStar`.

A `StepStarN priorLen first third` chain is either:
* `reflN` — length 0, with first = third.
* `transN headStep restChain` — length n+1, factoring as a head Step
  + a length-n tail.

Left-extension matches `StepStar`'s ctor shape (Step at the head).
The index explicitly counts Step instances; this is the well-founded
measure that the downstream cascade reasons about. -/
inductive StepStarN {scope : Nat} :
    Nat → RawTerm scope → RawTerm scope → Prop where
  /-- **Reflexivity at length 0.** -/
  | reflN (term : RawTerm scope) : StepStarN 0 term term
  /-- **Left-extension at length n+1.** Prepend a single Step to a
  length-`priorLen` chain to produce a length-`priorLen + 1` chain. -/
  | transN {first second third : RawTerm scope} {priorLen : Nat} :
      Step first second → StepStarN priorLen second third →
      StepStarN (priorLen + 1) first third

/-- **Forget the count.** Any `StepStarN` chain projects to a
`StepStar` chain by discarding the explicit length index.

Construction: structural induction on the counted chain, mapping
`reflN ⟶ StepStar.refl` and `transN ⟶ StepStar.trans`. -/
theorem StepStarN.toStepStar {scope : Nat}
    {priorLen : Nat} {firstTerm thirdTerm : RawTerm scope}
    (countedChain : StepStarN priorLen firstTerm thirdTerm) :
    StepStar firstTerm thirdTerm := by
  induction countedChain with
  | reflN term => exact StepStar.refl term
  | transN headStep _ tailToStepStar =>
      exact StepStar.trans headStep tailToStepStar

/-- **Recover the count existentially.** Any `StepStar` chain has
SOME explicit length witnessed by a `StepStarN` proof.

The count is not a function of the chain (which would require large
elimination from Prop) — it's an existential witness.  Downstream
consumers introduce the witness via `obtain ⟨length, countedChain⟩`
and reason about the explicit Nat from there.

Construction: Prop-to-Prop induction on the input chain, choosing
the length index by structural case analysis. -/
theorem StepStar.exists_N {scope : Nat}
    {firstTerm thirdTerm : RawTerm scope}
    (sourceChain : StepStar firstTerm thirdTerm) :
    ∃ priorLen, StepStarN priorLen firstTerm thirdTerm := by
  induction sourceChain with
  | refl term => exact ⟨0, StepStarN.reflN term⟩
  | trans headStep _ tailExists =>
      obtain ⟨tailLen, tailCounted⟩ := tailExists
      exact ⟨tailLen + 1, StepStarN.transN headStep tailCounted⟩

/-- **Single-step embedding at length 1.** Lift a single `Step` to a
length-1 `StepStarN` chain.

The shortest non-trivial counted chain — `transN` composed with
`reflN` at the tail.  Mirrors `StepStar.single` from
`StepStar.lean:188`. -/
theorem StepStarN.single {scope : Nat} {firstTerm secondTerm : RawTerm scope}
    (singleStep : Step firstTerm secondTerm) :
    StepStarN 1 firstTerm secondTerm :=
  StepStarN.transN singleStep (StepStarN.reflN secondTerm)

/-- **Full transitivity with length addition.** Compose two counted
chains end-to-end; the resulting length is the sum.

This is the load-bearing closure property for length-induction
proofs.  The arithmetic uses `Nat.succ_add` (core Nat lemma) — no
`omega`.

Proof structure:
* `reflN` case: first chain has length 0, so `firstLen + secondLen
  = secondLen` definitionally; return the second chain unchanged.
* `transN` case: peel off the head Step, compose the tail with the
  second chain by induction (yielding length `priorLen + secondLen`),
  re-prepend the head step (yielding length `priorLen + secondLen +
  1`).  Goal arithmetic `(priorLen + 1) + secondLen = (priorLen +
  secondLen) + 1` discharged by `rw [Nat.succ_add]`. -/
theorem StepStarN.trans_compose {scope : Nat}
    {firstTerm secondTerm thirdTerm : RawTerm scope}
    {firstLen secondLen : Nat}
    (firstChain : StepStarN firstLen firstTerm secondTerm)
    (secondChain : StepStarN secondLen secondTerm thirdTerm) :
    StepStarN (firstLen + secondLen) firstTerm thirdTerm := by
  induction firstChain with
  | reflN _ =>
      rw [Nat.zero_add]
      exact secondChain
  | transN headStep _ restCompose =>
      rw [Nat.succ_add]
      exact StepStarN.transN headStep (restCompose secondChain)

/-- **Length-preserving rename.** Renaming every term in a
`StepStarN` chain produces an equal-length counted chain on the
renamed terms.

Cites `Step.rename` from `StepRename.lean` to lift each individual
Step through the renaming.  The Nat index is preserved because
renaming does not introduce or eliminate Step instances. -/
theorem StepStarN.rename {sourceScope targetScope : Nat}
    {priorLen : Nat} {sourceTerm thirdTerm : RawTerm sourceScope}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (sourceChain : StepStarN priorLen sourceTerm thirdTerm) :
    StepStarN priorLen
      (RawTerm.rename rawRenaming sourceTerm)
      (RawTerm.rename rawRenaming thirdTerm) := by
  induction sourceChain with
  | reflN _ => exact StepStarN.reflN _
  | transN headStep _ tailIH =>
      exact StepStarN.transN (Step.rename rawRenaming headStep) tailIH

/-- **Length-preserving substitution.** Substituting every term in a
`StepStarN` chain produces an equal-length counted chain on the
substituted terms.

Cites `Step.subst` from `StepSubst.lean` to lift each individual Step
through the substitution.  The Nat index is preserved because
substitution does not introduce or eliminate Step instances. -/
theorem StepStarN.subst {sourceScope targetScope : Nat}
    {priorLen : Nat} {sourceTerm thirdTerm : RawTerm sourceScope}
    (rawSubst : RawTermSubst sourceScope targetScope)
    (sourceChain : StepStarN priorLen sourceTerm thirdTerm) :
    StepStarN priorLen
      (RawTerm.subst rawSubst sourceTerm)
      (RawTerm.subst rawSubst thirdTerm) := by
  induction sourceChain with
  | reflN _ => exact StepStarN.reflN _
  | transN headStep _ tailIH =>
      exact StepStarN.transN (Step.subst rawSubst headStep) tailIH

/-- **Smoke: identity-lambda counted-reduces to its argument at
length 1.**

Concrete fixture: `(lam (var 0)) unit` reduces to `unit` in exactly
one Step via `Step.beta`.  Lifts to `StepStarN 1` via `single`. -/
theorem StepStarN.identity_lam_beta_unit_smoke :
    let identityLamBody : RawTerm 1 :=
      .mkGen .gen_var (⟨0, Nat.zero_lt_succ 0⟩ : Fin 1) .childNil
    let domainAnn : RawTerm 0 :=
      .mkGen .gen_unit () .childNil
    let unitArg : RawTerm 0 :=
      .mkGen .gen_unit () .childNil
    let appTerm : RawTerm 0 :=
      .mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_lam ()
            (.childCons domainAnn (.childCons identityLamBody .childNil)))
          (.childCons unitArg .childNil))
    StepStarN 1 appTerm unitArg :=
  StepStarN.single HeadStep.beta.toStep

end FX1Poly.Core
