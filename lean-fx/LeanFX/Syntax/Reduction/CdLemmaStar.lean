import LeanFX.Syntax.Reduction.ParBi

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ## `Step.par.cd_lemma_star` — typed complete-development lemma (βι-only).

Statement: every typed parallel step `Step.par sourceTerm targetTerm`
that is `Step.par.isBi`-witnessed (i.e., uses no η-rule anywhere)
satisfies `Step.parStar targetTerm (Term.cd sourceTerm)`.

Together with `Step.par.cd_dominates` (every term parallel-reduces to
its complete development), this is the typed Tait–Martin-Löf complete-
development pair restricted to βι.  The diamond property and
confluence of `Step.parStar` for βι follow immediately.

η is excluded: `Term.cd` deliberately does not η-contract (§
CompleteDevelopment.lean), so a parallel step that fires η produces a
target outside `Term.cd`'s reach.  This is why `Step.par.isBi` gates
the lemma: η constructors of `Step.par` have no `isBi` case, so the
proof's `induction isBi` skips them vacuously.

## Proof architecture

Direct typed-level induction on `isBi` discharges 37 of the 54 βι
cases cleanly:

  * **Refl**: `Step.par.cd_dominates` lifted to `parStar`.
  * **Pure-cong (no contraction inside `cd`)** — lam, lamPi, pair,
    natSucc, listCons, optionSome, eitherInl, eitherInr — `simp only
    [Term.cd]` + matching `Step.parStar.<ctor>_cong` rule applied to
    IHs.
  * **Eliminator-cong (cd may contract)** — app, appPi, fst, snd,
    boolElim, natElim, natRec, listElim, optionMatch, eitherMatch,
    idJ — `simp only [Term.cd]` + `split` on the inner match; redex
    arms append a single contracting `Step.par` step via `snoc`;
    wildcard arm uses the cong rule.
  * **Shallow β/ι** — betaApp, betaAppPi, betaFstPair, betaSndPair,
    iotaBoolElim{True,False}, iotaNatElim{Zero,Succ}, etc. — `simp
    only [Term.cd]` exposes the same redex on the developed source;
    `Step.parStar.subst0_parStar` (β) or the appropriate IH (ι)
    closes.

The 17 **deep β/ι** cases (betaAppDeep, betaAppPiDeep, etc.) need
typed parStar-inversion to extract the contracted shape from the IH
(e.g., `Step.parStar (Term.lam body) target → ∃ body', target =
Term.lam body'`).  Lean's dependent-elimination check rejects direct
`cases step` on such inversions because constructors like `betaAppPi`
have target types involving the non-injective `Ty.subst0`.

The architecturally clean unblock is the **typed→raw bridge**
(`Step.par.toRawBridge`, Phase 4c, task #994):

  1. Lift `Step.par s t` to `RawStep.par s.toRaw t.toRaw` via
     a 56-case structural translation.
  2. Apply the already-proven raw `RawStep.par.lam_inv` (and
     companions) to extract structural information from the IH.
  3. Use the structural information to discharge the typed goal.

This file lands the smoke skeleton that confirms `induction isBi`'s
IH structure is correct.  Full cd_lemma_star awaits the bridge. -/

/-- Smoke skeleton that proves cd_lemma_star for the refl case via
the `cd_dominates → parStar` lift. -/
private theorem Step.par.cd_lemma_star_refl_only_smoke
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {termType : Ty level scope}
    (term : Term ctx termType) :
    Step.parStar term (Term.cd term) :=
  Step.par.toParStar (Step.par.cd_dominates term)

/-- Discharge of the `Step.par.isBi.refl` constructor case.  Pulled
out as a standalone helper so the eventual full `cd_lemma_star`
can reuse it without re-proving via `cd_dominates`. -/
private theorem Step.par.cd_lemma_star_refl_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {termType : Ty level scope}
    (term : Term ctx termType) :
    Step.parStar term (Term.cd term) :=
  Step.par.toParStar (Step.par.cd_dominates term)

/-- Discharge of the `Step.par.isBi.lam` constructor case.  Given
the body-IH (Step.parStar on the body's reduct), `simp [Term.cd]`
unfolds `Term.cd (Term.lam body)` to `Term.lam (Term.cd body)`,
then `Step.parStar.lam_cong` lifts the IH through the binder. -/
private theorem Step.par.cd_lemma_star_lam_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {body body' : Term (ctx.cons domainType) codomainType.weaken}
    (bodyIH : Step.parStar body' (Term.cd body)) :
    Step.parStar (Term.lam (codomainType := codomainType) body')
                 (Term.cd (Term.lam (codomainType := codomainType) body)) := by
  simp only [Term.cd]
  exact Step.parStar.lam_cong bodyIH

/-- Discharge of the `Step.par.isBi.lamPi` constructor case. -/
private theorem Step.par.cd_lemma_star_lamPi_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {body body' : Term (ctx.cons domainType) codomainType}
    (bodyIH : Step.parStar body' (Term.cd body)) :
    Step.parStar (Term.lamPi (domainType := domainType) body')
                 (Term.cd (Term.lamPi (domainType := domainType) body)) := by
  simp only [Term.cd]
  exact Step.parStar.lamPi_cong bodyIH

end LeanFX.Syntax
