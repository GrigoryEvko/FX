import LeanFX2.Algo.RawWHNF
import LeanFX2.Confluence.RawParStarCong
import LeanFX2.Reduction.RawParCompatible

/-! # Algo/RawWHNFCorrect — RawTerm.whnf reaches a parallel reduct

Headline theorem `RawTerm.whnf_reaches`:

```lean
∀ {scope} fuel (term : RawTerm scope),
    RawStep.parStar term (RawTerm.whnf fuel term)
```

Every output of `RawTerm.whnf` is reachable from the input via the
reflexive-transitive closure of parallel reduction.  Soundness of
the WHNF reducer with respect to the kernel reduction relation —
the reducer fires only β/ι, never invents reductions.

## Architecture

Induction on fuel × full enumeration of RawTerm (28 ctors).

For canonical heads (var, unit, lam, pair, boolTrue, …) the
function returns the input unchanged, so we close with
`parStar.refl`.

For elim heads with potential redex (app, fst, snd, boolElim, …)
the function recursively whnf's the relevant subterm.  We:

1. Invoke the IH on the subterm to get a parStar chain.
2. Lift via the cong helpers (`parStar.appLeft`, …) to a
   chain on the whole term.
3. Inspect whether the recursively-whnf'd subterm canonicalizes
   (via `?`-projection helpers from `RawWHNF.lean`).
4. If yes, append a single β/ι step plus another IH call on
   the contractum.
5. If no, the chain ends with the rebuilt elim.

The β/ι step uses the per-redex constructor in `RawStep.par`
(e.g., `betaApp`, `iotaBoolElimTrue`), promoted to `parStar`
via `RawStep.par.toStar`.

## Why this matters

Once we have `whnf_reaches`, decidable conversion modulo βι
follows from confluence: convertible terms reach a common reduct
(`RawStep.parStar.confluence`), and WHNF realises a candidate
reduct.  This is the foundation for `Algo/DecConv`. -/

namespace LeanFX2

variable {scope : Nat}

/-- Inversion: if `lamBody? term = some body`, then `term = .lam body`.

Proven by full case enumeration over all 28 RawTerm ctors — only
the `.lam` case returns `some`; every other case returns `none`,
which contradicts the hypothesis.  Uses `dsimp only` to force the
`?`-projection to reduce on each constructor. -/
theorem RawTerm.eq_lam_of_lamBody?_eq_some
    {body : RawTerm (scope + 1)}
    (term : RawTerm scope)
    (witness : RawTerm.lamBody? term = some body) :
    term = .lam body := by
  cases term with
  | lam bodyMatched =>
      have bodyEq : bodyMatched = body :=
        Option.some.inj witness
      exact bodyEq ▸ rfl
  | var _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | unit => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | app _ _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | pair _ _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | fst _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | snd _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | boolTrue => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | boolFalse => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | boolElim _ _ _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | natZero => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | natSucc _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | natElim _ _ _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | natRec _ _ _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | listNil => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | listCons _ _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | listElim _ _ _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | optionNone => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | optionSome _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | optionMatch _ _ _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | eitherInl _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | eitherInr _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | eitherMatch _ _ _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | refl _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | idJ _ _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | modIntro _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | modElim _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | subsume _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness

/-- Inversion for `pairComponents?`. -/
theorem RawTerm.eq_pair_of_pairComponents?_eq_some
    {firstValue secondValue : RawTerm scope}
    (term : RawTerm scope)
    (witness : RawTerm.pairComponents? term = some (firstValue, secondValue)) :
    term = .pair firstValue secondValue := by
  cases term with
  | pair firstMatched secondMatched =>
      have pairEq : (firstMatched, secondMatched) = (firstValue, secondValue) :=
        Option.some.inj witness
      have firstEq : firstMatched = firstValue := (Prod.mk.inj pairEq).1
      have secondEq : secondMatched = secondValue := (Prod.mk.inj pairEq).2
      exact firstEq ▸ secondEq ▸ rfl
  | var _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | unit => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | lam _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | app _ _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | fst _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | snd _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | boolTrue => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | boolFalse => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | boolElim _ _ _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | natZero => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | natSucc _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | natElim _ _ _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | natRec _ _ _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | listNil => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | listCons _ _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | listElim _ _ _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | optionNone => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | optionSome _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | optionMatch _ _ _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | eitherInl _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | eitherInr _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | eitherMatch _ _ _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | refl _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | idJ _ _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | modIntro _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | modElim _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | subsume _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness

end LeanFX2
