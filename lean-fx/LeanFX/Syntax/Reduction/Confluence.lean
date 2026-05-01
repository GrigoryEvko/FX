import LeanFX.Syntax.Reduction.Diamond

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! # Iterated complete development and confluence (W8.3 / #885).

This file builds typed Church-Rosser on top of the diamond
property (`Step.par.diamond`, proved in `Diamond.lean`).

At the typed level, `Step.par.cd_lemma_star` produces a
`Step.parStar` chain (not a single par), so the standard
strip-lemma + Hindley-Rosen argument from the raw level
(`RawConfluence.lean`) does not transfer directly: the chain's
length is not bounded by the input chain's length, defeating any
naive well-founded measure.

The route here is the **iterated complete development**.  Define
`cdIter n term = (Term.cd)^n term`.  Three lemmas drive the
proof:

* `Step.par.cd_monotone bi` — `Step.par.isBi`-witnessed steps
  lift to `parStar` between complete developments
  (`parStar (Term.cd source) (Term.cd target)`).  Tait-style
  induction with ~50 cases, each closed by the matching
  `parStar.<C>_cong` rule (cong cases) or by combining
  `subst0_parStar` with `cd_lemma_star` (β cases).

* `Step.parStar.cd_monotone` — chain induction over `cd_monotone`.

* `Step.parStar.cdIter_completion` — every `parStar.isBi` chain
  of length `n` reaches `cdIter n` of its source.

The headline `Step.parStar.confluence` then takes the maximum
of the two chain lengths and uses `cdIter (max n m)` as the
common reduct.

The `cdIter` definition itself is pure data — it iterates
`Term.cd` `count` times.  No proof obligations attach to it; the
work is in the theorems above. -/

/-- `Term.cdIter count term` applies the complete-development
operator `Term.cd` `count` times to `term`.  Pure structural
recursion on `count` — `cdIter 0 t = t`, `cdIter (n+1) t = cd
(cdIter n t)`.

Used by `Step.parStar.confluence` as the join point: every
`isBi`-chain of length `n` reaches `cdIter n source`, so two
chains of lengths `n` and `m` both reach `cdIter (max n m)
source` after enough cd-iterations. -/
@[reducible] def Term.cdIter
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} {termType : Ty level scope}
    (count : Nat) (term : Term context termType) :
    Term context termType :=
  match count with
  | 0 => term
  | Nat.succ predecessor => Term.cd (Term.cdIter predecessor term)

/-- `cdIter 0` is the identity. -/
theorem Term.cdIter_zero
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} {termType : Ty level scope}
    (term : Term context termType) :
    Term.cdIter 0 term = term :=
  rfl

/-- `cdIter (n+1)` is `cd` applied to `cdIter n`. -/
theorem Term.cdIter_succ
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} {termType : Ty level scope}
    (predecessorCount : Nat) (term : Term context termType) :
    Term.cdIter (predecessorCount + 1) term =
      Term.cd (Term.cdIter predecessorCount term) :=
  rfl

/-- `cdIter 1` is exactly `Term.cd`. -/
theorem Term.cdIter_one
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} {termType : Ty level scope}
    (term : Term context termType) :
    Term.cdIter 1 term = Term.cd term :=
  rfl

end LeanFX.Syntax
