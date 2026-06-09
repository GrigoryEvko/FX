import FX1Poly.Universe.LevelExprSimplify

/-! # FX1Poly/Universe/LevelExprImpredicativeClosure
    — decidable `denoteEquiv` on the CLOSED fragment, INCLUDING the impredicative `limax`

The predicative universe normalizer (`LevelExpr.simplify`) is SOUND but INCOMPLETE for the impredicative
`limax`: it ships only the two collapse rules (`limax lzero e ~ e`, `limax e lzero ~ lzero`) plus congruence,
and leaves `limax x y` untouched when neither operand is `lzero`.  It cannot DECIDE impredicative equivalence
because the collapse `denote (limax e1 e2) env = if denote e2 env = 0 then 0 else levelMax …` is
VALUE-DEPENDENT — the conditional branches on whether the codomain denotes zero.

That value-dependence enters ONLY through free variables in the codomain `e2`.  A CLOSED codomain (no `lvar`)
denotes a single constant under every environment, so its zero-test is settled STATICALLY — the impredicative
`limax` needs no predicativity gate when its operands are closed.  This file makes that precise:

  * `LevelExpr.isClosed` — structural "no `lvar`" predicate, recursing into BOTH `limax` children (the codomain
    whose zero-test drives the collapse is covered).
  * `LevelExpr.denote_closed_env_independent` — a closed `LevelExpr` denotes the same `Nat` under every
    environment.  The `limax` arm is the load-bearing case: both children are env-independent, so the
    conditional resolves identically on both sides — the value-dependence is pinned.
  * `LevelExpr.denoteEquiv_closed_iff` — for closed `e1`, `e2`, semantic equivalence (equal under EVERY env)
    reduces to equality under the single zero environment.
  * `LevelExpr.decidableDenoteEquivClosed` (★) — `Decidable (denoteEquiv e1 e2)` on the closed fragment, WITH
    `limax`, decided by one `Nat.decEq` at the zero environment.  This is "decide `denoteEquiv` without a
    predicativity gate" for the closed fragment: the impredicative `limax` is FULLY decided here.  It sharpens
    the boundary — open-term impredicative `denoteEquiv` is the value-dependent hard case, but the closed
    codomain is statically decidable.

Plus the two general impredicative-boundary `denoteEquiv` rules (open terms, strong codomain hypotheses):
`limax_denoteEquiv_lmax_of_codomainPos` (codomain never zero ⇒ behaves as ordinary `lmax`) and
`limax_denoteEquiv_lzero_of_codomainZero` (codomain always zero ⇒ the full impredicative collapse to `lzero`).

## Zero-axiom verification

`bothBoolTrue` splits `(a && b) = true` by structural Bool `cases` (no iff, no `simp`).  The env-independence
is `induction` on `LevelExpr` with the closedness hypothesis reverted into the motive; `lvar` is `Bool.noConfusion`,
the `&&` arms split via `bothBoolTrue`, and `lsucc`/`lmax`/`limax` `rw` by the IHs.  `decidableDenoteEquivClosed`
matches `Nat.decEq` and threads the iff's `mp`/`mpr` (propext-free).  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/AuditUniverse.lean`.
-/

namespace FX1Poly.Universe

/-- Propext-clean `(a && b) = true → a = true ∧ b = true` via structural Bool cases (no iff, no `simp`). -/
theorem bothBoolTrue {flagA flagB : Bool} (h : (flagA && flagB) = true) :
    flagA = true ∧ flagB = true := by
  cases flagA with
  | false => exact Bool.noConfusion h
  | true =>
    cases flagB with
    | false => exact Bool.noConfusion h
    | true => exact ⟨rfl, rfl⟩

/-- A `LevelExpr` is closed when it contains no `lvar`.  `limax` recurses into BOTH children (domain and
codomain), so closedness covers the codomain whose zero-test drives the impredicative collapse. -/
def LevelExpr.isClosed : LevelExpr → Bool
  | .lzero => true
  | .lsucc inner => inner.isClosed
  | .lmax left right => left.isClosed && right.isClosed
  | .limax left right => left.isClosed && right.isClosed
  | .lvar _ => false

/-- **Env-independence of closed denotations.**  A closed `LevelExpr` denotes the same `Nat` under every
environment.  The `limax` arm is the interesting one: both children are env-independent, so the codomain's
zero-test resolves identically on both sides ⇒ the value-dependent conditional is pinned. -/
theorem LevelExpr.denote_closed_env_independent (env1 env2 : Nat → Nat) (expr : LevelExpr) :
    expr.isClosed = true → expr.denote env1 = expr.denote env2 := by
  induction expr with
  | lzero => intro _; rfl
  | lvar idx => intro hClosed; exact Bool.noConfusion hClosed
  | lsucc inner ihInner =>
      intro hClosed
      show inner.denote env1 + 1 = inner.denote env2 + 1
      rw [ihInner hClosed]
  | lmax left right ihLeft ihRight =>
      intro hClosed
      have hSplit := bothBoolTrue (by
        show (left.isClosed && right.isClosed) = true
        exact hClosed)
      show LevelExpr.levelMax (left.denote env1) (right.denote env1)
        = LevelExpr.levelMax (left.denote env2) (right.denote env2)
      rw [ihLeft hSplit.1, ihRight hSplit.2]
  | limax left right ihLeft ihRight =>
      intro hClosed
      have hSplit := bothBoolTrue (by
        show (left.isClosed && right.isClosed) = true
        exact hClosed)
      show (if right.denote env1 = 0 then 0
            else LevelExpr.levelMax (left.denote env1) (right.denote env1))
         = (if right.denote env2 = 0 then 0
            else LevelExpr.levelMax (left.denote env2) (right.denote env2))
      rw [ihLeft hSplit.1, ihRight hSplit.2]

/-- **Closed `denoteEquiv` reduces to a single zero-env comparison.**  For closed `e1`, `e2`, semantic
equivalence (equal under EVERY env) is equivalent to equality under the single zero environment — because
each side is env-independent. -/
theorem LevelExpr.denoteEquiv_closed_iff {e1 e2 : LevelExpr}
    (hClosed1 : e1.isClosed = true) (hClosed2 : e2.isClosed = true) :
    LevelExpr.denoteEquiv e1 e2 ↔ e1.denote (fun _ => 0) = e2.denote (fun _ => 0) := by
  constructor
  · intro hEquiv
    exact hEquiv (fun _ => 0)
  · intro hAtZero env
    rw [LevelExpr.denote_closed_env_independent env (fun _ => 0) e1 hClosed1,
        LevelExpr.denote_closed_env_independent env (fun _ => 0) e2 hClosed2]
    exact hAtZero

/-- **★ Decidable `denoteEquiv` on the closed fragment — WITH `limax`, no predicativity gate.**  The
predicativity restriction the universe normalizer needs is unnecessary when both expressions are closed: the
single zero-env comparison decides it via `Nat.decEq`.  The impredicative `limax` is fully decided here, at
the exact boundary the open-term value-dependence makes hard. -/
def LevelExpr.decidableDenoteEquivClosed {e1 e2 : LevelExpr}
    (hClosed1 : e1.isClosed = true) (hClosed2 : e2.isClosed = true) :
    Decidable (LevelExpr.denoteEquiv e1 e2) :=
  match Nat.decEq (e1.denote (fun _ => 0)) (e2.denote (fun _ => 0)) with
  | isTrue hAtZero => isTrue ((LevelExpr.denoteEquiv_closed_iff hClosed1 hClosed2).mpr hAtZero)
  | isFalse hNotAtZero =>
      isFalse (fun hEquiv => hNotAtZero ((LevelExpr.denoteEquiv_closed_iff hClosed1 hClosed2).mp hEquiv))

/-- **`limax e1 e2 ~ lmax e1 e2` when the codomain is always positive.**  The non-collapse regime: if the
codomain never denotes `0`, `limax` behaves as ordinary `lmax`. -/
theorem LevelExpr.limax_denoteEquiv_lmax_of_codomainPos {e1 e2 : LevelExpr}
    (hPos : ∀ env, e2.denote env ≠ 0) :
    LevelExpr.denoteEquiv (LevelExpr.limax e1 e2) (LevelExpr.lmax e1 e2) :=
  fun env => LevelExpr.limax_denote_eq_lmax_when_codomain_nonzero e1 e2 env (hPos env)

/-- **`limax e1 e2 ~ lzero` when the codomain is always zero.**  The full impredicative collapse:
`Pi (x : Type e1). Prop : Prop` regardless of `e1`. -/
theorem LevelExpr.limax_denoteEquiv_lzero_of_codomainZero {e1 e2 : LevelExpr}
    (hZero : ∀ env, e2.denote env = 0) :
    LevelExpr.denoteEquiv (LevelExpr.limax e1 e2) LevelExpr.lzero :=
  fun env => by
    rw [LevelExpr.denote_limax, if_pos (hZero env), LevelExpr.denote_lzero]

end FX1Poly.Universe
