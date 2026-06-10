import FX1Poly.Universe.LevelExprSimplify

/-! Probe (#472): closed-fragment `denoteEquiv` decidability INCLUDING impredicative `limax`.
    The live universe normalizer (M22 `simplify`) is predicative — it cannot decide `limax` because the
    collapse `if codomain = 0 then 0 else max` is VALUE-DEPENDENT. But that value-dependence enters ONLY
    through free variables in the codomain. A CLOSED codomain denotes a constant, so its zero-test is static
    ⇒ `limax` needs no predicativity gate. Goal: env-independence for closed exprs + decidable closed denoteEquiv. -/

namespace FX1Poly.Universe

/-- Propext-clean `(a && b) = true → a = true ∧ b = true` via structural Bool cases (no iff, no simp). -/
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
predicativity restriction the M22 normalizer needs is unnecessary when both expressions are closed: the
single zero-env comparison decides it via `Nat.decEq`.  This contradicts the "open-term `denoteEquiv`
undecidable" framing exactly at the closed boundary — the impredicative `limax` is fully decided here. -/
def LevelExpr.decidableDenoteEquivClosed {e1 e2 : LevelExpr}
    (hClosed1 : e1.isClosed = true) (hClosed2 : e2.isClosed = true) :
    Decidable (LevelExpr.denoteEquiv e1 e2) :=
  match Nat.decEq (e1.denote (fun _ => 0)) (e2.denote (fun _ => 0)) with
  | isTrue hAtZero => isTrue ((LevelExpr.denoteEquiv_closed_iff hClosed1 hClosed2).mpr hAtZero)
  | isFalse hNotAtZero =>
      isFalse (fun hEquiv => hNotAtZero ((LevelExpr.denoteEquiv_closed_iff hClosed1 hClosed2).mp hEquiv))

/-! ## General impredicative boundary (open terms, strong codomain hypotheses) -/

/-- **`limax e1 e2 ~ lmax e1 e2` when the codomain is always positive.**  The non-collapse regime: if the
codomain never denotes `0`, `limax` behaves as ordinary `lmax`. -/
theorem LevelExpr.limax_denoteEquiv_lmax_of_codomainPos {e1 e2 : LevelExpr}
    (hPos : ∀ env, e2.denote env ≠ 0) :
    LevelExpr.denoteEquiv (LevelExpr.limax e1 e2) (LevelExpr.lmax e1 e2) :=
  fun env => LevelExpr.limax_denote_eq_lmax_when_codomain_nonzero e1 e2 env (hPos env)

/-- **`limax e1 e2 ~ lzero` when the codomain is always zero.**  The full impredicative collapse:
`Π (x : Type e1). Prop : Prop` regardless of `e1`. -/
theorem LevelExpr.limax_denoteEquiv_lzero_of_codomainZero {e1 e2 : LevelExpr}
    (hZero : ∀ env, e2.denote env = 0) :
    LevelExpr.denoteEquiv (LevelExpr.limax e1 e2) LevelExpr.lzero :=
  fun env => by
    rw [LevelExpr.denote_limax, if_pos (hZero env), LevelExpr.denote_lzero]

end FX1Poly.Universe

-- Zero-axiom verification
#print axioms FX1Poly.Universe.LevelExpr.denote_closed_env_independent
#print axioms FX1Poly.Universe.LevelExpr.denoteEquiv_closed_iff
#print axioms FX1Poly.Universe.LevelExpr.decidableDenoteEquivClosed
#print axioms FX1Poly.Universe.LevelExpr.limax_denoteEquiv_lmax_of_codomainPos
#print axioms FX1Poly.Universe.LevelExpr.limax_denoteEquiv_lzero_of_codomainZero
