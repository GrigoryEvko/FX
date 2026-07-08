import FX1Poly.Tier0.Type.Level.LevelExprImpredicativeClosure

/-! # FX1Poly/Universe/LevelDecision
    — WP-LEVEL: the universe-level algebra decided per FRAGMENT (max/succ/var + closed-imax),
      with the open-impredicative fragment PRECISELY WALLED as the residual

This file is the honest capstone for the level dimension of the WP ladder (`#2076`): "the
universe-level algebra decided" — decidable equality of `LevelExpr` under the `max`/`imax`/`succ`
theory (the classical Lean/Rocq level algebra, Géran CSL 2026, LIPIcs 363:39).

## What "decided" means here, honestly

Semantic equality is `LevelExpr.denoteEquiv e1 e2 := ∀ env, e1.denote env = e2.denote env`
(equal under EVERY valuation of the level variables).  This is the contentful notion — NOT
`simplify`-NF syntactic equality.  The classical result: `denoteEquiv` is decidable via a
UNIQUE canonical form (`max` over atoms `v+k` / constant `k`), soundness (the normalizer
preserves the denotation) + completeness (semantically-equal ⟹ equal NF, by evaluating at
distinguishing valuations).

The two contentful halves are ALREADY SHIPPED in the tower and re-exported here as the
capstone ledger:

  * **Soundness** — `LevelExpr.simplify_denoteEquiv` (`simplify` preserves the denotation under
    every env).
  * **Predicative completeness + decision** — `LevelExpr.denoteEquiv_iff_fullCanonicalize_eq`
    (semantic equality ↔ equal fully-canonicalized max-plus form, via the distinguishing
    `scaledPointEnvironment` valuations + `canonicalForm_unique`) and `LevelExpr.decideDenoteEquiv`.
  * **Closed-impredicative completeness + decision** — `LevelExpr.denoteEquiv_closed_iff`
    (a closed expr is env-independent, so semantic equality collapses to one zero-env
    comparison) and `LevelExpr.decidableDenoteEquivClosed`, which decides the impredicative
    `limax` WITHOUT a predicativity gate for the closed fragment.

## What this file ADDS

1. `LevelExpr.decideDenoteEquivDispatch` — ONE dispatcher: `Decidable (denoteEquiv e1 e2)`
   whenever both operands are predicative OR both are closed (`inDecidableFragment = true`).
   Packages the two shipped deciders behind a single entry point.
2. The two easy impredicative `denoteEquiv` congruences that push a `limax` toward a
   cofinal-variable codomain — `limax_lmax_distrib_denoteEquiv`
   (`limax a (lmax b c) ~ lmax (limax a b) (limax a c)`) and `limax_assoc_denoteEquiv`
   (`limax a (limax b c) ~ limax (lmax a b) c`) — pure `levelMax`-arithmetic, provable now,
   the first bricks toward the open-impredicative decision.
3. The honest fragment ledger `levelFragmentDecision` (predicativeOpen = decided,
   closedImpredicative = decided, openImpredicative = residual) + the capstone certificate
   `levelDecision_certificate` bundling soundness + both completeness iffs + the ledger.
4. Non-vacuity smokes through the dispatcher: an equal pair decides `true`, a distinguishing
   pair decides `false`, both for the predicative and the closed-imax fragments, plus a
   distribution-law instance cross-checked by the decider.
5. Rung markers: `fxLevel_hasDecidableLevelAlgebraOnDecidedFragments = true` (BACKED — the
   predicative-open + closed-impredicative algebra is genuinely decided with distinguishing-
   valuation completeness) and `fxLevel_hasFullDecidableLevelAlgebra = false` (the
   open-impredicative-over-variables fragment — `limax x y` with free variables in the
   codomain `y`, so the zero-test `denote y env = 0?` is valuation-dependent — is the
   precisely-named residual, requiring the `2^k` cofinal-variable case-split of Géran §Obs.10,
   NOT asserted this round).

## Zero-axiom verification

The dispatcher threads `bothBoolTrue` (Bool-cases) through the shipped deciders; the closedness
recovery is a structural Bool `cases`; the arithmetic lemmas are the equation compiler over
`levelMax` + `if_neg` + the audited `levelMax_assoc`/`levelMax_interchange`/`levelMax_self`;
`Nat.noConfusion` refutes `succ = 0`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/Tier0/Type/Level/LevelDecision.lean`.

## References

* Yoan Géran, *A Canonical Form for Universe Levels in Impredicative Type Theory*, CSL 2026,
  LIPIcs 363:39 — the `0`/`succ`/`max`/`imax` algebra, the canonical `max`-of-atoms form,
  Observation 10 (`imax(u,0) ~ 0`, `imax(u, S v) ~ max(u, S v)`), and the
  distinguishing-valuation (V-minimal over-valuation) completeness argument.
* Carneiro, *The Type Theory of Lean* (CMU 2019) — the level algebra this decides.
-/

namespace FX1Poly.Universe

/-! ## A `levelMax`-with-successor never denotes zero -/

/-- `levelMax a (b+1) ≠ 0`: a `levelMax` with a successor right operand is always positive,
regardless of the (possibly neutral) left operand.  Structural on the left: both arms reduce
the `levelMax` head to a `Nat.succ`, refuted against `0` by `Nat.noConfusion`.  Load-bearing
for the impredicative-assoc arithmetic (the inner `limax`'s zero-test on a `succ` codomain). -/
theorem LevelExpr.levelMax_succ_right_ne_zero :
    ∀ (valueA valueB : Nat), LevelExpr.levelMax valueA (valueB + 1) ≠ 0
  | 0, _ => fun succEqZero => Nat.noConfusion succEqZero
  | _ + 1, _ => fun succEqZero => Nat.noConfusion succEqZero

/-! ## Impredicative-boundary arithmetic

Two pure `Nat` identities over `levelMax` + the impredicative conditional, each the arithmetic
core of one `limax` `denoteEquiv` congruence below. -/

/-- **imax-over-lmax distribution, arithmetic core.**  With `levelMax` written `m`:
`(if m B C = 0 then 0 else m A (m B C)) = m (if B=0 then 0 else m A B) (if C=0 then 0 else m A C)`.
Four-way case split on `B, C` being zero/positive; the both-positive corner is the
self-distribution `m A (m B C) = m (m A B) (m A C)` discharged by `levelMax_interchange` +
`levelMax_self`.  The zero corners collapse by the `levelMax` unit laws. -/
theorem LevelExpr.levelMax_imax_lmax_distrib_arith :
    ∀ (valueA valueB valueC : Nat),
      (if LevelExpr.levelMax valueB valueC = 0 then 0
       else LevelExpr.levelMax valueA (LevelExpr.levelMax valueB valueC))
        = LevelExpr.levelMax
            (if valueB = 0 then 0 else LevelExpr.levelMax valueA valueB)
            (if valueC = 0 then 0 else LevelExpr.levelMax valueA valueC)
  | _, 0, 0 => rfl
  | valueA, 0, cc + 1 => by
      show LevelExpr.levelMax valueA (LevelExpr.levelMax 0 (cc + 1))
         = LevelExpr.levelMax 0 (LevelExpr.levelMax valueA (cc + 1))
      rw [LevelExpr.levelMax_zero_left (cc + 1),
          LevelExpr.levelMax_zero_left (LevelExpr.levelMax valueA (cc + 1))]
  | valueA, bb + 1, 0 => by
      show LevelExpr.levelMax valueA (LevelExpr.levelMax (bb + 1) 0)
         = LevelExpr.levelMax (LevelExpr.levelMax valueA (bb + 1)) 0
      rw [LevelExpr.levelMax_zero_right (bb + 1),
          LevelExpr.levelMax_zero_right (LevelExpr.levelMax valueA (bb + 1))]
  | valueA, bb + 1, cc + 1 => by
      show LevelExpr.levelMax valueA (LevelExpr.levelMax (bb + 1) (cc + 1))
         = LevelExpr.levelMax (LevelExpr.levelMax valueA (bb + 1))
                              (LevelExpr.levelMax valueA (cc + 1))
      rw [LevelExpr.levelMax_interchange valueA (bb + 1) valueA (cc + 1),
          LevelExpr.levelMax_self valueA]

/-- **imax-assoc, arithmetic core.**  The nested-`limax` codomain zero-test drives everything:
when the innermost codomain `C` is zero both sides collapse to `0`; when `C = cc+1` the inner
`limax` is positive (`levelMax_succ_right_ne_zero`), so the outer conditional fires and the two
sides agree by `levelMax_assoc`. -/
theorem LevelExpr.levelMax_imax_assoc_arith :
    ∀ (valueA valueB valueC : Nat),
      (if (if valueC = 0 then 0 else LevelExpr.levelMax valueB valueC) = 0 then 0
       else LevelExpr.levelMax valueA
              (if valueC = 0 then 0 else LevelExpr.levelMax valueB valueC))
        = (if valueC = 0 then 0
           else LevelExpr.levelMax (LevelExpr.levelMax valueA valueB) valueC)
  | _, _, 0 => rfl
  | valueA, valueB, cc + 1 => by
      show (if LevelExpr.levelMax valueB (cc + 1) = 0 then 0
            else LevelExpr.levelMax valueA (LevelExpr.levelMax valueB (cc + 1)))
         = LevelExpr.levelMax (LevelExpr.levelMax valueA valueB) (cc + 1)
      rw [if_neg (LevelExpr.levelMax_succ_right_ne_zero valueB cc)]
      exact (LevelExpr.levelMax_assoc valueA valueB (cc + 1)).symm

/-! ## Impredicative `denoteEquiv` congruences advancing the residual

Two sound `denoteEquiv` rules that push a `limax` structurally toward a cofinal-variable
codomain — the first bricks Géran's canonicalization uses to reduce every `imax` to
`imax(predicative, x)` irreducible nodes.  Neither DECIDES the open-impredicative fragment;
they shrink it. -/

/-- **`limax a (lmax b c) ~ lmax (limax a b) (limax a c)`** — `imax` distributes over `lmax`
in the codomain, denotationally.  Per-env reduction to `levelMax_imax_lmax_distrib_arith`. -/
theorem LevelExpr.limax_lmax_distrib_denoteEquiv
    (domainExpr leftCodomain rightCodomain : LevelExpr) :
    LevelExpr.denoteEquiv
      (LevelExpr.limax domainExpr (LevelExpr.lmax leftCodomain rightCodomain))
      (LevelExpr.lmax (LevelExpr.limax domainExpr leftCodomain)
                      (LevelExpr.limax domainExpr rightCodomain)) := by
  intro env
  exact LevelExpr.levelMax_imax_lmax_distrib_arith
          (domainExpr.denote env) (leftCodomain.denote env) (rightCodomain.denote env)

/-- **`limax a (limax b c) ~ limax (lmax a b) c`** — nested `imax` re-associates so the
innermost codomain (the actual zero-test driver) becomes cofinal.  Per-env reduction to
`levelMax_imax_assoc_arith`. -/
theorem LevelExpr.limax_assoc_denoteEquiv
    (domainExpr midExpr innerCodomain : LevelExpr) :
    LevelExpr.denoteEquiv
      (LevelExpr.limax domainExpr (LevelExpr.limax midExpr innerCodomain))
      (LevelExpr.limax (LevelExpr.lmax domainExpr midExpr) innerCodomain) := by
  intro env
  exact LevelExpr.levelMax_imax_assoc_arith
          (domainExpr.denote env) (midExpr.denote env) (innerCodomain.denote env)

/-! ## The unified dispatcher over the decided fragments -/

/-- A `denoteEquiv` pair is in the DECIDED fragment when both operands are predicative
(`limax`-free) OR both are closed (`lvar`-free).  Everything else — a `limax` with free
codomain variables against another expression — is the open-impredicative residual. -/
def LevelExpr.inDecidableFragment (e1 e2 : LevelExpr) : Bool :=
  (e1.isPredicative && e2.isPredicative) || (e1.isClosed && e2.isClosed)

/-- From `inDecidableFragment = true` and a FAILURE of the predicative conjunct, the closed
conjunct must hold.  Structural Bool `cases` on the predicative conjunct: the `true` branch
contradicts the failure, the `false` branch reduces `false || C` to `C`. -/
theorem LevelExpr.closedConjunct_of_fragment (e1 e2 : LevelExpr)
    (hFrag : LevelExpr.inDecidableFragment e1 e2 = true)
    (hNotPred : ¬ ((e1.isPredicative && e2.isPredicative) = true)) :
    (e1.isClosed && e2.isClosed) = true := by
  have hFragOr : ((e1.isPredicative && e2.isPredicative)
      || (e1.isClosed && e2.isClosed)) = true := hFrag
  cases hPredVal : (e1.isPredicative && e2.isPredicative) with
  | true => exact absurd hPredVal hNotPred
  | false =>
      rw [hPredVal] at hFragOr
      exact hFragOr

/-- **★ The unified level-equality decider.**  `Decidable (denoteEquiv e1 e2)` for every pair in
the decided fragment: predicative operands route through `decideDenoteEquiv` (max-plus canonical
form comparison, distinguishing-valuation completeness); otherwise the fragment hypothesis forces
both operands closed, routing through `decidableDenoteEquivClosed` (single zero-env `Nat.decEq`,
covering the impredicative `limax`). -/
def LevelExpr.decideDenoteEquivDispatch (e1 e2 : LevelExpr)
    (hFrag : LevelExpr.inDecidableFragment e1 e2 = true) :
    Decidable (LevelExpr.denoteEquiv e1 e2) :=
  if hPred : (e1.isPredicative && e2.isPredicative) = true then
    LevelExpr.decideDenoteEquiv e1 e2 (bothBoolTrue hPred).1 (bothBoolTrue hPred).2
  else
    LevelExpr.decidableDenoteEquivClosed
      (bothBoolTrue (LevelExpr.closedConjunct_of_fragment e1 e2 hFrag hPred)).1
      (bothBoolTrue (LevelExpr.closedConjunct_of_fragment e1 e2 hFrag hPred)).2

/-- The Boolean verdict of the dispatcher — `true` iff the pair is `denoteEquiv`.  Extracts the
`isTrue`/`isFalse` head so behavioral smokes pin the decision by `rfl`. -/
def LevelExpr.dispatchVerdict (e1 e2 : LevelExpr)
    (hFrag : LevelExpr.inDecidableFragment e1 e2 = true) : Bool :=
  match LevelExpr.decideDenoteEquivDispatch e1 e2 hFrag with
  | isTrue _ => true
  | isFalse _ => false

/-! ## Non-vacuity smokes — the dispatcher decides both verdicts on both fragments

Each is pinned by `rfl`: the whole decision (canonicalization / zero-env comparison) reduces
definitionally, so a fixture whose verdict flipped would fail to compile rather than admit a
false theorem. -/

/-- Predicative EQUAL pair decides `true`: `lmax (lvar 0) (lvar 0) ~ lvar 0` (idempotent dedup
in the max-plus canonical form). -/
theorem LevelExpr.smoke_dispatch_predicativeEqual_true :
    LevelExpr.dispatchVerdict (.lmax (.lvar 0) (.lvar 0)) (.lvar 0) rfl = true := rfl

/-- Predicative DISTINGUISHING pair decides `false`: distinct variables have distinct canonical
forms (they differ at the valuation that separates `lvar 0` from `lvar 1`). -/
theorem LevelExpr.smoke_dispatch_predicativeDistinct_false :
    LevelExpr.dispatchVerdict (.lvar 0) (.lvar 1) rfl = false := rfl

/-- Closed IMPREDICATIVE collapse decides `true`: `limax (lsucc lzero) lzero ~ lzero` (the
Prop-cofinal collapse `Pi (x : Type 1). Prop : Prop`), decided WITHOUT a predicativity gate. -/
theorem LevelExpr.smoke_dispatch_closedImaxCollapse_true :
    LevelExpr.dispatchVerdict (.limax (.lsucc .lzero) .lzero) .lzero rfl = true := rfl

/-- Closed IMPREDICATIVE distinguishing pair decides `false`: `limax (lsucc lzero) (lsucc lzero)`
denotes `1`, not `lzero`'s `0`. -/
theorem LevelExpr.smoke_dispatch_closedImaxDistinct_false :
    LevelExpr.dispatchVerdict (.limax (.lsucc .lzero) (.lsucc .lzero)) .lzero rfl = false := rfl

/-- The imax-over-lmax distribution law, cross-checked semantically by the decider on a closed
instance: `limax 1 (lmax 0 1)` and `lmax (limax 1 0) (limax 1 1)` both denote `1`, so the
dispatcher decides them `denoteEquiv` — an independent witness that
`limax_lmax_distrib_denoteEquiv` is a real equivalence. -/
theorem LevelExpr.smoke_dispatch_distributionInstance_true :
    LevelExpr.dispatchVerdict
      (.limax (.lsucc .lzero) (.lmax .lzero (.lsucc .lzero)))
      (.lmax (.limax (.lsucc .lzero) .lzero) (.limax (.lsucc .lzero) (.lsucc .lzero)))
      rfl = true := rfl

/-! ## The honest fragment ledger + capstone certificate -/

/-- The three fragments of the level algebra, by decidability status. -/
inductive LevelFragment where
  /-- `max`/`succ`/`var`, no `limax`; free variables allowed.  Decided by the max-plus
  canonical form (`decideDenoteEquiv`). -/
  | predicativeOpen : LevelFragment
  /-- With `limax`, but no free variables.  Decided by env-independence + one zero-env
  comparison (`decidableDenoteEquivClosed`). -/
  | closedImpredicative : LevelFragment
  /-- `limax` with free variables in the codomain, so the zero-test is valuation-dependent.
  The RESIDUAL — needs the `2^k` cofinal-variable case-split (Géran Obs. 10). -/
  | openImpredicative : LevelFragment
deriving DecidableEq, Repr

/-- Decidability status of a level fragment. -/
inductive LevelDecisionStatus where
  /-- `denoteEquiv` is decidable on this fragment, zero-axiom, with completeness. -/
  | decided : LevelDecisionStatus
  /-- `denoteEquiv` on this fragment is not decided this round — precisely named, walled. -/
  | residual : LevelDecisionStatus
deriving DecidableEq, Repr

/-- **The honest per-fragment ledger.**  Two fragments decided, the open-impredicative one is
the residual.  A three-state honesty map, not a single overclaiming boolean. -/
def levelFragmentDecision : LevelFragment → LevelDecisionStatus
  | .predicativeOpen => .decided
  | .closedImpredicative => .decided
  | .openImpredicative => .residual

/-- **BACKED rung marker.**  The max/succ/var (open) + max/imax/succ (closed) level algebra is
genuinely decided — soundness + distinguishing-valuation completeness + a `Decidable` instance,
zero-axiom and non-vacuous (see `levelDecision_certificate` + the dispatcher smokes). -/
def fxLevel_hasDecidableLevelAlgebraOnDecidedFragments : Bool := true

/-- **HONEST residual marker.**  The FULL algebra is NOT decided: `limax x y` with free
variables in the codomain `y` makes the zero-test `denote y env = 0?` valuation-dependent, and
neither shipped decider covers it.  Closing it needs the `2^k` cofinal-variable case-split of
Géran (CSL 2026, Obs. 10) atop the imax-distribution / imax-assoc congruences shipped here —
a separate arc, walled here rather than asserted. -/
def fxLevel_hasFullDecidableLevelAlgebra : Bool := false

/-- **★ The WP-LEVEL certificate.**  Bundles the contentful facts behind the ledger:

* soundness — `simplify` preserves the denotation-equivalence class;
* predicative completeness+decision — semantic equality ↔ equal fully-canonicalized max-plus
  form (the distinguishing-valuation argument, `denoteEquiv_iff_fullCanonicalize_eq`);
* closed-impredicative completeness+decision — semantic equality ↔ a single zero-env
  comparison (`denoteEquiv_closed_iff`, covering `limax`);
* the three-state honesty ledger (two decided, open-impredicative residual);
* the two backed/honest rung markers.

Every conjunct is a real theorem or a definitional `rfl` — nothing vacuous. -/
theorem levelDecision_certificate :
    (∀ (expr : LevelExpr), LevelExpr.denoteEquiv expr.simplify expr)
    ∧ (∀ (e1 e2 : LevelExpr),
        LevelExpr.isPredicative e1 = true → LevelExpr.isPredicative e2 = true →
        (LevelExpr.denoteEquiv e1 e2 ↔
          LevelExpr.MaxPlusForm.fullCanonicalize (LevelExpr.toMaxPlusForm e1) =
            LevelExpr.MaxPlusForm.fullCanonicalize (LevelExpr.toMaxPlusForm e2)))
    ∧ (∀ (e1 e2 : LevelExpr),
        LevelExpr.isClosed e1 = true → LevelExpr.isClosed e2 = true →
        (LevelExpr.denoteEquiv e1 e2 ↔
          e1.denote (fun _ => 0) = e2.denote (fun _ => 0)))
    ∧ levelFragmentDecision LevelFragment.predicativeOpen = LevelDecisionStatus.decided
    ∧ levelFragmentDecision LevelFragment.closedImpredicative = LevelDecisionStatus.decided
    ∧ levelFragmentDecision LevelFragment.openImpredicative = LevelDecisionStatus.residual
    ∧ fxLevel_hasDecidableLevelAlgebraOnDecidedFragments = true
    ∧ fxLevel_hasFullDecidableLevelAlgebra = false :=
  ⟨LevelExpr.simplify_denoteEquiv,
   fun e1 e2 hPred1 hPred2 => LevelExpr.denoteEquiv_iff_fullCanonicalize_eq e1 e2 hPred1 hPred2,
   fun _ _ hClosed1 hClosed2 => LevelExpr.denoteEquiv_closed_iff hClosed1 hClosed2,
   rfl, rfl, rfl, rfl, rfl⟩

end FX1Poly.Universe
