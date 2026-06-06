import FX1Poly.Modal.GradedSubstitutionAlgebra
import FX1Poly.Modal.SimpleStrongNormalization

/-! # FX1Poly/Modal/GradedReductionSubstitution — reduction is substitutive

The Tait abstraction lemma transports the hypothesis "every reducible instantiation of
the body is reducible" across a body reduction — which needs `GradedLambda.Reduces.substAt`: a single
β-step is preserved under the kernel single substitution.  It also needs SN-reflection
(`IsStronglyNormalizing.ofSubstAt`) to get `SN(body)` from `SN(body[var 0 / 0])`.

This file proves both, bridging the kernel `shift`/`substAt` (the focused-object `UsageDiscipline`
operations) to the σ-algebra of `GradedSubstitutionAlgebra`:

  * `shiftRenaming` + `shift_eq_renameTerm` / `shift_zero_eq_renameTerm` — the kernel `shift cut` IS
    `renameTerm (shiftRenaming cut)` (and `shift 0` is `renameTerm incrementIndex`).
  * `singleSubstitution` + `substAt_eq_applySubstitution` — the kernel `substAt cut replacement` IS
    `applySubstitution (singleSubstitution cut replacement)`.
  * `consSubstitution` + `substAt_zero_applySubstitution_lift` — **the β-composition (★)**:
    `substAt 0 argument (applySubstitution (liftSubstitution σ) body) = applySubstitution
    (consSubstitution argument σ) body`, the bridge from the kernel β-reduct to the σ-algebra's
    environment extension.
  * `GradedLambda.Reduces.applySubstitution` — reduction is preserved under ANY parallel substitution
    (β-case is exactly (★)); then `GradedLambda.Reduces.substAt` is a one-line corollary via the
    substAt bridge.  This routing — going through the σ-algebra rather than a direct de Bruijn
    substitution-swap — is what keeps the proof short: the σ-algebra's `lift` composition handles the
    binder bookkeeping once.
  * `GradedLambda.IsStronglyNormalizing.ofSubstAt` — SN of a single substitution reflects to SN of
    the term (any term reduction lifts to a substitution reduction).

## Zero-axiom verification

Funext-free; `ite` reduced via `rw [if_pos]`/`rw [if_neg]` (NOT `simp only`, which pulls propext
through the `ite` congruence); Nat order via explicit lemmas (`Nat.succ_lt_succ`,
`Nat.lt_of_succ_lt_succ`, `Nat.le_of_not_lt`, `Nat.lt_of_le_of_ne`, `Nat.succ_sub_one`,
`Nat.not_lt_zero`, `Nat.noConfusion`) — NEVER `omega` or `Nat.sub_add_cancel` (which leaks propext;
the `k - 1 + 1 = k` step instead `cases` the positive index and uses `Nat.succ_sub_one`).  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditModal.lean`.
-/

namespace FX1Poly.Modal

/-- The renaming that the kernel `shift cut` realizes: bump indices `≥ cut`. -/
def shiftRenaming (cut : Nat) : IndexRenaming :=
  fun index => if index < cut then index else index + 1

/-- **shift bridge**: the kernel `shift cut` is `renameTerm (shiftRenaming cut)`. -/
theorem shift_eq_renameTerm (term : GradedLambda) :
    ∀ (cut : Nat), GradedLambda.shift cut term = GradedLambda.renameTerm (shiftRenaming cut) term := by
  induction term with
  | var index =>
      intro cut
      show (if index < cut then GradedLambda.var index else GradedLambda.var (index + 1))
        = GradedLambda.var (if index < cut then index else index + 1)
      by_cases hlt : index < cut
      · rw [if_pos hlt, if_pos hlt]
      · rw [if_neg hlt, if_neg hlt]
  | lam body bodyIH =>
      intro cut
      show GradedLambda.lam (GradedLambda.shift (cut + 1) body)
        = GradedLambda.lam (GradedLambda.renameTerm (liftRenaming (shiftRenaming cut)) body)
      rw [bodyIH (cut + 1)]
      apply congrArg GradedLambda.lam
      apply GradedLambda.renameTerm_congr
      intro index
      cases index with
      | zero => rfl
      | succ k =>
          show (if k + 1 < cut + 1 then k + 1 else k + 1 + 1)
            = (if k < cut then k else k + 1) + 1
          by_cases hlt : k < cut
          · rw [if_pos (Nat.succ_lt_succ hlt), if_pos hlt]
          · rw [if_neg (fun hc => hlt (Nat.lt_of_succ_lt_succ hc)), if_neg hlt]
  | app function argument functionIH argumentIH =>
      intro cut
      show GradedLambda.app _ _ = GradedLambda.app _ _
      rw [functionIH cut, argumentIH cut]

/-- **shift bridge at 0**: `shift 0` is `renameTerm incrementIndex`. -/
theorem shift_zero_eq_renameTerm (term : GradedLambda) :
    GradedLambda.shift 0 term = GradedLambda.renameTerm incrementIndex term := by
  rw [shift_eq_renameTerm term 0]
  apply GradedLambda.renameTerm_congr
  intro index
  show (if index < 0 then index else index + 1) = index + 1
  rw [if_neg (Nat.not_lt_zero index)]

/-- The parallel substitution realizing the kernel `substAt cut replacement`: replace `cut`, decrement
above it, identity below. -/
def singleSubstitution (cut : Nat) (replacement : GradedLambda) : TermSubstitution :=
  fun index =>
    if index < cut then GradedLambda.var index
    else if index = cut then replacement else GradedLambda.var (index - 1)

/-- **substAt bridge**: the kernel `substAt cut replacement` is `applySubstitution (singleSubstitution
cut replacement)`. -/
theorem substAt_eq_applySubstitution (term : GradedLambda) :
    ∀ (cut : Nat) (replacement : GradedLambda),
      GradedLambda.substAt cut replacement term
        = GradedLambda.applySubstitution (singleSubstitution cut replacement) term := by
  induction term with
  | var index => intro _ _; rfl
  | lam body bodyIH =>
      intro cut replacement
      show GradedLambda.lam (GradedLambda.substAt (cut + 1) (GradedLambda.shift 0 replacement) body)
        = GradedLambda.lam (GradedLambda.applySubstitution
            (liftSubstitution (singleSubstitution cut replacement)) body)
      rw [bodyIH (cut + 1) (GradedLambda.shift 0 replacement)]
      apply congrArg GradedLambda.lam
      apply GradedLambda.applySubstitution_congr
      intro index
      cases index with
      | zero => rfl
      | succ k =>
          show (if k + 1 < cut + 1 then GradedLambda.var (k + 1)
              else if k + 1 = cut + 1 then GradedLambda.shift 0 replacement else GradedLambda.var (k + 1 - 1))
            = GradedLambda.renameTerm incrementIndex
              (if k < cut then GradedLambda.var k else if k = cut then replacement else GradedLambda.var (k - 1))
          by_cases hlt : k < cut
          · rw [if_pos (Nat.succ_lt_succ hlt), if_pos hlt]; rfl
          · by_cases heq : k = cut
            · rw [if_neg (fun hc => hlt (Nat.lt_of_succ_lt_succ hc)), if_pos (by rw [heq]),
                if_neg hlt, if_pos heq]
              exact shift_zero_eq_renameTerm replacement
            · rw [if_neg (fun hc => hlt (Nat.lt_of_succ_lt_succ hc)),
                if_neg (fun hc => heq (Nat.succ.inj hc)), if_neg hlt, if_neg heq]
              have cutltk : cut < k :=
                Nat.lt_of_le_of_ne (Nat.le_of_not_lt hlt) (fun hcc => heq hcc.symm)
              cases k with
              | zero => exact absurd cutltk (Nat.not_lt_zero cut)
              | succ predecessor =>
                  show GradedLambda.var (predecessor + 1 + 1 - 1)
                    = GradedLambda.var (predecessor + 1 - 1 + 1)
                  rw [Nat.succ_sub_one, Nat.succ_sub_one]
  | app function argument functionIH argumentIH =>
      intro cut replacement
      show GradedLambda.app _ _ = GradedLambda.app _ _
      rw [functionIH cut replacement, argumentIH cut replacement]

/-- Prepend a term to a substitution (the binder-extension of an environment). -/
def consSubstitution (head : GradedLambda) (tail : TermSubstitution) : TermSubstitution :=
  fun index =>
    match index with
    | 0 => head
    | next + 1 => tail next

/-- **The β-composition (★)**: substituting the argument at `0` into a `liftSubstitution`-substituted
body equals substituting under the extended `consSubstitution` environment.  This is the bridge from
the kernel β-reduct `substAt 0 argument body` to the σ-algebra's environment extension. -/
theorem substAt_zero_applySubstitution_lift (body argument : GradedLambda)
    (substitution : TermSubstitution) :
    GradedLambda.substAt 0 argument (GradedLambda.applySubstitution (liftSubstitution substitution) body)
      = GradedLambda.applySubstitution (consSubstitution argument substitution) body := by
  rw [substAt_eq_applySubstitution
        (GradedLambda.applySubstitution (liftSubstitution substitution) body) 0 argument,
    GradedLambda.applySubstitution_applySubstitution]
  apply GradedLambda.applySubstitution_congr
  intro index
  cases index with
  | zero => rfl
  | succ k =>
      show GradedLambda.applySubstitution (singleSubstitution 0 argument)
          (GradedLambda.renameTerm incrementIndex (substitution k)) = substitution k
      rw [GradedLambda.applySubstitution_renameTerm]
      have congrPointwise : GradedLambda.applySubstitution
            (fun j => singleSubstitution 0 argument (incrementIndex j)) (substitution k)
          = GradedLambda.applySubstitution (fun j => GradedLambda.var j) (substitution k) := by
        apply GradedLambda.applySubstitution_congr
        intro j
        show (if j + 1 < 0 then GradedLambda.var (j + 1)
            else if j + 1 = 0 then argument else GradedLambda.var (j + 1 - 1)) = GradedLambda.var j
        rw [if_neg (Nat.not_lt_zero (j + 1)), if_neg (fun hc => Nat.noConfusion hc), Nat.succ_sub_one]
      rw [congrPointwise, GradedLambda.applySubstitution_id]

/-- **Reduction is preserved under any parallel substitution** (the β-case is exactly the
composition (★)). -/
theorem GradedLambda.Reduces.applySubstitution {source reduct : GradedLambda}
    (step : GradedLambda.Reduces source reduct) :
    ∀ (substitution : TermSubstitution),
      GradedLambda.Reduces (GradedLambda.applySubstitution substitution source)
        (GradedLambda.applySubstitution substitution reduct) := by
  induction step with
  | beta body argument =>
      intro substitution
      show GradedLambda.Reduces
        (GradedLambda.app (GradedLambda.lam (GradedLambda.applySubstitution (liftSubstitution substitution) body))
          (GradedLambda.applySubstitution substitution argument))
        (GradedLambda.applySubstitution substitution (GradedLambda.substAt 0 argument body))
      rw [substAt_eq_applySubstitution body 0 argument, GradedLambda.applySubstitution_applySubstitution]
      have rhseq : GradedLambda.applySubstitution
            (fun index => GradedLambda.applySubstitution substitution (singleSubstitution 0 argument index)) body
          = GradedLambda.applySubstitution
            (consSubstitution (GradedLambda.applySubstitution substitution argument) substitution) body := by
        apply GradedLambda.applySubstitution_congr
        intro index
        cases index with
        | zero => rfl
        | succ _ => rfl
      rw [rhseq,
        ← substAt_zero_applySubstitution_lift body (GradedLambda.applySubstitution substitution argument) substitution]
      exact GradedLambda.Reduces.beta
        (GradedLambda.applySubstitution (liftSubstitution substitution) body)
        (GradedLambda.applySubstitution substitution argument)
  | congLam body body' _ bodyIH =>
      intro substitution
      exact GradedLambda.Reduces.congLam _ _ (bodyIH (liftSubstitution substitution))
  | congAppLeft function function' argument _ functionIH =>
      intro substitution
      exact GradedLambda.Reduces.congAppLeft _ _ _ (functionIH substitution)
  | congAppRight function argument argument' _ argumentIH =>
      intro substitution
      exact GradedLambda.Reduces.congAppRight _ _ _ (argumentIH substitution)

/-- **Reduction is preserved under the kernel single substitution** (the abstraction-lemma transport
engine; a corollary of `Reduces.applySubstitution` via the substAt bridge). -/
theorem GradedLambda.Reduces.substAt {source reduct : GradedLambda}
    (step : GradedLambda.Reduces source reduct) (cut : Nat) (replacement : GradedLambda) :
    GradedLambda.Reduces (GradedLambda.substAt cut replacement source)
      (GradedLambda.substAt cut replacement reduct) := by
  rw [substAt_eq_applySubstitution source cut replacement,
    substAt_eq_applySubstitution reduct cut replacement]
  exact step.applySubstitution (singleSubstitution cut replacement)

/-- **SN reflection**: if a single substitution of a term is strongly normalizing, so is the term
itself (any reduction of the term lifts to a reduction of the substitution). -/
theorem GradedLambda.IsStronglyNormalizing.ofSubstAt {term : GradedLambda} (cut : Nat)
    (replacement : GradedLambda)
    (sn : GradedLambda.IsStronglyNormalizing (GradedLambda.substAt cut replacement term)) :
    GradedLambda.IsStronglyNormalizing term := by
  have generalized : ∀ (substituted : GradedLambda), GradedLambda.IsStronglyNormalizing substituted →
      ∀ (original : GradedLambda), substituted = GradedLambda.substAt cut replacement original →
        GradedLambda.IsStronglyNormalizing original := by
    intro substituted snSubstituted
    induction snSubstituted with
    | intro substituted _ reductIH =>
        intro original subEq
        apply Acc.intro
        intro reduct stepReduct
        refine reductIH (GradedLambda.substAt cut replacement reduct) ?stepSub reduct rfl
        rw [subEq]
        exact stepReduct.substAt cut replacement
  exact generalized (GradedLambda.substAt cut replacement term) sn term rfl

end FX1Poly.Modal
