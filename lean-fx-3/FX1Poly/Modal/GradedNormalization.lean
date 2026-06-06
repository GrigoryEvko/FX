import FX1Poly.Modal.GradedReductionConfluence

/-! # FX1Poly/Modal/GradedNormalization — the verified β-normalizer for GradedLambda (CONF stage 3b-i)

The decision-procedure layer atop the reduction theory (SN + SR + confluence + unique normal forms).
This installment builds the **normalizer**: a function computing the β-normal form of any strongly-
normalizing `GradedLambda` term, bundled with proofs that the output is reached (`ReducesStar`) and
irreducible (`IsNormalForm`).

  * `lam_isNormalForm` / `var_app_isNormalForm` / `app_app_isNormalForm` — the normal-form closure
    facts (a term with normal components and a non-β head is normal).
  * `stepOrNormal` — **β-progress**: every term either reduces (with an explicit reduct + step witness)
    or is a normal form.  Structural recursion; the application head is examined to fire β.
  * `normalizeWithProof` — by `Acc.rec` on the SN accessibility (motive constant in the proof, so
    propext-free), produce the normal form with proofs it is reached and irreducible.
  * `normalize` + `normalize_reducesStar` + `normalize_isNormalForm` — the normalizer and its two
    correctness projections.

Next installment (CONF stage 3b-ii): decidable `Conv` via `normalize a = normalize b` (the unique-NF
bridge), completing the substrate into a full reference calculus with decidable definitional equality.

## Zero-axiom verification

The NF-closure lemmas are `cases` on `Reduces` (propext-clean — `GradedLambda` plain inductive);
`stepOrNormal` is structural recursion with the application head matched in the definition's pattern
(5 arms, no wildcards) so each arm's constructor appears concretely; `normalizeWithProof` is `Acc.rec`
with a motive constant in the accessibility proof.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/AuditModal.lean`.
-/

namespace FX1Poly.Modal

open FX1Poly.Core (ReflTransClosure)

/-- A lambda whose body is normal is itself normal (its only possible step is `congLam`). -/
theorem GradedLambda.lam_isNormalForm {body : GradedLambda} (bodyNF : GradedLambda.IsNormalForm body) :
    GradedLambda.IsNormalForm (.lam body) := by
  intro reduct step
  cases step with
  | congLam _ _ bodyStep => exact bodyNF bodyStep

/-- A variable applied to a normal argument is normal (not a β-redex; the variable head cannot step). -/
theorem GradedLambda.var_app_isNormalForm (index : Nat) {argument : GradedLambda}
    (argNF : GradedLambda.IsNormalForm argument) :
    GradedLambda.IsNormalForm (.app (.var index) argument) := by
  intro reduct step
  cases step with
  | congAppLeft _ _ _ varStep => cases varStep
  | congAppRight _ _ _ argStep => exact argNF argStep

/-- An application whose function is itself an application (a neutral head) — both parts normal — is
normal (not a β-redex; neither part can step). -/
theorem GradedLambda.app_app_isNormalForm {innerFunction innerArgument argument : GradedLambda}
    (funNF : GradedLambda.IsNormalForm (.app innerFunction innerArgument))
    (argNF : GradedLambda.IsNormalForm argument) :
    GradedLambda.IsNormalForm (.app (.app innerFunction innerArgument) argument) := by
  intro reduct step
  cases step with
  | congAppLeft _ _ _ funStep => exact funNF funStep
  | congAppRight _ _ _ argStep => exact argNF argStep

/-- **β-progress**: every term either reduces (with an explicit reduct + step witness) or is a normal
form.  Structural recursion on the term; the function head of an application is matched in the
definition's own pattern to decide whether a β-redex fires. -/
def GradedLambda.stepOrNormal : (term : GradedLambda) →
    PSum { reduct : GradedLambda // GradedLambda.Reduces term reduct } (GradedLambda.IsNormalForm term)
  | .var index => .inr (GradedLambda.var_isNormalForm index)
  | .lam body =>
      match GradedLambda.stepOrNormal body with
      | .inl ⟨body', step⟩ => .inl ⟨.lam body', GradedLambda.Reduces.congLam body body' step⟩
      | .inr bodyNF => .inr (GradedLambda.lam_isNormalForm bodyNF)
  | .app (.lam body) argument =>
      .inl ⟨GradedLambda.substAt 0 argument body, GradedLambda.Reduces.beta body argument⟩
  | .app (.var index) argument =>
      match GradedLambda.stepOrNormal argument with
      | .inl ⟨argument', step⟩ =>
          .inl ⟨.app (.var index) argument',
            GradedLambda.Reduces.congAppRight (.var index) argument argument' step⟩
      | .inr argNF => .inr (GradedLambda.var_app_isNormalForm index argNF)
  | .app (.app innerFunction innerArgument) argument =>
      match GradedLambda.stepOrNormal (.app innerFunction innerArgument) with
      | .inl ⟨function', step⟩ =>
          .inl ⟨.app function' argument,
            GradedLambda.Reduces.congAppLeft (.app innerFunction innerArgument) function' argument step⟩
      | .inr funNF =>
          match GradedLambda.stepOrNormal argument with
          | .inl ⟨argument', step⟩ =>
              .inl ⟨.app (.app innerFunction innerArgument) argument',
                GradedLambda.Reduces.congAppRight (.app innerFunction innerArgument) argument argument' step⟩
          | .inr argNF => .inr (GradedLambda.app_app_isNormalForm funNF argNF)

/-- The normalizer's core: by well-founded recursion on the SN accessibility, produce the normal form
together with proofs it is reached and irreducible.  `Acc.rec` with a motive constant in the
accessibility proof keeps this propext-free. -/
def GradedLambda.normalizeWithProof (term : GradedLambda)
    (sn : GradedLambda.IsStronglyNormalizing term) :
    { result : GradedLambda //
      GradedLambda.ReducesStar term result ∧ GradedLambda.IsNormalForm result } :=
  Acc.rec (motive := fun candidate _ =>
      { result : GradedLambda //
        GradedLambda.ReducesStar candidate result ∧ GradedLambda.IsNormalForm result })
    (fun candidate _ ih =>
      match GradedLambda.stepOrNormal candidate with
      | .inl ⟨reduct, step⟩ =>
          let ⟨result, reductStar, resultNF⟩ := ih reduct step
          ⟨result, ReflTransClosure.head step reductStar, resultNF⟩
      | .inr nf => ⟨candidate, ReflTransClosure.refl candidate, nf⟩)
    sn

/-- **The normalizer**: the β-normal form of a strongly-normalizing term. -/
def GradedLambda.normalize (term : GradedLambda) (sn : GradedLambda.IsStronglyNormalizing term) :
    GradedLambda :=
  (GradedLambda.normalizeWithProof term sn).val

/-- The normalizer's output is reached from the input by β-reduction. -/
theorem GradedLambda.normalize_reducesStar (term : GradedLambda)
    (sn : GradedLambda.IsStronglyNormalizing term) :
    GradedLambda.ReducesStar term (GradedLambda.normalize term sn) :=
  (GradedLambda.normalizeWithProof term sn).property.1

/-- The normalizer's output is a normal form (irreducible). -/
theorem GradedLambda.normalize_isNormalForm (term : GradedLambda)
    (sn : GradedLambda.IsStronglyNormalizing term) :
    GradedLambda.IsNormalForm (GradedLambda.normalize term sn) :=
  (GradedLambda.normalizeWithProof term sn).property.2

end FX1Poly.Modal
