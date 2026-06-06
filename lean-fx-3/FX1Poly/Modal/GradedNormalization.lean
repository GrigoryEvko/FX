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

**Decidable conversion (CONF stage 3b-ii) completes the substrate:**

  * `IsStronglyNormalizing.ofReducesStar` — SN preserved along multi-step reduction.
  * `normalize_of_isNormalForm` — normalizing a normal form returns it unchanged.
  * `joinable_iff_normalize_eq` — **conversion = normal-form equality**: two SN terms are β-convertible
    (join at a common reduct) iff their normal forms coincide.
  * `decidableJoinable` + `HasSimpleType.decidableConv` + `HasUsage.decidableConv` — **decidable
    β-conversion**: any two well-typed terms have decidable convertibility (it reduces to `DecidableEq`
    on their normal forms).
  * `var_notJoinable_of_ne` — non-vacuity: the decider genuinely distinguishes (distinct variables are
    not convertible).

With this the GradedLambda STLC substrate is a **full reference calculus**: SN + graded SR + confluence
+ unique normal forms + a verified normalizer + decidable definitional equality, all zero-axiom.

## Zero-axiom verification

The NF-closure lemmas are `cases` on `Reduces` (propext-clean — `GradedLambda` plain inductive);
`stepOrNormal` is structural recursion with the application head matched in the definition's pattern
(5 arms, no wildcards) so each arm's constructor appears concretely; `normalizeWithProof` is `Acc.rec`
with a motive constant in the accessibility proof.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/AuditModal.lean`.
-/

namespace FX1Poly.Modal

open FX1Poly.Core (ReflTransClosure Joinable)

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

/-- Strong normalization is preserved along a multi-step reduction (iterated forward closure of
`IsStronglyNormalizing.ofReduces`). -/
theorem GradedLambda.IsStronglyNormalizing.ofReducesStar {term reduct : GradedLambda}
    (star : GradedLambda.ReducesStar term reduct) :
    GradedLambda.IsStronglyNormalizing term → GradedLambda.IsStronglyNormalizing reduct := by
  induction star with
  | refl => exact fun sn => sn
  | head firstStep _ ih => exact fun sn => ih (sn.ofReduces firstStep)

/-- Normalizing a normal form returns it unchanged (a normal form only refl-reduces). -/
theorem GradedLambda.normalize_of_isNormalForm {term : GradedLambda}
    (sn : GradedLambda.IsStronglyNormalizing term) (nf : GradedLambda.IsNormalForm term) :
    GradedLambda.normalize term sn = term :=
  (nf.eq_of_reducesStar (GradedLambda.normalize_reducesStar term sn)).symm

/-- **Conversion = normal-form equality**: two strongly-normalizing terms are β-convertible (join at a
common reduct) iff their normal forms coincide.  Forward: confluence joins each term's reduct with its
normal form; a normal form only refl-reduces, so the join point IS the normal form, and uniqueness of
normal forms at the shared reduct equates them.  Backward: both terms reduce to the (common) normal
form. -/
theorem GradedLambda.joinable_iff_normalize_eq {a b : GradedLambda}
    (snA : GradedLambda.IsStronglyNormalizing a) (snB : GradedLambda.IsStronglyNormalizing b) :
    Joinable GradedLambda.Reduces a b ↔
      GradedLambda.normalize a snA = GradedLambda.normalize b snB := by
  constructor
  · rintro ⟨commonReduct, aToCommon, bToCommon⟩
    have aToNfA := GradedLambda.normalize_reducesStar a snA
    have nfA_NF : GradedLambda.IsNormalForm (GradedLambda.normalize a snA) :=
      GradedLambda.normalize_isNormalForm a snA
    have bToNfB := GradedLambda.normalize_reducesStar b snB
    have nfB_NF : GradedLambda.IsNormalForm (GradedLambda.normalize b snB) :=
      GradedLambda.normalize_isNormalForm b snB
    obtain ⟨meetA, commonToMeetA, nfAToMeetA⟩ := snA.confluent aToCommon aToNfA
    obtain ⟨meetB, commonToMeetB, nfBToMeetB⟩ := snB.confluent bToCommon bToNfB
    have commonToNfA : GradedLambda.ReducesStar commonReduct (GradedLambda.normalize a snA) := by
      rw [nfA_NF.eq_of_reducesStar nfAToMeetA]; exact commonToMeetA
    have commonToNfB : GradedLambda.ReducesStar commonReduct (GradedLambda.normalize b snB) := by
      rw [nfB_NF.eq_of_reducesStar nfBToMeetB]; exact commonToMeetB
    exact (snA.ofReducesStar aToCommon).uniqueNormalForm commonToNfA commonToNfB nfA_NF nfB_NF
  · intro normalFormsEqual
    exact ⟨GradedLambda.normalize a snA, GradedLambda.normalize_reducesStar a snA,
      by rw [normalFormsEqual]; exact GradedLambda.normalize_reducesStar b snB⟩

/-- **Decidable β-conversion** for strongly-normalizing terms: convertibility reduces to deciding the
equality of normal forms (`GradedLambda` has `DecidableEq`). -/
def GradedLambda.decidableJoinable {a b : GradedLambda}
    (snA : GradedLambda.IsStronglyNormalizing a) (snB : GradedLambda.IsStronglyNormalizing b) :
    Decidable (Joinable GradedLambda.Reduces a b) :=
  decidable_of_iff _ (GradedLambda.joinable_iff_normalize_eq snA snB).symm

/-- **Decidable β-conversion on the simply-typed fragment**: any two well-typed terms have decidable
convertibility (SN supplied by the Tait fundamental theorem). -/
def HasSimpleType.decidableConv {typeContextA typeContextB : List SimpleType} {a b : GradedLambda}
    {typeA typeB : SimpleType} (typedA : HasSimpleType typeContextA a typeA)
    (typedB : HasSimpleType typeContextB b typeB) :
    Decidable (Joinable GradedLambda.Reduces a b) :=
  GradedLambda.decidableJoinable typedA.stronglyNormalizing typedB.stronglyNormalizing

/-- **Decidable β-conversion on the usage-typed fragment** — inherited through grade erasure, with no
separate decision procedure. -/
def HasUsage.decidableConv {typeContextA typeContextB : List GType} {gradesA gradesB : GradeVector}
    {a b : GradedLambda} {typeA typeB : GType} (typedA : HasUsage typeContextA gradesA a typeA)
    (typedB : HasUsage typeContextB gradesB b typeB) :
    Decidable (Joinable GradedLambda.Reduces a b) :=
  GradedLambda.decidableJoinable typedA.stronglyNormalizing typedB.stronglyNormalizing

/-- Non-vacuity: the decision procedure genuinely DISTINGUISHES — distinct variables are not
β-convertible (each is its own normal form). -/
theorem GradedLambda.var_notJoinable_of_ne {indexA indexB : Nat} (hne : indexA ≠ indexB) :
    ¬ Joinable GradedLambda.Reduces (.var indexA) (.var indexB) := by
  intro joined
  have normalFormsEqual := (GradedLambda.joinable_iff_normalize_eq
    (GradedLambda.IsStronglyNormalizing.var indexA)
    (GradedLambda.IsStronglyNormalizing.var indexB)).mp joined
  rw [GradedLambda.normalize_of_isNormalForm _ (GradedLambda.var_isNormalForm indexA),
    GradedLambda.normalize_of_isNormalForm _ (GradedLambda.var_isNormalForm indexB)] at normalFormsEqual
  exact hne (GradedLambda.var.inj normalFormsEqual)

/-! ## β-conversion is an equivalence relation

The decidable relation `Joinable Reduces` deserves the name "definitional equality" only because it is
a genuine equivalence: reflexive and symmetric unconditionally, transitive whenever the middle term is
strongly normalizing (confluence joins the two reducts it reaches).  It also contains reduction. -/

/-- β-conversion is **reflexive** (every term joins with itself in zero steps). -/
theorem GradedLambda.Reduces.joinable_refl (term : GradedLambda) :
    Joinable GradedLambda.Reduces term term :=
  ⟨term, ReflTransClosure.refl term, ReflTransClosure.refl term⟩

/-- β-conversion is **symmetric** (swap the two reduction chains to the common reduct). -/
theorem GradedLambda.Reduces.joinable_symm {a b : GradedLambda}
    (conv : Joinable GradedLambda.Reduces a b) : Joinable GradedLambda.Reduces b a := by
  obtain ⟨commonReduct, aToCommon, bToCommon⟩ := conv
  exact ⟨commonReduct, bToCommon, aToCommon⟩

/-- **Reduction implies conversion**: a multi-step reduct is convertible with its source. -/
theorem GradedLambda.ReducesStar.joinable {a b : GradedLambda}
    (star : GradedLambda.ReducesStar a b) : Joinable GradedLambda.Reduces a b :=
  ⟨b, star, ReflTransClosure.refl b⟩

/-- β-conversion is **transitive** whenever the middle term is strongly normalizing: confluence joins
the two reducts the middle reaches, and the outer chains compose.  Only the middle term needs SN. -/
theorem GradedLambda.IsStronglyNormalizing.joinable_trans {a b c : GradedLambda}
    (snB : GradedLambda.IsStronglyNormalizing b)
    (convAB : Joinable GradedLambda.Reduces a b) (convBC : Joinable GradedLambda.Reduces b c) :
    Joinable GradedLambda.Reduces a c := by
  obtain ⟨leftReduct, aToLeft, bToLeft⟩ := convAB
  obtain ⟨rightReduct, bToRight, cToRight⟩ := convBC
  obtain ⟨meet, leftToMeet, rightToMeet⟩ := snB.confluent bToLeft bToRight
  exact ⟨meet, aToLeft.trans leftToMeet, cToRight.trans rightToMeet⟩

/-- **A β-redex is convertible with its contractum** — conversion contains β (a concrete witness that
the conversion relation is non-trivial). -/
theorem GradedLambda.Reduces.beta_joinable (body argument : GradedLambda) :
    Joinable GradedLambda.Reduces (.app (.lam body) argument)
      (GradedLambda.substAt 0 argument body) :=
  GradedLambda.ReducesStar.joinable (ReflTransClosure.single (GradedLambda.Reduces.beta body argument))

/-- **Transitivity on the simply-typed fragment**: the middle term's typing supplies SN, so conversion
is a genuine equivalence on well-typed terms. -/
theorem HasSimpleType.joinable_trans {typeContext : List SimpleType} {a b c : GradedLambda}
    {middleType : SimpleType} (typedMiddle : HasSimpleType typeContext b middleType)
    (convAB : Joinable GradedLambda.Reduces a b) (convBC : Joinable GradedLambda.Reduces b c) :
    Joinable GradedLambda.Reduces a c :=
  typedMiddle.stronglyNormalizing.joinable_trans convAB convBC

/-- **Transitivity on the usage-typed fragment** — the middle term's usage typing supplies SN. -/
theorem HasUsage.joinable_trans {typeContext : List GType} {grades : GradeVector}
    {a b c : GradedLambda} {middleType : GType}
    (typedMiddle : HasUsage typeContext grades b middleType)
    (convAB : Joinable GradedLambda.Reduces a b) (convBC : Joinable GradedLambda.Reduces b c) :
    Joinable GradedLambda.Reduces a c :=
  typedMiddle.stronglyNormalizing.joinable_trans convAB convBC

end FX1Poly.Modal
