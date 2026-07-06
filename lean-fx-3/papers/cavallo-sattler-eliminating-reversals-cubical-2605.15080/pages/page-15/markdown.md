E. Cavallo and C. Sattler

15

▶ Lemma 39. Over the environment (C : Ty, c₀ : C, c₁ : C), the function λp.thicken(p) : Path(C, c₀, c₁) → TPath(⟨i₀, i₁⟩C(i₀), c₀, c₁) is an equivalence.

Proof. Our proof of Proposition 38 uses only constructs on which we have already defined T. Thus we can mechanically derive from it a term of type TisContr(Σd₁:D(1,0).TPath(D,d₀,d₁)) over (D : I × I → Ty, d₀ : D(0,1)). Using Definition 37, we can go from TisContr to isContr. Taking D(i₀,i₁) := C(i₀) and d₀ := c₀ gives isContr(Σc₁:C(1).TPath(⟨i₀,i₁⟩C(i₀),c₀,c₁)). Thus λs.(s.1,thicken(s.2)) : Σc₁:C(1).Path(C,c₀,c₁) → Σc₁:C(1).TPath(⟨i₀,i₁⟩C(i₀),c₀,c₁) is a map between contractible types and therefore an equivalence. It follows [39, Theorem 4.7.7] that it is also a fiberwise equivalence.

We can use Lemma 39 inside the definition of equivalence to construct TGlue.

▶ Component 40 (T, glue). Over (A : Ty, P : Cof, T : [P] → Ty, e : [P] → T ≃_T A), define TGlue(A, P, T, e) := Glue(A, P, T, ê) where ê is derived from e by using Lemma 39 to replace each use of TPath with Path. Set Tglue(a, t) := glue(a, t) and Tunglue(g) := unglue(g).

The interpretation of suspensions is similar, but we use thicken and anti more directly.

▶ Component 41 (T, suspension). Define

|  TSusp(A) | := | Susp(A) | Tmerid(a) | := | thicken(merid(a))  |
| --- | --- | --- | --- | --- | --- |
|  Tnorth | := | north | Telim(C, n, s, m, t) | := | elim(C, n, s, ⟨a⟩anti(m(a)), t)  |
|  Tsouth | := | south |  |  |   |

For Tmeridβ(C, n, s, m, a), we compose cong_thicken(meridβ(C, n, s, ⟨a⟩thicken⁻¹(m(a)), a)) with the path thicken(thicken⁻¹(q)) ∼ q, using that thicken is an equivalence, then thicken the composed path to get a T-path.

This completes the definition of T, as summarized in the following theorem. We record that it preserves the constructs of MLTT_Σ,Id and the cofibration judgments for future use.

▶ Theorem 42. For every self-dual interval theory (Φ, φ), there is a representable map functor T: CTT[ℓRev_φΦ] → CTT[ℓΦ] in the coslice (MLTT_Σ,Id,U + COF)/RMC.

## 5 Spans

Abstracting from the particular case of T, we now develop tools—span RMCs and the span interpretation between suitable RMC functors F, G: CTT[ℓΦ] → CTT[ℓΨ]—that we use in §6 to prove that certain morphisms of models induced by RMC functors are weak equivalences. This construction at the level of RMCs is inspired by and resembles path object constructions at the level of models [22, §5], as well as Tabareau, Tanter, and Sozeau's univalent parametricity translation for the Calculus of Inductive Constructions [35].

### 5.1 The representable map category of spans

We write Span(C) for the category of spans in a category C, i.e., the category of functors from the diagram category {0 ← r → 1} into C. Given X ∈ Span(C), we write d⁰: X_r → X₀ and d¹: X_r → X₁ for its two projections.

▶ Proposition 43. If ℝ is an RMC, then Span(ℝ) is an RMC when equipped with the class of levelwise representable maps.