CAVALLO, HÖFER

**Theorem 5.6** ITT + CUA$_{\mathcal{U}}^{\bullet}$ $\not\vdash$ FE$_{\mathcal{U}}$.

**Proof.** Take $\mathbb{C}$ to be a model of ITT + FE + UA$_{\mathcal{U}}$ with extensive finite coproducts of types, as provided by Proposition 5.4. The combination FE + UA$_{\mathcal{U}}$ implies CUA$_{\mathcal{U}}^{\bullet}$, as FE tells us that $(A =_{I \to \mathcal{U}} B) \simeq (A \sim B)$. Thus **Poly**($\mathbb{C}$) $\models$ ITT + CUA$_{\mathcal{U}}^{\bullet}$ by Theorem 4.17, while **Poly**($\mathbb{C}$) $\not\vdash$ FE$_{\mathcal{U}}$ by Proposition 5.3. $\square$

## 6 Variations

Once UA$_{\mathcal{U}}$ was proposed by Voevodsky, it was quickly taken up as the canonical axiom for its intended purpose. Inequivalent variations on UA$_{\mathcal{U}}$ usually turn out to be significantly weaker, as in case of the “isomorphism reflection” that holds in Bauer and Winterhalter’s cardinal model [51, §8.3], or else inconsistent, as in the case of “qinv-univalence” [44, Exercise 4.6].

Unfortunately, we do not see evidence for a canonical form of “FE-free univalence”. In this section, we show that a few possible candidates are inequivalent; none stands out as the most natural. In Section 6.1, we show that CUA$_{\mathcal{U}}$ does not imply CUA$_{\mathcal{U}}^{\bullet}$. In Section 6.2, we identify an axiom CCUA$_{\mathcal{U}}$ that also satisfies ITT + CCUA$_{\mathcal{U}}$ $\not\vdash$ FE$_{\mathcal{U}}$ and ITT + CCUA$_{\mathcal{U}}$ + FE$_{\mathcal{U}}$ $\vdash$ UA$_{\mathcal{U}}$ but is not equivalent to CUA$_{\mathcal{U}}$ or CUA$_{\mathcal{U}}^{\bullet}$.

In Section 6.3, we recall a variant of univalence used by Van den Berg [46, Definition 2.13] which we call *approximate univalence* or UA$_{\mathcal{U}}^{\sim}$. It is an open question whether UA$_{\mathcal{U}}^{\sim}$ implies FE$_{\mathcal{U}}$; we do not resolve the question, but we pose a related question that avoids mention of a universe.

### 6.1 Non-familial categorical univalence

Our Theorem 5.6 is a priori more than an answer to Dorais’ question of whether ITT + CUA$_{\mathcal{U}}$ proves FE$_{\mathcal{U}}$: we prove not only that ITT + CUA$_{\mathcal{U}}$ $\not\vdash$ FE$_{\mathcal{U}}$ but that ITT + CUA$_{\mathcal{U}}^{\bullet}$ $\not\vdash$ FE$_{\mathcal{U}}$. One may then wonder if CUA$_{\mathcal{U}}^{\bullet}$ is strictly stronger than CUA$_{\mathcal{U}}$. This is indeed the case.

**Theorem 6.1** ITT + CUA$_{\mathcal{U}}$ $\not\vdash$ CUA$_{\mathcal{U}}^{\bullet}$.

**Proof.** Take $\mathbb{C}$ to be a model of ITT + FE + UA$_{\mathcal{U}}$ with extensive finite coproducts of types, as provided by Proposition 5.4. Then **Poly**($\mathbb{C}$) $\models$ CUA$_{\mathcal{U}}^{\bullet}$ by Theorem 4.17, and in particular **Poly**($\mathbb{C}$) $\models$ CUA$_{\mathcal{U}}$. We now consider the slice model **Poly**($\mathbb{C}$)/$\top\langle 1\rangle$ for $\top\langle -\rangle$ from Definition 5.1. That is, we work in the context $t$: $\top\langle 1\rangle$. However, we modify the interpretation of the universe $\mathcal{U}$.

Define $(\mathcal{U}', \mathsf{E}\ell')$ by $\mathcal{U}' := \mathcal{U} \times \top\langle 1\rangle \in \mathrm{Ty}_{\mathbf{Poly}(\mathbb{C})}(1)$ with $\mathsf{E}\ell'\langle A, t\rangle := A \in \mathrm{Ty}_{\mathbf{Poly}(\mathbb{C})}(\mathcal{U}')$. In the slice model, $\top\langle 1\rangle$ is contractible by Lemma 4.16, so this universe is closed under the same type formers as $\mathcal{U}$ and the projection $\pi: \mathcal{U}' \to \mathcal{U}$ is an equivalence. For $A, B: \mathcal{U}'$ in the slice model, the interpretation of id-to-ceq for $\mathcal{U}'$ is homotopic (by path induction) to the composite of $\mathsf{ap}_{\pi}$: $(A =_{\mathcal{U}'} B) \to (\pi A =_{\mathcal{U}} \pi B)$ followed by id-to-ceq: $(\pi A =_{\mathcal{U}} \pi B) \to (\pi A \cong \pi B)$. Since $\mathsf{ap}_{\pi}$ is an equivalence, CUA$_{\mathcal{U}'}$ holds in the slice model.

To see that CUA$_{\mathcal{U}'}^{\bullet}$ fails in the slice model, take $I := \top\langle 1 + 1\rangle$ and recall from Proposition 5.2 that there exist distinct $f_0 \neq f_1$: $I \to \top\langle 1\rangle$. For $k \in \{0, 1\}$, set $A_k := (\lambda i. \langle 1, f_k(i) \rangle) \in (\mathcal{U}')^I$. Then $A_0 \cong_{(\mathcal{U}')^I} A_1$ is by definition $1 \cong_{(\mathcal{U})^I} 1$ and thus inhabited, while $A_0 =_{(\mathcal{U}')^I} A_1$ would imply $f_0 = f_1$ and is thus empty. $\square$

### 6.2 Categorical categorical univalence

In our formulation of CUA$_{\mathcal{U}}$, we could have required that id-to-ceq be a *categorical* equivalence.

**Definition 6.2** *Categorical categorical univalence* (CCUA$_{\mathcal{U}}$) is the principle that the canonical map id-to-ceq: $(A =_{\mathcal{U}} B) \to (A \cong B)$ is a categorical equivalence for all $A, B: \mathcal{U}$.

A point in favor of CCUA$_{\mathcal{U}}$ is that it is a proposition (cf. Corollary 2.7); the structure of “being an equivalence” need not be a proposition without FE (cf. implication (iii) $\implies$ (viii) of Theorem 2.13). However, it is unusually strong relative to other identity type characterizations. For example, the equivalence $(\langle a, b \rangle =_{A \times B} \langle a', b' \rangle) \simeq (a =_A a') \times (b =_B b')$ characterizing identities in $\Sigma$ types cannot be shown to be a categorical equivalence in ITT. CCUA$_{\mathcal{U}}$ also seems brittle. Note that the “canonical” map id-to-ceq: $A =_{\mathcal{U}} B \to A \cong B$ is only canonically defined *up to homotopy* by the requirement id-to-ceq(refl$_A$) = id! It is not clear to us that different formulations of CCUA$_{\mathcal{U}}$ using homotopic definitions of id-to-ceq are interderivable.

14