CAVALLO, HÖFER

**Definition 6.13** *Approximate equivalence improvement* ($\mathsf{EI}^{\sim}$) is the principle that for all types $A, B$ and $e: A \simeq B$, we have some $e': A \cong B$ such that $\mathsf{ceq\text{-}to\text{-}eq}(e') \sim e$.

One FE-like corollary of $\mathsf{EI}^{\sim}$ is that if $P$ is a contractible type, then $A \to P$ is also contractible for every type $A$: by Lemma 2.5, we have $(A \to P) \simeq (A \to 1) \cong 1$. This is not provable in ITT, as Lemma 4.16 and Proposition 5.2 show. However, the exact relationship between $\mathsf{EI}^{\sim}$ and FE is a mystery to us:

**Question 6.14** *Does $\mathsf{ITT} + \mathsf{EI}^{\sim} \vdash \mathsf{FE}$?*

An answer to Question 6.14 might not tell us whether $\mathsf{ITT} + \mathsf{UA}_{\mathcal{U}}^{\sim} \vdash \mathsf{FE}_{\mathcal{U}}$, but it may be a more tractable question. The polynomial models refute $\mathsf{EI}^{\sim}$: $\top\langle 1\rangle$ and $\top\langle 1 + 1\rangle$ are equivalent (Remark 4.13) but not categorically equivalent (Lemma 4.14). Boulier, Pédrot, and Tabareau's *intensional function translation* [10, §3] sends a theory with FE to a syntactic model with $\mathsf{EI}^{\sim} \wedge \neg \mathsf{FE}$, but its function types do not satisfy any $\eta$ rule, so this does not answer the question for ITT as we define it. Shulman [38] has a recipe for expressing universal properties without FE that suggests stronger forms of $\mathsf{EI}^{\sim}$; for example, one can also ask that homotopic categorical equivalences are equal. It is not clear to us how these strengthenings relate to $\mathsf{EI}^{\sim}$ or to FE.

**Remark 6.15** Naturally, we can also consider *approximate categorical univalence* $\mathsf{CUA}_{\mathcal{U}}^{\sim}$: the principle that for all $A, B: \mathcal{U}$ and $e: A \cong B$, we have some $p: A =_{\mathcal{U}} B$ such that $\mathsf{id\text{-}to\text{-}ceq}(p) \sim e$. This is the weakest of all the univalence principles we have considered, but we do not know if it is strictly weaker than $\mathsf{CUA}_{\mathcal{U}}$.

## 7 Related work

To conclude, we comment on the status of weak forms of univalence in other known models of type theory without function extensionality.

### 7.1 Realizability models

Realizability is a standard source of models of ITT that refute extensionality principles, including FE; see Streicher [42, Theorem 2.9, §3.7]. However, most work combining features of realizability and homotopical semantics, such as that of Frumin and Van den Berg [20] and Uemura [45], constructs models that *do* satisfy FE. An exception is Speight's *groupoidal realizability* [41]; his function types have neither FE nor the $\eta$ rule. Speight constructs an impredicative universe of modest fibrations, but we do not know if this or any other universe in the model satisfies some kind of univalence.

### 7.2 Pédrot and Tabareau's parametric exceptional translation

The *parametric exceptional translation* [35] is another source of models of type theory without FE. Presented as a syntactic translation, it induces a construction $\mathbf{ParEx}(-)$ on models. Unlike $\mathbf{Poly}(-)$, however, $\mathbf{ParEx}(-)$ does not preserve any form of univalence that we know of. We sketch here a reason for the simplest form of the translation ($\mathbb{E} = 1$ and $\Omega_i(\star) = 1$). Kovács [31] has formalized this case in Agda.

Given a model $\mathbb{C}$, the category of contexts in $\mathbf{ParEx}(\mathbb{C})$ is $\int_{\Gamma \in \mathbb{C}} \mathbf{Ty}(\Gamma)$: objects are pairs $\Gamma = (\Gamma_S, \Gamma_P)$ as in $\mathbf{Poly}(\mathbb{C})$, but a morphism $\sigma: \Delta \to \Gamma$ is a pair of $\sigma_S: \Delta_S \to \Gamma_S$ in $\mathbb{C}$ and $\sigma_P: \Delta_P \to \Gamma_P \sigma_S$ in $\mathbf{Ty}(\Delta_S)$. We think of $\Gamma_P$ as selecting "valid" elements of $\Gamma_S$. Types $A \in \mathrm{Ty}(\Gamma)$ have components $A_S \in \mathrm{Ty}(\Gamma_S)$, $A_P \in \mathrm{Ty}(\Gamma_S, \Gamma_P, A_S)$, and $A_E \in \mathrm{Tm}(\Gamma, A_S)$. Again we think of $A_P$ as selecting valid elements of $A_S$, while $A_E$ is a distinguished "error" element. While intuitively $A_E$ should not be valid, this is not enforced.

The mismatch between $A \cong B$ and $A =_{\mathcal{U}} B$ is that for the former, categorical equivalences of the $-_S$ and $-_P$ components suffice, while the latter requires also that $A_E$ corresponds to $B_E$. For example, define $X^0, X^1 \in \mathrm{Ty}(1)$ by $X_S^k := 1 + 1$, $X_P^k(b) := 1$, and $X_E^k = \mathsf{in}_k(\star)$. The identity equivalence on $1 + 1$ defines a strict isomorphism $X^0 \cong X^1$ that cannot induce a path $X^0 =_{\mathcal{U}} X^1$ because it does not send $X_E^0$ to $X_E^1$.

### 7.3 Bordg's projective model

Bordg [8,9] describes a model of type theory with $\Sigma$ types, $\Pi$ types, identity types, and a universe $\mathcal{U}$ in the category $[\mathbf{BC}_2, \mathbf{Gpd}]$ of groupoid-valued presheaves on the two-element group. This model is based

17