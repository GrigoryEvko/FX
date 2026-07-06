The ∞-category of ∞-categories in simplicial type theory

**Lemma 3.10.** If $X$ is a category, then $\mathrm{Gl}(F_0, F_1, \alpha)$ is cocartesian.

PROOF. In light of Lemma 3.9, everything involved is a (simplicial) category. Accordingly, we may use the LARI condition of [5] to prove this result. Applying the results of [11], we are then further reduced to constructing this adjoint on objects.

Fix $i \cdot \mathbb{I} \to \mathbb{I}$ along with $x \cdot \mathbb{I} \to X$, $f_0^1 \cdot \mathbb{I} \to F_1(x)$ and $f_0^0 \cdot \mathbb{I} \to i(0) = 0 \to \alpha_x^{-1}(f_0^1)$. We begin by constructing a lift of $(f_0^1, f_0^0)$ and then we argue that it is suitably initial.

First, let us note that since $\alpha$ preserves cocartesian edges, if we have $g: F_0(x)$ which lies over $f: F_1(x)$, then $x \cdot g_0$ lies over $x \cdot f_0$ by a contractible choice of path since $\alpha(x \cdot g_0)$ is a cocartesian lift of the same data as $x \cdot f_0$. Consequently, we may construct the desired lifts:

$$f^1 = \lambda j : \mathbb{I}. x(-\wedge j) \cdot (f_0^1) \quad f^0 = \lambda j : \mathbb{I}, z : i(j) = 0. x(-\wedge j) \cdot (f_0^0(\_))$$

Assume now we are given $\alpha: \mathbb{I} \times \mathbb{I} \to \mathbb{I}$ and $\chi: \mathbb{I} \times \mathbb{I} \to X$ such that $i = \alpha(0, -)$ and $\chi(0, -) = x$ (we silently replace $x$ and $i$ by transport along these paths to treat them as reflexivity in what follows). We also assume we are given partial lifts: $g^1: (j: \mathbb{I}) \to F_1(\chi(1, j))$ $g^0: (j: \mathbb{I}) \to \alpha(1, j) = 0 \to \alpha_{\chi(1, j)}^{-1}(g^1(j))$ and $h_0^1: (k: \mathbb{I}) \to F_1(\chi(k, 0))$. $h_0^0: (k: \mathbb{I}) \to \alpha(k, 0) = 0 \to \alpha_{\chi(k, 0)}^{-1}(h_0^1(k))$. We may further assume that all of these are $\mathbb{I}$-annotated and that there are paths $q: (g^1(0), g^0(0)) = (h_0^1(1), h_0^0(1))$ and $p: (f^1(0), f^0(0)) = (h_0^1(0), h_0^0(0))$

We wish to show that there is a unique extension $(h_0^1, h_0^0)$ to all of $\mathbb{I} \times \mathbb{I}$ which matches with $h_0$, $e$, and $f$ over $p$ and $q$. First, we note that we may uniquely extend $h_0^1$ to $h^1$ since $F_1$ is cocartesian. Let us therefore replace $h_0^1, f^1$, and $g^1$ with $h^1$ so that our new goal is to construct an extension of $h_0^0$ given the following:

$$h_0^0: (k: \mathbb{I}) \to \alpha(k, 0) = 0 \to \alpha_{\chi(k, 0)}^{-1}(h^1(k, 0))$$

$$f^0: (j: \mathbb{I}) \to \alpha(0, j) = 0 \to \alpha_{\chi(0, j)}^{-1}(h^1(k, 0))$$

$$g^0: (j: \mathbb{I}) \to \alpha(1, j) = 0 \to \alpha_{\chi(1, j)}^{-1}(h^1(k, 1))$$

To prove this, we must perform a somewhat lengthy case analysis on $\alpha$. Since it is $\mathbb{I}$-annotated, we know that it is a $\mathbb{I}$-element of $\mathbb{I}[x_0, x_1]$ and we can analyze it somewhat extensively.

Case. $\alpha(0, -) = \lambda_{\_.1}$.

In this case, $\alpha = \lambda_{\_.1}$ by monotonicity, and so any extension is necessarily trivial.

Case. $\alpha(0, -) = \lambda_{\_.0}$.

Here, we have several sub-cases to consider:

Case. $\alpha(1, -) = \lambda_{\_.0}$.

In this case, the condition $\alpha(-, -) = 0$ holds in all cases, so this reduces precisely to the fact that $F_0$ is cocartesian. In particular, we note that we may extend $h^0$ in $F_0$ (not in the fiber) using the fact that $f^0$ is cocartesian. This extension is unique by construction and, since the input to the extension lies over $h^1$, it lives in the correct fiber (uniquely).

Case. $\alpha(1, -) = \lambda j. j$.

In this case, we must construct a lift of the following type:

$$(k, j: \mathbb{I}) \to k \wedge j = 0 \to \alpha_{\chi(k, j)}^{-1}(h^1(k, j))$$

Given $k, j: \mathbb{I}$, since everything is simplicial we may assume that $k \le j$ or $j \le k$. In other words, our condition is equivalent to $k = 0$ or $j = 0$; any extension is fully determined by the boundary conditions.

Case. $\alpha(1, -) = \lambda_{\_.1}$.

In this case, $\alpha = \lambda(k, j). k$ and so we may just take $h_0 = h_0^0$.

Case. $\alpha(0, -) = \lambda j. j$.

Here, we have several sub-cases to consider:

Case. $\alpha(1, -) = \lambda j. j$.

In this case, $\alpha(k, j) = j$ and so we may simply take $h^0 = f^0$.

Case. $\alpha(1, -) = \lambda_{\_.1}$.

In this case, $\alpha(k, j) = k \vee j$, so our condition $\alpha(k, j) = 0$ amounts to $k = 0 \wedge j = 0$. Consequently, we may take $h = f_0^0$.

**Corollary 3.11.** Cocartesian transport from $\mathrm{Gl}(F_0, F_1, \alpha)(-, 0)$ to $\mathrm{Gl}(F_0, F_1, \alpha)(-, 1)$ is given by $\alpha$.

PROOF. First, we note that given $f: \mathrm{Gl}(F_0, F_1, \alpha)(c, 0) \cong F_0(c)$, there is a functorial choice of edges:

$$\lambda i. (\alpha(f), \lambda_{\_.}(f, \text{refl})) : (i: \mathbb{I}) \to \mathrm{Gl}(F_0, F_1, \alpha)(c, i)$$

To show the desired identification, it suffices to show that this edge is cocartesian and, using the standard result that a natural transformation is an equivalence if and only if it is pointwise such, we restrict our attention to the case where $c \cdot \mathbb{I}_0 \to C$. This, however, is immediate in light of the above proof—in particular, cocartesian transport along a constant edge in $C$ is trivial.

### C.5 Classification of cocartesian fibrations

**Corollary 5.7.** Cocartesian transport induces an equivalence

$$\langle \mathbb{I} \mid \mathrm{Cat}^{X \times \Delta^1} \rangle \simeq \langle \mathbb{I} \mid \sum_{A_0, A_1, A_2: \mathrm{Cat}^X} A_0 \to {}^{\mathrm{cc}} A_1 \times A_1 \to {}^{\mathrm{cc}} A_2 \rangle.$$

PROOF. As before, one direction of this equivalence is given by taking fibers and cocartesian transports. We must construct a quasi-inverse.

Fix $F_0, F_1, F_2 \cdot \mathbb{I}_0 \to \mathcal{U}_{\mathbb{I}}$ cocartesian and $\alpha \cdot \mathbb{I}_0 \to {}^{\mathrm{cc}} F_1$ and $\beta \cdot \mathbb{I}_0 \to {}^{\mathrm{cc}} F_2$. We wish to apply Gl once more, but some additional care is required. As was described above in the text, we take $F_{01} = \mathrm{Gl}(F_0, F_1, \alpha) : C \times \mathbb{I} \to \mathcal{U}_{\mathbb{I}}$ and then consider $\gamma$ to be the composite $F_{01} \to {}^{\mathrm{cc}} F_1 \times \mathbb{I} \to {}^{\mathrm{cc}} F_2 \times \mathbb{I}$ where these operations are induced by cocartesian transport and $\mathbb{I} \times \beta$. Let us note that cocartesian transport preserves cocartesian edges—using 3-for-2 of cocartesian edges—and the transformation $F_1 \to F_2$ preserves cocartesian edges by assumption.

Consequently, we may glue along this once more to obtain a cocartesian family $F_{01,2} : C \times \mathbb{I} \times \mathbb{I} \to \mathcal{U}_{\mathbb{I}}$. Pre-composing with $\Delta^2 \to \mathbb{I} \times \mathbb{I}$, we obtain the desired family over $F_{012} : C \times \Delta^2 \to \mathcal{U}_{\mathbb{I}}$.

Unfolding, this family sends $(c, i, j)$ to the following type:

$$\sum_{x_2: F_2(c)} j = 0 \to \sum_{x_{01}: F_{01}(c, i)} \gamma(x_{01}) = (i, x_2)$$

$$\simeq \sum_{x_2: F_2(c)} j = 0 \to \sum_{x_1: \beta^{-1}(x_2)} i = 0 \to \alpha^{-1}(x_1)$$

There is then a canonical assignment $t_2 : F(c, i, j) \to F_{012}(c, i, j)$ given as follows:

$$x \mapsto ((c, - \vee i, - \vee j) \cdot (x), \lambda_{\_.} : j = 0 \, ((c, - \vee i, 0) \cdot (x), \lambda_{\_.} : i = 0. x))$$