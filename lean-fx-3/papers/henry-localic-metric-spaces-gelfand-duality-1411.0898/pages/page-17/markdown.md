2.6.4. **Lemma :** Let $p$ denote the canonical map from $[X, \mathbb{R}]$ to the point. Let $B$ be a basic sublocale then one has:

$$B \leqslant p^*(\text{“}B \text{ is admissible ”})$$

where we identify the proposition “$B$ is admissible” with a subset of $\{*\}$ and hence with an open sublocale of the point.

# **Proof :**

We will prove that in the theory classified by $[X, \mathbb{R}]$ (describe in [10]) the proposition asserting that $B$ is admissible can be deduced from the proposition corresponding to $B$.

Indeed, let $B$ be as in (1) and let $i$ and $j$ such that $u_i \leqslant v_j$. one has:

$$\begin{aligned} & B \vdash (U_i \ll f^*(\lceil -\infty, u_i[\rceil)) \wedge (V_j \ll f^*(\lceil v_j, +\infty[\rceil)), \\ & (U_i \ll f^*(\lceil -\infty, u_i[\rceil)) \vdash \bigvee_{U_i \ll U} (U \ll f^*(\lceil -\infty, u_i[\rceil)) \end{aligned}$$

and

$$(U \ll f^*(\lceil -\infty, u_i[\rceil)) \wedge (V \ll f^*(\lceil v_j, +\infty[\rceil)) \vdash (U \wedge V) = \emptyset.$$

Hence

$$B \vdash \bigvee_{\substack{U_i \ll U \\ V_j \ll V}} (V \wedge U = \emptyset)$$

but for any $U_i \ll U$ and $V_j \ll V$ if $(V \wedge U = \emptyset)$ then $\neg U \vee \neg V = X$ because

$$\begin{aligned} X &= (\neg U_i \vee U) \wedge (\neg V_j \vee V) \\ &= (\neg U_i \wedge \neg V_j) \vee (\neg U_i \wedge V) \vee (U \wedge \neg V_j) \vee (U \wedge V) \end{aligned}$$

The last term of the union can be removed by assumption, and we can duplicate the first, obtaining

$$\begin{aligned} X &= [(\neg U_i \wedge \neg V_j) \vee (\neg U_i \wedge V)] \vee [(U \wedge \neg V_j) \vee (\neg U_i \wedge \neg V_j)] \\ &= [(\neg U_i) \wedge (\neg V_j \vee V)] \vee [(\neg V_j) \wedge (\neg U_i \vee U)] \\ &= \neg U_i \vee \neg V_j \end{aligned}$$

Hence $B \vdash \neg U_i \vee \neg V_j$. As this is true for any $(i, j)$ such that $u_i \leqslant v_j$ we get the desired result.

$\square$

17