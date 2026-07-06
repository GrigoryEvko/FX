28:18

M. DORÉ, E. CAVALLO, AND A. MÖRTBERG

Vol. 22:2

Proof. The cases where $t$ is $\star$, $\hat{a}(\psi')$, or $s_{a,b,c}(\psi')$ are immediate from the definition, and the case where $t$ is a substitution application is direct by induction hypothesis. For $\text{fill}^{e \to r} \ell.[\phi] u$, we have two cases.

- If $\phi$ is satisfied at $\psi$, then $[\![\text{fill}^{e \to r} \ell.[\phi] u]\!]_\psi = [\![\phi]\!]_{(\psi,r[\psi])}$. Since $\psi$ is constant, so is $(\psi, r[\psi])$, and thus the result follows by induction hypothesis.
- Otherwise, we have

$$[\![\text{fill}^{e \to r} \ell.[\phi] u]\!]_\psi = (\![\![\phi]\!]_{(\psi(0),i)}^{\star})^{e-r[\psi(0)]}[\![u]\!]_\psi (\![\![\phi]\!]_{(\psi(1),i)}^{\star})^{r[\psi(1)]-e}$$

By induction hypothesis, we have $[\![u]\!]_\psi = 1$. Moreover, we have $\psi(0) = \psi(1)$, so

$$[\![\text{fill}^{e \to r} \ell.[\phi] u]\!]_\psi = (\![\![\phi]\!]_{(\psi(0),i)}^{\star})^{e-r[\psi(0)]}(\![\![\phi]\!]_{(\psi(0),i)}^{\star})^{r[\psi(0)]-e} = 1.$$

For 2-cells, we intuitively want to show that any cell

$${}^\lceil X|R^\rceil \mid j, k \vdash t : [j = 0 \mapsto u_0 \mid j = 1 \mapsto u_1 \mid k = 0 \mapsto v_0 \mid k = 1 \mapsto v_1]$$

induces an equality between the group elements $[\![u_0]\!]_{(k)}[\![v_1]\!]_{(j)}$ and $[\![v_0]\!]_{(j)}[\![u_0]\!]_{(k)}$. To make the induction go through, we prove a more general statement where instead of the boundary of $t$, we consider any “quadrilateral” of 1-cells tracing out a closed loop inside a 2-cell.

Lemma 3.21. For a convenient presentation $\langle X|R\rangle$ of a group $G$, a term ${}^\lceil X|R^\rceil \mid \Psi \vdash t$ cell, a substitution $\psi: (j, k) \to \Psi$, and a quadruple of substitutions $\delta_{0\bullet}, \delta_{1\bullet}, \delta_{\bullet 0}, \delta_{\bullet 1}: (i) \to (j, k)$ such that

$$\psi\delta_{0\bullet}(0) = \psi\delta_{\bullet 0}(0) \qquad \psi\delta_{0\bullet}(1) = \psi\delta_{\bullet 1}(0) \qquad \psi\delta_{1\bullet}(0) = \psi\delta_{\bullet 0}(1) \qquad \psi\delta_{1\bullet}(1) = \psi\delta_{\bullet 1}(1)$$

we have $[\![t]\!]_{\psi\delta_{\bullet 0}}[\![t]\!]_{\psi\delta_{1\bullet}} = [\![t]\!]_{\psi\delta_{0\bullet}}[\![t]\!]_{\psi\delta_{\bullet 1}}$.

Proof. In the situation of the statement, we abbreviate $\delta_{ee'} := \delta_{e\bullet}(e') = \delta_{\bullet e'}(e)$ for $e, e' \in \{0, 1\}$. We go by structural induction on $t$ as follows.

- For $t[\psi']$, we have

$$\begin{aligned} [\![t[\psi']]\!]_{\psi\delta_{\bullet 0}}[\![t[\psi']]\!]_{\psi\delta_{1\bullet}} &= [\![t]\!]_{\psi'\psi\delta_{\bullet 0}}[\![t]\!]_{\psi'\psi\delta_{1\bullet}} \\ &= [\![t]\!]_{\psi'\psi\delta_{0\bullet}}[\![t]\!]_{\psi'\psi\delta_{\bullet 1}} = [\![t[\psi']]\!]_{\psi\delta_{0\bullet}}[\![t[\psi']]\!]_{\psi\delta_{\bullet 1}} \end{aligned}$$

where the middle step is by induction hypothesis.

- For $\star$, we have $[\![\star]\!]_{\psi\delta_{\bullet 0}}[\![\star]\!]_{\psi\delta_{1\bullet}} = 1 \cdot 1 = [\![\star]\!]_{\psi\delta_{0\bullet}}[\![\star]\!]_{\psi\delta_{\bullet 1}}$.
- For $\hat{a}(\psi')$, we have

$$\begin{aligned} [\![\hat{a}(\psi')]\!]_{\psi\delta_{\bullet 0}}[\![\hat{a}(\psi')]\!]_{\psi\delta_{1\bullet}} &= g_a(\psi'\psi\delta_{00})^{-1}g_a(\psi'\psi\delta_{10})g_a(\psi'\psi\delta_{10})^{-1}g_a(\psi'\psi\delta_{11}) \\ &= g_a(\psi'\psi\delta_{00})^{-1}g_a(\psi'\psi\delta_{11}) \\ &= g_a(\psi'\psi\delta_{00})^{-1}g_a(\psi'\psi\delta_{01})g_a(\psi'\psi\delta_{01})^{-1}g_a(\psi'\psi\delta_{11}) \\ &= [\![\hat{a}(\psi')]\!]_{\psi\delta_{0\bullet}}[\![\hat{a}(\psi')]\!]_{\psi\delta_{\bullet 1}}. \end{aligned}$$

- For $[\![s_{a,b,c}(\psi')]\!]_\psi$, the same argument applies as for $\hat{a}(\psi')$.
- For $[\![\text{fill}^{e \to r} \ell.[\phi] u]\!]_\psi$, we proceed as follows. For simplicity we restrict our attention to the case $e = 0$; a symmetric argument applies for $e = 1$.

First, we use our induction hypothesis to prove the following: for all $\delta: (i) \to (j, k)$, we have

$$[\![\text{fill}^{0 \to r} \ell.[\phi] u]\!]_{\psi\delta} = (\![\![\phi]\!]_{(\psi\delta(0),i)}^{\star})^{-r[\psi\delta(0)]}[\![u]\!]_{\psi\delta}([\![\phi]\!]_{(\psi\delta(1),i)}^{\star})^{r[\psi\delta(1)]}.$$