Vol. 22:2

AUTOMATING BOUNDARY FILLING IN CUBICAL TYPE THEORIES

28:19

If $\phi$ is not satisfied at $\psi\delta$ then this is true by definition. Suppose then that $\phi$ is satisfied at $\psi\delta$, i.e., there is $(s = e' \mapsto t) \in \phi$ with $s[\psi\delta] = e'$. Define substitutions $\delta'_{0\bullet}, \delta'_{1\bullet}, \delta'_{\bullet 0}, \delta'_{\bullet 1}: (i) \to (i, \ell)$ by

$$\delta'_{0\bullet} := (i, \delta) \qquad \qquad \delta'_{1\bullet} := (i, r[\psi\delta])$$

$$\delta'_{\bullet 0} := \begin{cases} (0, 0) & \text{if } r[\psi\delta(0)] = 0 \\ (0, i) & \text{if } r[\psi\delta(0)] = 1 \end{cases} \qquad \qquad \delta'_{\bullet 1} := \begin{cases} (1, 0) & \text{if } r[\psi\delta(1)] = 0 \\ (1, i) & \text{if } r[\psi\delta(1)] = 1 \end{cases}$$

By induction hypothesis applied to the cell $\lceil X|R \rceil \mid \Psi[s = e'], \ell \vdash t$ cell, the substitution $((\psi\delta)[s = e'], \ell): (i, \ell) \to (\Psi[s = e'], \ell)$, and the four substitutions $\delta'_{0\bullet}, \delta'_{1\bullet}, \delta'_{\bullet 0}, \delta'_{\bullet 1}$ just defined, we have

$$[t]_{((\psi\delta)[s = e'], \ell)\delta'_{\bullet 0}} [t]_{((\psi\delta)[s = e'], \ell)\delta'_{1\bullet}} = [t]_{((\psi\delta)[s = e'], \ell)\delta'_{0\bullet}} [t]_{((\psi\delta)[s = e'], \ell)\delta'_{\bullet 1}}. \quad (3.2)$$

Calculating, we have

$$\begin{aligned} [t]_{((\psi\delta)[s = e'], \ell)\delta'_{0\bullet}} &= [t]_{((\psi\delta)[s = e'], 0)} = [t[\ell \mapsto 0]]_{(\psi\delta)[s = e']} = [u]_{(\psi\delta)[s = e']} = [u]_{\psi\delta} \\ [t]_{((\psi\delta)[s = e'], \ell)\delta'_{1\bullet}} &= [t]_{((\psi\delta)[s = e'], r[\psi\delta])} = [\phi]_{(\psi\delta, r[\psi\delta])} = [\text{fill}^{0 \to r} \ell. [\phi] u]_{\psi\delta} \\ [t]_{((\psi\delta)[s = e'], \ell)\delta'_{\bullet 0}} &= ([t]_{((\psi\delta)[s = e'](0), i)})^{r[\psi\delta(0)]} = ([\phi]_{(\psi\delta(0), i)})^{r[\psi\delta(0)]} \\ [t]_{((\psi\delta)[s = e'], \ell)\delta'_{\bullet 1}} &= ([t]_{((\psi\delta)[s = e'](1), i)})^{r[\psi\delta(1)]} = ([\phi]_{(\psi\delta(1), i)})^{r[\psi\delta(1)]} \end{aligned}$$

where in the last two rows we use case analysis on $r[\psi\delta(0)]$ and $r[\psi\delta(1)]$ and Lemma 3.20. Rearranging (3.2), we thus have

$$[\text{fill}^{0 \to r} \ell. [\phi] u]_{\psi\delta} = ([\phi]_{(\psi\delta(0), i)})^{-r[\psi\delta(0)]} [u]_{\psi\delta} ([\phi]_{(\psi\delta(1), i)})^{r[\psi\delta(1)]}$$

as desired.

Returning to the main claim, we now have

$$\begin{aligned} & [\text{fill}^{0 \to r} \ell. [\phi] u]_{\psi\delta_{\bullet 0}} [\text{fill}^{0 \to r} \ell. [\phi] u]_{\psi\delta_{1\bullet}} \\ = & ([\phi]_{(\psi\delta_{00}, i)})^{-r[\psi\delta_{00}]} [u]_{\psi\delta_{\bullet 0}} [u]_{\psi\delta_{1\bullet}} ([\phi]_{(\psi\delta_{11}, i)})^{r[\psi\delta_{11}]} \\ = & ([\phi]_{(\psi\delta_{00}, i)})^{-r[\psi\delta_{00}]} [u]_{\psi\delta_{0\bullet}} [u]_{\psi\delta_{\bullet 1}} ([\phi]_{(\psi\delta_{11}, i)})^{r[\psi\delta_{11}]} \\ = & [\text{fill}^{0 \to r} \ell. [\phi] u]_{\psi\delta_{0\bullet}} [\text{fill}^{0 \to r} \ell. [\phi] u]_{\psi\delta_{\bullet 1}} \end{aligned}$$

as required.

**Corollary 3.22.** *Let $\langle X|R \rangle$ be a convenient presentation of a group $G$. For any pair of words $v, w$ on $X$ there exists a cell*

$$\lceil X|R \rceil \mid i, k \vdash t : [\partial i \mapsto \star \mid k = 0 \mapsto \lceil v \rceil(i) \mid k = 1 \mapsto \lceil w \rceil(i)]$$

*if and only if $v \equiv_G w$.*

*Proof.* One direction was already proven in Proposition 3.17. For the converse, suppose we have such a cell $t$. By applying Lemma 3.21 with the $\delta_{0\bullet} = (0, i)$, $\delta_{1\bullet} = (1, i)$, $\delta_{\bullet 0} = (i, 0)$, and $\delta_{\bullet 1} = (i, 1)$, we get that $[\lceil v \rceil(i)]_{(i)} [\star]_{(i)} = [\star]_{(i)} [\lceil w \rceil(i)]_{(i)}$. By Lemma 3.20 and Lemma 3.19, this means that $v \equiv_G w$.

**Theorem 3.23.** *KAN is undecidable. More specifically, there are contexts $\Gamma$ for which there is no algorithmic decision procedure for the problem $\Gamma \mid i, k \vdash ? : [\phi]$ uniformly in Kan boundaries $\Gamma \mid i, k \vdash \phi$ bdy.*