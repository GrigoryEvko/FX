$(d) \Rightarrow (e)$ If $\delta(U) < q$ then there exists a positive $\epsilon$ such that $\delta(U) < q - 2\epsilon$. Take $V = B_\epsilon f_U$ yields the result as $U \leqslant f^* f_U \leqslant f^* B_\epsilon f_U = f^* V$.

$(e) \Rightarrow (a)$ Using $(e)$ one gets immediately the inclusion

$$\Delta_q = \bigvee_{U \in \mathcal{O}(X) < q} U \times U \subseteq \bigvee_{V \in \mathcal{O}(Y) < q} f^*(V) \times f^*(V) = (f \times f)^*(\Delta_q)$$

$\square$

3.1.9. Proposition : Let $f : X \to Y$ be a map between two pre-metric locales, let $\epsilon$ and $\eta$ be two positive rational numbers, then the following conditions are equivalent:

(a) \(\Delta_{\eta}\leqslant (f\times f)^{*}\Delta_{\epsilon}\)
(b) If \(U\in \mathcal{O}(X)\) and \(\delta (U) <   \eta\) then \(\delta (f_1(U)) <   \epsilon\)
(c) If \(U \in \mathcal{O}(X)\) and \(\delta(U) < \eta\) then there exists \(V \in \mathcal{O}(Y)\) such that \(\delta(V) < \epsilon\) and \(U \leqslant f^{*}(V)\).

The point of this proposition is to define a uniform map:

Definition : One says that a map $f$ is a uniform map if for all $\epsilon$ there exists $\eta$ satisfying the conditions of the previous proposition.

Proof :

The proof essentially follows the same lines as the proof of 3.1.8:

\((a)\Rightarrow (b)\) The argument for \((a)\Rightarrow (b)\) in 3.1.8 applies in exactly the same way here.
\((b)\Rightarrow (c)\) If \(\delta (f_1(U) <   \epsilon\) , then there exists \(q\) such that \(\delta (B_qf_1(U)) <   \epsilon\) hence one can take \(V = B_qf_1(U)\)
\((c)\Rightarrow (a)\) One has

$$\Delta_\eta = \bigvee_{\delta(U) < \eta} U \times U$$

but for each $U$ such that $\delta(U) < \eta$, there exists $V$ such that $\delta(V) < \epsilon$ and $U \leqslant f^*(V)$, hence

$$\Delta_\eta \leqslant \bigvee_{\delta(V) < \epsilon} f^* V \times f^* V = (f \times f)^* (V \times V)$$

$\square$

26