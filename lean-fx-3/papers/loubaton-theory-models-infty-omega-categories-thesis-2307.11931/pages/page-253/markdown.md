5.1. MARKED \((\infty, \omega)\)-CATEGORIES

According to proposition 4.2.1.60 and by construction, the morphisms

$$\operatorname{colim}(\tau_n^i F^\natural \otimes K) \to \tau_n^i (\operatorname{colim} F^\natural \otimes K) \quad \text{and} \quad \operatorname{colim}(tF \otimes K_0) \to t(\operatorname{colim} F \otimes K_0)$$

are epimorphisms. The marked $(\infty, \omega)$-categories $\operatorname{colim}(F \otimes K^\sharp)$ and $(\operatorname{colim} F) \otimes K^\sharp$ then have the same marked cells. □

**Proposition 5.1.2.2.** *Let $C$ be a $(\infty, \omega)$-category, $D$ a marked $(\infty, \omega)$-category and $K, L$ two $(\infty, 1)$-categories.*

(1) *The underlying $(\infty, \omega)$-category of $C^\flat \otimes K^\sharp$ is $C \otimes K$.*
(2) *The canonical morphism $C^\sharp \otimes K^\sharp \to C^\sharp \times K^\sharp$ is an equivalence.*

*Proof.* The first assertion is obvious.

Let $a$ be a globular sum and $[k]$ an object of $\Delta$. We claim that the following two squares are cocartesian:

$$\coprod_n \coprod_{\mathbf{D}_n \to a} \mathbf{D}_n \otimes [k] \longrightarrow \coprod_n \tau_n a \otimes [k] \longrightarrow a \otimes [k]$$
$$\updownarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad$$
$$\coprod_n \coprod_{\mathbf{D}_n \to a} \tau_n^i (\mathbf{D}_n \otimes [k]) \longrightarrow \coprod_n \tau_n^i (\tau_n a \otimes [k]) \longrightarrow (a^\sharp \times [k]^\sharp)^\sharp$$

The cocartesianess of the left square is a consequence of propositions 4.2.1.62 and 4.2.1.61. The outer square is cocartesian by definition, and by left cancellation, this implies the cocartesianess of the right square. The lemma 2.2.2.8 then implies that the underlying category of $a^\sharp \otimes [k]^\sharp$ is $a \times [k]$. As every cell of $a^\sharp \otimes [k]^\sharp$ is marked, this concludes the proof of the second assertion. □

**Proposition 5.1.2.3.** *Let $D$ be an $(\infty, \omega)$-category, $C$ a marked $(\infty, \omega)$-category and $K$ an $(\infty, 1)$-category. The canonical morphism $(D^\sharp \times C) \otimes K^\sharp \to D^\sharp \times (C \otimes K^\sharp)$ is an equivalence.*

*Proof.* As $\times$ and $\otimes$ preserve colimits, we can reduce to the case where $D$ is an element of $\Theta$, $C$ of $t\Theta$ and $K$ of $\Delta$, and we proceed by induction on the dimension of $D$. Remark first that if $D$ is $[0]$, the result is obvious, and if it is $(\mathbf{D}_1)_t$, the result follows from the second assertion of proposition 5.1.2.2. Suppose then the result is true at the stage $n$. Using once again the fact that $\times$ and $\otimes$ preserve colimits, we can reduce to the case where $D^\sharp$ is $[a, 1]^\sharp$, $C$ is $[b, 1]$ with $b$ an element of $\Theta_t$ of dimension $n$, and $K^\sharp$ is $[1]^\sharp$.

The formula given in proposition 5.1.1.34 implies that $([a, 1]^\sharp \times [b, 1]) \otimes [1]^\sharp$ is the colimit of the sequence:

$$([a, 1]^\sharp \vee [b, 1]) \otimes [1]^\sharp \longleftarrow [a^\sharp \times b, 1] \otimes [1]^\sharp \longrightarrow ([b, 1] \vee [a, 1]^\sharp) \otimes [1]^\sharp \qquad (5.1.2.4)$$

243