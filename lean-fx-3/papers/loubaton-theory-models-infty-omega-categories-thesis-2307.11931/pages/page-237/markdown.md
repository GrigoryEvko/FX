4.3. GRAY OPERATIONS

is an equivalence. The two previous morphisms then induce a comparison:

$$F_{|\Theta^{+}} \to \mathrm{N} \circ \pi_{0} \circ F_{|\Theta^{+}} \to H_{|\Theta^{+}}$$

By extension by colimits, this produces a natural transformation $\phi : F \to H$ extending $\psi$. The full sub $\infty$-groupoid of objects $C$ such that $\phi_{C} : F(C) \to H(C)$ is an equivalence is closed by colimits, contains globes, and so is the maximal sub $\infty$-groupoid. $\square$

The previous corollary implies that the equations (4.3.1.7), (4.3.1.8) and (4.3.1.9) characterize respectively the Gray cylinder, the Gray cone, and the Gray $\circ$-cone.

**Corollary 4.3.3.24.** *The colimit preserving endofunctor $F : (\infty, \omega)$-cat $\to (\infty, \omega)$-cat, sending $[a, n]$ to the colimit of the span*

$$\coprod_{k \leq n} \{k\} \leftarrow \coprod_{k \leq n} a \otimes \{k\} \to a \otimes [n]$$

*is equivalent to the identity.*

*Proof.* The proposition 4.3.3.15 implies that the restriction of $F$ to globes is equivalent to the restriction of the identity to globes. As the identity is the 0-iterated suspension, we can apply corollary 4.3.3.23. $\square$

The last corollary implies that for any $(\infty, \omega)$-category $C$ and any globular sum $a$, the simplicial $\infty$-groupoid

$$\begin{array}{l} \Delta^{op} \to \infty\text{-grd} \\ [n] \mapsto \operatorname{Hom}([a, n], C) \end{array}$$

is a $(\infty, 1)$-category.

**Theorem 4.3.3.25.** *Let $C$ be an $(\infty, \omega)$-category. The two following canonical squares are cartesian:*

$$\begin{array}{ccc} 1 \longrightarrow 1 \stackrel{co}{\star} C & & 1 \longrightarrow C \star 1 \\ \downarrow & \downarrow & \downarrow \\ \{0\} \longrightarrow [C, 1] & & \{1\} \longrightarrow [C, 1] \end{array}$$

*The five squares appearing in the following canonical diagram are both cartesian and cocartesian:*

$$\begin{array}{ccc} & C \otimes \{0\} & \longrightarrow 1 \\ & \downarrow & \downarrow \\ C \otimes \{1\} & \longrightarrow C \otimes [1] & \longrightarrow C \star 1 \\ \downarrow & \downarrow & \downarrow \\ 1 & \longrightarrow 1 \stackrel{co}{\star} C & \longrightarrow [C, 1] \end{array}$$

227