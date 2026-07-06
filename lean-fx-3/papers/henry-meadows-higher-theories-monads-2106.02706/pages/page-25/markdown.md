model structure. For each pair of objects $x, y \in \mathcal{Y}, x', y' \in \mathcal{X}$ such that $f(x) = g(x'), f(y) = g(y')$, we have a homotopy pullback:

$$\begin{array}{ccc} \text{Map}_{\mathcal{D}}((x, x'), (y, y')) & \longrightarrow & \text{Map}_{\mathcal{X}}(x, y) \\ \downarrow & & \downarrow \\ \text{Map}_{\mathcal{Y}}(x, y) & \longrightarrow & \text{Map}_{\mathcal{Z}}(f(x), f(y)) \end{array}$$

This follows from the construction of homotopy pullbacks in Bergner's model structure. The result now follows from the description of homotopy colimits internal to a fibrant simplicial category ([15, Remark A.3.3.13]) and the fact that homotopy pullbacks and homotopy colimits of simplicial sets commute (see [15, 6.1.3.14]).

Finally, we will need the following lemma that is essentially a consequence of Theorem 3.22:

**Lemma 3.25.** *Let $U_1 : \mathcal{D}_1 \to \mathcal{C}$ and $U_2 : \mathcal{D}_2 \to \mathcal{C}$ be two monadic right adjoint functors, with left adjoints $L_1$ and $L_2$ and $t : \mathcal{D}_1 \to \mathcal{D}_2$ be a functor such that $U_1 \simeq U_2 t$. Then $t$ is an equivalence of $\infty$-categories if and only if the natural transformation $L_2 \to t L_1$ obtained from the isomorphism $U_1 \to U_2 t$ through the adjunction is an equivalence.*

*Proof.* Under the equivalence Theorem 3.22, $t$ corresponds to a morphisms of monads $\text{End}(U_2) \to \text{End}(U_1)$, and $t$ is an equivalence if and only if this morphism of monads is an equivalence. At the level of underlying endofunctors, the morphism of monads identifies with a natural transformation $U_2 L_2 \to U_1 L_1$ induced by the action of $U_2 L_2$ on $U_1 \simeq U_2 \circ t$. Thus, it can be described as the natural transformation $U_2 L_2 \to U_1 L_1 \simeq U_2 t L_1$ obtained under the adjunction $L_1 \dashv U_1$ from the map $U_2 L_2 U_2 t \to U_2 t$ induced by the counit $L_2 U_2 \to Id$.

Unfolding this, we see that up canonical isomorphism, this map $U_2 L_2 \to U_1 L_1$ is exactly the image under $U_2$ of the natural transformation $L_2 \to t L_1$. As $U_2$ is conservative it indeed follows that the morphism of monads is an equivalence if and only if $L_2 \to t L_1$ is an equivalence.

*Remark 3.26.* In the rest of the paper, we will never use explicitly use the notion of monads, but always work with monads through the equivalence of

25