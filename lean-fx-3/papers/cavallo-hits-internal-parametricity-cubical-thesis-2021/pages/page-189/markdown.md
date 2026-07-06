Function types and the extent operator 177

because $p$ and $q$ were introduced prior to $x$: they precede $x$ in the context, so are not deleted by $\setminus x$.

As was the case for cubical equality, Lemma 9.2.2 is one of a laundry list of results we will be able to prove relating bridges in compound types to bridges in their component types. In particular, we can characterize bridges in path types: a path between bridges is the same as a bridge between paths.

**Lemma 9.2.3 (Bridges in path types).** Let $y : \mathbb{I}, x : \mathbb{I} \gg A$ type, $x : \mathbb{I} \gg M_0 \in A[0/y]$, and $x : \mathbb{I} \gg M_0 \in A[0/y]$ be given together with $P_0 \in \text{Path}(y.A[0/x], M_0[0/x], M_1[0/x])$ and $P_1 \in \text{Path}(y.A[1/x], M_0[1/x], M_1[1/x])$. Then we have an isomorphism of the following type.

$$
\begin{aligned}
\text{Bridge}(x.\text{Path}(y.A, M_0, M_1), P_0, P_1) \\
\simeq \\
\text{Path}(y.\text{Bridge}(x.A, P_0 y, P_1 y), \lambda^\mathbb{I}x. M_0, \lambda^\mathbb{I}x. M_1)
\end{aligned}
$$

*Proof.* Like the function extensionality isomorphism for paths, this isomorphism simply swaps the order of binders. Given $p$ of the former type, we have $\lambda^\mathbb{I}y. \lambda^\mathbb{I}x. p x y$ in the latter; given $q$ in the former, we have $\lambda^\mathbb{I}x. \lambda^\mathbb{I}y. q y x$ in the latter. (We use here the fact that restriction ignores path interval variables.) These are evidently inverses up to exact equality. $\square$

The above, read in reverse, doubles as a characterization of paths in bridge types. The type of bridges across many compound types can be characterized in the same way and with the same proof as the type of paths, as in the case of products. There are, however, key differences. As our next step, we consider function types, a case where the stories diverge.

## 9.3 Function types and the extent operator

In Section 3.2, we proved two results characterizing the behavior of paths at function type. First, we had *function extensionality* (Lemma 3.2.5), a practically trivial result characterizing the type $\text{Path}(x.(a : A) \to B, F_0, F_1)$ when $A$ does not depend on $x$. Second, we gave a more general characterization for the case where $A$ does depend on $x$, the proof of which relied on the existence of coercion for paths (Lemma 3.2.6).

For bridges, we again want the more general characterization, in accordance with the standard definition of relation at function type used in classical parametricity and logical relations more generally: two functions are related when they take related arguments to