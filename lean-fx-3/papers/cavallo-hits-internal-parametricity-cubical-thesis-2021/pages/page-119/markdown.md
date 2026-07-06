Identity types 107

Conversely, one can easily use the eliminator for the identity type to transform identities $Q \in \text{Id}(A, M_0, M_1)$ into paths, starting the existence of reflexive paths.

$$\text{elim}(a_0, a_1, p, \text{Path}(A, a_0, a_1); M_0, M_1; Q; a, \lambda^\sharp x, a) \in \text{Path}(A, M_0, M_1)$$

In fact, one may straightforwardly show that these functions would constitute an isomorphism between $\text{Path}(A, M_0, M_1)$ and $\text{Id}(A, M_0, M_1)$. This would seem to suggest that we may *define* identity types to be path types—after all, we intended path types to play the role of identity types from the start. To do so, we would have to give some definition of the identity type eliminator as an operator on path types, a term satisfying the following typing rule.

$$\frac{M_0 \in A \quad M_1 \in A \quad P \in \text{Path}(A, M_0, M_1) \quad a : A \gg N \in B[a/a_0, a/a_1, \lambda^\sharp \dots a/p]}{\text{“elim”}(a_0, a_1, p, B; M_0, M_1; P; a, N) \in B[M_0/a_0, M_1/a_1, P/p]}$$

This much is possible: we may define the eliminator directly as follows.

$$\text{“elim”}(a_0, a_1, p, B; M_0, M_1; P; a, N) := \text{coe}_{x, B[M_0/a_0, H_x 1/a_1, H_x/p]}^{0 \to 1} (N[M_0/a])$$
$$\text{where } H_x := \lambda^\sharp y, \text{hcom}_A^{0 \to y} (M_0; x \equiv 0 \hookrightarrow y, M_0, x \equiv 1 \hookrightarrow y, P, y)$$

The term $H_x$ here is constructed so that $H_0 = \lambda^\sharp \dots M_0$ and $H_1 = P$, allowing us to transfer terms over the former to terms over the latter by coercion.

While this term has the correct *type*, however, it fails to satisfy the *equation* required of an identity eliminator: the reduction rule “elim”($a_0, a_1, p, B; M, M; \lambda^\sharp(M); a, N) = N[M/a]$. The equation can be shown to hold up to a path, but there is no reason it should hold up to exact equality in general. The representative counterexamples involve composition in the universe, so we will not present them here; a detailed walkthrough can be found in [Ang19, §3.4]. The situation is actually quite dire: Swan has shown that, under certain basic assumptions, the semantic path types in cubical set models cannot be used constructively as an interpretation of identity types [Swa18b].

Of course, this does not mean that there is no way to construct identity types, only that they will not coincide with path types. As we saw above, the problem with the naive construction is that it is not closed under coercion. This parallels the issue we encountered back in Section 5.1, where we found that the naive interpretation of quotients failed to be closed under composition. The solution will be the same: introduce formal coercions.

As mentioned in Section 5.1, formal coercions are not a satisfactory general solution to coercion in higher inductive types: they require the resulting type to be as large as the types of its parameters, which precludes, *e.g.*, universes closed under quotients. However, we can improve on this “worst case” by introducing only formal coercions *between indices*