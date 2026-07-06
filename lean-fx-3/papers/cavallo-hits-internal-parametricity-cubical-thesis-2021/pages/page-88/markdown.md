76

Cubical type theory

The key step, then, is to construct paths $\text{coe}_{x,A}^{x\to 0}(px) \rightsquigarrow a_0$, $\text{coe}_{x,A}^{x\to 1}(px) \rightsquigarrow a_1$, and $\text{coe}_{x,A}^{x\to y}(px) \rightsquigarrow py$. We can produce the third, which implies the others, as follows.

$$\text{coe}_{z.\text{Path}(A[z/x],\text{coe}_{x,A}^{x\to z}(px),pz)}^{x\to y}(\lambda^\perp\dots px) \in \text{Path}(A[y/x],\text{coe}_{x,A}^{x\to y}(px),py)$$

That is, the equation holds by reflexivity when $y$ is $x$, so we can extend it to all other values of $y$ by coercion. $\square$

Remark 3.2.7. In the case where $A$ is degenerate, Lemma 3.2.6 gives us the following isomorphism.

$$\text{Path}(x.(a:A) \to B, f_0, f_1)$$

$$\simeq$$

$$(a_0:A)(a_1:A)(p:\text{Path}(A,a_0,a_1)) \to \text{Path}(x.B[px/a],f_0a_0,f_1a_1)$$

We can re-derive the alternative characterization in Lemma 3.2.5 from this principle by singleton contractibility: any pair of arguments $a_1, p$ is equal up to a path to $a_0, \lambda^\perp\dots a_0$.

We round out this section with a couple of results that we will not prove in detail—they are not particularly difficult, but are easiest to prove with a larger toolbox of lemmas than we want to set up here—but which will be useful in the future.

The first of these shows that in order to characterize the path family at some type, we do not need to build an isomorphism explicitly: we only need one of the inverse conditions, the one showing that the characterization is a retract of the path family.

Lemma 3.2.8 (Characterization by retract). Let $A$ type and $R:A \times A \to \mathbb{U}$ and suppose we have two functions as follows.

$$f:(a_0,a_1:A) \to R\langle a_0,a_1\rangle \to \text{Path}(A,a_0,a_1)$$

$$g:(a_0,a_1:A) \to \text{Path}(A,a_0,a_1) \to R\langle a_0,a_1\rangle$$

If we have paths $g a_0 a_1 (f a_0 a_1 q) \rightsquigarrow q$ for all $a_0, a_1: A$, then $\text{Path}(A, a_0, a_1)$ is isomorphic to $R\langle a_0, a_1\rangle$ for all $a_0, a_1: A$. Moreover, in this case any function with the type of $f$ or $g$ is an isomorphism.

Proof (sketch). See [Rij18, Corollary 1.2.6] for a more detailed proof (in HoTT).

Such a family of retracts implies that the product type $(a_1:A) \times R\langle a_0,a_1\rangle$ is a retract of $(a_1:A) \times \text{Path}(A,a_0,a_1)$. The latter is a singleton type, therefore contractible. A retract of a contractible type is also contractible, so $(a_1:A) \times R\langle a_0,a_1\rangle$ is contractible.

Given any family of functions with the same type as $f$ or $g$, the induced map from $(a_1:A) \times R\langle a_0,a_1\rangle$ to $(a_1:A) \times \text{Path}(A,a_0,a_1)$ is an isomorphism, because any function between contractible types is an isomorphism. That the induced map is an isomorphism in turn implies that the original family of functions is a family of isomorphisms [Rij18, Proposition 1.2.4].