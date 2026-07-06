The relativity principle 193

(Lemma 9.2.2, Theorem 9.3.2, and Lemma 9.2.3). Applying each of these characterizations in turn beginning with $\text{Bridge}(x.A \simeq B, i_0, i_1)$, we arrive at a type readily seen to be isomorphic to the right hand side above. Specifically, the characterizations deliver us to a type of tuples consisting of a family of functions $\text{Bridge}(x.A, a_0, a_1) \rightarrow \text{Bridge}(x.B, i_0, a_0, i_1, a_1)$ indexed over $a_0, a_1$, two families of functions in the opposite direction, and proofs that these are left and right inverses respectively for every $a_0, a_1$. It then remains only to pull the indices $a_0, a_1$ out to the top level. $\square$

**Theorem 10.2.3 (Relativity).** Let $A, B$ type be given. Then the following function is an isomorphism.

$$\lambda p. \lambda \langle a, b \rangle. \text{Bridge}(x.p x, a, b) \in \text{Bridge}(U, A, B) \rightarrow (A \times B \rightarrow U)$$

*Proof.* We use the Gel types to build our candidate inverse.

$$\lambda R. \lambda^I x. \text{Gel}_x(A, B, R) \in (A \times B \rightarrow U) \rightarrow \text{Bridge}(U, A, B)$$

We have two inverse conditions to show.

1. $(R: A \times B \rightarrow U) \rightarrow (\lambda \langle a, b \rangle. \text{Bridge}(x.\text{Gel}_x(A, B, R), a, b)) \rightsquigarrow R.$

By function extensionality (Lemma 3.2.5), it suffices to construct a path in $U$ from $\text{Bridge}(x.\text{Gel}_x(A, B, R), a, b)$ to $R \langle a, b \rangle$ for all $a: A$ and $b: B$. In turn, by univalence (Theorem 3.2.9), it is enough to give an *isomorphism* from $\text{Bridge}(x.\text{Gel}_x(A, B, R), a, b)$ to $R \langle a, b \rangle$ for all $a, b$.

Such an isomorphism is provided up to exact equality by the constructor and eliminator for the Gel type, with functions in either direction defined as follows.

$$\begin{aligned} \lambda t. \lambda^I x. \text{gel}_x(a, b, t) &\in R \langle a, b \rangle \rightarrow \text{Bridge}(x.\text{Gel}_x(A, B, R), a, b) \\ \lambda q. \text{ungel}(x.q x) &\in \text{Bridge}(x.\text{Gel}_x(A, B, R), a, b) \rightarrow R \langle a, b \rangle \end{aligned}$$

By the reduction and uniqueness rules for Gel types, these functions cancel each other up to exact equality.

2. $(p: \text{Bridge}(U, A, B)) \rightarrow (\lambda^I x. \text{Gel}_x(A, B, \text{Bridge}(x.p x, -, -))) \rightsquigarrow p.$

Let $p: \text{Bridge}(U, A, B)$ be given. By the characterization of paths in bridges (Lemma 9.2.3), it is equivalent to give a bridge between paths of the following type.

$$\text{Bridge}(x.\text{Path}(U, \text{Gel}_x(A, B, \text{Bridge}(x.p x, -, -)), p x), \lambda^I \_ A, \lambda^I \_ B)$$

Now we take advantage of univalence to replace the inner type of paths in $U$ above with a type of isomorphisms, finding that the above type is isomorphic to the following.

$$\text{Bridge}(x.\text{Gel}_x(A, B, \text{Bridge}(x.p x, -, -)) \simeq p x, \text{coe}_{-A}^{0 \simeq 1}, \text{coe}_{-B}^{0 \simeq 1})$$