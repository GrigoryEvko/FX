Iterated smash products

203

To show that a commutator $F \in (A_*, B_* : \mathsf{U}_*) \to A_* \wedge_* B_* \to B_* \wedge_* A_*$ is an isomorphism, for example, it suffices to show that the composite $\lambda c. F B_* A_* (F B_* A_* c)$ is the (pointed) identity function for every $A_*, B_* : \mathsf{U}_*$. By the same token, we can show that a pair of associator functions

$$
G \in (A_*, B_*, C_* : \mathsf{U}_*) \to (A_* \wedge_* B_*) \wedge_* C_* \to A_* \wedge_* (B_* \wedge_* C_*)
$$

$$
H \in (A_*, B_*, C_* : \mathsf{U}_*) \to A_* \wedge_* (B_* \wedge_* C_*) \to (A_* \wedge_* B_*) \wedge_* C_*
$$

constitute an isomorphism by showing that the two round-trip composites are identities. The pentagon identity displayed in Chapter 8 can also be cast as the equality of a round-trip composite to the identity function at a type of the form $(\bullet)$; higher coherences amount to equalities between such equalities. We cannot expect that *every* parametric term of the form $(\bullet)$ is an identity function, because the existence of basepoints makes the pointed constant function a possibility. However, we will see that this is the only exception. It is moreover easy to check that such a function is not constant by testing it on small inputs, namely the pointed type $\mathsf{Bool}_* := \langle \mathsf{Bool}, \mathsf{tt} \rangle$. For example, $K \in (A_*, B_* : \mathsf{U}_*) \to A_* \wedge_* B_* \to A_* \wedge_* B_*$ is an identity function if and only if we have $K \mathsf{Bool}_* \mathsf{Bool}_* \langle \langle \mathsf{ff}, \mathsf{ff} \rangle \rightsquigarrow \langle \langle \mathsf{ff}, \mathsf{ff} \rangle \rangle$.

To illustrate the argument, we start with the binary case.

**Theorem 10.5.2.** Any function $(A_*, B_* : \mathsf{U}_*) \to A_* \wedge_* B_* \to A_* \wedge_* B_*$ is either the polymorphic identity or the polymorphic constant pointed function.

The proof of this theorem will involve a bit of serious higher-dimensional programming. We want to avoid clouding the main thrust of the proof with routine verification of boundary conditions, so we will mainly dispatch higher-dimensional obligations without much comment. Our argument is not that one is *completely* saved from verifying such conditions. Rather, our claim is that parametricity permits the characterization of terms of the form $(\bullet)$ without being swamped in complexity as $n$ increases.

We first introduce a couple of auxiliary terms that will come in handy for checking coherence conditions.

**Definition 10.5.3 (Concatenation by inverse).** let $M \in A$, $r \in \mathbb{I}$, and $x : \mathbb{I} \gg N \in A$ with $r \equiv 1 \gg M = N[1/x] \in A$ be given. For any $s \in \mathbb{I}$, define $\operatorname{conc-inv}_A^{r,s}(M, x.N) \in A$ as follows.

$$
\operatorname{conc-inv}_A^{r,s}(M, x.N) := \operatorname{hcom}_A^{1 \to s}(M; r \equiv 0 \hookrightarrow \dots M, r \equiv 1 \hookrightarrow x.N)
$$

The term $\operatorname{conc-inv}_A^{r,0}(M, x.N)$ is the result of concatenating $M$ (as a path in direction $r$) with the inverse of $x.N$; we will use the general form $\operatorname{conc-inv}_A^{r,s}(M, x.N)$ to relate the composite to other terms.