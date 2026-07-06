110 Case studies

with path types.

$$\text{elim}(a_0, a_1, p, B; M_0, M_1; \text{refl}(M); a, N) \longmapsto N[M/a]$$

**Comparing MLTT and cubical identity types** In Martin-Löf type theory, the J eliminator is unnecessarily weak from the perspective of the computational semantics. Indeed, as noted in Section 2.1.5.4, the semantics justify an equality reflection rule that recovers *exact* equalities from elements of the identity type. It is worth examining why our definition of identity types for cubical type theory fails to satisfy the same principles.

The equality reflection rule in MLTT, for one, relies on the fact that the only values of the identity type are $\text{refl}(M)$ terms. Thus, the only way a type $\text{Id}(A, M_0, M_1)$ can be inhabited in an empty context is if the elements $M_0$ and $M_1$ are exactly equal. In cubical type theory, on the other hand, an element of an identity type may be an fcoe or fhcom term, in which case it does not follow that the two indices are exactly equal.

*A fortiori*, the MLTT semantics of identity types also validates the “K” rule, which constructs elements of type families over loops (identities from a given $a$ to $a$) rather than arbitrary identities.

$$\frac{M \in A \quad \begin{array}{c} a : A, p : \text{Id}(A, a, a) \gg B \text{ type} \\ P \in \text{Id}(A, M, M) \quad a : A \gg N \in B[\text{refl}(a)/p] \\ \hline K(a, p, B; M; P; a, N) \in B[M/a, P/p] \end{array}}{\text{K}(a, p, B; M; P; a, N)} \text{ (MLTT)}$$

K is implemented by the reduction $K(a, p, B; M; \text{refl}(M'); a, N) \longmapsto N[M'/a]$. The K rule does not imply equality reflection on its own, but does imply that any loop $P \in \text{Id}(A, M, M)$ is equal to $\text{refl}(M)$ up to higher identity.

If we were to try to implement the K eliminator for our cubical identity types, on the other hand, we find ourselves stuck at the case $K(a, p, B; M; \text{fcoe}_{x, M_0, M_1}^{r \to s}(P); a, N)$. While the compound term $\text{fcoe}_{x, M_0, M_1}^{r \to s}(P)$ is a loop by assumption, the inner identity $P$ need not be. We cannot therefore progress by recursively applying K to $P$. In short, because of the presence of fcoe terms, applying the eliminator at one index may require the recursive application of the eliminator at a different index. This provides some justification for the form of the J eliminator for identity types and eliminators for indexed inductive types more generally: we require a type family $a_0 : A, a_1 : A, p : \text{Path}(A, a_0, a_1) \gg B$ type defined on all possible indices, not only on those indices that can be inhabited using the generating constructors.