CHAPTER 3. COMPLICIAL SETS AS A MODEL OF \((\infty, \omega)\)-CATEGORIES

whose left vertical morphisms are weak equivalences. As weak equivalences are stable by pushouts along cofibrations and by composition, the canonical morphism $[1]_t \otimes [a, 1] \to [[1]_t \otimes a, 1]$ is a weak equivalence. As the canonical morphism $[1]_t \otimes [a, 1] \to [a, 1]$ is the composite of $[1]_t \otimes [a, 1] \to [[1]_t \otimes a, 1]$ with the weak equivalence $[[1]_t \otimes a, 1] \to [a, 1]$, it is a weak equivalence.

We proceed similarly to demonstrate that for all marked complicial sets $K$, $K \otimes [e, 1]_t \to K \otimes [0]$ is a weak equivalence.

The theorem 3.1.2.13 and the proposition 2.2.1.10 then imply that the functor $\otimes : \mathrm{tPsh}(\Delta)^1 \times \mathrm{tSeg}(A) \to \mathrm{tSeg}(A)$ is a left Quillen functor.

**Construction 3.1.4.7.** Let $a$ be an object of $A$ and $l, m, n$ three integers. By construction, $[l] \otimes [m] \otimes [a, n]$ is a quotient of

$$P_{a,l,m,n} := \underset{[[k_0], k_1] \to [m] \otimes [n]}{\mathrm{colim}} \underset{[[k_2], k_3] \to [l] \otimes [k_1]}{\mathrm{colim}} [[k_2] \otimes [k_0] \otimes a, k_3]$$

while $([l] \times [m]) \otimes [a, n]$ is a quotient of

$$Q_{a,l,m,n} := \underset{[[k_4], k_3] \to ([l] \times [n]) \otimes [m]}{\mathrm{colim}} [[k_4] \otimes a, k_3].$$

Lemma 1.2.5.10 and the Gray module structure on $A$ then induce a morphism

$$P_{a,l,m,n} \to Q_{a,l,m,n}.$$

We can check that this morphism passes to the quotient and then induces a natural morphism

$$[l] \otimes [m] \otimes [a, n] \to ([l] \times [m]) \otimes [a, n].$$

By extension by colimit, this induces, for any Segal $A$-category $C$, and any pair of simplicial sets $K, L$, a morphism

$$K \otimes L \otimes C \to (K \times L) \otimes C.$$

Moreover, we can check that this natural transformation between $\_ \otimes \_ \otimes \_$ and $(\_ \times \_) \otimes \_$ extends to stratified simplicial sets and stratified Segal $A$-categories. Eventually, by construction and using the equality (1.2.5.12), we get a commutative square

$$\begin{array}{c} K \otimes L \otimes M \otimes C \longrightarrow (K \times L) \otimes M \otimes C \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \downarrow \\ K \otimes (L \times M) \otimes C \longrightarrow (K \times L \times M) \otimes C \end{array}$$

for any stratified Segal $A$-category $C$ and any stratified simplicial sets $K, L, M$.

**Theorem 3.1.4.8.** *A Gray module structure on $A$ induces a Gray module structure on $\mathrm{tSeg}(A)$. The family of intelligent truncations is defined in 3.1.4.3, and the tensoring by $\mathrm{tPsh}(\Delta)^1$ is defined in 3.1.4.4. The natural comparison maps between $K \otimes (L \otimes C)$ and $(K \times L) \otimes C$ are provided by the construction 3.1.4.7.*

*Proof.* The proposition 3.1.4.6 states that the functor $\_ \otimes \_$ constructed in 3.1.4.4 is a left Quillen functor. The first condition of the definition 3.1.4.2 follows from construction 3.1.4.7, and the two other are obviously fulfilled.

112