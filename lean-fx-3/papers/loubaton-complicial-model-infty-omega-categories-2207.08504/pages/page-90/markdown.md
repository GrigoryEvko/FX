CHAPTER 2. STUDY OF COMPLICIAL SETS

Lemma 2.4.2.7. D-Trivial fibrations between complicial sets have the right lifting property against $\partial[n] \to [n]$.

Proof. Let $C$ be the class of cofibrations having the right lifting property against D-equivalences. The lemma 2.4.2.6 implies that for any $K \to L$ in $C$, the induced morphism:

$$L \cup K \star [0] \to L \star [0]$$

is in $C$. The class $C$ is then closed under Leibniz join. Furthermore, it includes $\partial[1] \to [1]$, and then, by induction, it includes $\partial[n] \to [n]$ for any integer $n$. $\square$

Lemma 2.4.2.8. D-Trivial fibrations between complicial sets have the right lifting property against $[n] \to [n]_t$.

Proof. Let $p$ be D-trivial fibrations between complicial sets, and $C_{n,p}$ be the set of objects $A$ such that $p$ has the right lifting property against:

$$A \to \tau_{n-1}^i(A).$$

This set is then closed under colimits, and by zigzags of acyclic cofibrations. Let $k \le n$ be two integers. We define $\mathbb{P}(k, n, p)$ to be the statement that

$$\Sigma[n-k]_\circ \star [k-1] \quad \text{and} \quad [k-1]_\circ \overset{\text{co}}{\star} \Sigma[n-k]$$

are in $C_{n+1,p}$. The statement $\mathbb{P}(0, 0, f)$ corresponds to the belonging of $\mathbf{D}_1$ to $C_{1,p}$, which is obviously true. Suppose that $0 < k$ and $\mathbb{P}(k-1, n, p)$. According to theorem 2.3.2.1, the object $\Sigma[n-k]_\circ \star [k-1]$ is linked by a zigzag of acyclic cofibrations to the colimit of

$$(\Sigma[n-k]_\circ \vee [1]) \star [k-2] \leftarrow (\Sigma[n-k]_\circ) \star [k-2] \to (\Sigma[n-k+1]_\circ) \star [k-2]$$

The center object and the left hand object are in $C_{n+1,p}$ because there are invariant under $\tau_n^i$, and the right hand object is in $C_{n+1,p}$ by induction hypothesis. The object $\Sigma[n-k]_\circ \star [k-1]$ is then in $C_{n+1,p}$. We demonstrate similarly that $[k-1]_\circ \overset{\text{co}}{\star} \Sigma[n-k]$ is in $C_{n+1,p}$.

This then implies $\mathbb{P}(k, n, p)$. Eventually, $\mathbb{P}(0, n+1, p)$ is equivalent to $\mathbb{P}(n, n, p(a, b))$ for any pair of objects $(a, b) \in X_0$. The statement $\mathbb{P}(k, n, p)$ is then true for any $k, n$ and D-trivial fibrations between complicial sets $p$. This implies that $p$ has the right lifting property against $[n] \to [n]_t$. $\square$

Theorem 2.4.2.9. Let $p$ be a map between complicial sets. Then $p$ is a weak equivalence if and only if it is a D-equivalence.

Proof. According to lemmas 2.4.2.3 and 2.4.2.4 we can restrict ourselves to the case where $p$ is a fibration. If it is a weak equivalence, $p$ is then a trivial fibration and is then a D-equivalence. Suppose now that $p$ is a D-equivalence. According to proposition 2.4.2.5, $p$ is then a D-trivial fibration. Lemmas 2.4.2.7 and 2.4.2.8 imply that $p$ is a trivial fibration. $\square$

Definition 2.4.2.10. Let $p: X \to Y$ be a morphism between complicial sets. The morphism $p$ is essentially surjective for marked simplicial sets if for any $x \in Y_0$, there exists $\bar{x} \in X_0$ together with a marked cell $\bar{x} \to x$. The morphism $f$ is fully faithful if the induced morphisms:

$$X(a, b) \to Y(pa, pb)$$

are weak equivalences for any $a, b \in X_0$.

90