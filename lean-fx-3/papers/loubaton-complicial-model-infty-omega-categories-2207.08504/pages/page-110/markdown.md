CHAPTER 3. COMPLICIAL SETS AS A MODEL OF \((\infty, \omega)\)-CATEGORIES

(1) for any stratified simplicial set $M$, the following square commutes

$$
\begin{array}{c} K \otimes (L \otimes (M \otimes a)) \longrightarrow (K \times L) \otimes (M \otimes a) \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \downarrow \\ K \otimes ((L \times M) \otimes a) \longrightarrow (K \times L \times M) \otimes a \end{array}
$$

(2) The functor $[0] \otimes \_ : A \to A$ is the identity.

(3) For any integer $n$, for any object $a$ such that $\tau_n^i(a) = a$ and for any stratified simplicial set $K$, we have $\tau_{n+1}^i(K \otimes a) = K \otimes a$.

Here, the model category $\mathrm{tPsh}(\Delta)^1$ corresponds to the model structure for 1-complicial sets on stratified simplicial sets given in theorem 2.2.1.8.

**Construction 3.1.4.3.** Let $A$ be a nice model category of stratified presheaves on an elegant Reedy category, endowed with intelligent $n$-truncation for $n \in \mathbb{N} \cup \{\omega\}$. We now construct a family of intelligent $n$-truncation for $n \in \mathbb{N} \cup \{\omega\}$ for $\mathrm{tSeg}(A)$.

Let $k$ be any non negative integer. The *intelligent $k$-truncation functor*, denoted by $\tau_k^i$, is the colimit-preserving functor such that $\tau_k^i([a, n]) = [\tau_{k-1}^i(a), n]$ and $\tau_k^i[e, 1]_t = [e, 1]_t$. The intelligent $0$-truncation functor, denoted by $\tau_0^i$, is the colimit-preserving functor such that $\tau_0^i([a, n])$ fits in the following pushout

$$
\begin{array}{c} \coprod_{ob(a) \times \mathrm{Hom}([1], [n])} [e, 1] \longrightarrow [\tau_0^i(a), n] \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \downarrow \\ \coprod_{ob(a) \times \mathrm{Hom}([1], [n])} [e, 1]_t \longrightarrow \tau_0^i([a, n]) \end{array}
$$

and such that $\tau_0^i[e, 1]_t = [e, 1]_t$. As the intelligent $k$-truncations on $A$ are left Quillen functors, the intelligent $k$-truncations on $\mathrm{tSeg}(A)$ preserve generating Reedy cofibrations and Segal extensions. It is straightforward that they also send $[e, 1]_t \to [0]$ and $E^{\cong} \to (E^{\cong})'$ to weak equivalences. According to theorem 3.1.2.13, they are left Quillen functors.

**Construction 3.1.4.4.** We consider the colimit-preserving functor

$$
\_ \otimes \_ : \mathrm{Psh}(\Delta) \times \mathrm{Seg}(A) \to \mathrm{Seg}(A)
$$

whose value on $([n], [a, m])$ fits in the pushout

$$
\begin{array}{c} \coprod_{l \leq m} \mathrm{colim}_{[k_0, k_1] \to [n] \otimes \{l\}} [[k_0] \otimes a, k_1] \longrightarrow \mathrm{colim}_{[k_0, k_1] \to [n] \otimes [m]} [[k_0] \otimes a, k_1] \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \downarrow \\ \coprod_{l \leq m} \mathrm{colim}_{[k_0, k_1] \to [n] \otimes \{l\}} [e, k_1] \longrightarrow [n] \otimes [a, m] \end{array}
$$

where $\_ \otimes \_ : (\infty, 1)$-cat $\times (\infty, 1)$-cat $\to (\infty, 2)$-cat is the Gray tensor product defined in theorem 1.2.4.1. We extend $\_ \otimes \_$ to a functor

$$
\_ \otimes \_ : \mathrm{tPsh}(\Delta) \times \mathrm{tSeg}(A) \to \mathrm{tSeg}(A)
$$

110