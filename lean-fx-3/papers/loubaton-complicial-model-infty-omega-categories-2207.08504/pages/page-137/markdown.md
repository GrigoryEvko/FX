3.3. COMPLICIAL SETS AS OF MODEL OF \((\infty, n)\)-CATEGORIES

sending $[K, n]$ to the pushout:

$$\begin{array}{c} \coprod_{i \leq n} K \boxtimes \{i\} \longrightarrow K \boxtimes [n] \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \coprod_{i \leq n} [0] \longrightarrow j([K, n]) \end{array}$$

and $[[0], 1]_t$ to $[1]_t$. As $\_ \boxtimes \_$ is a left Quillen bifunctor, and as $\tilde{j}([[0], 1]_t \to [0]) = [1]_t \to [0]$ and $\tilde{j}([[0], E^{eq}] \to [0]) = E^{eq} \to [0]$ are weak equivalences, the theorem 3.1.2.13 implies that the functor $j^\omega$ is a left Quillen functor. By definition of the Gray pre-tensor product, we remark that $\tilde{j}([[k], n] \to [[k]_t, n])$ is a pushout of a disjoint union of $[k + 1] \to [k + 1]_t$, and $j^\omega$ then induces for any $n < \omega$, a left Quillen functor

$$j^{n+1} : \mathrm{tSeg}(\mathrm{tPsh}(\Delta)^n) \to \mathrm{tPsh}(\Delta)^{n+1}.$$

**Proposition 3.3.1.10.** *For any $n \in \mathbb{N} \cup \{\omega\}$, the functor*

$$j^{n+1} : \mathrm{tPsh}(\Delta)^{n+1} \to \mathrm{tSeg}(\mathrm{tPsh}(\Delta)^n)$$

*preserves globes up to isomorphisms.*

*Proof.* This is a direct consequence of the isomorphism $j^{n+1}[K, 1] \cong \Sigma K$ natural in $K$. $\square$

**Theorem 3.3.1.11.** *For all integers $n$, the model structure $\mathrm{tPsh}(\Delta)^n$ for $n$-complicial sets is a model of $(\infty, n)$-categories.*

*Proof.* We will proceed by induction. For the initialization, remark that we have two functors

$$\begin{array}{c c c c c c} i^0 : \mathrm{Psh}(\Delta) & \to & \mathrm{tPsh}(\Delta)^0 & j^0 : \mathrm{tPsh}(\Delta)^0 & \to & \mathrm{Psh}(\Delta) \\ [n] & \mapsto & \tau_0^i[n] & [n], [n]_t & \mapsto & [n] \end{array}$$

which are obviously left Quillen. As we have $j^0 i^0 \cong \mathrm{id}$ and a weakly invertible natural transformation $\mathrm{id} \to i^0 j^0$, these two functors are Quillen equivalences, and $\mathrm{tPsh}(\Delta)^0$ is then a model of $(\infty, 0)$-categories.

Suppose now that $\mathrm{tPsh}(\Delta)^n$ is a model of $(\infty, n)$-categories. Theorem 3.1.3.5 then implies that $\mathrm{tSeg}(\mathrm{tPsh}(\Delta)^n)$ is a model of $(\infty, n + 1)$-categories.

The propositions 3.3.1.7 and 3.3.1.10 state that the left Quillen functor

$$i^\omega j^\omega : \mathrm{tPsh}(\Delta)^\omega \to \mathrm{tPsh}(\Delta)^\omega$$

preserves globes, and the corollary 2.4.4.14 then implies that $i^\omega j^\omega$ is equivalent up to homotopy to the identity. As a consequence, the left Quillen functor

$$i^{n+1} j^{n+1} : \mathrm{tPsh}(\Delta)^{n+1} \to \mathrm{tPsh}(\Delta)^{n+1}$$

is also equivalent up to homotopy to the identity. The proposition 3.3.1.7 and 3.3.1.10 also implies that the composite functor

$$j^{n+1} i^{n+1} : \mathrm{tSeg}(\mathrm{tPsh}(\Delta)^n) \to \mathrm{tSeg}(\mathrm{tPsh}(\Delta)^n)$$

preserves globes. According to the proposition 3.1.3.4, $j^{n+1} i^{n+1}$ is equivalent up to homotopy to the identity. The two functors $i^{n+1}$ and $j^{n+1}$ are then homotopy inverse, and are then both Quillen equivalence. Being equivalent to $\mathrm{tSeg}(\mathrm{tPsh}(\Delta)^n)$, the model category $\mathrm{tPsh}(\Delta)^{n+1}$ is then a model of $(\infty, n + 1)$-categories. $\square$

137