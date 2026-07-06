where the left morphism corresponds to the top arrow of the $n^{th}$ orientals, and the right morphism is in $M$. We can now extend the strictification functor to stratified simplicial sets:

$$\begin{array}{rcl} |-|: & \mathbf{Strat} & \rightarrow & \infty\text{-}\mathbf{Cat}^{+m} \\ & (K, M) & \mapsto & (|K|, \overline{|M|}) \end{array}$$

This functor is cocontinuous and induces an adjunction:

$$\mathbf{Strat} \xleftarrow[\downarrow]{\perp} \infty\text{-}\mathbf{Cat}^{+m}$$

The right adjoint is called the *stratified Street nerve*.

**4.53 Remark.** In the case $m = \infty$, this adjunction models the forgetful functor from strict $\infty$-categories to weak $(\infty, \infty)$-categories (given by the stratified Street nerve $N$). The left adjoint corresponds to the “strictification functor” that sends a weak $(\infty, \infty)$-category to a strict $\infty$-category in a universal way.

**4.54 Proposition.** *The stratified Street nerve sends fibrant objects of $\infty\text{-}\mathbf{Cat}_{Sat\text{-}Ind}^{+m}$ to fibrant objects of $\mathbf{Strat}_V^{+m}$.*

*Proof.* Suppose first that $m < \infty$ and let $(X, M)$ be a fibrant $m$-marked $\infty$-category for the saturated inductive left semi-model structure. According to Corollary 4.30, $M$ consists of coinductively invertible arrows of $X$, and $N((X, M))$ is equal to the stratified simplicial set associated with the Street nerve of $X$ defined in [32, Définition 5.2.1]. Theorem 5.2.12 of *op. cit.* then implies that the stratified Street nerve sends fibrant objects of the saturated inductive left semi-model structure on $\infty\text{-}\mathbf{Cat}^{+m}$ to $m$-complicial sets.

Now, let $C$ be a fibrant $\infty$-marked $\infty$-category for the saturated inductive left semi-model structure. As the stratified Street nerve preserves directed colimits, there is an isomorphism

$$N(C) \cong \operatorname{Colim}_{n \in \mathbb{N}} N(\tau_n C)$$

For all $n$, $\tau_n C$ is fibrant for the saturated inductive left semi-model structure for $n$-marked $\infty$-categories, and $N(\tau_n C)$ is then a fibrant object of the model structure for $n$-complicial sets. As the model structure for $\infty$-complicial sets is $\omega$-combinatorial, fibrant objects are stable under directed colimits, and $N(C)$ is fibrant. $\square$

**4.55 Lemma.** *Let $(K, M)$ be a stratified simplicial set and $L$ a simplicial set. We denote $N$ the set of degenerate simplices of $L$. There exists an isomorphism*

$$|(K, M) \star (L, N)| \cong |(K, M)| \star |(L, N)|$$

*natural in $K$ and $L$.*

*Proof.* Proposition 7.13 of [6] provides a natural isomorphism $|K \star L| \cong |K| \star |L|$. Moreover, Lemma 2.24 implies that $\overline{|M| \star |N|} = \overline{|M| \star |N|}$. Since we have $|(K, M) \star (L, N)| \cong (|K \star L|, \overline{|M \star N|})$ and $(|K| \star |L|, \overline{|M| \star |N|})$, this concludes the proof. $\square$

55