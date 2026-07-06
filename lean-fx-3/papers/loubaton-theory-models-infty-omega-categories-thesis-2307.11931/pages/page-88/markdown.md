CHAPTER 2. STUDY OF THE COMPLICIAL MODEL

Proof. The first equality is a consequence of the fact that $\_ \boxtimes \_ \to \_ \otimes \_$ is pointwise a entire acyclic cofibration.

For the second one, we have to show that $(X \otimes Y)_{\mathrm{mk}} = (\iota(X_{\mathrm{mk}}) \otimes \iota(Y_{\mathrm{mk}}))_{\mathrm{mk}}$. The unit of the adjunction $(\iota, (\_)_{\mathrm{mk}})$ induces a morphism $h : (X \otimes Y)_{\mathrm{mk}} \to (\iota(X_{\mathrm{mk}}) \otimes \iota(Y_{\mathrm{mk}}))_{\mathrm{mk}}$. This morphism is an entire acyclic cofibration according to proposition 2.1.2.9, and the corollary 2.2 of [ORV20] and the fact that $(\_)_{\mathrm{mk}}$ is a left Quillen functor.

We then have lifts in the following diagram:

$$\begin{array}{ccc} (X \otimes Y)_{\mathrm{mk}} & \xrightarrow{id} & (X \otimes Y)_{\mathrm{mk}} \\ \downarrow \quad \searrow \quad \searrow \\ (\iota(X_{\mathrm{mk}}) \otimes \iota(Y_{\mathrm{mk}}))_{\mathrm{mk}} & & \end{array}$$

As both $k$ and $h$ are the identity on the underlying simplicial sets, this implies that the stratifications of $(X \otimes Y)_{\mathrm{mk}}$ and $(X \otimes Y)_{\mathrm{mk}}$ coincide, and this two objects are then equal. $\square$

We can then deduce the following proposition:

**Proposition 2.2.2.7.** *The Gray tensor product is associative, and is a left Quillen bifunctor in $\mathrm{mPsh}(\Delta)$.*

Proof. The first assertion is a consequence of proposition 2.2.2.6 and the fact that the binary operation $\otimes$ on $\mathrm{tPsh}(\Delta)$ is associative. The second one is a consequence of proposition 2.2.2.6 and [ORV20, Theorem 2.1]. $\square$

We now give a lemma investigating the interaction between the truncation, the intelligent truncation and the Gray tensor product.

**Lemma 2.2.2.8.** *Let $C$ and $D$ be two stratified simplicial sets.*

(1) *The following canonical square is cocartesian*

$$\begin{array}{ccc} \coprod_n \tau_n C \otimes \tau_n D & \longrightarrow & C \otimes D \\ \downarrow & & \downarrow \\ \coprod_n \tau_n^i (\tau_n C \otimes \tau_n D) & \longrightarrow & C \times D \end{array}$$

(2) *If $D$ is invariant under $\tau_2^i$, the following canonical square is cocartesian*

$$\begin{array}{ccc} \coprod_n \tau_n C \otimes D & \longrightarrow & C \otimes D \\ \downarrow & & \downarrow \\ \coprod_n \tau_{n+1}^i (\tau_n C \otimes D) & \longrightarrow & C \otimes \tau_1^i D \end{array}$$

78