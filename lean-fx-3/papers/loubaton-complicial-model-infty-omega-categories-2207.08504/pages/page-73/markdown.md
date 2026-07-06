2.2. THE COMPLICIAL MODEL

**Definition 2.2.2.6.** Let $X$ and $Y$ be two marked simplicial sets. We define the *Gray tensor product* of $X$ and $Y$ as the marked simplicial set

$$X \otimes Y := (\iota(X) \otimes \iota(Y))_{\mathrm{mk}}$$

where $(\iota_{(\underline{\quad})}_{\mathrm{mk}}, \iota)$ is the adjunction 2.2.1.12. As $\_ \boxtimes \_ \to \_ \otimes \_$ is pointwise a entire acyclic cofibration, we have an equality:

$$X \otimes Y := (\iota(X) \boxtimes \iota(Y))_{\mathrm{mk}}.$$

**Proposition 2.2.2.7.** *We have equalities*

$$(\_ \boxtimes \_)_{\mathrm{mk}} = (\_ \otimes \_)_{\mathrm{mk}} = (\_)_{\mathrm{mk}} \otimes (\_)_{\mathrm{mk}}.$$

*Proof.* The first equality is a consequence of the fact that $\_ \boxtimes \_ \to \_ \otimes \_$ is pointwise a entire acyclic cofibration.

For the second one, we have to show that $(X \otimes Y)_{\mathrm{mk}} = (\iota(X_{\mathrm{mk}}) \otimes \iota(Y_{\mathrm{mk}}))_{\mathrm{mk}}$. The unit of the adjunction $(\iota, (\_)_{\mathrm{mk}})$ induces a morphism $h : (X \otimes Y)_{\mathrm{mk}} \to (\iota(X_{\mathrm{mk}}) \otimes \iota(Y_{\mathrm{mk}}))_{\mathrm{mk}}$. This morphism is an entire acyclic cofibration according to proposition 2.1.2.11, and the corollary 2.2 of [ORV20] and the fact that $(\_)_{\mathrm{mk}}$ is a left Quillen functor.

We then have lifts in the following diagram:

$$\begin{array}{c} (X \otimes Y)_{\mathrm{mk}} \xrightarrow{id} (X \otimes Y)_{\mathrm{mk}} \\ h \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ (\iota(X_{\mathrm{mk}}) \otimes \iota(Y_{\mathrm{mk}}))_{\mathrm{mk}} \end{array}$$

As both $k$ and $h$ are the identity on the underlying simplicial sets, this implies that the stratifications of $(X \otimes Y)_{\mathrm{mk}}$ and $(X \otimes Y)_{\mathrm{mk}}$ coincide, and this two objects are then equal.

We can then deduce the following proposition:

**Proposition 2.2.2.8.** *The Gray tensor product is associative, and is a left Quillen bifunctor in $\mathrm{mPsh}(\Delta)$.*

*Proof.* The first assertion is a consequence of proposition 2.2.2.7 and the fact that the binary operation $\otimes$ on $\mathrm{tPsh}(\Delta)$ is associative. The second one is a consequence of proposition 2.2.2.7 and [ORV20, Theorem 2.1].

**Construction 2.2.2.9.** Let $X$ be a marked simplicial set. We define the *suspension* of $X$, noted by $\Sigma X$, as the following pushout:

$$\begin{array}{c} X \otimes \partial[1] \longrightarrow X \otimes [1] \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \partial[1] \longrightarrow \Sigma X \end{array}$$

This assignation defines a cocontinuous functor $\Sigma : \mathrm{mPsh}(\Delta) \to \mathrm{mPsh}(\Delta)_{\partial[1]}$. For every acyclic cofibration $K \to L$, we have cartesian squares

$$\begin{array}{c} L \otimes \partial[1] \longrightarrow K \otimes [1] \cup L \otimes \partial[1] \longrightarrow L \otimes [1] \\ \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \partial[1] \longrightarrow \Sigma K \longrightarrow \Sigma L \end{array}$$

73