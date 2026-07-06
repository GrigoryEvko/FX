2.2. THE COMPLICIAL MODEL

- the *face partition operator*:

$$\begin{array}{rcl} \Pi^1_{p,q} : & [p] & \to & [n] \\ & k & \mapsto & k \end{array} \qquad \begin{array}{rcl} \Pi^2_{p,q} : & [q] & \to & [n] \\ & k & \mapsto & k+p. \end{array}$$

**Definition 2.2.2.2** ([Ver08c, Definition 128]). Let $(X, tX)$ and $(Y, tY)$ be two stratified simplicial sets. We define the *Gray tensor product* of $(X, tX)$ and $(Y, tY)$ as the stratified simplicial set

$$(X, tX) \otimes (Y, tY) := (X \times Y, tX \otimes tY)$$

where $tX \otimes tY$ is the set of pairs $(x, y)$ such that for any partitions $(p, q)$ of $n$ either $\Pi^1_{p,q}x$ or $\Pi^2_{p,q}y$ is thin.

**Remark 2.2.2.3.** Let $X, Y$ be two stratified simplicial sets such that all simplices of $X$ are thin. The morphism $X \otimes Y \to X \times Y$ is then an isomorphism.

**2.2.2.4.** In [Ver08c], it is shown that the Gray tensor is associative. The problem of this operation comes from the fact that it doesn't commute with colimits. Verity then defines an other binary operation, which is cocontinuous, the *Gray pretensor* ([Ver08c, definition 135]) $(X, tX) \boxtimes (Y, tY) := (X \times Y, tX \boxtimes tY)$, together with a natural transformation:

$$\_ \boxtimes \_ \to \_ \otimes \_$$

that is pointwise an entire acyclic cofibration ([Ver08b, lemma 149]). Moreover, in [ORV20], it is shown that this pretensor is a Quillen bifunctor for the model structure on $\text{tPsh}(\Delta)$.

**Definition 2.2.2.5** (Gray tensor product for marked simplicial sets). Let $X$ and $Y$ be two marked simplicial sets. We define the *Gray tensor product* of $X$ and $Y$ as the marked simplicial set

$$X \otimes Y := (\iota(X) \otimes \iota(Y))_{\text{mk}}$$

where $((\_)_{\text{mk}}, \iota)$ is the adjunction 2.2.1.8. As $\_ \boxtimes \_ \to \_ \otimes \_$ is pointwise a entire acyclic cofibration, we have an equality:

$$X \otimes Y := (\iota(X) \boxtimes \iota(Y))_{\text{mk}}.$$

**Proposition 2.2.2.6.** *We have equalities*

$$(\_ \boxtimes \_)_{\text{mk}} = (\_ \otimes \_)_{\text{mk}} = (\_)_{\text{mk}} \otimes (\_)_{\text{mk}}.$$

77