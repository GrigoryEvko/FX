CHAPTER 2. STUDY OF COMPLICIAL SETS

The intelligent $n$-truncation is then a left Quillen functor.

It's associated right adjoint is called the $n$-truncation and is denoted by

$$\tau_n : \mathrm{mPsh}(\Delta) \to \mathrm{mPsh}(\Delta).$$

### 2.2.2 Gray operations on marked simplicial sets

Construction 2.2.2.1 (Verity). For any $n, p, q \ge 0$ such that $n = p + q$, we define:

- the degeneration partition operator:

$$\begin{array}{rcll} \Pi^1_{p,q} : & [n] & \to & [p] \\ & k & \mapsto & k \quad \text{if } k \le p \\ & k & \mapsto & p \quad \text{if } k > p \end{array} \qquad \qquad \begin{array}{rcll} \Pi^2_{p,q} : & [n] & \to & [q] \\ & k & \mapsto & 0 \quad \text{if } k \le p \\ & k & \mapsto & k - p \quad \text{if } k > p. \end{array}$$

- the face partition operator:

$$\begin{array}{rcl} \Pi^1_{p,q} : & [p] & \to & [n] \\ & k & \mapsto & k \end{array} \qquad \qquad \begin{array}{rcll} \Pi^2_{p,q} : & [q] & \to & [n] \\ & k & \mapsto & k + p. \end{array}$$

Definition 2.2.2.2 (Verity). Let $(X, tX)$ and $(Y, tY)$ be two stratified simplicial sets. We define the Gray tensor product of $(X, tX)$ and $(Y, tY)$ as the stratified simplicial set

$$(X, tX) \otimes (Y, tY) := (X \times Y, tX \otimes tY)$$

where $tX \otimes tY$ is the set of pairs $(x, y)$ such that for any partitions $(p, q)$ of $n$ either $\Pi^1_{p,q}x$ or $\Pi^2_{p,q}y$ is thin.

Remark 2.2.2.3. Let $X, Y$ be two stratified simplicial sets such that all simplices of $X$ are thin. The morphism $X \otimes Y \to X \times Y$ is then an isomorphism.

Proposition 2.2.2.4. There is a canonical isomorphism

$$(X \otimes Y)^{\mathrm{op}} \cong Y^{\mathrm{op}} \otimes X^{\mathrm{op}}$$

natural in $X$ and $Y$.

Proof. At the level of simplicial sets, this two objects are obviously isomorphic in a unique way. It is sufficient to check that the unique isomorphism preserves the marking, which is left to the reader. $\square$

Remark 2.2.2.5. In [Ver08c], it is shown that the Gray tensor is associative. The problem of this operation comes from the fact that it doesn't commute with colimits. Verity then defines an other binary operation, which is cocontinuous, the Gray pretensor ([Ver08c, definition 135]) $(X, tX) \boxtimes (Y, tY) := (X \times Y, tX \boxtimes tY)$, together with a natural transformation:

$$\_ \boxtimes \_ \to \_ \otimes \_$$

that is pointwise an entire acyclic cofibration ([Ver08b, lemma 149]). Moreover, in [ORV20], it is shown that this pretensor is a Quillen bifunctor for the model structure on $\mathrm{tPsh}(\Delta)$.

72