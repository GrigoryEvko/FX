2.2. THE COMPLICIAL MODEL

Proof. Let $C^{\natural}$ and $D^{\natural}$ be the underlying simplicial sets of $C$ and $D$. Remark first that the two vertical morphisms of the first square are the identity. The induced morphism

$$\coprod_{n} \tau_{n}^{i}(\tau_{n}C \otimes \tau_{n}D) \coprod_{\coprod_{n} \tau_{n}C \otimes \tau_{n}D} C \otimes D \to C \times D \tag{2.2.2.9}$$

is then the identity of $C^{\natural} \times D^{\natural}$ at the level of underlying simplicial sets. To conclude, one has to show that every simplex $C^{\natural} \times D^{\natural}$ that is marked in the right term of (2.2.2.9) is also marked in the left term. For this, let $n$ be a non negative integer, $x \in C_{k}^{\natural}$ and $y \in D_{k}^{\natural}$, such that $x$ is marked in $C$ and $y$ is marked in $D$. The $k$-simplex $(x, y)$ then is in the image of $\tau_{k-1}^{i}(\tau_{k-1}C \otimes \tau_{k-1}D)$ and is then marked in the left term of (2.2.2.9). This concludes the proof of the first assertion.

The two vertical morphisms of the second square also are the identity and the induced morphism

$$\coprod_{n} \tau_{n+1}^{i}(\tau_{n}C \otimes D) \coprod_{\coprod_{n} \tau_{n}C \otimes D} C \otimes D \to C \otimes \tau_{1}^{i}D \tag{2.2.2.10}$$

is then once again the identity of $C^{\natural} \times D^{\natural}$ at the level of underlying simplicial sets. Unfolding the definition, the marking of the left term is the smaller one that includes the one of $C \otimes D$ and every $k$-simplex $(x, y)$ such that both $x$ and $d^{k}x$ are marked in $C$.

Let $(x, y)$ be a $k$-simplex of $C^{\natural} \times D^{\natural}$. Suppose first that it is marked in $C \otimes D$. Remark that $(x, y)$ is then marked in $\tau_{k}C \otimes D$, and so is in the left term of (2.2.2.10). Suppose now that both $x$ and $d^{k}x$ are marked in $C$. This implies that $s^{k-1}d^{k}x$ is in the image of $\tau_{k-1}C$. The simplex $(s^{k-1}d^{k}x, y)$ is then in the image of $\tau_{k}^{i}(\tau_{k-1}C \otimes D)$ and is then marked in the left term of (2.2.2.10).

Now remark that we have

$$d^{k-1}(s^{k-1}x, s^{k}y) = (x, s^{k-1}d^{k-1}y) \qquad d^{k}(s^{k-1}x, s^{k}y) = (x, y)$$

$$d^{k+1}(s^{k-1}x, s^{k}y) = (s^{k-1}d^{k}x, y)$$

and both the $(k-1)$ and $(k+1)$ faces of $(s^{k-1}x, s^{k}y)$ are marked. We leave it to the reader to check that by definition every sub $l$-simplex $z$ of $(s^{k-1}x, s^{k}y)$ containing the points $k-1$, $k$ and $k+1$ is marked in $C \otimes D$, and so in $\tau_{k}C \otimes D$, and, therefore, in the left term of (2.2.2.10). As the marking is stable by complicial thinness extension, this implies that $(x, y)$ is also marked in the left term of (2.2.2.10).

The marking of the right term of (2.2.2.10) is then included in the marking of the left term. They then coincide, which concludes the proof. $\square$

Remark 2.2.2.11. The reason for including the assumption that $D$ is invariant under $\tau_{2}^{i}$ is solely because it will be the only relevant case. If we remove this assumption, the statement remains true, but the proof becomes a little bit more technical.

79