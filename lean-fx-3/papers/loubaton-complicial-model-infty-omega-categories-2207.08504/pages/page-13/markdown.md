1.1. BASIC CONSTRUCTIONS

## 1.1 Basic constructions

### 1.1.1 $(0, \omega)$-Categories

Definition 1.1.1.1. A globular set is a presheaf on the category of globes G, which is the category induces by the diagram

$$\mathbf{D}_0 \xrightarrow[i_0]{i_0^+} \mathbf{D}_1 \xrightarrow[i_1]{i_1^+} \mathbf{D}_2 \xrightarrow[i_2]{i_2^+} \dots$$

with the relations $i_n^+ i_{n-1}^\epsilon = i_n^- i_{n-1}^\epsilon$ for any $n > 0$ and $\epsilon \in \{+, -\}$. For any $n > k$ and $\epsilon \in \{+, -\}$, we also denote by $i_k^\epsilon$ the composite $\mathbf{D}_k \xrightarrow{i_k} \mathbf{D}_{k+1} \xrightarrow{f} \mathbf{D}_n$ where $f$ is any map. These and the identity arrows are the only maps in the category G.

If $X$ is a globular set, we denote by $X_n$ the set $X(\mathbf{D}_n)$. Its elements are called $n$-cells. The 0-cells are sometimes called objects. The maps $X_n \to X_k$ induced by $i_k^\epsilon : \mathbf{D}_k \to \mathbf{D}_n$ is denoted by $\pi_k^\epsilon$.

Definition 1.1.1.2. An $\omega$-category is a globular set $X$ together with

(1) operations of compositions

$$X_n \times_{X_k} X_n \to X_n \quad (0 \le k < n)$$

which associate to two $n$-cells $(x, y)$ verifying $\pi_k^-(x) = \pi_k^+(y)$, a $n$-cells $x \circ_k y$,

(2) as well as units

$$X_n \to X_{n+1}$$

which associate to an $n$-cell $x$, a $(n+1)$-cell $\mathbb{I}_x$,

and satisfying the following axioms:

(1) \(\forall x\in X_n,\pi_n^\epsilon (\mathbb{I}_x) = x.\)
(2) \(\pi_k^+(x\circ_n y) = \pi_k^+(x)\) and \(\pi_k^-(x\circ_n y) = \pi_k^-(y)\) whenever the composition is defined and \(k\leqslant n\)
(3) \(\pi_k^\epsilon (x\circ_n y) = \pi_k^\epsilon (x)\circ_n\pi_k^\epsilon (y)\) whenever the composition is defined and \(k > n\)
(4) \(x\circ_{n}\mathbb{I}_{\pi_{n}^{-}x} = x\) and \(\mathbb{I}_{\pi_n^+ x}\circ_n x = x.\)
(5) \((x\circ_{n}y)\circ_{n}z = x\circ_{n}(y\circ_{n}z)\) as soon as one of these is defined.
(6) If \( k < n \)

$$(x \circ_n y) \circ_k (z \circ_n w) = (x \circ_k z) \circ_n (y \circ_k w)$$

when the left-hand side is defined.

A $n$-cell $a$ is non trivial if is not in the image of the application $\mathbb{I} : X_{n-1} \to X_n$.

A morphism of $\omega$-categories is a map of globular sets commuting with compositions and units. The category of $\omega$-categories is denoted by $\omega$-cat.

Definition 1.1.1.3. By abuse of notation, we also denote by $\mathbf{D}_n$ the $\omega$-category that admits for any $k < n$ only two $k$-non-trivial cells, denoted by $e_k^-$ and $e_k^+$, and a single $n$-non-trivial cell, denoted by $e_n$ verifying :

$$\pi_l^-(e_k^\epsilon) = e_l^- \quad \pi_l^+(e_k^\epsilon) = e_l^+ \quad \text{for } l \le k < n$$

$$\pi_l^-(e_n) = e_l^- \quad \pi_l^+(e_n) = e_l^+ \quad \text{for } l \le n$$

13