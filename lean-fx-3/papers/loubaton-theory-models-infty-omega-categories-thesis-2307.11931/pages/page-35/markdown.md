1.1. BASIC CONSTRUCTIONS

**Theorem 1.2.3.13.** *In the category of $(0, \omega)$-categories, there exists an isomorphism, natural in $A$, between $[A, 1] \otimes [1]$ and the colimit of the following diagram*

$$[1] \vee [A, 1] \xleftarrow{\triangledown} [A \otimes \{0\}, 1] \longrightarrow [A \otimes [1], 1] \longleftarrow [A \otimes \{1\}, 1] \xrightarrow{\triangledown} [A, 1] \vee [1]$$

We also provide similar formulas for the *Gray cone* and the *Gray $\circ$-cone*.

**Theorem 1.2.3.14.** *There is a natural identification between $1 \stackrel{\circ\circ}{\star} [A, 1]$ and the colimit of the following diagram*

$$[1] \vee [A, 1] \xleftarrow{\triangledown} [A, 1] \longrightarrow [A \star 1, 1]$$

*There is a natural identification between $[A, 1] \star 1$ and the colimit of the following diagram*

$$[1 \stackrel{\circ\circ}{\star} A, 1] \longleftarrow [A, 1] \xrightarrow{\triangledown} [A, 1] \vee [1]$$

## 1.1 Basic constructions

### 1.1.1 $(0, \omega)$-Categories

**1.1.1.1.** A *globular set* is a presheaf on the *category of globes* G, which is the category induces by the diagram

$$\mathbf{D}_0 \xrightarrow[i_0]{i_0^+} \mathbf{D}_1 \xrightarrow[i_1]{i_1^+} \mathbf{D}_2 \xrightarrow[i_2]{i_2^+} \dots$$

with the relations $i_n^+ i_{n-1}^\epsilon = i_n^- i_{n-1}^\epsilon$ for any $n > 0$ and $\epsilon \in \{+, -\}$. We also denote by $i_k^\epsilon$ the map $\mathbf{D}_k \to \mathbf{D}_n$ for $k < n$ obtained by composing any string of arrows ending with $i_k^\epsilon$. These and the identity arrows are the only maps in the category G.

If $X$ is a globular set, one denotes by $X_n$ the set $X(\mathbf{D}_n)$. Its elements are called *n-cells*. The 0-cells are sometimes called *objects*. The maps $X_n \to X_k$ induced by $i_k^\epsilon : \mathbf{D}_k \to \mathbf{D}_n$ is denoted by $\pi_k^\epsilon$.

# **1.1.1.2.** An $\omega$-*category* is a globular set $X$ together with

(1) operations of *compositions*

$$X_n \times_{X_k} X_n \to X_n \quad (0 \le k < n)$$

which associate to two $n$-cells $(x, y)$ verifying $\pi_k^-(x) = \pi_k^+(y)$, a $n$-cells $x \circ_k y$,

25