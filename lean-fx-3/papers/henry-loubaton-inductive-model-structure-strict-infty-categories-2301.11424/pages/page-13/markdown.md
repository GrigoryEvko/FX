## 2.3 Tensor Product of $m$-Marked $\infty$-Categories

In this section, we construct two monoidal closed structures on the category of $m$-marked $\infty$-categories, respectively called the *pseudo-Gray* tensor product $\ominus$ and the *lax-Gray* tensor product $\ominus$. Both are obtained by putting different markings on the Gray tensor product from Construction 2.11. For example, the lax-Gray tensor product $\mathbb{D}_1 \ominus \mathbb{D}_1$ is $C_1^*$,

$$C_1 = \begin{pmatrix} \bullet & \longrightarrow & \bullet \\ \downarrow & \swarrow & \downarrow \\ \bullet & \longrightarrow & \bullet \end{pmatrix}$$

while $\mathbb{D}_1 \ominus \mathbb{D}_1$ is the $m$-marked polygraph $(C_1, \overline{D})$, where $D$ only contains the unique 2-dimensional generator of $C_1$. So, unless $m = 0$ or $m = 1$, the two tensor products are distinct. At the derived or homotopy-theoretic level, the pseudo-Gray tensor product should correspond to the Cartesian product.

The formal definition is as follows:

**2.21 Construction.** Given two $m$-marked $\infty$-categories $(X, M)$ and $(Y, N)$, we define two sets of arrows in $X \otimes Y$:

- $M \ominus N$ is the set of arrows of the form $x \otimes y \in X \otimes Y$ where either $x \in M$ or $y \in N$.
- $M \ominus N$ contains all arrows in $M \ominus N$ together with all arrows of the form $x \otimes y$ with $x$ and $y$ both of dimension strictly greater than 0.

Note that $M \ominus N$ and $M \ominus N$ are not markings on $X \otimes Y$: they are not stable under composition. So we define:

$$(X, M) \ominus (Y, N) = (X \otimes Y, \overline{M \ominus N})$$

$$(X, M) \ominus (Y, N) = (X \otimes Y, \overline{M \ominus N})$$

We will show in Lemma 2.42 that both make the category of $m$-marked $\infty$-categories into a monoidal closed category.

In order to show this, it is convenient to introduce the following notations:

**2.22 Notation.** For $A$ and $B$ subsets of arrows in $\infty$-categories, we denote by $A \otimes B$ the set of arrows of the form $a \otimes b \in X \otimes Y$ for $a \in A$ and $b \in B$. For an $\infty$-category $X$, we denote by $X_{\geq 0}$ the set of all arrows of $X$ and by $X_{>0}$ the set of all arrows of dimension strictly greater than 0. We can hence, for $(X, M)$ and $(Y, N)$ two $m$-marked $\infty$-categories, rewrite the definitions above as:

$$\begin{aligned} M \ominus N &= (M \otimes Y_{\geq 0}) \cup (X_{\geq 0} \otimes N) \\ M \ominus N &= (M \ominus N) \cup (X_{>0} \otimes Y_{>0}) \\ &= (M \otimes Y_{\geq 0}) \cup (X_{\geq 0} \otimes N) \cup (X_{>0} \otimes Y_{>0}) \end{aligned}$$

By definition of the Gray tensor product, we have the following result:

**2.23 Lemma.** *Let $X$ and $Y$ be two $\infty$-categories. Then:*

$$\begin{aligned} \overline{X_{\geq 0} \otimes Y_{\geq 0}} &= (X \otimes Y)_{\geq 0} \\ \overline{X_{>0} \otimes Y_{\geq 0} \cup X_{\geq 0} \otimes Y_{>0}} &= (X \otimes Y)_{>0}. \end{aligned}$$

13