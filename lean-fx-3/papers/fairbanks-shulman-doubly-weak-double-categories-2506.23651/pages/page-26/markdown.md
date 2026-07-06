26

AARON DAVID FAIRBANKS AND MICHAEL SHULMAN

defined in Section 2, so the monad is the same as $T_2^1$ constructed above whose category of algebras is **I-2-Cat**.

Similarly, the free double category monad on $1 \vee 1$-**CatDblGph** (double graphs equipped with horizontal and vertical 1-category structure) restricts to the subcategory **DblCptd** (double graphs equipped with free 1-category structure and maps sending generating 1-cells to generating 1-cells). This induced monad on **DblCptd** is $T_{\mathbf{d}}^1$, whose category of algebras is **IDblCat**.

To upgrade these to definitions of bicategories and doubly weak double categories, we need only introduce the following additional operations.

**Definition 5.4.** A **represented** implicit 2-category $X$ is equipped with

- 1-cell composition 2-cells

$$X(1) \times_0 X(1) \rightarrow X(2_1^2) \quad \text{and} \quad X(1) \times_0 X(1) \rightarrow X(2_2^1)$$

(where the domain is length 2 paths of 1-cells) and

- 1-cell identity 2-cells

$$X(0) \rightarrow X(2_1^0) \quad \text{and} \quad X(0) \rightarrow X(2_0^1)$$

satisfying laws that ensure these 2-cells form inverse pairs from and to the given 1-cell paths.

Similarly, a **represented** implicit double category $X$ is equipped with

- 1-cell composition 2-cells

$$\begin{aligned} X(1^H) \times_0 X(1^H) &\rightarrow X(2_{0,1}^{2,0}), & X(1^H) \times_0 X(1^H) &\rightarrow X(2_{0,2}^{1,0}), \\ X(1^V) \times_0 X(1^V) &\rightarrow X(2_{2,0}^{0,1}), & X(1^V) \times_0 X(1^V) &\rightarrow X(2_{1,0}^{0,2}) \end{aligned}$$

(where the domains are length 2 paths of horizontal or vertical 1-cells) and

- 1-cell identity creation 2-cells

$$\begin{aligned} X(0) &\rightarrow X(2_{0,1}^{0,0}), & X(0) &\rightarrow X(2_{0,0}^{1,0}), \\ X(0) &\rightarrow X(2_{0,0}^{0,1}), & X(0) &\rightarrow X(2_{1,0}^{0,0}) \end{aligned}$$

satisfying laws that ensure these 2-cells form inverse pairs from and to the given 1-cell paths.

In Sections 2 and 3 respectively we characterized bicategories and doubly weak double categories as represented implicit 2-categories and double categories. Hence, by the above algebraic definitions:

**Proposition 5.5.** *The category $\mathbf{W-2-Cat_{st}}$ of bicategories and strict functors is monadic over the category 2-Cptd of 2-computads.*

*Likewise, the category $\mathbf{WDblCat_{st}}$ of doubly weak double categories and strict functors is monadic over the category DblCptd of double computads.* $\square$

Now by the cancellation lemma (Lemma 4.3), since **I-2-Cat** is also monadic over **2-Cptd**, we have that $\mathbf{W-2-Cat_{st}}$ is furthermore monadic over **I-2-Cat**; similarly, $\mathbf{WDblCat_{st}}$ is monadic over **IDblCat**. However, let us also say how to *present* these monads on **I-2-Cat** and **IDblCat**; we do this because in the next section, we will obtain 2-monads from the same presentations.

Since the category of algebras for a finitary monad on an l.f.p. category is again l.f.p., we can just apply the machinery of presentations of monads again with $\mathcal{H} =$