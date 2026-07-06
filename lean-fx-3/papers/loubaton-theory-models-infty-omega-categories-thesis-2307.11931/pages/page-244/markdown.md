CHAPTER 5. THE \((\infty,1)\)-CATEGORY OF MARKED \((\infty,\omega)\)-CATEGORIES

and by whiskering with (possibly unmarked) cells of lower dimension. A $n$-cell $a : \mathbf{D}_n \to (C, tC)$ is marked if it belongs to $tC_n$.

A marked morphism $f : (C, tC) \to (D, tT)$ is the data of a morphism on the underlying $(0, \omega)$-categories such that $f(tC_n) \subset tD_n$. The category of marked $(0, \omega)$-categories is denoted by $(0, \omega)$-cat$_\text{m}$.

5.1.1.2. There are two canonical ways to mark an $(0, \omega)$-category. For $C \in (0, \omega)$-cat, we define $C^\sharp := (C, (C_n)_{n>0})$ and $C^\flat := (C, (\mathbb{I}(C_{n-1})_{n>0}))$. The first one corresponds to the case where all cells are marked, and the second one where only the identities are marked. These two functors fit in the following adjoint triple:

$$(\_)^\flat : (0, \omega)\text{-cat} \xrightarrow{\perp} (0, \omega)\text{-cat}_\text{m} : (\_)^\sharp \qquad (\_)^\sharp : (0, \omega)\text{-cat}_\text{m} \xrightarrow{\perp} (0, \omega)\text{-cat} : (\_)^\sharp$$

where $(\_)^\sharp$ is the obvious forgetfull functor. To simplify notations, for a marked $(0, \omega)$-category $C$, the marked $(\infty, \omega)$-categories $(C^\sharp)^\flat$ and $(C^\sharp)^\sharp$ will be simply denoted by $C^\flat$ and $C^\sharp$.

Example 5.1.1.3. For $n$ an integer, we denote by $(\mathbf{D}_n)_t$ the marked $(0, \omega)$-category whose underlying $(0, \omega)$-category is $\mathbf{D}_n$ and whose only non-trivial marked cell is the top dimensional one.

Definition 5.1.1.4. We define the category $t\Theta$ as the full subcategory of $(0, \omega)$-cat$_\text{m}$ whose objects are of shape $a^\flat$ for $a$ a globular sum, or $(\mathbf{D}_n)_t$ for an integer $n \in \mathbb{N}$. Remark that this subcategory is dense in $(0, \omega)$-cat$_\text{m}$.

5.1.1.5. We define the $(\infty, 1)$-category of stratified $\infty$-presheaves on $\Theta$, noted by tPsh$^\infty(\Theta)$, as the full sub $(\infty, 1)$-category of Psh$^\infty(t\Theta)$ whose objects correspond to $\infty$-presheaves $X$ such that the induced morphism $X((\mathbf{D}_n)_t) \to X(\mathbf{D}_n)$ is a monomorphism.

Proposition 5.1.1.6. The $(\infty, 1)$-category tPsh$^\infty(\Theta)$ is locally cartesian closed.

Proof. The $(\infty, 1)$-category tPsh$^\infty(\Theta)$ is the localization of the $(\infty, 1)$-category Psh$^\infty(t\Theta)$ along the set of map $\widehat{I}$ with

$$I := \{(\mathbf{D}_n)_t \coprod_{\mathbf{D}_n} (\mathbf{D}_n)_t \to (\mathbf{D}_n)_t\}_n.$$

As Psh$^\infty(t\Theta)$ is locally cartesian closed, we have to show that for any integer $n > 0$ and any cartesian square in Psh$^\infty(t\Theta)$:

$$\begin{array}{c} X' \xrightarrow{\quad} X \\ \downarrow \quad \downarrow \\ (\mathbf{D}_n)_t \coprod_{\mathbf{D}_n} (\mathbf{D}_n)_t \longrightarrow (\mathbf{D}_n)_t \end{array}$$

234