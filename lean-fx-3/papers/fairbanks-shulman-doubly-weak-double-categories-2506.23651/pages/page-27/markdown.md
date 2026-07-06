DOUBLY WEAK DOUBLE CATEGORIES

27

**I-2-Cat** and **IDblCat**. Thus, considering the double case explicitly for concreteness and variety, we start with $A \in [\text{ob IDblCat}_f, \text{IDblCat}]$ defined by

$$A(c) = \begin{cases} 2_{0,1}^{2,0} \sqcup 2_{0,2}^{1,0} & \text{if } c = 1^H \sqcup_0 1^H \\ 2_{2,0}^{0,1} \sqcup 2_{1,0}^{0,2} & \text{if } c = 1^V \sqcup_0 1^V \\ 2_{0,1}^{0,0} \sqcup 2_{0,0}^{1,0} \sqcup 2_{0,0}^{0,1} \sqcup 2_{1,0}^{0,0} & \text{if } c = 0 \end{cases}$$

where we implicitly identify the representable objects in **DblCptd** with their images under the free functor in **IDblCat**. Then an $FA$-algebra is an implicit double category equipped with the 1-cell composition and identity creation 2-cell operations as specified above. We then describe another $B \in [\text{ob IDblCat}_f, \text{IDblCat}]$ with two maps $B \Rightarrow UFA$ and consider the coequalizer in $\text{Mnd}_f(\text{IDblCat})$ of the induced parallel pair $FB \Rightarrow FA$, to obtain a monad $T_4^\text{w}$ on **IDblCat** whose algebras are represented implicit double categories. Similarly, we get a monad $T_2^\text{w}$ on **I-2-Cat** whose algebras are represented implicit 2-categories.

We can also describe the free algebras of these monads more directly.

**Proposition 5.6.** *The free bicategory on an implicit 2-category $\mathbf{X}$ admits the following description.*

- *Its 0-cells are those of $\mathbf{X}$.*
- *Its 1-cells are freely generated from those of $\mathbf{X}$ by binary composition and identities.*
- *Its 2-cells with a given boundary are those in $\mathbf{X}$ with boundary given by erasing parentheses and identities, with composition as in $\mathbf{X}$.*

*Similarly, the free doubly weak double category on an implicit double category $\mathbf{X}$ admits the following description.*

- *Its 0-cells are those of $\mathbf{X}$.*
- *Its 1-cells of both sorts are freely generated from those of $\mathbf{X}$ by binary composition and identities.*
- *Its 2-cells with a given boundary are those in $\mathbf{X}$ with boundary given by erasing parentheses and identities, with composition as in $\mathbf{X}$.*

*Proof.* We describe the 2-category case; the double-category case is similar. First note that given a path $f_1, \dots, f_n$ from $A$ to $B$ in an implicit 2-category $\mathbf{X}$, the implicit 2-category obtained from $\mathbf{X}$ by freely adjoining a 1-cell $f: A \to B$ and an isomorphism $f_1, \dots, f_n \cong f$ is described as follows: its 0-cells and 1-cells are those of $\mathbf{X}$ plus the 1-cell $f$, and the 2-cells in $\mathbf{X}'$ with a given boundary are those in $\mathbf{X}$ with boundary obtained by replacing all occurrences of $f$ with $f_1, \dots, f_n$. It is easy to verify this implicit 2-category satisfies the claimed universal property. Similarly, we can adjoin any number of such 1-cells with isomorphisms.

Now the free represented implicit 2-category (equivalently, bicategory) on an implicit 2-category defined as in **Definition 5.4** is a sequential colimit of such steps of adjoining isomorphisms. Specifically, starting from $\mathbf{X}_0 = \mathbf{X}$, we adjoin a 1-cell as above for *every* path in $\mathbf{X}_0$ of length 2 or 0, obtaining a new implicit 2-category $\mathbf{X}_1$. We then repeat for every path of length 2 or 0 in $\mathbf{X}_1$, obtaining $\mathbf{X}_2$, and so on. This yields a chain of inclusions

$$\mathbf{X}_0 \to \mathbf{X}_1 \to \mathbf{X}_2 \to \dots .$$

Since the monad on 2-computads for implicit 2-categories is finitary, the colimit $\mathbf{X}_\infty$ of this chain in **I-2-Cat** is its colimit in **2-Cptd** equipped with the evident