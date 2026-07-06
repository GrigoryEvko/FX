**Lemma 6.2.8.** Let $\mathsf{A}$ be an Eilenberg–Zilber category. Then for all $f: X \to Y$ in $\mathsf{Set}^{\mathsf{A}^{\mathrm{op}}}$ each relative latching map $\widehat{\ell}_a f$ is a monomorphism if and only if each component $f_a: X_a \hookrightarrow Y_a$ is a monomorphism, and either hypothesis implies that for each $a \in \mathsf{A}$, the latching square below is a pullback:

$$\begin{array}{ccc} L_a X & \xrightarrow{L_a f} & L_a Y \\ \downarrow & \downarrow & \downarrow \\ X_a & \xrightarrow{f_a} & Y_a. \end{array}$$

*Proof.* When $f: X \to Y$ is a monomorphism, each map in the latching square is a monomorphism, and it is easy to see that the latching square is a pullback. It suffices to show that $L_a X$ surjects onto the pullback $X_a \times_{Y_a} L_a Y$. If the image of $x \in X_a$ is degenerate, with $f(x) = y' \cdot \epsilon$, then we may choose a section $\delta$ of $\epsilon$ and observe that $x$ and $x \cdot \delta \cdot \epsilon$ have the same image under $f$, proving that $x$ is degenerate. Thus the latching square is a pullback and then the relative latching map is a monomorphism, the union of the subobjects of $Y_a$.

The converse implication holds for general Reedy categories without the Eilenberg–Zilber hypothesis [Rie, §8].

Lemma 6.2.8 may be summarized by saying that when $\mathsf{A}$ is an Eilenberg–Zilber category, the injective Reedy monomorphisms, defined below, are just the pointwise monomorphisms.

**Definition 6.2.9** (Berger–Moerdijk). A map $f: X \to Y$ in $\mathsf{Set}^{\mathsf{A}^{\mathrm{op}}}$ is an **injective Reedy monomorphism** if for all $a \in \mathsf{A}$, the map $\widehat{\ell}_a f$ is a monomorphism.

The injective Reedy monomorphisms form the left class of a weak factorization system that is left-lifted along the left adjoint $\widehat{\ell}_{\bullet -}$ displayed below from the (monomorphism, equivariant split epimorphism) weak factorization system on $\mathsf{Set}^{\mathsf{G}^{\mathrm{op}}}$, which in turn is the “injective” or left lifting of the (monomorphism, split epimorphism) weak factorization system on $\mathsf{Set}^{\mathrm{obA}}$.$^{13}$

$$\begin{array}{ccc} \mathcal{M}_{\mathrm{inj}}[\mathsf{A}] & \longrightarrow & \mathcal{M}_{\mathrm{inj}} \\ \downarrow & \downarrow & \downarrow \\ (\mathsf{Set}^{\mathsf{A}^{\mathrm{op}}})^2 & \xrightarrow{\widehat{\ell}_{\bullet -}} & (\mathsf{Set}^{\mathsf{G}^{\mathrm{op}}})^2. \end{array}$$

When $\mathsf{A}$ is an Eilenberg–Zilber category, Corollary 6.2.6 tells us that any monomorphism $f$ factors as a transfinite composite of pushouts of maps of the form (6.2.7) where $\widehat{\ell}_n f \in \mathsf{Set}^{\mathsf{G}(n)^{\mathrm{op}}}$ is a monomorphism. The groupoid $\mathsf{G}(n)$ of isomorphisms between objects of degree $n$ is equivalent to the disjoint union of the 1-object groupoids associated to automorphism groups $\operatorname{Aut}(a)$, where the disjoint union is over the set of isomorphism classes of objects of degree $n$.$^{14}$ So $\mathsf{Set}^{\mathsf{G}(n)^{\mathrm{op}}}$ is equivalent to the product of categories of the form $\mathsf{Set}^{\operatorname{Aut}(a)^{\mathrm{op}}}$ where $\deg(a) = n$.

Thus, we study the (injective monomorphism, injective split epimorphism) weak factorization system on the category $\mathsf{Set}^{\mathsf{G}^{\mathrm{op}}}$ of right $G$-sets, for $G$ a group. In this category, the injective monomorphisms are just the monomorphisms, while the injective split epimorphisms are the $G$-split epimorphisms: maps of right $G$-sets that admit a $G$-equivariant section.

$^{13}$Projective Reedy weak factorization systems may be defined similarly using the “projective” or right lifting to $\mathsf{Set}^{\mathbb{C}}$ [BM11, 1.6, 1.8].

$^{14}$In both $\square$ and $\triangle$ there is a unique object of degree $n$, but this is not a requirement of the Eilenberg–Zilber axioms.

71