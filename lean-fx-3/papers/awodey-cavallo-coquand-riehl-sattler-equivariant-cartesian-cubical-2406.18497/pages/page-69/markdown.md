6.2. **Eilenberg–Zilber categories.** The categories $\triangle$ and $\square$ are both *Reedy categories*—the former in Dan Kan's original 'strict' sense and the latter in the 'generalized' sense of [BM11]—that are moreover *Eilenberg–Zilber categories*, defined below. These properties enable inductive arguments concerning the monomorphisms in the presheaf categories **sSet** and **cSet** respectively.

A Reedy category $\mathsf{A}$ comes with classes of 'degree-decreasing' and 'degree-increasing maps,' defined relative to a degree function $\deg: \mathrm{ob}\mathsf{A} \rightarrow \mathbb{N}$. In the case of Eilenberg–Zilber categories, defined below, the degree-decreasing maps are the split epimorphisms, while the degree-increasing maps are the monomorphisms.

**Definition 6.2.1** ([BM11, 6.7]). An **Eilenberg–Zilber** category is a small category $\mathsf{A}$ equipped with a degree function $\deg: \mathrm{ob}\mathsf{A} \rightarrow \mathbb{N}$ so that

- (i) Isomorphisms preserve the degree, whereas non-invertible monomorphisms or split epimorphisms strictly raise and lower the degree, respectively, when moving from their domain to their codomain.
- (ii) Every $f \in \mathrm{mor}\mathsf{A}$ may be factored as a split epimorphism followed by a monomorphism.
- (iii) Any pair of split epimorphisms with common domain has an **absolute pushout**: a pushout in $\mathsf{A}$ that is preserved by the Yoneda embedding $\updownarrow: \mathsf{A} \hookrightarrow \mathrm{Set}^{\mathsf{A}^{\mathrm{op}}}$.

Berger and Moerdijk observe that $\triangle$ is an Eilenberg–Zilber category [BM11, 6.8]. By [Cam23, Theorem 8.12(1)], the cartesian cube category is as well (as could also be checked by directly verifying that each pair of epimorphisms in $\square$ with common domain has an absolute pushout).

We review a few results from general Reedy category theory [RV14; Rie] and then explain what is special about Eilenberg–Zilber categories. Let $\mathsf{A}$ be an Eilenberg–Zilber category and write $\mathsf{A} \in \mathrm{Set}^{\mathsf{A}^{\mathrm{op}} \times \mathsf{A}}$ for the hom bifunctor of arrows in $\mathsf{A}$. Let

$$\mathrm{sk}_n \mathsf{A} \hookrightarrow \mathsf{A} \in \mathrm{Set}^{\mathsf{A}^{\mathrm{op}} \times \mathsf{A}}$$

denote the subfunctor of arrows of degree at most $n$, by which we mean arrows that factor through an object of degree $n$.

**Definition 6.2.2** (boundaries of representable functors). For $a \in \mathsf{A}$, write $\mathsf{A}_a \in \mathrm{Set}^{\mathsf{A}}$ and $\mathsf{A}^a \in \mathrm{Set}^{\mathsf{A}^{\mathrm{op}}}$ for the co- and contravariant representable functors. If $a \in \mathsf{A}$ has degree $n$, write

$$\begin{aligned} \overleftarrow{\partial} \mathsf{A}_a &:= \mathrm{sk}_{n-1} \mathsf{A}_a & \in \mathrm{Set}^{\mathsf{A}} & \text{and} \\ \overrightarrow{\partial} \mathsf{A}^a &:= \mathrm{sk}_{n-1} \mathsf{A}^a & \in \mathrm{Set}^{\mathsf{A}^{\mathrm{op}}}. \end{aligned}$$

The external (pointwise) product defines a bifunctor $\mathrm{Set}^{\mathsf{A}} \times \mathrm{Set}^{\mathsf{A}^{\mathrm{op}}} \xrightarrow{-\times-} \mathrm{Set}^{\mathsf{A}^{\mathrm{op}} \times \mathsf{A}}$. For any $a \in \mathsf{A}$, the exterior Leibniz product

$$(6.2.3) \quad \mathsf{A}_a \times \overrightarrow{\partial} \mathsf{A}^a \cup \overleftarrow{\partial} \mathsf{A}_a \times \mathsf{A}^a \xrightarrow{(\overleftarrow{\partial} \mathsf{A}_a \hookrightarrow \mathsf{A}_a) \times (\overrightarrow{\partial} \mathsf{A}^a \hookrightarrow \mathsf{A}^a)} \mathsf{A}_a \times \mathsf{A}^a$$

defines the subfunctor of pairs of morphisms $h \cdot g$ with $\mathrm{dom}(h) = \mathrm{cod}(g) = a$ in which at least one of the morphisms $g$ and $h$ has degree less than the degree of $a$. There is a natural 'composition' map whose domain is the external product of the contravariant and covariant representables

$$(6.2.4) \quad \mathsf{A}_a \times \mathsf{A}^a \xrightarrow{\circ} \mathsf{A}.$$

Its image is the subfunctor of arrows in $\mathsf{A}$ that factor through $a$, but (6.2.4) is not in general a monomorphism: e.g., this fails to be the case whenever $a$ has non-identity automorphisms.

By Definition 6.2.1(i), the groupoid core $\mathsf{G} \subset \mathsf{A}$ of a Reedy category decomposes as a coproduct $\mathsf{G} = \coprod_{n \in \mathbb{N}} \mathsf{G}(n)$, where $\mathsf{G}(n)$ is the subgroupoid of isomorphisms between objects of degree $n$. Any

69