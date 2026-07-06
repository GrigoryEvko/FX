$$\begin{array}{c} \pi_1^*(c) \xrightarrow{\pi_{12}^* \epsilon} \pi_2^*(c) \\ \searrow \pi_{13}^* \downarrow \pi_{23}^* \epsilon \\ \pi_3^*(c) \end{array}$$

We define $Des(f, \mathcal{C})$ to be the category of objects of $\mathcal{C}(\mathcal{E})$ endowed with a descent data (and morphisms being the morphisms in $\mathcal{C}(\mathcal{E})$ whose pull-back along $\pi_1$ and $\pi_2$ commute to the $\epsilon$). If $c_0 \in \mathcal{C}(\mathcal{T})$ then $f^*c$ is naturally endowed with a descent data and this defines a functor from $\mathcal{C}(\mathcal{T})$ to $Des(f, \mathcal{C})$. One says that objects of $\mathcal{C}$ descend along $f$, or that $f$ is a descent morphism$^4$ for $\mathcal{C}$ if this functor induces an equivalence between $\mathcal{C}(\mathcal{T})$ and $Des(f, \mathcal{C})$.

It is for example proved in [13] that both objects and locales descend along open surjections. That is, for $\mathcal{C}(\mathcal{T}) = \mathcal{T}$ and $\mathcal{C}(\mathcal{T})$ being the category of internal locales of $\mathcal{T}$ the geometric morphisms which are open and surjective are descent morphisms.

In another language, the fact that objects of $\mathcal{C}$ descend along all open surjections, or more generally along all geometric morphisms belonging to some Grothendieck topology one the 2-category of topos exactly means that $\mathcal{C}$ is a stack for this topology.

## 2.5 Spaces of numbers

2.5.1. As mentioned in the introduction we are assuming that the base topos has a natural number object denoted by $\mathbb{N}$ (see [12, A2.5 and D5.1]). And from this natural number object one defines as usual the set $\mathbb{Z}$ of relative integers and $\mathbb{Q}$ of rational numbers with all their usual operations and properties.

2.5.2. $\mathbb{R}$ will denote the formal locale of real numbers, i.e., classifying locale of the geometric propositional theory of Dedekind real numbers (continuous real number). When it is spatial (for example in presence of the law of excluded middle) it is the set of real numbers endowed with its classical topology. In any case, it agrees with the localic completion (as we define in 3.3.12) of $\mathbb{Q}$ for the Archimedean distance. $\mathbb{C}$ denote the formal locale of complex numbers, i.e. $\mathbb{R} \times \mathbb{R}$ endowed with its usual multiplication and addition.

2.5.3. Similarly will define a locale $\overline{\mathbb{R}_+^\infty}$ in which the distance function will take value. As earlier work of C.J.Mulvey showed we only care about knowing when a distance is smaller than some rational number, hence $\overline{\mathbb{R}_+^\infty}$ will be defined as the classifying locale of the theory of $P \subset \mathbb{Q}_+^*$ such that if $q \in P$ and $q < q'$ then $q' \in P$ and if $q \in P$ then there exists $q' < q$ such that $q' \in P$.

$^4$We follow the terminology of [12], it is in fact more common to say that $f$ is an effective descent morphism.

13