**A.8 Theorem.** *Let $\mathcal{C}$ be a combinatorial left semi-model category, and let $S$ be a set of morphisms between cofibrant objects in $\mathcal{C}$. Then there is another left semi-model category $\mathcal{C}_S$, called the left Bousfield localization of $\mathcal{C}$ at $S$, with the same underlying category as $\mathcal{C}$, such that:*

- • $\mathcal{C}_S$ has the same cofibrations as $\mathcal{C}$, and the identity functor $\mathcal{C} \to \mathcal{C}_S$ is a left Quillen functor.
- • *A left Quillen functor $\mathcal{C} \to \mathcal{D}$ to any other left semi-model structure is a left Quillen functor $\mathcal{C}_S \to \mathcal{D}$ if and only if it sends the morphisms in $S$ to weak equivalences.*

The fibrant objects of $\mathcal{C}_S$ are the objects that are fibrant in $\mathcal{C}$ and are "S-local". However, in order to define $S$-local objects, one needs to define mapping spaces. To avoid this, we provide the following characterization:

**A.9 Lemma.** *Let $\mathcal{C}_S$ be a left Bousfield localization of $\mathcal{C}$. Assume that all morphisms in $S$ are cofibrations between cofibrant objects (or have been replaced by equivalent cofibrations). For each cofibration $i: A \to B \in S$, let $\nabla i$ be a cofibration between cofibrant objects homotopy equivalent to the map $B \coprod_A B \to B$, for example a factorization*

$$B \coprod_A B \stackrel{\nabla i}{\rightsquigarrow} I_A B \stackrel{\sim}{\to} B$$

*and let $\nabla^k i$ be a series of cofibrations obtained by iterating this process, that is, $\nabla^k i = \nabla(\nabla^{k-1} i)$. Then an object is fibrant in $\mathcal{C}_S$ if and only if it is fibrant in $\mathcal{C}$ and has the right lifting property against $\nabla^k i$ for all $k$ and all $i \in S$.*

Finally, we can form Reedy model structures in this context as well. This is very similar to the treatment of classical Reedy model structures (see, for example, Chapter 5.2 in [26]).

Given a Reedy category $R$ and $\mathcal{C}$ a premodel category, the category of functors $\mathcal{C}^R$ has a premodel structure whose (anodyne) fibrations and (anodyne) cofibrations are the Reedy (anodyne) fibrations and cofibrations. That is, a natural transformation $f_r: X(r) \to Y(r)$ in $\mathcal{C}^R$ is an (anodyne) cofibration if and only if for each $r \in R$ the natural map

$$X(r) \coprod_{L_r X} L_r Y \to Y(r)$$

where

$$L_r X = \underset{\substack{r' \to r \in R^+ \\ r' \neq r}}{\text{Colim}} X(r')$$

is an (anodyne) cofibration. Dually, this natural transformation is an (anodyne) fibration if the natural map

$$X(r) \to Y(r) \times_{M_r Y} M_r X$$

where

$$M_r X = \underset{\substack{r \to r' \in R^- \\ r' \neq r}}{\text{Lim}} X(r')$$

is an (anodyne) fibration. We have:

62