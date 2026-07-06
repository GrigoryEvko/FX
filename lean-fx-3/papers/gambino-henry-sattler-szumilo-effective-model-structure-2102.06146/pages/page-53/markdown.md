- A lextensive category is said to be *locally connected* if every object is a van Kampen coproduct of connected objects.

The terminology of Definition 11.1 is compatible with the notion of a locally connected Grothendieck topos. For example, the category of sheaves of set over a locally connected topological space is locally connected. The category of presheaves over a category $\mathcal{I}$ is locally connected, its connected objects are called the “orbit” of $I$, i.e., the presheaves whose category of elements is connected, or equivalently whose colimits is a singleton. The coproduct completion of a category with finite limits is also a locally connected category.

Let us now fix a lextensive category $\mathcal{E}$. We denote by $\mathcal{E}^{\text{con}}$ the full subcategory of of $\mathcal{E}$ of connected objects. It is important to note that even if $\mathcal{E}$ is a Grothendieck topos, this category is in general not a small category, as the next example illustrates.

**Example 11.2.** If $\mathcal{E} = \text{Set}^{[1]} = \text{Fam Set}$, then the connected objects of $\mathcal{E}$ are the objects of the form $X \to \ast$ for an arbitrary set $X$. In particular $\mathcal{E}^{\text{con}}$ is equivalent to the category of all sets. More generally, if $\mathcal{C}$ is a category with finite limits, and $\text{Fam } \mathcal{C}$ is its coproduct completion, then $(\text{Fam } \mathcal{C})^{\text{con}} = \mathcal{C}$.

**Lemma 11.3.** *Let $X$ be a connected object in a lextensive category. Then $\text{Hom}_{\text{Set}}(X, -)$ commutes with van Kampen coproducts.*

*Proof.* Given a map $f: X \to \coprod A_i$, then $X = \coprod X_i$ where $X_i = X \times_A A_i$, but as $X$ is connected all the $X_i$ except one are the initial object. As $X$ is itself non-initial, then exactly one of the $X_i$ is non initial and hence $X = X_i$ and the map $X \to \coprod A_i$ factors into $X \to A_i$ for a unique $i$. $\square$

For a possibly large category $\mathcal{D}$, we write $\text{Psh } \mathcal{D}$ for the category of small presheaves on $\mathcal{D}$, that is the category of presheaves on $\mathcal{D}$ that can be written as small colimits of representables. We denote by $\text{sPsh } \mathcal{D}$ the category of small simplicial presheaves, or equivalently simplicial objects in $\text{Psh } \mathcal{D}$. In general, limits of small presheaves can fail to be small, but if we assume that $\mathcal{D}$ has $\alpha$-small limits, then $\text{Psh } \mathcal{D}$ also has $\alpha$-small limits. This is proved in [DL07] as Theorem 4.3 applied to Example 4.1.1.

**Proposition 11.4.** *Let $\mathcal{D}$ be a category with finite limits. Then $\text{sPsh } \mathcal{D}$ carries the projective model structure, in which an arrow $f: X \to Y$ if a fibration, trivial fibration or weak equivalence if and only if for all $d \in \mathcal{D}$, the arrow $f_d: X(d) \to Y(d)$ is one.*

*Proof.* This is proved in [CD09] under the assumption that $\mathcal{D}$ has all limits. However, the proof applies unchanged if we only assume that $\text{sPsh } \mathcal{D}$ has finite limits, as long as we do not require that a model category has all limits, but only finite limits. Indeed the only use of limits in $\mathcal{D}$ in the proof is to show that $\text{Psh } \mathcal{D}$ has all limits. Moreover, [DL07, Theorem 4.3 applied to Example 4.1.1] shows that if the category $\mathcal{D}$ has finite limits then the category $\text{Psh } \mathcal{D}$ of small presheaves on $\mathcal{D}$ also has finite limits. Note that the existence of the corresponding weak factorisation system in $\text{sPsh } \mathcal{D}$ follows from the generalised small object argument with respect to locally small class of arrows exactly as explained in [CD09] $\square$

The claim of Proposition 11.4 follows also from the assumption that $\text{sPsh } \mathcal{D}$ has finite limits, which is a weaker condition than the existence of finite limits in $\mathcal{D}$.

53