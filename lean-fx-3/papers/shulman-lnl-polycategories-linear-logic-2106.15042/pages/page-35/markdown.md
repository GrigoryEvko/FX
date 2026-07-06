Vol. 19:2

LNL POLYCATEGORIES AND DOCTRINES OF LINEAR LOGIC

1:35

of $G$ to $\mathcal{P}$ that we call **proto-extremal**:

$$\left\{ \begin{array}{c} \mathcal{P} \\ \mathcal{C} \xrightarrow[G]{} |\mathbb{D}| \end{array} \right\}.$$

A **morphism of $\mathbb{D}$-sketches** is a functor in LNLPoly/$|\mathbb{D}|$ that preserves proto-extremal cones; a **transformation** is an arbitrary 2-cell in LNLPoly/$|\mathbb{D}|$. This defines a 2-category $\mathbb{D}$-Sketch.

A $\mathbb{D}$-sketch is **realized** if every proto-extremal cone is in fact $\pi$-extremal. It is **saturated** if whenever $H : \mathcal{C} \to \mathcal{P}$ is proto-extremal, where $K$ is the vertex of $\mathcal{C}$, and $\phi : H(K) \cong K'$ is an isomorphism in $\mathcal{P}$ such that $\pi(\phi)$ is an identity, the cone $H_\phi : \mathcal{C} \to \mathcal{P}$ constructed before Proposition 4.29 is also proto-extremal. It is **precomplete** if for any $\mathbb{D}$-cone $G : \mathcal{C} \to |\mathbb{D}|$, any lift of its reduct $\partial\mathcal{C} \hookrightarrow \mathcal{C} \to |\mathbb{D}|$ to $\mathcal{P}$ can be extended to a proto-extremal cone:

$$\begin{array}{c} \partial\mathcal{C} \longrightarrow \mathcal{P} \\ \downarrow \quad \exists \quad \nearrow \quad \downarrow \pi \\ \mathcal{C} \xrightarrow[G]{} |\mathbb{D}| \end{array}$$

Finally, it is (**$\mathbb{D}$-**)complete** if it is realized, saturated, and precomplete.

**Proposition 5.6.** *The 2-category of $\mathbb{D}$-complete sketches is equivalent, as a strict 2-category, to the 2-category $\mathbb{D}$-Cat of $\mathbb{D}$-categories.*

*Proof.* We regard a $\mathbb{D}$-category as a sketch by designating every $\pi$-extremal lift of a $\mathbb{D}$-cone as proto-extremal. This defines a 2-functor $\mathbb{D}$-Cat $\to \mathbb{D}$-Sketch, which lands inside the $\mathbb{D}$-complete sketches (using Proposition 4.29) and is an isomorphism on hom-categories. Moreover, precompleteness and realization make any $\mathbb{D}$-complete sketch into a $\mathbb{D}$-category, while in the presence of these properties saturation is equivalent (using Proposition 4.28) to saying that all $\pi$-extremal lifts of $\mathbb{D}$-cones are proto-extremal; hence the functor is essentially surjective as well. $\square$

$\mathbb{D}$-Sketch is a complete and cocomplete strict 2-category, with limits and colimits created in LNLPoly. If $\mathbb{D}$ is small, $\mathbb{D}$-Sketch is even locally presentable. It is also better-endowed with adjunctions, particularly ones arising from doctrine morphisms.

**Definition 5.7.** Let $\mathbb{D}_1, \mathbb{D}_2$ be LNL doctrines. A **doctrine map $\mathfrak{F} : \mathbb{D}_1 \to \mathbb{D}_2$** is a functor $|\mathfrak{F}| : |\mathbb{D}_1| \to |\mathbb{D}_2|$ together with, for each $\mathbb{D}_1$-cone $G : \mathcal{C} \to |\mathbb{D}_1|$, a $\mathbb{D}_2$-cone $\mathcal{C}_{\mathfrak{F}} \to |\mathbb{D}_2|$ and an isomorphism of abstract cones $\mathcal{C} \cong \mathcal{C}_{\mathfrak{F}}$ (preserving the vertex) making the evident square commute.

**Proposition 5.8.** *Any doctrine map $\mathfrak{F} : \mathbb{D}_1 \to \mathbb{D}_2$ induces a strict 2-adjunction (i.e. an adjunction of Cat-enriched categories)*

$$\mathfrak{F}_* : \mathbb{D}_1\text{-Sketch} \rightleftarrows \mathbb{D}_2\text{-Sketch} : \mathfrak{F}^*.$$

*Proof.* We have a 2-adjunction

$$\mathfrak{F}_* : \text{LNLPoly}/|\mathbb{D}_1| \rightleftarrows \text{LNLPoly}/|\mathbb{D}_2| : \mathfrak{F}^*$$