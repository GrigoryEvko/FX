Vol. 19:2

LNL POLYCATEGORIES AND DOCTRINES OF LINEAR LOGIC

1:5

that are associative, unital, and equivariant in all reasonable ways. (Note that by equivariance, all the compositions are uniquely determined by those in which $\Theta_2, \Gamma_2, \Delta'_2$ are empty.)

**Definition 2.2.** A **functor** $H : \mathcal{P} \to \mathcal{Q}$ between LNL polycategories consists of functions between their linear and nonlinear objects and morphisms, preserving domains, codomains, structural actions, identities, and composites. A **transformation** $\alpha : H \Rightarrow K : \mathcal{P} \to \mathcal{Q}$ between functors consists of:

- (i) For each nonlinear object $X$ of $\mathcal{P}$, a nonlinear morphism $\alpha_X \in \mathcal{Q}(HX; KX)$.
- (ii) For each linear object $A$ of $\mathcal{P}$, a linear morphism $\alpha_A \in \mathcal{Q}(|HA; KA)$.
- (iii) For each nonlinear $f \in \mathcal{P}(\Theta; Y)$, we have $\alpha_Y \circ Hf = Kf \circ (\alpha_\Theta)^2$.
- (iv) For each linear $f \in \mathcal{P}(\Theta \mid \Gamma; \Delta)$, we have $(\alpha_\Delta) \circ Hf = Kf \circ (\alpha_\Theta \mid \alpha_\Gamma)$.

This defines a strict 2-category LNLPoly.

LNL polycategories are such a rich structure that they include many better-known structures as special cases. (The reader unfamiliar with any of the structures mentioned below is free to take the asserted characterization as a definition.)

- **Symmetric polycategories** can be identified with LNL polycategories having no nonlinear objects (and hence no nonlinear morphisms). These model the judgmental structure of classical multiplicative-additive linear logic.
- **Symmetric multicategories** can be identified with LNL polycategories having no nonlinear objects and in which all (linear) morphisms are *co-unary*, i.e. have a codomain of length 1. These model the judgmental structure of intuitionistic multiplicative-additive linear logic.
- Even more degenerately, ordinary **categories** can be identified with LNL polycategories having no nonlinear objects and in which all (linear) morphisms are both unary and co-unary.
- **Cartesian multicategories** can be identified with LNL polycategories having no linear objects and no linear morphisms (here the former does not quite imply the latter, as there are homsets $\mathcal{P}(\Theta \mid ;)$). These model the judgmental structure of intuitionistic (nonlinear) logic.
- By an **LNL multicategory** we will mean an LNL polycategory in which all linear morphisms are co-unary. These model the judgmental structure of intuitionistic linear logic (with exponentials); they do not quite appear in the literature, though a structure like them is the goal of [HT21] (see Example 3.10).

**Remark 2.3.** In fact, each of the above five subcategories is a slice category LNLPoly/$\mathcal{S}$ for some subterminal object $\mathcal{S}$. The terminal object of LNLPoly has one linear object, one nonlinear object, and all hom-sets singletons; thus a subterminal object has at most one object of each sort and each hom-set a subsingleton.

The slice category LNLPoly/$\mathcal{S}$ over a subterminal is thus the full subcategory of LNLPoly consisting of those objects $\mathcal{P}$ whose unique map to the terminal object factors through $\mathcal{S}$. This means that $\mathcal{P}$ has only objects of the sorts that $\mathcal{S}$ does, and only morphisms of the arity and co-arity that $\mathcal{S}$ does.

For example, let SYMPOLY be the subterminal object with one linear object, no nonlinear objects, and all linear homsets singletons. Then LNLPoly/SYMPOLY consists of LNL

$^2$Here if $\Theta = (X_1, \ldots, X_n)$ then $Kf \circ (\alpha_\Theta)$ denotes $(\cdots (Kf \circ_{X_1} \alpha_{X_1}) \circ_{X_2} \alpha_{X_2} \cdots) \circ_{X_n} \alpha_{X_n}$, and similarly elsewhere.