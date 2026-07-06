Vol. 19:2

LNL POLYCATEGORIES AND DOCTRINES OF LINEAR LOGIC

1:39

This information uniquely determines the other linear homsets by the F-isomorphism:

$$\mathcal{P}(X_1, \dots, X_n \mid \mathsf{F}Y; \mathsf{F}Z) \cong \mathcal{P}(X_1, \dots, X_n, Y \mid ; \mathsf{F}Z).$$

However, passing back along these isomorphisms yields multicategorical composition operations on the linear homsets (6.1):

$$\begin{aligned} \mathcal{P}(\Upsilon, X \mid ; \mathsf{F}Y) \times \mathcal{P}(\Theta \mid ; \mathsf{F}X) &\cong \mathcal{P}(\Upsilon \mid \mathsf{F}X; \mathsf{F}Y) \times \mathcal{P}(\Theta \mid ; \mathsf{F}X) \\ &\to \mathcal{P}(\Upsilon, \Theta \mid ; \mathsf{F}Y). \end{aligned}$$

This composition treats the universal morphisms $\chi \in \mathcal{P}(X \mid ; \mathsf{F}X)$ as identities. Moreover, naturality of the F-isomorphisms implies that these operations are associative in the limited sense that the two composite functions

$$\mathcal{P}(\Theta_3, Y \mid ; \mathsf{F}Z) \times \mathcal{P}(\Theta_2, X \mid ; \mathsf{F}Y) \times \mathcal{P}(\Theta_1 \mid ; \mathsf{F}X) \to \mathcal{P}(\Theta_3, \Theta_2, \Theta_1 \mid ; \mathsf{F}Z)$$

are equal. However, because of the restricted universal property of $\mathsf{F}$, nothing forces the two composite functions

$$\mathcal{P}(\Theta_3, X, Y \mid ; \mathsf{F}Z) \times \mathcal{P}(\Theta_2 \mid ; \mathsf{F}Y) \times \mathcal{P}(\Theta_1 \mid ; \mathsf{F}X) \Rightarrow \mathcal{P}(\Theta_3, \Theta_2, \Theta_1 \mid ; \mathsf{F}Z) \quad (6.2)$$

to be equal, as they would be if the homsets (6.1) formed a (cartesian) multicategory. This means the linear homsets (6.1) have the structure of a *cartesian pre-multicategory* in the sense of [SL13].

Finally, composing with the universal morphism $\chi \in \mathcal{P}(X \mid ; \mathsf{F}X)$ provides a function

$$\mathcal{P}(\Theta; X) \to \mathcal{P}(\Theta \mid ; \mathsf{F}X)$$

that respects the cartesian actions, identities, and compositions. Moreover, the linear morphisms in the image of this map are *central*, meaning that the two morphisms (6.2) are equal if one of the morphisms into $\mathsf{F}X$ or $\mathsf{F}Y$ is in this image. Thus, we conclude that a strictly well-sorted $\mathbb{D}$-category can be identified with a *cartesian Freyd multicategory* in the sense of [SL13]: a cartesian multicategory $\mathcal{V}$ of “values”, a cartesian pre-multicategory $\mathcal{C}$ of “computations”, and an identity-on-objects functor $\text{return} : \mathcal{V} \to \mathcal{C}$ that preserves centrality. (I am indebted to Max New for this observation.)

A similar doctrine with $|\mathbb{D}| = \text{SYMSKEW}$ yields symmetric Freyd multicategories. However, I don’t believe there is a sorted doctrine such that the strictly well-sorted $\mathbb{D}$-categories can be identified with bare (cartesian or symmetric) pre-multicategories. We can “remove” the extra information of the nonlinear morphisms by requiring either that the only nonlinear morphisms are projections, or that the nonlinear morphisms coincide with the central linear ones; but neither of these conditions is enforceable doctrinally. (Similarly, a *duploid* [MM13] is an adjunction of ordinary categories with certain restrictions: adjunctions can be modeled doctrinally over the base ADJ from Example 4.9, but the duploid conditions are not doctrinal.)

A nonlinear product $X \times Y$ in a cartesian Freyd multicategory is the same as a *tensor* in the sense of [SL13]: a (pre)multicategorical tensor in $\mathcal{V}$ that is preserved by return. As shown in [SL13, §8], a cartesian Freyd multicategory with all such tensors (and units) is equivalent to a Freyd-category in the sense of [PT99]: a cartesian monoidal category $\mathcal{V}$, a symmetric premonoidal category [PR97] $\mathcal{C}$, and an identity-on-objects symmetric premonoidal functor $\text{return} : \mathcal{V} \to \mathcal{C}$ that preserves centrality. (Alternatively, one can use the characterization of Freyd-categories from [Lev04], which is akin to those of CBPV structures in Proposition 3.13.)