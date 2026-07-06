1:38

M. SHULMAN

Vol. 19:2

left-hand objects, U taking values in left-hand objects, ⊥ defined on right-hand objects, and ∩ taking values in right-hand objects. And we take the U and ∩ cones as sorting. Then a D-category is strictly well-sorted just when it has a choice of U and ∩ that are bijective onto the left-hand and right-hand objects respectively. A straightforward extension of Lemma 3.8 now shows that this is the same as its being the double-Kleisli adjunction of Proposition 3.18 constructed from the linearly distributive category with storage $\mathcal{P}^{\mathrm{L}}$. Thus, the 2-categories of linearly distributive or $*$-autonomous categories with storage, and their variants with limits and colimits, are equivalent to D -sCat for some sorted LNL doctrine D.

Example 6.8. By making one of the sorts in SMADJ (Example 4.8) derived from the other, we obtain sorted doctrines for lax symmetric monoidal monads or comonads.

Example 6.9. Recall the LNL multicategory LINPOL from Example 5.4. We now rechristen it SYMSKEW, calling its two linear objects L and T; thus there is a unique morphism $\Gamma \to \mathrm{L}$ when $\Gamma$ consists entirely of L's, and a unique morphism $\Gamma \to \mathrm{T}$ when $\Gamma$ contains no more than one T. We make this a sorted doctrine D with T primitive, L derived, sorting cone $\mathrm{L} \to \mathrm{T}$ (with vertex L), and no other cones.

A strictly well-sorted D-category is determined by the objects over T and the morphisms with target over T. Every object over L is the image of one over T by a functor that we may either leave implicit or denote G. We call a morphism over $\Gamma \to \mathrm{T}$ loose if $\Gamma$ consists entirely of L's; thus the loose homsets are of the form $\mathcal{P}(\mathsf{GA}_1, \ldots, \mathsf{GA}_n; B)$. We call a morphism over $\Gamma \to \mathrm{T}$ tight if $\Gamma$ contains a T; these tight homsets are uniquely determined by those where the first element of $\Gamma$ is T, i.e. of the form $\mathcal{P}(A_1, \mathsf{GA}_2, \ldots, \mathsf{GA}_n; B)$. This yields a doctrine for the symmetric skew multicategories of [BL20, §5]; the morphism j from tight to loose morphisms:

$$\mathcal{P}(A_1, \mathsf{GA}_2, \ldots, \mathsf{GA}_n; B) \to \mathcal{P}(\mathsf{GA}_1, \mathsf{GA}_2, \ldots, \mathsf{GA}_n; B)$$

is given by composition with the universal arrow $\mathsf{GA}_1 \to A_1$ over the sorting cone.

In a skew multicategory regarded as an LNL polycategory over SYMSKEW, a tight unit 1 (with restricted universal property) is a "left universal nullary map classifier". Similarly, for objects A and B over T, with corresponding objects GA and GB over L, a tensor product $A \otimes \mathsf{GB}$ (which also lies over T) is a "left universal tight binary map classifier" (see [BL18, §4.4]); and a hom $\mathsf{GA} \to B$ (also lying over T) corresponds to the notion of "closedness" from [BL18, §4.5]. Thus, by [BL18, BL20], we have sorted LNL doctrines for (symmetric) skew monoidal categories and (symmetric) skew closed categories. In particular, the "noninvertible associator" of a skew monoidal category is represented as a comparison map

$$(A \otimes \mathsf{GB}) \otimes \mathsf{GC} \longrightarrow A \otimes \mathsf{G}(B \otimes \mathsf{GC})$$

whose noninvertibility is unsurprising due to the different placements of G. (However, a symmetric closed skew-monoidal category is not a bifibration over SYMSKEW; it lacks some universal properties, such as a tensor product of two loose objects.)

Example 6.10. Let D be the sorted doctrine with $|\mathbb{D}| = \mathrm{CBPV}$, with a single cone for F that is sorting. Thus, a strictly well-sorted D-category is a linearly subunary LNL multicategory with an F satisfying a restricted universal property, and such that F is bijective from the nonlinear objects to the linear ones. Thus, it consists of a cartesian multicategory together with additional linear homsets

$$\mathcal{P}(X_1, \ldots, X_n \mid ; \mathsf{FZ}). \tag{6.1}$$