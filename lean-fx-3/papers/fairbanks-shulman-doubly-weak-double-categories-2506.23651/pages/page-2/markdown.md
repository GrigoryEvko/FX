2

AARON DAVID FAIRBANKS AND MICHAEL SHULMAN

categories in **Cat**). The two different sorts of 1-cell are then, respectively, the morphisms in the category-of-objects and the objects in the category-of-morphisms. Now just as a bicategory is a “weakly enriched category” in the 2-category *Cat* of categories, the definition of internal category can be weakened so that it satisfies the usual associativity and unit laws only up to coherent isomorphism (a so-called “internal pseudo-category” [Fer06]). This results in the *pseudo double categories* from [GP99].

However, pseudo double categories are weak in only one direction: composition of morphisms in the category-of-objects is still strict. Many of the weak double categories arising naturally do satisfy this constraint (e.g. the double category of categories, whose two sorts of 1-cells are functors, which compose in a strict way, and profunctors, which do not). But there are some situations in which one would like a notion of double category where composition is weak in both directions. For example:

- Every strict 2-category $\mathcal{C}$ has a strict double category of “squares” a.k.a. “quintets”,$^{1}$ where both sorts of 1-cells are those of $\mathcal{C}$, and the squares are 2-cells in $\mathcal{C}$ of the form

But if $\mathcal{C}$ is a *bicategory*, then this would have to be a double category that is weak in both directions.

- As shown in [BHKP02], any topological space has a fundamental double groupoid consisting of points as 0-cells, continuous paths as both kinds of 1-cells, and homotopy classes of homotopies as 2-cells. The double groupoid constructed in [BHKP02] is made strict by quotienting the paths by “thin homotopy”, but it would be more natural to have weak composition in both directions, since concatenation of paths is not strictly associative.
- A *proarrow equipment* [Woo82] can be defined as a pseudofunctor of bicategories $\mathcal{C} \rightarrow \mathcal{D}$ that is bijective on objects, locally full and faithful, and such that every 1-cell in its image is a left adjoint. This is intended as an abstraction of examples such as the pseudofunctor $\mathcal{C}at \rightarrow \mathcal{P}rof$ assigning to each functor its representable profunctor. As observed in [Ver92, Shu08], a proarrow equipment gives rise to a double category, whose objects are those shared by $\mathcal{C}$ and $\mathcal{D}$, whose two sorts of 1-cell are those of $\mathcal{C}$ and $\mathcal{D}$ respectively, and whose 2-cells come from $\mathcal{D}$. However, this is only a pseudo double category if $\mathcal{C}$ is a strict 2-category. When $\mathcal{C}$ and $\mathcal{D}$ are both bicategories, this double category should be weak in both directions.

In practice, often $\mathcal{C}$ is strict, but not always. Two examples where it is not are the inclusion $\mathcal{S}pan(\mathbf{E}) \rightarrow \mathcal{P}oly(\mathbf{E})$ of the bicategory of spans in the bicategory of polynomials [KG13, Web15], for any locally cartesian closed category $\mathbf{E}$; and the inclusion $\mathcal{C}atAna(\mathbf{E}) \rightarrow \mathcal{P}rof(\mathbf{E})$ of internal anafunctors [Bar06, Rob12] into internal profunctors, for any topos $\mathbf{E}$.

- A special case of an equipment is when the 1-cells of $\mathcal{C}$ are defined to be adjunctions in $\mathcal{D}$ (pointing in the direction of the left adjoints; these are

$^{1}$This unlovely term arises from the fact that to determine a 2-cell in this double category requires five data: a 2-cell in $\mathcal{C}$ and four 1-cells in $\mathcal{C}$ that form its boundary (the decomposition of its source and target as composites not being determined by the 2-cell itself).