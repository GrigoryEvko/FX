cofibrations, fibrations) and (cofibrations, acyclic fibrations). Therefore, a cofibration with a cofibrant domain is an equivalence if and only if it is an acyclic cofibration.

In particular, the full subcategory of $\mathcal{C}$ consisting of cofibrant objects forms a model category, except that it may not be closed under limits and colimits—hence the need to consider the non-cofibrant objects of $\mathcal{C}$ as well.

The basic theory of left semi-model categories operates similarly to Quillen model categories: the homotopy category can be defined by formally inverting the maps in $\mathcal{W}$ or by defining a homotopy relation between bifibrant objects. See [39] or [23]$^4$. The $\infty$-categorical localization is also considered in the appendices of [31] (under the assumption that the factorization systems are functorial, which will always be the case in this paper), and it functions similarly to the corresponding localization in Quillen model categories.

### A.5 Definition.

- A premodel category is said to be combinatorial if its underlying category is locally presentable and both factorization systems are cofibrantly generated. It is said to be \(\omega\)-combinatorial if furthermore the underlying category is locally \(\omega\)-presentable and the codomains of the generating cofibrations and acyclic cofibrations are \(\omega\)-small.
- A Quillen adjunction between premodel categories is an adjunction \( L: \mathcal{C} \leftrightarrows \mathcal{D}: R \) such that \( L \) sends cofibrations and anodyne cofibrations to cofibrations and anodyne cofibrations, or equivalently, such that \( R \) sends fibrations and anodyne fibrations to fibrations and anodyne fibrations.
- A monoidal premodel category is a premodel category \(\mathcal{C}\), endowed with a monoidal closed structure, such that the monoidal unit is cofibrant, and for each pair of cofibrations \(i: A \to B\) and \(j: C \to D\), the map

$$ i \widehat{\otimes} j : B \otimes C \coprod_{A \otimes C} A \otimes D \to B \otimes D $$

is also a cofibration. Moreover, if $i$ or $j$ is anodyne, then $i \widehat{\otimes} j$ is also anodyne.

A left semi-model category is said to be *combinatorial* or *monoidal* if its underlying category is, and an adjunction between left semi-model categories is said to be a *Quillen adjunction* if it is a Quillen adjunction of the underlying premodel categories.

There are more general notions of monoidal structures or Quillen adjunctions for left semi-model structures that only involve the cofibrations between cofibrant objects, such as the "weak Quillen functors" discussed in [23]. However, we do not need these generalizations in the present paper.

Similarly to what happens with Quillen model categories, Quillen adjunctions between left semi-model categories induce adjunctions between their homotopy categories and even between their $\infty$-categorical localizations (see, for example, [23]).

### A.6 Definition.

A Quillen adjunction $F: C \leftrightarrows D: R$ is a *Quillen equivalence* if the induced adjunction between their homotopy categories is an equivalence of categories.

$^4$Semi-model categories are particular cases of weak model structures as defined in [23], so the results from this work can be applied.

60