so the latter has the right type to be the display of the former. Thus we expect:

\( \left(\left(\text{Path } A \times y\right)\right)_{A : \text{Type}_i, x : A, y : A}^d \equiv \)

\( \left(\left(\text{PathP } (\lambda i. P (p i)) x' y'\right)\right)_{A : \text{Type}_i, P : A \to \text{Type}_i, x : A, x' : P x, y : A, y' : P y, p : \text{Path } A \times y}. \)

With this given, the singular semi-simplicial types are defined by corecursion. Rather than write this explicitly using the corecursor from section 3.1, we use a copattern-matching syntax, including a 'displayed corecursive call' \(\mathrm{Sing}^{\mathrm{d}}\).

Sing : Type → SST
Z (Sing A) = A
S (Sing A) x = Sing \( ^{d} \)  A ( \( \lambda \)  y → Path A x y)

A calculation then yields:

Z (Sing A) = A
 \( Z^{d} \)  (S (Sing A)  \( x_{i1} \) )  \( x_{i1} \)  = Path A  \( x_{i1} \)   \( x_{i1} \) 
 \( Z^{dd} \)  ( \( S^{d} \)  (S (Sing A)  \( x_{i1} \) )  \( x_{i1} \)   \( \beta_{i1} \) )  \( x_{i1} \)   \( \beta_{i1} \)   \( \beta_{i1} \) 
= PathP ( \( \lambda i \rightarrow Path A x_{i1} \beta_{i1} i \) )  \( \beta_{i1} \beta_{i1} \) 
 \( Z^{ddd} \)  ( \( S^{dd} \)  ( \( S^{d} \)  (S (Sing A)  \( x_{i1} \) )  \( x_{i1} \beta_{i1} \) )  \( x_{i1} \beta_{i1} \beta_{i1} \beta_{i1} f_{i1} \) )  \( x_{i1} \beta_{i1} \beta_{i1} \beta_{i1} f_{i1} \beta_{i1} f_{i1} f_{i1} \beta_{i1} f_{i1} f_{i1} \beta_{i1} f_{i1} f_{i1} \beta_{i1} f_{i1} f_{i1} \beta_{i1} f_{i1} f_{i1} \beta_{i1} f_{i1} f_{i1} \beta_{i1} f_{i1} f_{i1} \)

#### 3.2.2 Nerves of categories

The semi-simplicial nerve of a 1-category can also be defined by corecursion. Let Cat denote the type of 1-categories, defined as a record inside dTT (extended by record types), and recall that in section 1 we computed Cat \( ^{d} \) to consist of ‘displayed categories’ in the usual sense [AL19]. Thus we can define:

Nerve : Cat → SST
Z (Nerve C) = ob C
S (Nerve C) x = Nerve \( ^{d} \)  C (coslice C x)

Here for a category \(\mathcal{C}\) and object \(x: \text{ob } \mathcal{C}\), by coslice \(\mathcal{C} x\) we mean the coslice category \(x / \mathcal{C}\), regarded as a displayed category over \(\mathcal{C}\) via the forgetful functor. Note that a definition of coslice: \((\mathcal{C}: \text{Cat}) \to \text{ob } \mathcal{C} \to \text{Cat}^{\mathrm{d}} \mathcal{C}\) at the global level in dTT automatically induces the definition of the dependent coslice coslice\(^{\mathrm{d}}\). A similar idea works for bicategories, and any other kind of category for which we can define a displayed (co)slice.

#### 3.2.3 Topological singular complexes

In section 3.2.1 we constructed the singular semi-simplicial type associated to the intrinsic \(\infty\)-groupoid structure of any type. But we can also construct a more classical singular semi-simplicial set associated to a topological space. For any type Top of 'topological space' definable inside of dTT as a record, we have a displayed version Top\(^{d}\). In some cases, particularly 'nonalgebraic' ones such as open-set spaces, an element of Top\(^{d}\) X is more general than an Y : Top with a map Y → X; but at least from such a Y we can construct its fibers as a displayed space. Thus, as long as we can construct, for any x : X, a space of 'continuous paths in X starting at x' with an endpoint projection down to X, we can make it a displayed space paths X x over X, and use this to construct the singular semi-simplicial types:

33