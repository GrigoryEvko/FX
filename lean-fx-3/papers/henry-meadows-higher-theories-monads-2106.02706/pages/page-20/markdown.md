where the $B$ index denotes fiber over $B$. The (contravariant) functoriality in $B$ of these all these constructions and the naturality of these equivalence hence follows immediately from the straightening construction.

The functor $\mathbf{Mon}(\mathcal{C})_{/\mathrm{End}(X)} \rightarrow \mathbf{Mon}(\mathcal{C})$ is the obvious forgetful functor and is hence a right fibration (by the dual of [15, Corollary 2.1.2.2]). The functor $\theta : \mathcal{C}^{+}[X] \rightarrow \mathcal{C}$ constructed in [16, Proposition 4.7.1.39] induces a right fibration $\mathbf{Mon}(\mathcal{C}^{+}[X]) \rightarrow \mathbf{Mon}(\mathcal{C})$ (also by [16, Proposition 4.7.1.39]). As $T_X$ is sent to $\mathrm{End}(X)$ by this functor, this induces a right fibration $\mathbf{Mon}(\mathcal{C}^{+}[X])_{/T_X} \rightarrow \mathbf{Mon}(\mathcal{C})_{/\mathrm{End}(X)}$. This clearly equips the first three categories with right fibrations to $\mathbf{Mon}(\mathcal{C})$ with the first two functor being compatible to these (by functoriality of the slice construction).

The functor $\mathbf{LMod}^X(\mathcal{X}) \rightarrow \mathbf{Mon}(\mathcal{C})$ is simply the composite of the functor $\mathbf{LMod}^X(\mathcal{X}) \rightarrow \mathbf{LMod}(\mathcal{X})$ with the forgetful functor $\mathbf{LMod}(\mathcal{X}) \rightarrow \mathbf{Mon}(\mathcal{C})$, it can be seen as the top of arrow in the pullback:

$$\begin{array}{ccc} \mathbf{LMod}^X(\mathcal{X}) & \longrightarrow & \{X\} \times \mathbf{Mon}(\mathcal{C}) \\ \downarrow & \downarrow & \downarrow \\ \mathbf{LMod}(\mathcal{X}) & \longrightarrow & \mathcal{X} \times \mathbf{Mon}(\mathcal{C}) \end{array}$$

Given that the bottom map is an iso-fibration, it follows that $\mathbf{LMod}^X(\mathcal{X}) \rightarrow \mathbf{Mon}(\mathcal{C})$ is a quasi-fibration. The fact that it is a right fibration will be deduced later from the equivalence with the right fibration $\mathbf{Mon}(\mathcal{C}^{+}[X]) \rightarrow \mathbf{Mon}(\mathcal{C})$ (see [16, Corollary 4.7.1.42]).

So, if we consider the diagram:

$$\begin{array}{ccc} \mathbf{Mon}(\mathcal{C}^{+}[X]) & \longrightarrow & \mathbf{LMod}^X(\mathcal{X}) \\ & \searrow & \downarrow \\ & \mathbf{Mon}(\mathcal{C}) & \end{array}$$

where the diagonal map is the map $\theta'$ mentioned above (whose fibre over $B$ is $\mathbf{Mon}(\mathcal{C}^{+}[X])_B$), the horizontal map is the equivalence of [16, Theorem 4.7.1.34], and the vertical map is the forgetful functor, which is a cartesian fibration. One can then check from the explicit construction of the horizontal map given in [16] that the above diagram commutes, since all functors involved are induced by 'forgetful functors' between various full subcategories of functor categories from (nerve of) 1-categories. Hence producing the last compatibility we needed. $\square$

20