Relative Elegance and Cartesian Cubes with One Connection

3

from the 3-cube to itself. This map has no (split epi, mono) factorization, a state of affairs forbidden in an elegant Reedy category.¹

Thus, while Sattler [Sat19] and Streicher and Weinberger [SW21] have identified an adjoint triple of Quillen adjunctions relating $\widehat{\Omega}_{\Lambda V}^{ty}$ and $\widehat{\Lambda}^{kq}$, it is not known whether there is a Quillen equivalence. In particular, it is unclear how to prove that a round-trip composite $\widehat{\Omega}_{\Lambda V}^{ty} \to \widehat{\Lambda}^{kq} \to \widehat{\Omega}_{\Lambda V}^{ty}$ is weakly equivalent to the identity in the absence of an elegant Reedy structure on $\Omega_{\Lambda V}$.

In this article we consider an overlooked cube category: the category $\Omega_V$ of cubes with cartesian structure and a single connection. (We arbitrarily choose the “max” or “negative” connection, but this choice plays no role.) Presheaves on this category satisfy conditions sufficient to obtain a cubical-type model structure $\widehat{\Omega}_V^{ty}$ using existing techniques [CMS20; Awo23]. Moreover, the arguments used in [Sat19; SW21] adapt readily from $\Omega_{\Lambda V}$ to $\Omega_V$, providing a Quillen adjoint triple relating $\widehat{\Omega}_V^{ty}$ with $\widehat{\Lambda}^{kq}$.

Like the Dedekind cube category, $\Omega_V$ is not Reedy. In this case, the archetypical problematic map is $(x, y, z) \mapsto (x \vee y, y \vee z, z \vee x)$.² However, $\Omega_V$ does embed nicely in a Reedy category, namely the category of finite inhabited join-semilattices: we have a functor $i: \Omega_V \to \mathbf{SLat}_{\mathrm{fin}}^{\mathrm{inh}}$ sending the $n$-cube to the $n$-fold product of the poset $\{0 < 1\}$. While $\mathbf{SLat}_{\mathrm{fin}}^{\mathrm{inh}}$ is not itself elegant, it satisfies a relativized form of elegance with respect to the subcategory $\Omega_V$. Whereas elegance would require the Yoneda embedding $\mathcal{L}: \mathbf{SLat}_{\mathrm{fin}}^{\mathrm{inh}} \to \mathrm{PSh}(\mathbf{SLat}_{\mathrm{fin}}^{\mathrm{inh}})$ to preserve pushouts of spans of degeneracy maps, here it is the nerve $N_i := i^* \mathcal{L}: \mathbf{SLat}_{\mathrm{fin}}^{\mathrm{inh}} \to \mathrm{PSh}(\Omega_V)$ that preserves such pushouts. We say that $\mathbf{SLat}_{\mathrm{fin}}^{\mathrm{inh}}$ is elegant relative to $i$, or that $i$ is an elegant embedding.

We find that the useful properties of elegant Reedy categories can be extended, in an appropriately relativized form, to categories $\mathbf{C}$ with an elegant embedding $i: \mathbf{C} \to \mathbf{R}$ in a Reedy category. In particular, we show that any presheaf over $\mathbf{C}$ admits a homotopically well-behaved cellular decomposition whose cells are automorphism quotients of objects in the image of $N_i$. With these tools in hand, we are able to establish that the Quillen adjunctions relating $\widehat{\Omega}_V^{ty}$ and $\widehat{\Lambda}^{kq}$ are Quillen equivalences. We thus identify a cubical-type model structure presenting $\infty$-Gpd, compatible with a constructive interpretation of either HoTT or of cubical type theory with one connection.

## Outline

We begin in Section 2 with a brief review of model structures, Quillen equivalences, Reedy categories, and the Kan–Quillen model structure on simplicial sets. In Section 3, we present an improvement on the first part of [Sat17]: a series of increasingly specialized criteria under which candidate (cofibration, trivial fibration) and (trivial cofibration, fibration) factorization systems induce a model structure, culminating in a theorem tailored to models of type theory with universes.

¹A simpler map without a (split epi, mono) factorization in $\Omega_{\Lambda V}$ is $(x, y) \mapsto (x, x \vee y)$, but this is an idempotent and so admits such a factorization in the idempotent completion $\overline{\Omega}_{\Lambda V}$ (characterized in [Sat19, Theorem 2.1]). The aforementioned 3-cube endomap does not: it does have an (epi, mono) factorization in $\overline{\Omega}_{\Lambda V}$, but the left map does not split. It is the idempotent completion that counts when we consider whether elegant Reedy techniques apply.

²See Appendix A.1 for a proof that neither $\Omega_V$ nor its idempotent completion is Reedy.

2025/10/16 00:43