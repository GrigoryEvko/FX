4.1.4. **Proposition :** *Let $\mathcal{H}$ be a pre-Banach locale, then its completion $\widetilde{\mathcal{H}}$ is naturally endowed with a structure of Banach locale such that the map $\mathcal{H} \rightarrow \widetilde{\mathcal{H}}$ is a linear isometric map.*

# **Proof :**

Everything comes more or less immediately from 3.3.11 for the construction of operations and from 3.2.3 and 3.2.4 for the verification of the axioms:

Indeed, as $\mathcal{H} \times \mathcal{H}$ has a fiberwise dense image in $\widetilde{\mathcal{H}} \times \widetilde{\mathcal{H}}$, the canonical (uniform) map $p : \mathcal{H} \times \mathcal{H} \rightarrow \mathcal{H} \rightarrow \widetilde{\mathcal{H}}$ extends into a map $\widetilde{\mathcal{H}} \times \widetilde{\mathcal{H}} \rightarrow \widetilde{\mathcal{H}}$. Similarly, the opposite map $m : \mathcal{H} \rightarrow \mathcal{H}$ is isometric and hence extends into a map $m : \widetilde{\mathcal{H}} \rightarrow \widetilde{\mathcal{H}}$ and one checks all the group axioms on $\widetilde{\mathcal{H}}$ because they hold in $\mathcal{H}$, that $\widetilde{\mathcal{H}}$ is metric and that $\mathcal{H}^n$ has a fiberwise dense image in $\widetilde{\mathcal{H}}^n$.

The action of the locale of complex numbers on $\widetilde{\mathcal{H}}$ is obtained in the same way: for each $\lambda \in \mathcal{Q}[i]$ the multiplication by $\lambda$ is a uniform map $\mathcal{H} \rightarrow \mathcal{H}$ and hence extends into a map $\widetilde{\mathcal{H}} \rightarrow \mathcal{H}$, giving a map $\mathcal{Q}[i] \times \widetilde{\mathcal{H}} \rightarrow \widetilde{\mathcal{H}}$ and all the axioms of compatibility with the group law are also satisfied by a density argument.

Finally, we already know that there is a distance function on $\widetilde{\mathcal{H}}$ we only have to check that $\|x\| = d(0, x)$ is a norm and that $d(x, y) = \|x - y\|$. But this also immediately comes from a density argument by 3.2.4. $\square$

4.1.5. **Corollary :** *Banach locale are complete metric locales.*

# **Proof :**

Let $\mathcal{H}$ be a Banach locale, in particular $\mathcal{H}$ is a metric locale and hence by 3.2.2 it identifies with a sublocale of $\widetilde{\mathcal{H}}$. More precisely, as the inclusion is a linear map, $\mathcal{H}$ identifies with a localic subgroup of a locally positive localic group $\widetilde{\mathcal{H}}$, hence thanks to the constructive version of the closed subgroups theorem proved by P.T. Johnstone in [11], one concludes that $\mathcal{H}$ is fiberwise closed (weakly closed in the terminology of [11]) in $\widetilde{\mathcal{H}}$ and hence is also complete (see the remark at the end of 3.3.12). $\square$

4.1.6. In particular, the action of $\mathcal{Q}[i]$ on a Banach locale extends to an action of its completion $\mathbb{C}$. Indeed (assuming that $\mathcal{H}$ is complete), the map $B_n 0 \times \mathcal{Q}[i] \rightarrow \mathcal{H}$ is uniform (it is $n$-Lipschitz) and hence it extends into $\overline{B_n 0} \times \mathbb{C} \rightarrow \mathcal{H}$. One has a family of compatible maps $B_n 0 \times \mathbb{C} \rightarrow \mathcal{H}$ which gives rise to a map $\mathcal{H} \times \mathbb{C} \rightarrow \mathcal{H}$.

4.1.7. Similarly to what is done in section 3.6, a pre-Banach space in the usual (constructive) sense is exactly the same as a pre-Banach locale whose underlying locale is a discrete topological space. To such a Banach space one can associate its completion which is going to be a Banach locale. Conversely to any Banach locale one can associate its space of points which is a Banach space, and these

53