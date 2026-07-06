Relative Elegance and Cartesian Cubes with One Connection

61

Consider the set $S := \{011, 101, 110\} \subseteq L \subseteq [1]^3$. Let $v, v', v''$ be any pairwise distinct elements of $S$ and note that we have

$$(v \wedge_L v') \vee (v \wedge_L v'') = v \wedge_L (v' \vee v'') = v \wedge_L \top = v.$$

This implies the following.

- (a) $v \wedge_L v' \neq v \wedge_L v''$: otherwise we have $(v \wedge_L v') \vee (v \wedge_L v'') = v \wedge_L v''$ and thus $v = v \wedge_L v''$, but $v$ and $v''$ are incomparable.
- (b) $v \wedge_L v' \neq \bot$: otherwise we again have $(v \wedge_L v') \vee (v \wedge_L v'') = v \wedge_L v''$.

Thus the meets $011 \wedge_L 101, 011 \wedge_L 110$, and $011 \wedge_L 110$ are pairwise distinct and lie outside the image of $u$, which by a cardinality argument implies that $L$ is the whole of $[1]^3$.

The lowering map $f$ of our supposed factorization must then be $u$ itself; it remains to show that $u$ cannot be a lowering map. Consider the semilattice morphism $t: [1]^3 \to [2]$ defined by $t(x, y, z) := x \vee 2y \vee 2z$. We have the following commutative diagram in $\overline{\Omega}_v$, where $d_1$ and $s_1$ are the simplex face and degeneracy maps from Definition 2.22:

$$\begin{array}{c} [1]^3 \xrightarrow{t} [2] \xrightarrow{s_1} [1] \\ u \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ [1]^3 \xrightarrow{t} [2]. \end{array}$$

The face map $d_1$ is split monic and therefore a raising map. If $u$ were a lowering map, this square would have a diagonal lift. But as $t$ is surjective, there can be no diagonal $[1]^3 \to [1]$ making the lower triangle commute.

### A.2 Dedekind cubes

As mentioned in the introduction, it is an open question whether the cubical-type model structure for presheaves on the Dedekind cube category $\overline{\Omega}_{\wedge V}$ is equivalent to the Kan-Quillen model structure $\overline{\Delta}^{\mathrm{aq}}$; see Streicher and Weinberger [SW21] for further discussion. In this appendix, we show that $\overline{\Omega}_{\wedge V}$ supports no relatively elegant embedding in a Reedy category, thus that our argument for $\overline{\Omega}_V$ admits no naive adaptation to the two-connection case.

Definition A.2 The Dedekind cube category $\overline{\Omega}_{\wedge V}$ is the Lawvere theory of bounded distributive lattices.

$\overline{\Omega}_{\wedge V}$ admits an alternative description arising from the duality between finite bounded distributive lattices and finite posets [Wra93], analogous to the description of $\overline{\Omega}_V$ as a full subcategory of SLat:

Proposition A.3 $\overline{\Omega}_{\wedge V}$ is equivalent to the full subcategory of Pos consisting of posets of the form $[1]^n$ for $n \in \mathbb{N}$.

We will only need this latter description.

2025/10/16 00:43