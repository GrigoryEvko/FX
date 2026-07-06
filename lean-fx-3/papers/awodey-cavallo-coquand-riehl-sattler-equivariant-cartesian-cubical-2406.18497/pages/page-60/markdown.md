of cubical species and thus a composable pair of pullbacks of cubical sets

$$\begin{array}{c} U _ {\kappa} \cong \mathcal {F} ^ {\kappa} (\varpi) \longrightarrow \Gamma \mathbb {F} ^ {\kappa} (\Delta \varpi) \longrightarrow \Gamma \mathbb {F} ^ {\kappa} (\varpi) =: \Gamma \mathbb {U} _ {\kappa} \\ \psi_ {\varpi} \Biggl \downarrow \quad \text {   } \quad \Gamma \psi_ {\Delta \varpi} \Biggl \downarrow \quad \text {   } \quad \Gamma \psi_ {\varpi} \\ V _ {\kappa} \xrightarrow [ \eta ]{} \Gamma \Delta V _ {\kappa} \xrightarrow {} \Gamma \mathbb {V} _ {\kappa} \end{array}$$

showing that both definitions agree (cf. [Awo24, 12]).

By Remark 5.3.6 and Proposition 2.3.5:

**Proposition 5.3.7.** *The equivariant premodel structure on cubical sets has universes in the sense of Definition 2.3.6 for the equivariant fibrations given by the classifiers $\pi: \dot{U}_{\kappa} \to U_{\kappa}$ for sufficiently large inaccessible cardinals $\kappa$.* $\square$

With Propositions 5.3.7 and 5.3.2, we have satisfied the hypotheses of Proposition 3.5.5, so from Proposition 5.3.1 we may conclude:

**Proposition 5.3.8.** *The universes in the equivariant premodel structure on cubical sets are univalent.* $\square$

We now leverage the results of §3.6 to prove that the bases of these universe are equivariantly fibrant objects. Note, however, that in contrast to the analogous result for cubical species, this is not a direct consequence of Proposition 3.6.10.

**Proposition 5.3.9.** *The bases of the universal fibrations for the equivariant premodel structure on cubical sets are fibrant objects.*

*Proof.* As in the proof of Proposition 4.4.7, we can use Proposition 3.6.9 to show that $U$ is fibrant, though in a more subtle way. First, we again equip $U$ with the reflexive relation defined by the object of equivalences constructed by Lemma 3.5.1:

$$\begin{array}{c} U \\ \downarrow \\ U \xleftarrow [ s ]{} \operatorname {E q} (\dot {U}) \xrightarrow [ t ]{} U. \end{array}$$

The map $(s, t): \operatorname{Eq}(\dot{U}) \to U \times U$ is again a fibration by its construction. By univalence, Proposition 5.3.8, the map $t: \operatorname{Eq}(\dot{U}) \to U$ is a trivial fibration and in particular a fibration.

Now the equivariant premodel structure lacks an interval $I$ as required by Proposition 3.6.9, but by the definition of the equivariant fibrations, the images of the maps $(s, t): \operatorname{Eq}(\dot{U}) \to U \times U$ and $t: \operatorname{Eq}(\dot{U}) \to U$ under $\Delta$ are uniform fibrations in $\mathsf{cSet}^{\mathbb{E}}$, and we are trying to show that $\Delta U$ is uniformly fibrant. Since the interval (pre)model structure on cubical species does have such an interval, and the remaining hypotheses of Proposition 3.6.9 are also satisfied for the reflexive relation $\Delta \operatorname{Eq}(\dot{U}) \rightrightarrows \Delta U$, we can conclude that $\Delta U$ is indeed uniformly fibrant. Thus, $U$ is equivariantly fibrant. $\square$

By applying Lemma 3.7.2, we see that:

**Proposition 5.3.10.** *The equivariant premodel structure satisfies the fibration extension property.* $\square$

These results assemble into the main theorem of this section.

**Theorem 5.3.11.** *The category of cubical sets admits a Quillen model structure in which the cofibrations are the monomorphisms and the fibrations are the equivariant fibrations. This model is cylindrical and cartesian closed and satisfies the Frobenius condition, equivalence extension property, and fibration extension property. Moreover, it has univalent universes whose bases are fibrant objects.*

60