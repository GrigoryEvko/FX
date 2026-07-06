- the unit and counit of the adjunctions are weak equivalences on fibrant objects.

We now move to the case of a countably lextensive category $\mathcal{E}$. Despite the fact that the theorem concerns only the fibrant objects of $\mathfrak{s}_e\mathcal{E}$, the proof will depend on the homotopy theory of all, not necessarily fibrant, semisimplicial objects in $\mathcal{E}$. We define a general morphism of $\mathfrak{s}_e\mathcal{E}$ to be a weak equivalence if it has a fibrant replacement (as constructed from factorisations of Lemma 12.1) that is a pointwise weak equivalence in $\mathfrak{s}_e\mathcal{E}_{\mathrm{fib}}$. This is analogous to the characterisation of weak equivalences between simplicial objects in the model structure of Theorem 9.9. The weak equivalences, fibrations and cofibrations defined in this section do not form a model structure on $\mathfrak{s}_e\mathcal{E}$, but we can still prove that they are sufficiently well-behaved for our purposes. For example, the definition of weak equivalences immediately implies that trivial cofibrations are weak equivalences. On the other hand, not all trivial fibrations are weak equivalences.

**Remark 12.9.** If $\mathcal{E}$ is countably lextensive then $\mathfrak{s}_e\mathcal{E}$ is a weak model category in the sense of [Hen18] with weak equivalences, fibrations and cofibrations as defined above. This can be derived from (the dual of) [Hen18, Proposition 2.3.3] and properties of the classes established in this section. In fact, as every object of $\mathfrak{s}_e\mathcal{E}$ is cofibrant, this is even a right semi-model category, as long as we use the definition of a semi-model category in [Fre09] and not that in [Spi01] (see [Hen20, Section 3] for the explanation of differences between the two definitions). Our discussion of homotopy theory of semisimplicial objects can be phrased both in terms of this weak model structure or right semi-model structure. However, we prefer to provide more elementary arguments to make this section more self-contained.

**Proposition 12.10.** *If $\mathcal{E}$ has finite coproducts, then the forgetful functor $\mathfrak{s}\mathcal{E} \to \mathfrak{s}_e\mathcal{E}$ has a left adjoint. It is given by*

$$(LX)_n = \coprod_{[n] \to [m]} X_m$$

*where the coproduct is over all degeneracy operators $[n] \to [m]$ in $\Delta$.*

*Proof.* The functor $L$ is the left Kan extension along $\Delta_+ \to \Delta$. If it can be computed pointwise, it is given by the formula

$$(LX)_n = \underset{[n] \to [m]}{\operatorname{colim}} X_m$$

where the colimit is taken over the comma category $[n] \downarrow \Delta_+^{\mathrm{op}}$. (Its objects are arbitrary simplicial operators $[n] \to [m]$, but its morphisms are just the face operators.) It follows from the existence of the degeneracy/face unique factorisation system in $\Delta$ that the discrete category of degeneracy operators $[n] \to [m]$ is cofinal in this category. Hence the colimit above can be rewritten as the coproduct in the statement of the proposition. Thus if $\mathcal{E}$ has finite coproducts, this colimit exists which concludes the proof.

**Lemma 12.11.** *The free functor $L: \mathfrak{s}_e\mathcal{E} \to \mathfrak{s}\mathcal{E}$ preserves cofibrations and trivial cofibrations.*

*Proof.* It can be checked easily that the natural transformation from the initial functor to $L$ satisfies the assumptions of Lemma 3.20, so it is enough to verify that $L$ sends the generating cofibrations and trivial cofibrations to cofibrations and trivial cofibrations, respectively. These generators are of the form $\underline{\Lambda}_+[n] \mapsto \underline{\Delta}_+[n]$ or $\underline{\partial\Delta}_+[n] \mapsto \underline{\Delta}_+[n]$ the image by $L$ is computed as in Set, thus giving $\underline{\Lambda}^k[n] \mapsto \underline{\Delta[n]}$ or $\underline{\partial\Delta[n]} \mapsto \underline{\Delta[n]}$, i.e., the generating cofibrations and trivial cofibrations in $\mathfrak{s}\mathcal{E}$.

60