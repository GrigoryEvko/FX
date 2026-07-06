**Proposition 4.4.5.** *The interval premodel structure on cubical species has universes in the sense of Definition 2.3.6 for the fibrations given by the classifiers $\pi: \mathbb{U}_\kappa \to \mathbb{U}_\kappa$ for sufficiently large inaccessible cardinals $\kappa$.* □

With Propositions 4.4.5 and 4.4.2, we have satisfied the hypotheses of Proposition 3.5.5, so from Proposition 4.4.1 we may conclude:

**Proposition 4.4.6.** *The universes in the interval premodel structure on cubical species are univalent.* □

By Definition 4.3.12 and Theorem 4.3.14, our fibrations are characterized in the way demanded by Proposition 3.6.9. Thus Proposition 3.6.10 applies and we may conclude:

**Proposition 4.4.7.** *The bases of the universal fibrations for the interval premodel structure on cubical species are fibrant objects.* □

By applying Lemma 3.7.2, we see that:

**Proposition 4.4.8.** *The interval premodel structure satisfies the fibration extension property.* □

These results assemble into the main theorem of this section.

**Theorem 4.4.9.** *The category of cubical species admits a Quillen model structure in which the cofibrations are the monomorphisms and the fibrations are the unbiased fibrations of 3.6.7(ii). This model is cylindrical and cartesian closed and satisfies the Frobenius condition, equivalence extension property, and fibration extension property. Moreover, it has univalent universes whose bases are fibrant objects.*

*Proof.* The only result of the statement that we have not yet proven is the fact that the interval premodel structure is in fact a model structure, but this follows formally from Proposition 3.7.3, by Proposition 4.4.8 and the fact that all objects are cofibrant. □

Thus, the interval model structure on the topos of cubical species is a model of homotopy type theory.

## 5. THE EQUIVARIANT MODEL STRUCTURE ON CUBICAL SETS

Having established a model structure on the category of cubical species, we now transfer it to a model structure, and a model of homotopy type theory, on the category cSet of cartesian cubical sets. The results of §4 both provide conceptual justification for the constructions in this section and also simplify many of the proofs.

In §5.1, we introduce an adjoint triple of functors between cubical sets and cubical species and establish the basic properties of these functors. In §5.2, we lift the cylindrical premodel structure from cubical species to cubical sets by using the constant diagram functor $\Delta: \text{cSet} \to \text{cSet}^\times$ to create the fibrations and trivial fibrations. We give explicit characterizations of these classes that reveal that the trivial fibrations are again the trivial fibrations of §2.2, while the fibrations are novel, defining a class of maps we call *equivariant fibrations*.

As the cofibrations in the resulting premodel structure on cubical sets are again the monomorphisms, these are created by the functor $\Delta$ as well, but the trivial cofibrations and weak equivalences are not, so in particular it will again take work to prove that the right-lifted premodel structure in fact defines a Quillen model structure. This is achieved in §5.3, which proves the analogue of Theorem 4.4.9 for cubical sets. For some of the constituent results, the proofs are formal, specializing the results of §3; for other statements, the results of that section do not apply and we leverage the results of §4 instead.

52